use std::marker::PhantomData;

use buf_trait::Buf;

use crate::raw::nodes;
use crate::raw::nodes::Index;
use crate::raw::nodes::Node;
use crate::raw::RawTrie;
use crate::Sub;

use super::entries::Entries;

/// An iterator over all values of a [`Trie`][crate::Trie] whose keys start with
/// a particular prefix.
///
/// See [`Trie::prefixes()`][crate::Trie::prefixes].
pub struct Prefixes<'a, 'key, K: Buf + ?Sized, V, I: Index> {
  root: Node<I>,
  key: &'key [u8],
  data: &'a Entries<V, I>,
  prefixes: nodes::Prefixes<'a, 'key, I>,
  _ph: PhantomData<fn() -> &'a K>,
}

impl<'a, 'key, K: Buf + ?Sized, V, I: Index> Prefixes<'a, 'key, K, V, I> {
  pub(crate) fn new(
    trie: &'a RawTrie<K, V, I>,
    root: Node<I>,
    key: &'key K,
  ) -> Self {
    let key = key.as_bytes();
    Self {
      root,
      key,
      prefixes: trie.nodes.prefixes(root, key),
      data: &trie.data,
      _ph: PhantomData,
    }
  }
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iterator for Prefixes<'a, '_, K, V, I> {
  type Item = (&'a K, &'a V);

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      let (node, Some(next), last) = self.prefixes.next()? else {
        continue;
      };
      let Some((key_len, value)) = self.data.get(next) else {
        continue;
      };

      let key = self.prefixes.nodes.key(node, Some(key_len));
      let key_rest = &key.as_bytes()[self.root.depth..];
      if last && !self.key.starts_with(key_rest) {
        return None;
      }

      unsafe {
        // SAFETY: This is a trie element, and not an intermediate, so this
        // is key is not "torn".
        return Some((K::from_bytes(key), value));
      }
    }
  }
}

/// A mutable iterator over all values of a [`Trie`][crate::Trie] whose keys
/// start with a particular prefix.
///
/// See [`Trie::prefixes_mut()`][crate::Trie::prefixes_mut].
pub struct PrefixesMut<'a, 'key, K: Buf + ?Sized, V, I: Index> {
  root: Node<I>,
  key: &'key [u8],
  data: &'a Entries<V, I>,
  prefixes: nodes::Prefixes<'a, 'key, I>,
  _ph: PhantomData<fn() -> (&'a K, &'a mut V)>,
}

impl<'a, 'key, K: Buf + ?Sized, V, I: Index> PrefixesMut<'a, 'key, K, V, I> {
  pub(crate) fn new(
    trie: &'a mut RawTrie<K, V, I>,
    root: Node<I>,
    key: &'key K,
  ) -> Self {
    let key = key.as_bytes();
    Self {
      root,
      key,
      prefixes: trie.nodes.prefixes(root, key),
      data: &mut trie.data,
      _ph: PhantomData,
    }
  }
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iterator
  for PrefixesMut<'a, '_, K, V, I>
{
  type Item = (&'a K, &'a mut V);

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      let (node, Some(next), last) = self.prefixes.next()? else {
        continue;
      };

      let entry = unsafe {
        // SAFETY: nodes::Prefixes will never repeat the indices it produces.
        self.data.get_mut_may_alias(next)
      };
      let Some((key_len, value)) = entry else { continue };

      let key = self.prefixes.nodes.key(node, Some(key_len));
      let key_rest = &key.as_bytes()[self.root.depth..];
      if last && !self.key.starts_with(key_rest) {
        return None;
      }

      unsafe {
        // SAFETY: This is a trie element, and not an intermediate, so this
        // is key is not "torn".
        return Some((K::from_bytes(key), value));
      }
    }
  }
}

/// A depth-first iterator over all nonempty subtries of a
/// [`Trie`][crate::Trie].
///
/// See [`Trie::subs()`][crate::Trie::subs].
pub struct Subs<'a, K: Buf + ?Sized, V, I: Index> {
  raw: &'a RawTrie<K, V, I>,
  dfs: nodes::Dfs<'a, I>,
  _ph: PhantomData<fn() -> (&'a K, &'a V)>,
}

impl<'a, K: Buf + ?Sized, V, I: Index> Subs<'a, K, V, I> {
  pub(crate) fn new(trie: &'a RawTrie<K, V, I>, root: Node<I>) -> Self {
    Self {
      raw: trie,
      dfs: trie.nodes.dfs(root),
      _ph: PhantomData,
    }
  }
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iterator for Subs<'a, K, V, I> {
  type Item = Sub<'a, K, V, I>;

  fn next(&mut self) -> Option<Self::Item> {
    if let Some(next) = self.dfs.next() {
      return Some(Sub { raw: self.raw, node: next });
    }

    None
  }
}

/// An in-order iterator over all values of a [`Trie`][crate::Trie].
///
/// See [`Trie::iter()`][crate::Trie::iter].
pub struct Iter<'a, K: Buf + ?Sized, V, I: Index> {
  data: &'a Entries<V, I>,
  dfs: nodes::Dfs<'a, I>,
  _ph: PhantomData<fn() -> &'a K>,
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iter<'a, K, V, I> {
  pub(crate) fn new(trie: &'a RawTrie<K, V, I>, root: Node<I>) -> Self {
    Self {
      dfs: trie.nodes.dfs(root),
      data: &trie.data,
      _ph: PhantomData,
    }
  }
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iterator for Iter<'a, K, V, I> {
  type Item = (&'a K, &'a V);

  fn next(&mut self) -> Option<Self::Item> {
    while let Some(next) = self.dfs.next() {
      let Some(idx) = self.dfs.nodes.get(next) else {
        continue;
      };
      let Some((key_len, value)) = self.data.get(idx) else {
        continue;
      };
      if key_len != next.depth {
        continue;
      }

      let key = self.dfs.nodes.key(next, Some(key_len));
      unsafe {
        // SAFETY: This is a trie element, and not an intermediate, so this
        // is key is not "torn".
        return Some((K::from_bytes(key), value));
      }
    }

    None
  }
}

/// An in-order mutable iterator over all values of a [`Trie`][crate::Trie].
///
/// See [`Trie::iter_mut()`][crate::Trie::iter_mut].
pub struct IterMut<'a, K: Buf + ?Sized, V, I: Index> {
  data: &'a Entries<V, I>,
  dfs: nodes::Dfs<'a, I>,
  _ph: PhantomData<fn() -> (&'a K, &'a mut V)>,
}

impl<'a, K: Buf + ?Sized, V, I: Index> IterMut<'a, K, V, I> {
  pub(crate) fn new(trie: &'a mut RawTrie<K, V, I>, root: Node<I>) -> Self {
    Self {
      dfs: trie.nodes.dfs(root),
      data: &mut trie.data,
      _ph: PhantomData,
    }
  }
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iterator for IterMut<'a, K, V, I> {
  type Item = (&'a K, &'a mut V);

  fn next(&mut self) -> Option<Self::Item> {
    while let Some(next) = self.dfs.next() {
      let Some(idx) = self.dfs.nodes.get(next) else {
        continue;
      };
      let entry = unsafe {
        // SAFETY: nodes::Prefixes will never repeat the indices it produces.
        self.data.get_mut_may_alias(idx)
      };

      let Some((key_len, value)) = entry else {
        continue;
      };
      if key_len != next.depth {
        continue;
      }

      let key = self.dfs.nodes.key(next, Some(key_len));
      unsafe {
        // SAFETY: This is a trie element, and not an intermediate, so this
        // is key is not "torn".
        return Some((K::from_bytes(key), value));
      }
    }

    None
  }
}
