use buf_trait::Buf;

use crate::raw::nodes;
use crate::raw::nodes::Index;
use crate::raw::Prefix;
use crate::raw::RawTrie;

use super::entries::Entries;

/// An iterator over all values of a [`Trie`][crate::Trie] whose keys start with
/// a particular prefix.
///
/// See [`Trie::prefixes()`][crate::Trie::prefixes].
pub struct Prefixes<'a, 'key, K: Buf + ?Sized, V, I: Index> {
  prefix: Prefix<'a>,
  suffix: &'key [u8],
  data: &'a Entries<K, V, I>,
  prefixes: nodes::Prefixes<'a, 'key, I>,
}

impl<'a, 'key, K: Buf + ?Sized, V, I: Index> Prefixes<'a, 'key, K, V, I> {
  pub(crate) fn new(
    trie: &'a RawTrie<K, V, I>,
    prefix: Prefix<'a>,
    suffix: &'key K,
  ) -> Self {
    Self {
      prefix,
      suffix: suffix.as_bytes(),
      prefixes: trie.nodes.prefixes(prefix.node(), suffix.as_bytes()),
      data: &trie.data,
    }
  }
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iterator for Prefixes<'a, '_, K, V, I> {
  type Item = (&'a K, &'a V);

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      let (_, Some(next), last) = self.prefixes.next()? else { continue };
      let Some((key, value)) = self.data.get(next) else { continue };

      let key_rest = &key.as_bytes()[self.prefix.len()..];
      if last && !self.suffix.starts_with(key_rest) {
        return None;
      }

      return Some((key, value));
    }
  }
}

/// A mutable iterator over all values of a [`Trie`][crate::Trie] whose keys
/// start with a particular prefix.
///
/// See [`Trie::prefixes_mut()`][crate::Trie::prefixes_mut].
pub struct PrefixesMut<'a, 'key, K: Buf + ?Sized, V, I: Index> {
  prefix: Prefix<'a>,
  suffix: &'key [u8],
  data: &'a Entries<K, V, I>,
  prefixes: nodes::Prefixes<'a, 'key, I>,
}

impl<'a, 'key, K: Buf + ?Sized, V, I: Index> PrefixesMut<'a, 'key, K, V, I> {
  pub(crate) fn new(
    trie: &'a mut RawTrie<K, V, I>,
    prefix: Prefix<'a>,
    suffix: &'key K,
  ) -> Self {
    Self {
      prefix,
      suffix: suffix.as_bytes(),
      prefixes: trie.nodes.prefixes(prefix.node(), suffix.as_bytes()),
      data: &mut trie.data,
    }
  }
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iterator
  for PrefixesMut<'a, '_, K, V, I>
{
  type Item = (&'a K, &'a mut V);

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      let (_, Some(next), last) = self.prefixes.next()? else { continue };

      let entry = unsafe {
        // SAFETY: nodes::Prefixes will never repeat the indices it produces.
        self.data.get_mut_may_alias(next)
      };
      let Some((key, value)) = entry else { continue };

      let key_rest = &key.as_bytes()[self.prefix.len()..];
      if last && !self.suffix.starts_with(key_rest) {
        return None;
      }

      return Some((key, value));
      /*unsafe {
        // SAFETY:
        // We never mutate through self.data.keys, so we can produce arbitrary
        // immutable references to it without problems, so the first cast
        // is safe.
        //
        // Each node in the trie points to a *unique* entry, so the entry
        // pointer is not duplicated elsewhere, so the second cast is safe.
        let key = &*(key as *const K);
        let value = &mut *(value as *mut V);
        return Some((key, value));
      }*/
    }
  }
}

/// An in-order iterator over all values of a [`Trie`][crate::Trie].
///
/// See [`Trie::mut()`][crate::Trie::iter].
pub struct Iter<'a, K: Buf + ?Sized, V, I: Index> {
  data: &'a Entries<K, V, I>,
  dfs: nodes::Dfs<'a, I>,
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iter<'a, K, V, I> {
  pub(crate) fn new(trie: &'a RawTrie<K, V, I>, prefix: Prefix<'a>) -> Self {
    Self {
      dfs: trie.nodes.dfs(prefix.node()),
      data: &trie.data,
    }
  }
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iterator for Iter<'a, K, V, I> {
  type Item = (&'a K, &'a V);

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      // The outer Option indicates "end of iteration", the inner option
      // whether this represents an actual data element.
      let Some(next) = self.dfs.next()? else { continue };
      let entry = self.data.get(next);

      if entry.is_some() {
        return entry;
      }
    }
  }
}

/// An in-order mutable iterator over all values of a [`Trie`][crate::Trie].
///
/// See [`Trie::iter_mut()`][crate::Trie::iter_mut].
pub struct IterMut<'a, K: Buf + ?Sized, V, I: Index> {
  data: &'a Entries<K, V, I>,
  dfs: nodes::Dfs<'a, I>,
}

impl<'a, K: Buf + ?Sized, V, I: Index> IterMut<'a, K, V, I> {
  pub(crate) fn new(
    trie: &'a mut RawTrie<K, V, I>,
    prefix: Prefix<'a>,
  ) -> Self {
    Self {
      dfs: trie.nodes.dfs(prefix.node()),
      data: &mut trie.data,
    }
  }
}

impl<'a, K: Buf + ?Sized, V, I: Index> Iterator for IterMut<'a, K, V, I> {
  type Item = (&'a K, &'a mut V);

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      // The outer Option indicates "end of iteration", the inner option
      // whether this represents an actual data element.
      let Some(next) = self.dfs.next()? else { continue };
      let entry = unsafe {
        // SAFETY: nodes::Prefixes will never repeat the indices it produces.
        self.data.get_mut_may_alias(next)
      };

      if entry.is_some() {
        return entry;
      }
    }
  }
}
