//! `twie` \[twaɪ\] - Fast, compressed prefix tries.
//!
//! This crate provides a [`Trie`] type that implements an associative container
//! with slice-like keys. It has the following properties.
//!
//! - Most one-shot operations are worst-case O(n), where n is the length of
//!   the key in bytes. This may require at most 2n tree hops, but the internal
//!   representation tries to minimize this where possible.
//!
//! - Finding all prefixes of a string that are in the trie is also O(n). These
//!   prefixes are provided in order.
//!
//! - Building a trie out of, e.g., an iterator is quadratic.
//!
//! - Subtries of the whole trie (i.e. all entries with some particular prefix)
//!   can be operated on like regular tries (insertion is only supported from
//!   the root, unfortunately).
//!
//! - Memory for storing keys is shared.
//!
//! - The trie's internal indexing type is configurable, which allows trading
//!   off maximum key size for shrinking the size of tree nodes, and thus,
//!   memory usage.
//!
//! ```
//! # use twie::Trie;
//! let words = Trie::<str, i32>::from([
//!   ("poise", 0),
//!   ("poison", 1),
//!   ("poisonous", 2),
//!   ("poison #9", 3),
//! ]);
//! # eprintln!("{}", words.dump());
//!
//! assert_eq!(
//!   words.prefixes("poisonous snake").map(|(k, _)| k).collect::<Vec<_>>(),
//!   ["poison", "poisonous"],
//! )
//! ```
//!
//! <details>
//! <summary>Here's a pretty diagram of what this trie looks like in memory.</summary>
#![doc = concat!("<pre><code>", include_str!("poison_trie.txt"),"</code></pre>")]
//! </details>

use std::fmt;
use std::mem;

use crate::raw::Prefix;
use crate::raw::RawTrie;

pub use crate::raw::iter::Iter;
pub use crate::raw::iter::IterMut;
pub use crate::raw::iter::Prefixes;
pub use crate::raw::iter::PrefixesMut;
pub use crate::raw::nodes::Index;

mod impls;
mod raw;

mod sealed {
  pub struct Seal;
}

pub use buf_trait::Buf;
use byteyarn::YarnBox;

/// An radix prefix trie, optimized for searching for known prefixes of a
/// string (for a fairly open-ended definition of "string").
///
/// `K` can be anything that implements [`Buf`], which is anything that is kind
/// of like a slice. Most commonly, you will see `Trie<str, V>` or
/// `Trie<[u8], V>`, but `Trie<[u16], V>` works fine too.
///
/// The extra `I` parameter can be any unsigned integer type; it specifies the
/// size of the trie's internal indices. `u32` is a "good reasonable default".
/// This type essentially bounds how big the strings inside it can be.
/// Insertion operations will panic if indices run out.
///
/// The core implementation is a sixteen-trie (i.e. nybbles of the key are used
/// to index into children) with several compactness optimizations.
///
/// Entries can be inserted into the trie, but not removed; this type of trie
/// is designed to be built once and accessed often.
pub struct Trie<K: Buf + ?Sized, V, I: Index = u32> {
  raw: RawTrie<K, V, I>,
}

impl<K: Buf + ?Sized, V, I: Index> Trie<K, V, I> {
  /// Creates a new, empty trie.
  pub fn new() -> Self {
    Self {
      raw: RawTrie::new(),
    }
  }

  /// Converts this trie into a subtrie reference.
  ///
  /// This function is useful for passing the whole trie in as a subtrie when
  /// writing `trie.sub("")` is inconvenient.
  #[inline]
  pub fn as_ref(&self) -> Sub<K, V, I> {
    Sub {
      prefix: Prefix::ROOT,
      raw: &self.raw,
    }
  }

  /// Converts this trie into a mutable subtrie reference.
  ///
  /// This function is useful for passing the whole trie in as a subtrie when
  /// writing `trie.sub_mut("")` is inconvenient.
  #[inline]
  pub fn as_mut(&mut self) -> SubMut<K, V, I> {
    SubMut {
      prefix: Prefix::ROOT,
      raw: &mut self.raw,
    }
  }

  /// Finds the element with the given key, if present.
  ///
  /// Note that this function finds matches byte-for-byte, but according to
  /// a `PartialEq` implementation.
  ///
  /// ```
  /// # use twie::Trie;
  /// let trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(trie.get("foobar"), Some(&64));
  /// assert_eq!(trie.get("foobaz"), None);
  /// ```
  #[inline]
  pub fn get(&self, key: &K) -> Option<&V> {
    self.as_ref().get(key)
  }

  /// Finds the element with the given key, if present.
  ///
  /// Note that this function finds matches byte-for-byte, but according to
  /// a `PartialEq` implementation.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(trie.get_mut("foobar"), Some(&mut 64));
  /// assert_eq!(trie.get_mut("foobaz"), None);
  /// ```
  #[inline]
  pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
    self.as_mut().get_mut(key)
  }

  /// Finds the entry with the longest byte-wise prefix of `key`. This will
  /// always succeed if an empty key is present in the trie.
  ///
  /// ```
  /// # use twie::Trie;
  /// let trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(trie.longest_prefix("foobar"), Some(("foobar", &64)));
  /// assert_eq!(trie.longest_prefix("foobaz"), Some(("foo", &32)));
  /// assert_eq!(trie.longest_prefix("fog"), None);
  /// ```
  #[inline]
  pub fn longest_prefix(&self, key: &K) -> Option<(&K, &V)> {
    self.as_ref().longest_prefix(key)
  }

  /// Finds the entry with the longest byte-wise prefix of `key`. This will
  /// always succeed if an empty key is present in the trie.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(trie.longest_prefix_mut("foobar"), Some(("foobar", &mut 64)));
  /// assert_eq!(trie.longest_prefix_mut("foobaz"), Some(("foo", &mut 32)));
  /// assert_eq!(trie.longest_prefix_mut("fog"), None);
  /// ```
  #[inline]
  pub fn longest_prefix_mut(&mut self, key: &K) -> Option<(&K, &mut V)> {
    self.as_mut().longest_prefix_mut(key)
  }

  /// Creates a subtrie view for the given key.
  ///
  /// Subtries can be used for accessing part of the tree under a prefix, and
  /// offer all of the `&self` operations of a trie.
  ///
  /// ```
  /// # use twie::Trie;
  /// let trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub("foo");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.get("bar"), Some(&64));
  /// ```
  #[inline]
  pub fn sub<'a>(&'a self, key: &'a K) -> Sub<'a, K, V, I> {
    Sub {
      prefix: Prefix::new(&self.raw, &Prefix::ROOT, key.as_bytes()),
      raw: &self.raw,
    }
  }

  /// Creates a mutable subtrie view for the given key.
  ///
  /// Mutable subtries can be used for accessing part of the tree under a
  /// prefix, and offer all of the `&mut self` operations of a trie, except the
  /// ones that mutate.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub_mut("foo");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.get_mut("bar"), Some(&mut 64));
  /// ```
  #[inline]
  pub fn sub_mut<'a>(&'a mut self, key: &'a K) -> SubMut<'a, K, V, I> {
    SubMut {
      prefix: Prefix::new(&self.raw, &Prefix::ROOT, key.as_bytes()),
      raw: &mut self.raw,
    }
  }

  /// Returns an iterator over all prefixes of `key` present in the trie, in
  /// lexicographic order. [`Trie::get()`] and [`Trie::longest_prefix()`] are
  /// implemented in terms of this.
  ///
  /// ```
  /// # use twie::Trie;
  /// let trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// let prefixes = trie.prefixes("foobar").collect::<Vec<_>>();
  /// assert_eq!(prefixes, vec![("foo", &32), ("foobar", &64)]);
  ///
  /// let prefixes = trie.prefixes("foob").collect::<Vec<_>>();
  /// assert_eq!(prefixes, vec![("foo", &32)]);
  ///
  /// let prefixes = trie.prefixes("bar").collect::<Vec<_>>();
  /// assert_eq!(prefixes, vec![]);
  /// ```
  #[inline]
  pub fn prefixes<'key>(&self, key: &'key K) -> Prefixes<'_, 'key, K, V, I> {
    self.as_ref().prefixes(key)
  }

  /// Like [`Trie::prefixes()`], but the references are mutable.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// let prefixes = trie.prefixes_mut("foobar").collect::<Vec<_>>();
  /// assert_eq!(prefixes, vec![("foo", &mut 32), ("foobar", &mut 64)]);
  ///
  /// let prefixes = trie.prefixes_mut("foob").collect::<Vec<_>>();
  /// assert_eq!(prefixes, vec![("foo", &mut 32)]);
  ///
  /// let prefixes = trie.prefixes_mut("bar").collect::<Vec<_>>();
  /// assert_eq!(prefixes, vec![]);
  /// ```
  #[inline]
  pub fn prefixes_mut<'key>(
    &mut self,
    key: &'key K,
  ) -> PrefixesMut<'_, 'key, K, V, I> {
    self.as_mut().prefixes_mut(key)
  }

  /// Returns an iterator over the whole trie, in lexicographic order.
  ///
  /// This function needs to allocate space that is O(m) where m is the length
  /// of the longest key in the trie.
  ///
  /// ```
  /// # use twie::Trie;
  /// let trie: Trie<_, _> = [("foobaz", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(
  ///   trie.iter().collect::<Vec<_>>(),
  ///   vec![("foobar", &64), ("foobaz", &32)],
  /// );
  /// ```
  #[inline]
  pub fn iter(&self) -> Iter<'_, K, V, I> {
    self.as_ref().iter()
  }

  /// Like [`Trie::iter()`], but the references are mutable.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foobaz", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(
  ///   trie.iter_mut().collect::<Vec<_>>(),
  ///   vec![("foobar", &mut 64), ("foobaz", &mut 32)],
  /// );
  /// ```
  #[inline]
  pub fn iter_mut(&mut self) -> IterMut<'_, K, V, I> {
    self.as_mut().iter_mut()
  }

  /// Inserts a new key into the trie, returning the previous occupant if one
  /// was present.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(trie.insert("foo", 42), Some(32));
  /// assert_eq!(trie.insert("foob", 42), None);
  ///
  /// assert_eq!(trie.get("foo"), Some(&42));
  /// assert_eq!(trie.get("foob"), Some(&42));
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if the trie runs out of indices while inserting.
  #[inline]
  pub fn insert<'a>(
    &mut self,
    key: impl Into<YarnBox<'a, K>>,
    value: V,
  ) -> Option<V>
  where
    K: 'a,
  {
    let mut value = Some(value);
    let ptr = self.get_or_insert_with(key, || value.take().unwrap());
    value.map(|v| mem::replace(ptr, v))
  }

  /// Gets a key, or, if it's not present, creates a new entry with the given
  /// value.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(trie.get_or_insert("foo", 42), &mut 32);
  /// assert_eq!(trie.get_or_insert("foob", 42), &mut 42);
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if the trie runs out of indices while inserting.
  #[inline]
  pub fn get_or_insert<'a>(
    &mut self,
    key: impl Into<YarnBox<'a, K>>,
    value: V,
  ) -> &mut V
  where
    K: 'a,
  {
    self.get_or_insert_with(key, || value)
  }

  /// Like [`Trie::get_or_insert()`], but inserts the default value.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(trie.get_or_insert_default("foo"), &mut 32);
  /// assert_eq!(trie.get_or_insert_default("foob"), &mut 0);
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if the trie runs out of indices while inserting.
  #[inline]
  pub fn get_or_insert_default<'a>(
    &mut self,
    key: impl Into<YarnBox<'a, K>>,
  ) -> &mut V
  where
    K: 'a,
    V: Default,
  {
    self.get_or_insert_with(key, Default::default)
  }

  /// Like [`Trie::get_or_insert()`], but takes a callback that is only called
  /// if the entry is empty.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(trie.get_or_insert_with("foo", || unreachable!()), &mut 32);
  /// assert_eq!(trie.get_or_insert_with("foob", || 0), &mut 0);
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if the trie runs out of indices while inserting.
  #[inline]
  pub fn get_or_insert_with<'a>(
    &mut self,
    key: impl Into<YarnBox<'a, K>>,
    value: impl FnOnce() -> V,
  ) -> &mut V
  where
    K: 'a,
  {
    let key = key.into();
    let key_len = key.as_bytes().len();
    unsafe {
      let idx = self
        .raw
        .mutate(&mut { Prefix::ROOT }, key.into_bytes())
        .unwrap();

      self.raw.data.init(idx, key_len, value)
    }
  }

  /// Looks up a key: if it is not in the trie, it inserts it, using `on_insert`
  /// to create the value; otherwise, calls `on_update` on it.
  ///
  /// Exactly one of the callbacks will be called.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  ///
  /// assert_eq!(
  ///   trie.insert_or_update(
  ///     "foo",
  ///     || unreachable!(),
  ///     |slot| *slot /= 2,
  ///   ),
  ///   &mut 16,
  /// );
  ///
  /// assert_eq!(
  ///   trie.insert_or_update(
  ///     "foob",
  ///     || 42,
  ///     |slot| unreachable!(),
  ///   ),
  ///   &mut 42,
  /// );
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if the trie runs out of indices while inserting.
  #[inline]
  pub fn insert_or_update(
    &mut self,
    key: &K,
    on_insert: impl FnOnce() -> V,
    on_update: impl FnOnce(&mut V),
  ) -> &mut V {
    let mut called_it = false;
    let v = self.get_or_insert_with(key, || {
      called_it = true;
      on_insert()
    });

    if !called_it {
      on_update(v)
    }

    v
  }

  /// Dumps the trie's internal structure as a pretty string.
  ///
  /// The format of this string is unstable. Do not rely on it.
  ///
  /// # Panics
  ///
  /// Panics if this function is called in release mode.
  pub fn dump(&self) -> String
  where
    V: fmt::Debug,
  {
    self.as_ref().dump()
  }
}

/// A reference to some subtrie of a [`Trie`].
///
/// Subtrie views are created with [`Trie::sub()`] and similar functions.
///
/// This type is [`Copy`].
pub struct Sub<'a, K: Buf + ?Sized, V, I: Index = u32> {
  raw: &'a RawTrie<K, V, I>,
  prefix: Prefix<'a>,
}

impl<'a, K: Buf + ?Sized, V, I: Index> Sub<'a, K, V, I> {
  /// Finds the element with the given key, if present.
  ///
  /// Note that this function finds matches byte-for-byte, but according to
  /// a `PartialEq` implementation.
  ///
  /// See [`Trie::get()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub("foob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.get("ar"), Some(&64));
  /// assert_eq!(sub.get("foobar"), None);
  /// ```
  #[inline]
  pub fn get(self, key: &K) -> Option<&'a V> {
    let expected_len = key.byte_len() + self.prefix.len();
    self
      .prefixes(key)
      .last()
      .and_then(|(k, v)| (k.byte_len() == expected_len).then_some(v))
  }

  /// Finds the entry with the longest byte-wise prefix of `key`. This will
  /// always succeed if an empty key is present in the trie.
  ///
  /// See [`Trie::longest_prefix()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub("foob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.longest_prefix("ar"), Some(("foobar", &64)));
  /// assert_eq!(sub.longest_prefix("az"), None);
  /// ```
  #[inline]
  pub fn longest_prefix(self, key: &K) -> Option<(&'a K, &'a V)> {
    self.prefixes(key).last()
  }

  /// Creates a subtrie view for the given key.
  ///
  /// This is a subtrie of a subtrie, so the prefix the returned subtrie
  /// represents is that of `self` plus `key`.
  ///
  /// See [`Trie::sub()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub("fo");
  /// let sub = sub.sub("ob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.get("ar"), Some(&64));
  /// ```
  #[inline]
  pub fn sub<'b>(&'b self, key: &'b K) -> Sub<'b, K, V, I> {
    Sub {
      prefix: Prefix::new(self.raw, &self.prefix, key.as_bytes()),
      raw: self.raw,
    }
  }

  /// Returns an iterator over all prefixes of `key` present in the subtrie, in
  /// lexicographic order. Note that `key` is *relative* to the subtrie, so
  /// searching for `"bar"` in `sub("foo")` is like searching for
  /// "foobar" in the whole trie.
  ///
  /// See [`Trie::prefixes()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub("foob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// let prefixes = sub.prefixes("ars").collect::<Vec<_>>();
  /// assert_eq!(prefixes, vec![("foobar", &64)]);
  /// ```
  #[inline]
  pub fn prefixes<'key>(self, key: &'key K) -> Prefixes<'a, 'key, K, V, I> {
    Prefixes::new(self.raw, self.prefix, key)
  }

  /// Returns an iterator over this subtrie.
  ///
  /// See [`Trie::iter()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let trie: Trie<_, _> = [("foobaz", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub("foobar");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(
  ///   sub.iter().collect::<Vec<_>>(),
  ///   vec![("foobar", &64)],
  /// );
  /// ```
  #[inline]
  pub fn iter(self) -> Iter<'a, K, V, I> {
    Iter::new(self.raw, self.prefix)
  }

  /// Dumps the trie's internal structure as a pretty string.
  ///
  /// The format of this string is unstable. Do not rely on it.
  ///
  /// See [`Trie::dump()`].
  ///
  /// # Panics
  ///
  /// Panics if this function is called in release mode.
  pub fn dump(self) -> String
  where
    V: fmt::Debug,
  {
    assert!(
      cfg!(debug_assertions),
      "dump() can only be called in debug mode"
    );
    raw::dump(self.raw, &self.prefix)
  }
}

/// A reference to some subtrie of a [`Trie`].
///
/// Subtrie views are created with [`Trie::sub()`] and similar functions.
///
/// This type can be somewhat awkward to use due to language limitations.
/// See [`SubMut::as_mut()`] for the details.
pub struct SubMut<'a, K: Buf + ?Sized, V, I: Index = u32> {
  raw: &'a mut RawTrie<K, V, I>,
  prefix: Prefix<'a>,
}

impl<'a, K: Buf + ?Sized, V, I: Index> SubMut<'a, K, V, I> {
  /// Reborrows this view.
  ///
  /// This function is useful for code that wants a [`Sub`] instead of a
  /// [`SubMut`].
  #[inline]
  pub fn as_ref(&self) -> Sub<K, V, I> {
    Sub {
      raw: self.raw,
      prefix: self.prefix,
    }
  }

  /// Mutably reborrows this view.
  ///
  /// This function is necessary to call a function on a particular [`SubMut`]
  /// multiple times because it is a non-[`Clone`] type, and every other
  /// function consumes it on-call. This is necessary so this functions can
  /// return data for `'a` rather than whatever temporary `&self` lifetime they
  /// have.
  #[inline]
  pub fn as_mut(&mut self) -> SubMut<K, V, I> {
    SubMut {
      raw: self.raw,
      prefix: self.prefix,
    }
  }

  /// Converts this view into an immutable one.
  ///
  /// This is like [`SubMut::as_ref()`], except the lifetime is the same as
  /// for this view, which is why it needs to consume.
  #[inline]
  pub fn into_ref(self) -> Sub<'a, K, V, I> {
    Sub {
      raw: self.raw,
      prefix: self.prefix,
    }
  }

  /// Finds the element with the given key, if present.
  ///
  /// Note that this function finds matches byte-for-byte, but according to
  /// a `PartialEq` implementation.
  ///
  /// See [`Trie::get()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let mut sub = trie.sub_mut("foob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.as_mut().get("ar"), Some(&64));
  /// assert_eq!(sub.as_mut().get("foobar"), None);
  /// ```
  #[inline]
  pub fn get(self, key: &K) -> Option<&'a V> {
    self.into_ref().get(key)
  }

  /// Finds the element with the given key, if present.
  ///
  /// Note that this function finds matches byte-for-byte, but according to
  /// a `PartialEq` implementation.
  ///
  /// See [`Trie::get_mut()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let mut sub = trie.sub_mut("foob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.as_mut().get_mut("ar"), Some(&mut 64));
  /// assert_eq!(sub.as_mut().get_mut("foobar"), None);
  /// ```
  #[inline]
  pub fn get_mut(self, key: &K) -> Option<&'a mut V> {
    let expected_len = key.byte_len() + self.prefix.len();
    self
      .longest_prefix_mut(key)
      .and_then(|(k, v)| (k.byte_len() == expected_len).then_some(v))
  }

  /// Finds the entry with the longest byte-wise prefix of `key`. This will
  /// always succeed if an empty key is present in the trie.
  ///
  /// See [`Trie::longest_prefix()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let mut sub = trie.sub_mut("foob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.as_mut().longest_prefix("ar"), Some(("foobar", &64)));
  /// assert_eq!(sub.as_mut().longest_prefix("az"), None);
  /// ```
  #[inline]
  pub fn longest_prefix(self, key: &K) -> Option<(&'a K, &'a V)> {
    self.into_ref().longest_prefix(key)
  }

  /// Finds the entry with the longest byte-wise prefix of `key`. This will
  /// always succeed if an empty key is present in the trie.
  ///
  /// See [`Trie::longest_prefix_mut()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let mut sub = trie.sub_mut("foob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.as_mut().longest_prefix_mut("ar"), Some(("foobar", &mut 64)));
  /// assert_eq!(sub.as_mut().longest_prefix_mut("az"), None);
  /// ```
  #[inline]
  pub fn longest_prefix_mut(self, key: &K) -> Option<(&'a K, &'a mut V)> {
    self.prefixes_mut(key).last()
  }

  /// Creates a subtrie view for the given key.
  ///
  /// This is a subtrie of a subtrie, so the prefix the returned subtrie
  /// represents is that of `self` plus `key`.
  ///
  /// See [`Trie::sub()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let mut sub = trie.sub_mut("fo");
  /// let sub = sub.sub("ob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.get("ar"), Some(&64));
  /// ```
  #[inline]
  pub fn sub<'b>(&'b self, key: &'b K) -> Sub<'b, K, V, I> {
    Sub {
      prefix: Prefix::new(self.raw, &self.prefix, key.as_bytes()),
      raw: self.raw,
    }
  }

  /// Creates a mutable subtrie view for the given key.
  ///
  /// This is a subtrie of a subtrie, so the prefix the returned subtrie
  /// represents is that of `self` plus `key`.
  ///
  /// See [`Trie::sub_mut()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let mut sub = trie.sub_mut("fo");
  /// let sub = sub.sub_mut("ob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(sub.get_mut("ar"), Some(&mut 64));
  /// ```
  #[inline]
  pub fn sub_mut<'b>(&'b mut self, key: &'b K) -> SubMut<'b, K, V, I> {
    SubMut {
      prefix: Prefix::new(self.raw, &self.prefix, key.as_bytes()),
      raw: self.raw,
    }
  }

  /// Returns an iterator over all prefixes of `key` present in the subtrie, in
  /// lexicographic order. Note that `key` is *relative* to the subtrie, so
  /// searching for `"bar"` in `sub("foo")` is like searching for
  /// "foobar" in the whole trie.
  ///
  /// See [`Trie::prefixes()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub_mut("foob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// let prefixes = sub.prefixes("ars").collect::<Vec<_>>();
  /// assert_eq!(prefixes, vec![("foobar", &64)]);
  /// ```
  #[inline]
  pub fn prefixes<'key>(self, key: &'key K) -> Prefixes<'a, 'key, K, V, I> {
    self.into_ref().prefixes(key)
  }

  /// Like [`SubMut::prefixes()`], but the references are mutable.
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foo", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub_mut("foob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// let prefixes = sub.prefixes_mut("ars").collect::<Vec<_>>();
  /// assert_eq!(prefixes, vec![("foobar", &mut 64)]);
  /// ```
  #[inline]
  pub fn prefixes_mut<'key>(
    self,
    key: &'key K,
  ) -> PrefixesMut<'a, 'key, K, V, I> {
    PrefixesMut::new(self.raw, self.prefix, key)
  }

  /// Returns an iterator over this subtrie.
  ///
  /// See [`Trie::iter()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foocar", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub_mut("foobar");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(
  ///   sub.iter().collect::<Vec<_>>(),
  ///   vec![("foobar", &64)],
  /// );
  /// ```
  #[inline]
  pub fn iter(self) -> Iter<'a, K, V, I> {
    self.into_ref().iter()
  }

  /// Like [`SubMut::iter()`], but the references are mutable.
  ///
  /// See [`Trie::iter_mut()`].
  ///
  /// ```
  /// # use twie::Trie;
  /// let mut trie: Trie<_, _> = [("foocar", 32), ("foobar", 64)].into();
  /// # eprintln!("{}", trie.dump());
  /// let sub = trie.sub_mut("foob");
  /// # eprintln!("{}", sub.dump());
  ///
  /// assert_eq!(
  ///   sub.iter_mut().collect::<Vec<_>>(),
  ///   vec![("foobar", &mut 64)],
  /// );
  /// ```
  #[inline]
  pub fn iter_mut(self) -> IterMut<'a, K, V, I> {
    IterMut::new(self.raw, self.prefix)
  }

  /// Dumps the trie's internal structure as a pretty string.
  ///
  /// The format of this string is unstable. Do not rely on it.
  ///
  /// See [`Trie::dump()`].
  ///
  /// # Panics
  ///
  /// Panics if this function is called in release mode.
  pub fn dump(&self) -> String
  where
    V: fmt::Debug,
  {
    assert!(
      cfg!(debug_assertions),
      "dump() can only be called in debug mode"
    );
    raw::dump(self.raw, &self.prefix)
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn empty() {
    let trie = Trie::<str, ()>::new();
    iter_eq(trie.iter(), &[]);
    iter_eq(trie.prefixes(""), &[]);
    iter_eq(trie.longest_prefix(""), &[]);
  }

  #[test]
  fn get() {
    let trie = trie_set(&["a", "b", "abc", "abd", "abcef"]);
    assert!(trie.get("a").is_some());
    assert!(trie.get("ab").is_none());
    assert!(trie.get("abc").is_some());
    assert!(trie.get("abd").is_some());
    assert!(trie.get("abe").is_none());
    assert!(trie.get("abcef").is_some());
    assert!(trie.get("abceg").is_none());
    assert!(trie.get("c").is_none());
  }

  #[test]
  fn prefixes() {
    let trie = trie_set(&["a", "b", "abc", "abd"]);
    iter_eq(trie.prefixes("abc"), &["a", "abc"]);
    iter_eq(trie.prefixes("abcde"), &["a", "abc"]);
    iter_eq(trie.longest_prefix("abcde"), &["abc"]);

    let trie = trie_set(&["", "a", "b", "ab"]);
    iter_eq(trie.longest_prefix("c"), &[""]);

    let trie = trie_set(&["0", "00", "07"]);
    iter_eq(trie.prefixes("0777"), &["0", "07"]);
  }

  #[test]
  fn iterator() {
    let trie = trie_set(&["a", "abc", "A", "abd"]);
    iter_eq(trie.iter(), &["A", "a", "abc", "abd"]);
    iter_eq(trie.sub("ab").iter(), &["abc", "abd"]);
    iter_eq(trie.sub("a").iter(), &["a", "abc", "abd"]);
    iter_eq(trie.sub("abcd").iter(), &[]);
    iter_eq(trie.sub("c").iter(), &[]);
  }

  fn trie_set(items: &[&str]) -> Trie<str, ()> {
    let mut trie = Trie::<str, ()>::new();
    for &k in items {
      let inserted = trie.insert(k, ()).is_none();
      eprintln!("{}\n", trie.dump());

      assert!(inserted, "at: {k}");
    }
    trie
  }

  fn iter_eq<'a, V: 'a>(
    items: impl IntoIterator<Item = (&'a str, &'a V)>,
    expected: &[&str],
  ) {
    assert_eq!(
      items.into_iter().map(|(k, _)| k).collect::<Vec<_>>(),
      expected,
    );
  }
}
