use std::marker::PhantomData;
use std::mem;
use std::mem::ManuallyDrop;
use std::mem::MaybeUninit;
use std::ptr::NonNull;

use buf_trait::Buf;
use byteyarn::YarnBox;

use crate::raw::nodes::Index;
use crate::raw::nodes::Node;
use crate::raw::nodes::OutOfIndices;
use crate::raw::Prefix;

/// The actual user-provided data stored by the trie, separate from the tree
/// structure.
pub struct Entries<K: Buf + ?Sized, V, I: Index> {
  keys: Vec<YarnBox<'static, [u8]>>,
  values: StealthVec<Entry<V, I>>,
  _ph: PhantomData<fn(&K) -> &K>,
}

pub struct Entry<V, I: Index> {
  /// A index-length pair into Data.keys, referring to which key this entry
  /// uses.
  ///
  /// If the second entry is equal to I::EMPTY, it means this entry is
  /// uninitialized.
  ///
  /// Also, neither of these are actually nodes, we're just using the node
  /// type for convenience.
  key: [Node<I>; 2],

  /// The value itself.
  value: MaybeUninit<V>,
}

impl<V, I: Index> Drop for Entry<V, I> {
  fn drop(&mut self) {
    if !self.key[1].is_empty() {
      unsafe {
        self.value.assume_init_drop();
      }
    }
  }
}

/// A deconstructed `Vec<T>` that ensures we only ever manipulate the data for
/// the entries vector through raw pointers, except when creating new entries.
///
/// This is necessary to allow disjoint borrows of its elements without tripping
/// MIRI.
struct StealthVec<T> {
  ptr: *mut T,
  cap: usize,
  len: usize,
}

impl<T> StealthVec<T> {
  fn new() -> Self {
    Self {
      ptr: NonNull::dangling().as_ptr(),
      cap: 0,
      len: 0,
    }
  }

  fn get(&self, entry: usize) -> &T {
    debug_assert!(
      entry < self.len,
      "trie: entry index {entry} out of bounds {}; this is a bug",
      self.len
    );

    unsafe { &*self.ptr.add(entry) }
  }

  // SAFETY: This is has no aliasing guardrails!
  //
  // Also, calling with_entries_vec() invalidates any references created by this
  // function.
  #[allow(clippy::mut_from_ref)]
  unsafe fn get_mut_may_alias(&self, entry: usize) -> &mut T {
    debug_assert!(
      entry < self.len,
      "trie: entry index {entry} out of bounds {}; this is a bug",
      self.len
    );

    unsafe { &mut *self.ptr.add(entry) }
  }

  // SAFETY: `cb` MUST NOT panic.
  unsafe fn with_vec(&mut self, cb: impl FnOnce(&mut Vec<T>)) {
    let mut vec = ManuallyDrop::new(unsafe {
      Vec::from_raw_parts(self.ptr, self.len, self.cap)
    });
    cb(&mut vec);
    self.ptr = vec.as_mut_ptr();
    self.cap = vec.capacity();
    self.len = vec.len();
  }
}

impl<T> Drop for StealthVec<T> {
  fn drop(&mut self) {
    let mut to_drop = Vec::new();
    unsafe {
      // SAFETY: mem::swap cannot panic. We use swap instead of replace, because
      // dropping an intermediate Vec<T> inside the closure could cause a panic
      // inside of an element's dtor.
      self.with_vec(|v| mem::swap(v, &mut to_drop));
    }
  }
}

impl<K: Buf + ?Sized, V: Clone, I: Index> Clone for Entries<K, V, I> {
  fn clone(&self) -> Self {
    let mut data = Self::new();
    data.keys = self.keys.clone();

    let new_entries = (0..self.values.len)
      .map(|i| {
        let e = self.values.get(i);

        let value = if e.key[1].is_empty() {
          MaybeUninit::uninit()
        } else {
          MaybeUninit::new(unsafe { e.value.assume_init_ref().clone() })
        };

        Entry { key: e.key, value }
      })
      .collect();

    unsafe {
      // The destructor of Vec cannot panic here, because it is empty.
      data.values.with_vec(|v| *v = new_entries);
    }
    data
  }
}

impl<K: Buf + ?Sized, V, I: Index> Entries<K, V, I> {
  pub fn new() -> Self {
    Self {
      keys: vec![],
      values: StealthVec::new(),
      _ph: PhantomData,
    }
  }

  pub fn new_entry(
    &mut self,
    prefix: &Prefix,
    suffix: YarnBox<[u8]>,
    maybe_key: Option<usize>,
  ) -> Result<usize, OutOfIndices> {
    let new = self.values.len;
    let mut entry = Entry {
      key: [Node::EMPTY, Node::EMPTY],
      value: MaybeUninit::uninit(),
    };

    if let Some(moved_key) = maybe_key {
      entry.key[0] = self.values.get(moved_key).key[0];
    }

    let keyhole = entry.key[0]
      .try_into()
      .ok()
      .map(|idx: usize| &mut self.keys[idx]);

    if keyhole
      .as_ref()
      .is_some_and(|k| k.as_bytes()[prefix.len()..].starts_with(&suffix))
    {
      unsafe {
        // SAFETY: Vec::push does not panic unless we try to allocate half of
        // the address space, which we can assume can't happen here.
        self.values.with_vec(|v| v.push(entry));
      }
      return Ok(new);
    }

    let key = if prefix.prev().is_none() {
      suffix.immortalize()
    } else {
      let mut key = vec![0; prefix.len() + suffix.len()].into_boxed_slice();
      key[prefix.len()..].copy_from_slice(&suffix);

      let mut prefix = prefix;
      loop {
        key[prefix.len() - prefix.chunk().len()..prefix.len()]
          .copy_from_slice(prefix.chunk());

        match prefix.prev() {
          Some(prev) => prefix = prev,
          None => break,
        }
      }

      YarnBox::from(key)
    };

    if let Some(keyhole) = keyhole.filter(|k| key.starts_with(k.as_bytes())) {
      *keyhole = key;
    } else {
      entry.key[0] = self.keys.len().try_into()?;
      self.keys.push(key);
    }

    unsafe {
      // SAFETY: Vec::push does not panic unless we try to allocate half of
      // the address space, which we can assume can't happen here.
      self.values.with_vec(|v| v.push(entry));
    }
    Ok(new)
  }

  /// Returns whether a value is initialized.
  pub fn is_init(&self, entry: usize) -> bool {
    !self.values.get(entry).key[1].is_empty()
  }

  /// Gets the value in `entry`, if present.
  pub fn get(&self, entry: usize) -> Option<(&K, &V)> {
    let e = self.values.get(entry);
    let [key, len] = e.key;
    let key = &&self.keys[key.idx()].as_bytes()[..len.try_into().ok()?];
    unsafe { Some((K::from_bytes(key), e.value.assume_init_ref())) }
  }

  /// Gets the value in `entry`, if present.
  ///
  /// # Safety
  ///
  /// It is the caller's responsibility to not cause aliasing hazards using
  /// this function.
  pub unsafe fn get_mut_may_alias(&self, entry: usize) -> Option<(&K, &mut V)> {
    let e = self.values.get_mut_may_alias(entry);
    let [key, len] = e.key;
    let key = &&self.keys[key.idx()].as_bytes()[..len.try_into().ok()?];
    unsafe { Some((K::from_bytes(key), e.value.assume_init_mut())) }
  }

  /// Initializes `entry` if it isn't.
  pub unsafe fn init(
    &mut self,
    entry: usize,
    key_len: usize,
    cb: impl FnOnce() -> V,
  ) -> &mut V {
    if self.is_init(entry) {
      // SAFETY: Nothing else in this code path access the entries vector.
      return unsafe {
        self.values.get_mut_may_alias(entry).value.assume_init_mut()
      };
    }

    // SAFETY: cb() must be called before key_len is written to, so that the
    // entry is left untouched if cb() panics.
    let new = cb();

    let e = unsafe {
      // SAFETY: Nothing else in this code path accesses the entries vector.
      self.values.get_mut_may_alias(entry)
    };
    e.key[1] = Node::must(key_len);
    e.value.write(new)
  }
}
