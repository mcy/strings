use std::mem;
use std::mem::ManuallyDrop;
use std::mem::MaybeUninit;
use std::ptr::NonNull;

use crate::raw::nodes::Index;
use crate::raw::nodes::OutOfIndices;
use crate::raw::nodes::Ptr;

/// The actual user-provided data stored by the trie, separate from the tree
/// structure.
pub struct Entries<V, I: Index> {
  values: StealthVec<Entry<V, I>>,
}

// SAFETY: Although there are some sketchy functions that go & -> &mut, these
// MUST NOT be called except through a &Entries that was derived from an &mut
// Entries. They exist only so that iterators can vend multiple distinct
// elements without making MIRI lose its mind.
unsafe impl<V, I: Index> Send for Entries<V, I> {}
unsafe impl<V, I: Index> Sync for Entries<V, I> {}

pub struct Entry<V, I: Index> {
  /// The length of the key, which may be longer than this entry's depth in the
  /// trie. This entry is empty if `key_len` is Ptr::EMPTY.
  key_len: Ptr<I>,

  /// The value itself.
  value: MaybeUninit<V>,
}

impl<V, I: Index> Drop for Entry<V, I> {
  fn drop(&mut self) {
    if !self.key_len.is_empty() {
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

impl<V: Clone, I: Index> Clone for Entries<V, I> {
  fn clone(&self) -> Self {
    let mut data = Self::new();

    let new_entries = (0..self.values.len)
      .map(|i| {
        let e = self.values.get(i);

        let value = if e.key_len.is_empty() {
          MaybeUninit::uninit()
        } else {
          MaybeUninit::new(unsafe { e.value.assume_init_ref().clone() })
        };

        Entry { key_len: e.key_len, value }
      })
      .collect();

    unsafe {
      // The destructor of Vec cannot panic here, because it is empty.
      data.values.with_vec(|v| *v = new_entries);
    }
    data
  }
}

impl<V, I: Index> Entries<V, I> {
  pub fn new() -> Self {
    Self { values: StealthVec::new() }
  }

  pub fn new_entry(&mut self) -> Result<usize, OutOfIndices> {
    let new = self.values.len;
    unsafe {
      // SAFETY: Vec::push does not panic unless we try to allocate half of
      // the address space, which we can assume can't happen here.
      self.values.with_vec(|v| {
        v.push(Entry {
          key_len: Ptr::EMPTY,
          value: MaybeUninit::uninit(),
        })
      });
    }
    Ok(new)
  }

  /// Returns whether a value is initialized.
  pub fn is_init(&self, entry: usize) -> bool {
    !self.values.get(entry).key_len.is_empty()
  }

  /// Gets the value in `entry`, if present.
  pub fn get(&self, entry: usize) -> Option<(usize, &V)> {
    let e = self.values.get(entry);
    unsafe { Some((e.key_len.idx(), e.value.assume_init_ref())) }
  }

  /// Gets the value in `entry`, if present.
  ///
  /// # Safety
  ///
  /// It is the caller's responsibility to not cause aliasing hazards using
  /// this function.
  pub unsafe fn get_mut_may_alias(
    &self,
    entry: usize,
  ) -> Option<(usize, &mut V)> {
    let e = self.values.get_mut_may_alias(entry);
    unsafe { Some((e.key_len.idx(), e.value.assume_init_mut())) }
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
    e.key_len = Ptr::must(key_len);
    e.value.write(new)
  }
}
