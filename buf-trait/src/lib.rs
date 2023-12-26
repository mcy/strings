//! The `Buf` trait.
//!
//! This crate provides a trait for abstracting over buffer-like types, such
//! as `str` and `[u8]`. This is a much stronger property than, say,
//! implementing [`AsRef<[u8]>`]. These are variable-length types that you might
//! want to store as a raw byte buffer and then transmute to and from `&[u8]`.
//!
//! This crate provides all the functionality necessary for doing so safely,
//! correctly, and in `const`.

#![no_std]

use core::alloc::Layout;
use core::mem;
use core::slice;
use core::slice::SliceIndex;

/// A trait for abstracting over `str`, `[u8]`, and other byte-string-like
/// types.
///
/// See the [crate docs](self) for more information.
///
/// # Safety
///
/// This trait should only be implemented on types that are, essentially, a
/// thin wrapper over a `[T]` for some Copy type `T`. In particular, the
/// following must be valid operations:
///   1. Transmute `&impl Buf` to `&[T]`, where `T` has no uninitialized bits
///      (no padding, etc).
///   2. Transmute `&[T]` to `&impl Buf` if the contents of that `&[T]`
///      originated from operation (1).
///   3. Copy `&impl Buf` to an appropriately-aligned buffer, and then transmute
///      the resulting `&[T]` to that `&impl Buf` again.
///
/// `T` may be zero-sized, but functions will panic in this case.
pub unsafe trait Buf {
  /// The element type of the underlying type. This is used for computing e.g.
  /// alignment and stride.
  type Element: Copy;

  /// The length of this value, in elements.
  fn elem_len(&self) -> usize {
    mem::size_of_val(self) / mem::size_of::<Self::Element>()
  }

  /// The length of this value, in bytes.
  fn byte_len(&self) -> usize {
    mem::size_of_val(self)
  }

  /// Converts a reference to a [`Buf`] into its underlying bytes.
  fn as_bytes(&self) -> &[u8] {
    as_bytes(self)
  }

  /// Converts a byte slice to a reference to a [`Buf`].
  ///
  /// # Safety
  ///
  /// `bytes` must have been either constructed via transmuting from `&Self`,
  /// or a bytewise copy of a `Self`.
  unsafe fn from_bytes(bytes: &[u8]) -> &Self {
    as_buf(bytes)
  }

  /// Converts a reference to a [`Buf`] into its underlying bytes.
  fn as_bytes_mut(&mut self) -> &mut [u8] {
    as_bytes_mut(self)
  }

  /// Converts a byte slice to a reference to a [`Buf`].
  ///
  /// # Safety
  ///
  /// `bytes` must have been either constructed via transmuting from `&Self`,
  /// or a bytewise copy of a `Self`.
  unsafe fn from_bytes_mut(bytes: &mut [u8]) -> &mut Self {
    as_buf_mut(bytes)
  }

  /// Performs a slicing operation on `self` with respect to byte indices.
  ///
  /// # Safety
  ///
  /// This function does not perform any checking beyonds bounds checking. For
  /// example, if called on `str`, this function may slice through a multi-byte
  /// Unicode scalar, producing a `&str` that violate's `str`'s validity
  /// constraints (i.e., Undefined Behavior).
  unsafe fn slice_along_bytes<Idx>(&self, index: Idx) -> Option<&Self>
  where
    Idx: SliceIndex<[u8], Output = [u8]>,
  {
    self.as_bytes().get(index).map(|b| Self::from_bytes(b))
  }
}

/// Computes the layout of `buf`.
///
/// This function is `const`, unlike [`Layout::for_value()`].
pub const fn layout_of<B: ?Sized + Buf>(buf: &B) -> Layout {
  unsafe {
    Layout::from_size_align_unchecked(
      as_bytes(buf).len(),
      mem::align_of::<B::Element>(),
    )
  }
}

/// Converts a reference to a [`Buf`] into its underlying bytes.
///
/// Unlike [`Buf::as_bytes()`], this function is `const`.
pub const fn as_bytes<B: ?Sized + Buf>(buf: &B) -> &[u8] {
  assert!(
    mem::size_of::<B::Element>() > 0,
    "buf-trait: cannot use ZST as in type-erased context"
  );

  let ptr = &buf as *const &_ as *const &[B::Element];

  unsafe {
    let buf = *ptr;
    // SAFETY: The safety rules of `Buf` make this valid.
    let ptr = buf as *const _ as *const u8;
    let len = buf.len() * mem::size_of::<B::Element>();
    slice::from_raw_parts(ptr, len)
  }
}

/// Converts a mutable reference to a [`Buf`] into its underlying bytes.
pub fn as_bytes_mut<B: ?Sized + Buf>(mut buf: &mut B) -> &mut [u8] {
  assert!(
    mem::size_of::<B::Element>() > 0,
    "buf-trait: cannot use ZST as in type-erased context"
  );

  let ptr = &mut buf as *mut &mut _ as *mut &mut [B::Element];

  unsafe {
    let buf = &mut *ptr;
    // SAFETY: The safety rules of `Buf` make this valid.
    let ptr = buf as *mut _ as *mut u8;
    slice::from_raw_parts_mut(ptr, mem::size_of_val(&**buf))
  }
}

/// Converts a byte slice to a reference to a [`Buf`].
///
/// Unlike [`Buf::from_bytes()`], this function is `const`.
///
/// # Safety
///
/// See [`Buf::from_bytes()`].
pub const unsafe fn as_buf<B: ?Sized + Buf>(bytes: &[u8]) -> &B {
  assert!(
    mem::size_of::<B::Element>() > 0,
    "buf-trait: cannot use ZST as in type-erased context"
  );

  let buf = slice::from_raw_parts(
    bytes.as_ptr().cast::<B::Element>(),
    bytes.len() / mem::size_of::<B::Element>(),
  );

  let ptr = &buf as *const &[_] as *const &B;
  *ptr
}

/// Converts a mutable byte slice to a reference to a [`Buf`].
///
/// # Safety
///
/// See [`Buf::from_bytes()`].
pub unsafe fn as_buf_mut<B: ?Sized + Buf>(bytes: &mut [u8]) -> &mut B {
  assert!(
    mem::size_of::<B::Element>() > 0,
    "buf-trait: cannot use ZST as in type-erased context"
  );

  let mut buf = slice::from_raw_parts_mut(
    bytes.as_mut_ptr().cast::<B::Element>(),
    bytes.len() / mem::size_of::<B::Element>(),
  );

  let ptr = &mut buf as *mut &mut [_] as *mut &mut B;
  *ptr
}

unsafe impl<T: Pod + Copy> Buf for [T] {
  type Element = T;
}

unsafe impl Buf for str {
  type Element = u8;
}

/// Helper trait for generating implementations of `Buf` on slice types.
///
/// # Safety
///
/// Implement only on types with no padding.
unsafe trait Pod {}

unsafe impl Pod for u8 {}
unsafe impl Pod for u16 {}
unsafe impl Pod for u32 {}
unsafe impl Pod for u64 {}
unsafe impl Pod for u128 {}
unsafe impl Pod for usize {}
unsafe impl Pod for i8 {}
unsafe impl Pod for i16 {}
unsafe impl Pod for i32 {}
unsafe impl Pod for i64 {}
unsafe impl Pod for i128 {}
unsafe impl Pod for isize {}

unsafe impl Pod for bool {}
unsafe impl Pod for char {}

unsafe impl Pod for f32 {}
unsafe impl Pod for f64 {}

unsafe impl<T: ?Sized> Pod for &T {}
unsafe impl<T: ?Sized> Pod for &mut T {}
unsafe impl<T: ?Sized> Pod for *const T {}
unsafe impl<T: ?Sized> Pod for *mut T {}

unsafe impl<T, const N: usize> Pod for [T; N] {}
