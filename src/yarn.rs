//!

use std::cmp::Ordering;
use std::fmt;
use std::hash::Hash;
use std::hash::Hasher;
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;
use std::str;
use std::str::Utf8Error;

use crate::raw::RawYarn;
use crate::yarn_ref::YarnRef;
use crate::Utf8Chunks;

#[cfg(doc)]
use crate::yarn;

/// A yarn is an immutable, optimized string type.
///
/// See the [crate documentation](crate) for general information.
#[repr(transparent)]
pub struct Yarn<'a, Buf = [u8]>
where
  Buf: crate::Buf + ?Sized,
{
  raw: RawYarn,
  _ph: PhantomData<&'a Buf>,
}

impl<'a, Buf> Yarn<'a, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  /// Returns a reference to an empty yarn of any lifetime.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let empty: &Yarn = Yarn::empty();
  /// assert_eq!(empty, "");
  /// ```
  ///
  /// This will also be found by the `Default` impl for `&Yarn`.
  pub fn empty<'b>() -> &'b Self {
    unsafe {
      // SAFETY: Yarn is a transparent wrapper over RawYarn; even though
      // Yarn has a destructor, this is fine, because this lifetime is 'static
      // and will thus never run a destructor.
      mem::transmute::<&'b RawYarn, &'b Self>(RawYarn::empty())
    }
  }

  /// Returns a yarn pointing to the given slice, without copying.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let foo = Yarn::new(b"Byzantium");
  /// assert_eq!(foo.len(), 9);
  /// ```
  ///
  /// This function is not `const`, but the similar function
  /// [`Yarn::from_buf()`] is.
  pub fn new<Slice: AsRef<Buf> + ?Sized>(slice: &'a Slice) -> Self {
    Self::from_buf(slice.as_ref())
  }

  /// Returns a yarn pointing to the given slice, without copying.
  ///
  /// ```
  /// # use byteyarn::*;
  /// const FOO: Yarn = Yarn::from_buf(b"Byzantium");
  /// assert_eq!(FOO.len(), 9);
  /// ```
  pub const fn from_buf(buf: &'a Buf) -> Self {
    YarnRef::from_buf(buf).as_owned()
  }

  /// Returns a new yarn containing the contents of the given slice.
  /// This function will always return an inlined string, or `None` if the
  /// given buffer is too big.
  ///
  /// Note that the maximum inlined size is architecture-dependent.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let smol = Yarn::from_buf_inlined("smol");
  /// assert_eq!(smol.unwrap(), "smol");
  ///
  /// let big = Yarn::from_buf_inlined("biiiiiiiiiiiiiiig");
  /// assert!(big.is_none());
  /// ```
  pub const fn from_buf_inlined(buf: &Buf) -> Option<Self> {
    match YarnRef::from_buf_inlined(buf) {
      Some(y) => Some(y.as_owned()),
      None => None,
    }
  }

  /// Returns a yarn containing a single UTF-8-encoded Unicode scalar.
  /// This function does not allocate: every `char` fits in an inlined yarn.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let a = Yarn::<str>::from_char('a');
  /// assert_eq!(a, "a");
  /// ```
  pub const fn from_char(c: char) -> Self {
    YarnRef::<Buf>::from_char(c).as_owned()
  }

  /// Returns a yarn by taking ownership of an allocation.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let str = String::from("big string box").into_boxed_str();
  /// let yarn = Yarn::<str>::from_str_box(str);
  /// assert_eq!(yarn, "big string box");
  /// ```
  pub fn from_str_box(string: Box<str>) -> Self {
    let raw = RawYarn::from_box(string.into());
    unsafe {
      // SAFETY: both [u8] and str can be safely constructed from a str. We have
      // unique ownership of raw's allocation because from_box guarantees it.
      Self::from_raw(raw)
    }
  }

  /// Returns a yarn by taking ownership of an allocation.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let str = String::from("big string box");
  /// let yarn = Yarn::<str>::from_string(str);
  /// assert_eq!(yarn, "big string box");
  /// ```
  pub fn from_string(string: String) -> Self {
    Self::from_str_box(string.into())
  }

  /// Checks whether this yarn is empty.
  ///
  /// ```
  /// # use byteyarn::*;
  /// assert!(yarn!("").is_empty());
  /// assert!(!yarn!("xyz").is_empty());
  /// ```
  pub const fn is_empty(&self) -> bool {
    self.as_ref().is_empty()
  }

  /// Returns the length of this yarn, in bytes.
  ///
  /// ```
  /// # use byteyarn::*;
  /// assert_eq!(yarn!("").len(), 0);
  /// assert_eq!(yarn!("42").len(), 2);
  /// assert_eq!(yarn!("猫").len(), 3);
  /// assert_eq!(yarn!("🐈‍⬛").len(), 10);
  ///
  /// assert_eq!(byarn!(b"").len(), 0);
  /// assert_eq!(byarn!(b"xyz").len(), 3);
  /// assert_eq!(byarn!(&[1, 2, 3]).len(), 3);
  /// ```
  pub const fn len(&self) -> usize {
    self.as_ref().len()
  }

  /// Converts this yarn into a slice.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let yarn = yarn!("jellybeans");
  /// let s: &str = yarn.as_slice();
  /// assert_eq!(s, "jellybeans");
  ///
  /// let yarn = byarn!(b"jellybeans");
  /// let s: &[u8] = yarn.as_slice();
  /// assert_eq!(s, b"jellybeans");
  /// ```
  pub const fn as_slice(&self) -> &Buf {
    unsafe {
      // SAFETY: converting back to buf from raw is ok here because this is
      // evidently a round-trip.
      YarnRef::raw2buf(self.as_bytes())
    }
  }

  /// Converts this owning yarn into a reference yarn.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let yarn = yarn!("jellybeans");
  /// let ry = yarn.as_ref();
  /// assert_eq!(ry, "jellybeans");
  /// ```
  pub const fn as_ref(&self) -> YarnRef<Buf> {
    if let Some(inl) = YarnRef::from_buf_inlined(self.as_slice()) {
      return inl;
    }

    let raw = match self.raw.on_heap() {
      true => unsafe {
        // SAFETY: The returned YarnRef will prevent self from being used
        // until this raw yarn goes away, because it borrows self.
        RawYarn::alias_slice(self.as_bytes())
      },
      false => self.raw,
    };

    unsafe {
      // SAFETY: The lifetime of the output is shorter than that of
      // the input, so raw is valid for a yarn reference. Even in the case
      // that self.on_heap, the aliased slice will not outlive the &self of
      // this function.
      YarnRef::from_raw(raw)
    }
  }

  /// Converts this owning yarn into a reference yarn, with the same lifetime
  /// as this yarn.
  ///
  /// Note that if this yarn is on the heap, this function will return `None`.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let yarn = yarn!("jellybeans");
  /// let ry: YarnRef<'static, str> = yarn.to_ref().unwrap();
  /// assert_eq!(ry, "jellybeans");
  ///
  /// let boxed = Yarn::<str>::from_string(String::from("jellybeans"));
  /// assert!(boxed.to_ref().is_none());
  /// ```
  pub const fn to_ref(&self) -> Option<YarnRef<'a, Buf>> {
    if self.raw.on_heap() {
      return None;
    }

    unsafe {
      // SAFETY: The lifetime of the output is equal than that of
      // the input, so raw is valid for a yarn reference. We have excluded the
      // on_heap case above.
      Some(YarnRef::from_raw(self.raw))
    }
  }

  /// Converts this yarn into a byte slice.
  /// ```
  /// # use byteyarn::*;
  /// assert_eq!(yarn!("").as_bytes(), b"");
  /// assert_eq!(yarn!("猫").as_bytes(), b"\xE7\x8C\xAB");
  ///
  /// assert_eq!(byarn!(b"xyz").as_bytes(), b"xyz");
  /// assert_eq!(byarn!(&[1, 2, 3]).as_bytes(), [1, 2, 3]);
  /// ```
  pub const fn as_bytes(&self) -> &[u8] {
    self.raw.as_slice()
  }

  /// Converts this yarn into a boxed slice, potentially by copying it.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let boxed = yarn!("jellybeans").into_box();
  /// assert_eq!(&boxed[..], b"jellybeans");
  /// ```
  pub fn into_box(self) -> Box<[u8]> {
    let mut raw = self.into_raw();
    if !raw.on_heap() {
      return raw.as_slice().into();
    }

    unsafe {
      // SAFETY: raw is guaranteed to be on the heap, so this slice is on the
      // heap with the correct layout; because we called into_raw(), this
      // reference is uniquely owned.
      Box::from_raw(raw.as_mut_slice())
    }
  }

  /// Converts this yarn into a vector, potentially by copying it.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let mut vec = byarn!(b"jellybeans").into_vec();
  /// vec.extend_from_slice(b" & KNUCKLES");
  /// let yarn = Yarn::from_vec(vec);
  ///
  /// assert_eq!(yarn, b"jellybeans & KNUCKLES");
  /// ```
  pub fn into_vec(self) -> Vec<u8> {
    self.into_box().into()
  }

  /// Converts this yarn into a byte yarn.
  pub const fn into_bytes(self) -> Yarn<'a, [u8]> {
    unsafe {
      // SAFETY: The lifetimes are the same, and [u8] is constructible from
      // either a [u8] or str, so this is just weakening the user-facing type.
      Yarn::from_raw(self.into_raw())
    }
  }

  /// Extends the lifetime of this yarn if this yarn is dynamically known to
  /// point to immortal memory.
  ///
  /// If it doesn't, the contents are copied into a fresh heap allocation.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let bytes = Vec::from(*b"crunchcrunchcrunch");
  /// let yarn = Yarn::<[u8]>::from(&bytes);
  ///
  /// let immortal: Yarn<'static, [u8]> = yarn.immortalize();
  /// drop(bytes);  // Show that Yarn continues to exist despite `bytes` going
  ///               // away.
  ///
  /// assert_eq!(immortal, b"crunchcrunchcrunch");
  /// ```
  pub fn immortalize(self) -> Yarn<'static, Buf> {
    if self.raw.is_immortal() {
      unsafe {
        // SAFETY: We just validated that this raw is in fact suitable for use
        // with 'static lifetime, and all this cast is doing is extending the
        // lifetime on self.
        return Yarn::from_raw(self.into_raw());
      }
    }

    let raw = RawYarn::copy_slice(self.as_bytes());
    unsafe {
      // SAFETY: RawYarn::copy_slice always returns an immortal, uniquely-owned
      // value.
      Yarn::from_raw(raw)
    }
  }

  /// Returns a yarn consisting of the concatenation of the given slices.
  ///
  /// Does not allocate if the resulting concatenation can be inlined.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let yarn = Yarn::<str>::concat(&["foo", "bar", "baz"]);
  /// assert_eq!(yarn, "foobarbaz");
  /// ```
  pub fn concat(bufs: &[impl AsRef<Buf>]) -> Self {
    let total_len = bufs
      .iter()
      .map(|b| YarnRef::buf2raw(b.as_ref()).len())
      .sum();
    let iter = bufs.iter().map(|b| YarnRef::buf2raw(b.as_ref()));

    unsafe { Self::from_raw(RawYarn::concat(total_len, iter)) }
  }

  /// Tries to inline this yarn, if it's small enough.
  ///
  /// This operation has no directly visible side effects, and is only intended
  /// to provide a way to relieve memory pressure. In general, you should not
  /// have to call this function directly.
  pub fn inline_in_place(&mut self) {
    if let Some(inlined) = Self::from_buf_inlined(self.as_slice()) {
      *self = inlined;
    }
  }

  /// Leaks any heap allocation associated with this yarn.
  ///
  /// The allocation is tagged as "static", so upcasting via
  /// [`Yarn::immortalize()`] will not need to reallocate.
  pub fn leak(&mut self) {
    if !self.raw.on_heap() {
      return;
    }

    unsafe {
      // SAFETY: We have unique ownership of this yarn, and we know it's HEAP,
      // so updating the tag from HEAP to STATIC will not change anything
      // except to make it immutable and to inhibit the destructor.
      self.raw = RawYarn::from_ptr_len_tag(
        self.as_bytes().as_ptr(),
        self.len(),
        RawYarn::STATIC,
      );
    }
  }

  /// Returns an iterator over the UTF-8 (or otherwise) chunks in this string.
  ///
  /// This iterator is also used for the `Debug` and `Display` formatter
  /// implementations.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let yarn = byarn!(b"abc\xFF\xFE\xFF\xF0\x9F\x90\x88\xE2\x80\x8D\xE2\xAC\x9B!");
  /// let chunks = yarn.utf8_chunks().collect::<Vec<_>>();
  /// assert_eq!(chunks, [
  ///   Ok("abc"),
  ///   Err(&[0xff][..]),
  ///   Err(&[0xfe][..]),
  ///   Err(&[0xff][..]),
  ///   Ok("🐈‍⬛!"),
  /// ]);
  ///
  /// assert_eq!(format!("{yarn:?}"), r#""abc\xFF\xFE\xFF🐈‍⬛!""#);
  /// assert_eq!(format!("{yarn}"), "abc���🐈‍⬛!");
  /// ```
  pub fn utf8_chunks(&self) -> Utf8Chunks {
    Utf8Chunks::new(self.as_bytes())
  }

  /// Returns a new yarn wrapping the given raw yarn.
  ///
  /// # Safety
  ///
  /// If `raw` is aliased, its lifetime must not be shorter than 'a.
  ///
  /// If `raw` is heap-allocated, no other yarn must be holding it.
  pub(crate) const unsafe fn from_raw(raw: RawYarn) -> Self {
    Self {
      raw,
      _ph: PhantomData,
    }
  }

  /// Consumes self, inhibits the destructor, and returns the raw yarn.
  pub(crate) const fn into_raw(self) -> RawYarn {
    let raw = self.raw;
    mem::forget(self);
    raw
  }
}

impl<Buf> Yarn<'static, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  /// Returns a yarn pointing to the given slice, without copying. This function
  /// has the benefit of creating a yarn that remembers that it came from a
  /// static string, meaning that it can be dynamically upcast back to a
  /// `'static` lifetime.
  ///
  /// This function will *not* be found by `From` impls.
  pub const fn from_static_buf(buf: &'static Buf) -> Self {
    YarnRef::from_static_buf(buf).as_owned()
  }
}

impl<'a> Yarn<'a, [u8]> {
  /// Returns a yarn containing a single byte, without allocating.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let a = Yarn::from_byte(0x20);
  /// assert_eq!(a, b" ");
  /// ```
  pub const fn from_byte(c: u8) -> Self {
    YarnRef::from_byte(c).as_owned()
  }

  /// Returns a yarn by taking ownership of the given allocation.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let str = Box::new([0xf0, 0x9f, 0x90, 0x88, 0xe2, 0x80, 0x8d, 0xe2, 0xac, 0x9b]);
  /// let yarn = Yarn::from_box(str);
  /// assert_eq!(yarn, "🐈‍⬛".as_bytes());
  /// ```
  pub fn from_box(bytes: Box<[u8]>) -> Self {
    let raw = RawYarn::from_box(bytes);
    unsafe { Self::from_raw(raw) }
  }

  /// Returns a yarn by taking ownership of the given allocation.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let str = vec![0xf0, 0x9f, 0x90, 0x88, 0xe2, 0x80, 0x8d, 0xe2, 0xac, 0x9b];
  /// let yarn = Yarn::from_vec(str);
  /// assert_eq!(yarn, "🐈‍⬛".as_bytes());
  /// ```
  pub fn from_vec(bytes: Vec<u8>) -> Self {
    Self::from_box(bytes.into_boxed_slice())
  }

  /// Tries to convert this yarn into a UTF-8 yarn via [`str::from_utf8()`].
  ///
  /// ```
  /// # use byteyarn::*;
  /// let yarn = byarn!(&[0xf0, 0x9f, 0x90, 0x88, 0xe2, 0x80, 0x8d, 0xe2, 0xac, 0x9b]);
  /// assert_eq!(yarn.to_utf8().unwrap(), "🐈‍⬛");
  ///
  /// assert!(byarn!(b"\xFF").to_utf8().is_err());
  /// ```
  pub fn to_utf8(self) -> Result<Yarn<'a, str>, Utf8Error> {
    self.to_utf8_or_bytes().map_err(|(_, e)| e)
  }

  /// Tries to convert this yarn into a UTF-8 yarn via [`str::from_utf8()`].
  ///
  /// If conversion fails, the original yarn is returned with the error.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let blob = byarn!(&[0xff; 5]);
  /// let (bad, _) = blob.to_utf8_or_bytes().unwrap_err();
  ///
  /// assert_eq!(bad, &[0xff; 5]);
  /// ```
  pub fn to_utf8_or_bytes(self) -> Result<Yarn<'a, str>, (Self, Utf8Error)> {
    if let Err(e) = str::from_utf8(self.as_bytes()) {
      return Err((self, e));
    }
    unsafe { Ok(Yarn::from_raw(self.into_raw())) }
  }

  /// Returns a mutable reference into this yarn's internal buffer.
  ///
  /// If the buffer is not uniquely owned (e.g., it is an alias of some other
  /// buffer or a string constant) this function will first perform a copy and
  /// possibly a heap allocation.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let mut yarn = byarn!(b"const but very long");
  /// assert!(yarn.try_mut().is_none());
  ///
  /// let mut smol = byarn!(b"smol const");
  /// smol.try_mut().unwrap()[3] = b'g';
  /// assert_eq!(smol, b"smog const");
  /// ```
  pub fn try_mut(&mut self) -> Option<&mut [u8]> {
    self.inline_in_place();
    if !self.raw.on_heap() && !self.raw.is_small() {
      return None;
    }

    Some(self.as_mut())
  }

  /// Returns a mutable reference into this yarn's internal buffer.
  ///
  /// If the buffer is not uniquely owned (e.g., it is an alias of some other
  /// buffer or a string constant) this function will first perform a copy and
  /// possibly a heap allocation.
  ///
  /// ```
  /// # use byteyarn::*;
  /// let mut yarn = byarn!(b"const but very long");
  /// yarn.as_mut()[17] = b'_';
  /// assert_eq!(yarn, b"const but very lo_g");
  /// ```
  #[allow(clippy::should_implement_trait)]
  pub fn as_mut(&mut self) -> &mut [u8] {
    self.inline_in_place();
    if !self.raw.on_heap() && !self.raw.is_small() {
      *self = Self::from_box(mem::take(self).into_box());
    }

    unsafe { self.raw.as_mut_slice() }
  }
}

impl Yarn<'_, str> {
  /// Builds a new yarn from the given formatting arguments
  /// (see [`format_args!()`]), allocating only when absolutely necessary.
  ///
  /// In general, you'll want to use the [`yarn!()`] macro, instead.
  pub fn from_fmt(args: fmt::Arguments) -> Self {
    unsafe { Yarn::from_raw(RawYarn::from_fmt_args(args)) }
  }

  /// Converts this yarn into a string slice.
  pub fn as_str(&self) -> &str {
    self.as_slice()
  }

  /// Converts this yarn into a boxed slice, potentially by copying it.
  pub fn into_str_box(self) -> Box<str> {
    self.into_string().into()
  }

  /// Converts this yarn into a string, potentially by copying it.
  pub fn into_string(self) -> String {
    unsafe { String::from_utf8_unchecked(self.into_vec()) }
  }
}

impl<Buf> Deref for Yarn<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  type Target = Buf;
  fn deref(&self) -> &Buf {
    self.as_slice()
  }
}

impl<Buf> Drop for Yarn<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  fn drop(&mut self) {
    unsafe { self.raw.destroy() }
  }
}

impl<Buf> Clone for Yarn<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  fn clone(&self) -> Self {
    if let Some(yr) = self.to_ref() {
      return yr.as_owned();
    }

    let copy = RawYarn::copy_slice(self.as_bytes());
    unsafe { Self::from_raw(copy) }
  }
}

impl<Buf: crate::Buf + ?Sized> fmt::Debug for Yarn<'_, Buf> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Debug::fmt(&self.as_ref(), f)
  }
}

impl<Buf: crate::Buf + ?Sized> fmt::Display for Yarn<'_, Buf> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt::Display::fmt(&self.as_ref(), f)
  }
}

impl<Slice, Buf> PartialEq<Slice> for Yarn<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
  Slice: AsRef<Buf> + ?Sized,
{
  fn eq(&self, that: &Slice) -> bool {
    self.as_slice() == that.as_ref()
  }
}

impl<Buf: crate::Buf + Eq + ?Sized> Eq for Yarn<'_, Buf> {}

impl<Slice, Buf> PartialOrd<Slice> for Yarn<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
  Slice: AsRef<Buf> + ?Sized,
{
  fn partial_cmp(&self, that: &Slice) -> Option<Ordering> {
    self.as_slice().partial_cmp(that.as_ref())
  }
}

impl<Buf: crate::Buf + ?Sized> Ord for Yarn<'_, Buf> {
  fn cmp(&self, that: &Self) -> Ordering {
    self.as_slice().cmp(that.as_slice())
  }
}

impl<Buf: crate::Buf + ?Sized> Hash for Yarn<'_, Buf> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.as_slice().hash(state)
  }
}

impl<Buf: crate::Buf + ?Sized> Default for Yarn<'_, Buf> {
  fn default() -> Self {
    <&Self>::default().clone()
  }
}

impl<Buf: crate::Buf + ?Sized> Default for &Yarn<'_, Buf> {
  fn default() -> Self {
    Yarn::empty()
  }
}
