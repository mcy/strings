use std::alloc;
use std::fmt;
use std::fmt::Write;
use std::mem;
use std::mem::MaybeUninit;
use std::num::NonZeroUsize;
use std::slice;

/// The core implementation of yarns.
///
/// This type encapsulates the various size optimizations that yarns make; this
/// wrapper is shared between both owning and non-owning yarns.
#[repr(C)]
#[derive(Copy, Clone)]
pub struct RawYarn {
  ptr: PtrOrBytes,
  len: NonZeroUsize,
}

#[repr(C)]
#[derive(Copy, Clone)]
union PtrOrBytes {
  bytes: [u8; mem::size_of::<*const u8>()],
  ptr: *const u8,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct Small {
  data: [u8; mem::size_of::<RawYarn>() - 1],
  len: u8,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct Slice {
  ptr: *const u8,
  len: usize,
}

enum Layout<'a> {
  Small(&'a Small),
  Slice(&'a Slice),
}

enum LayoutMut<'a> {
  Small(&'a mut Small),
  Slice(&'a mut Slice),
}

// RawYarn does not expose &mut through &self.
unsafe impl Send for RawYarn {}
unsafe impl Sync for RawYarn {}

#[test]
fn has_niche() {
  assert_eq!(mem::size_of::<RawYarn>(), mem::size_of::<Option<RawYarn>>());
}

impl RawYarn {
  /// The number of bytes beyond the length byte that are usable for data.
  /// This is 7 on 32-bit and 15 on 64-bit.
  pub const SSO_LEN: usize = {
    let bytes_usable = mem::size_of::<usize>() * 2 - 1;
    let max_len = 1 << (8 - 2);

    let sso_len = if bytes_usable < max_len {
      bytes_usable
    } else {
      max_len
    };

    assert!(
      sso_len >= 4,
      "yarns are not supported on architectures with pointers this small"
    );

    sso_len
  };

  /// The tag for an SSO yarn.
  pub const SMALL: u8 = 0b11;
  /// The tag for a yarn that came from an immortal string slice.
  pub const STATIC: u8 = 0b01;
  /// The tag for a yarn that points to a dynamic string slice, on the heap,
  /// that we uniquely own.
  pub const HEAP: u8 = 0b10;
  /// The tag for a yarn that points to a dynamic string slice we don't
  /// uniquely own.
  ///
  /// Because the first word can never be zero, aliased yarns can never have
  /// zero length.
  pub const ALIASED: u8 = 0b00;

  /// Mask for extracting the tag out of the lowest byte of the yarn.
  const SHIFT8: u32 = u8::BITS - 2;
  const SHIFT: u32 = usize::BITS - 2;

  const MASK8: usize = !0 << Self::SHIFT8;
  const MASK: usize = !0 << Self::SHIFT;

  /// Returns the kind of yarn this is (one of the constants above).
  #[inline(always)]
  pub const fn kind(&self) -> u8 {
    // This used to be
    //
    // let ptr = self as *const Self as *const u8;
    // let hi_byte = unsafe {
    //  // SAFETY: ptr is valid by construction; regardless of which union member
    //  // is engaged, the lowest byte is always initialized.
    //  *ptr.add(std::mem::size_of::<Self>() - 1)
    // };
    // hi_byte >> Self::SHIFT8
    //
    // But LLVM apparently upgrades this to a word-aligned load (i.e. the code
    // below) regardless. :D

    (self.len.get() >> Self::SHIFT) as u8
  }

  /// Creates a new, non-`SMALL` yarn with the given pointer, length, and tag.
  ///
  /// # Safety
  ///
  /// `ptr` must be valid for reading `len` bytes.
  ///
  /// If tag is `STATIC`, then `ptr` must never be deallocated. If the tag is
  /// `HEAP`, `ptr` must be free-able via dealloc with a (len, 1) layout and
  /// valid for writing `len` bytes.
  #[inline(always)]
  pub const unsafe fn from_ptr_len_tag(
    ptr: *const u8,
    len: usize,
    tag: u8,
  ) -> Self {
    assert!(
      len < usize::MAX / 4,
      "yarns cannot be larger than a quarter of the address space"
    );
    debug_assert!(
      tag != 0 || len != 0,
      "zero-length and zero tag are not permitted simultaneously."
    );
    debug_assert!(tag != Self::SMALL);

    Self {
      ptr: PtrOrBytes { ptr },
      len: NonZeroUsize::new_unchecked(len | (tag as usize) << Self::SHIFT),
    }
  }

  /// Returns the currently valid union variant for this yarn.
  #[inline(always)]
  const fn layout(&self) -> Layout {
    match self.is_small() {
      true => unsafe {
        // SAFETY: When self.is_small, the small variant is always active.
        Layout::Small(mem::transmute::<&RawYarn, &Small>(self))
      },
      false => unsafe {
        // SAFETY: Otherwise, the slice variant is always active.
        Layout::Slice(mem::transmute::<&RawYarn, &Slice>(self))
      },
    }
  }

  /// Returns the currently valid union variant for this yarn.
  #[inline(always)]
  fn layout_mut(&mut self) -> LayoutMut {
    match self.is_small() {
      true => unsafe {
        // SAFETY: When self.is_small, the small variant is always active.
        LayoutMut::Small(mem::transmute::<&mut RawYarn, &mut Small>(self))
      },
      false => unsafe {
        // SAFETY: Otherwise, the slice variant is always active.
        LayoutMut::Slice(mem::transmute::<&mut RawYarn, &mut Slice>(self))
      },
    }
  }

  /// Returns a reference to an empty `RawYarn` of any lifetime.
  #[inline]
  pub fn empty<'a>() -> &'a RawYarn {
    static STORAGE: MaybeUninit<RawYarn> = MaybeUninit::new(RawYarn::new(b""));
    unsafe {
      // SAFETY: MaybeUninit::new() creates well-initialized memory.
      STORAGE.assume_init_ref()
    }
  }

  /// Returns a `RawYarn` pointing to the given static string, without copying.
  #[inline]
  pub const fn new(s: &'static [u8]) -> Self {
    if s.len() < Self::SSO_LEN {
      unsafe {
        // SAFETY: We just checked s.len() < Self::SSO_LEN.
        return Self::from_slice_inlined_unchecked(s.as_ptr(), s.len());
      }
    }

    unsafe {
      // SAFETY: s is a static string, because the argument is 'static.
      Self::from_ptr_len_tag(s.as_ptr(), s.len(), Self::STATIC)
    }
  }

  /// Returns an empty `RawYarn`.
  #[inline(always)]
  pub const fn len(self) -> usize {
    match self.layout() {
      Layout::Small(s) => s.len as usize & !Self::MASK8,
      Layout::Slice(s) => s.len & !Self::MASK,
    }
  }

  /// Returns whether this `RawYarn` needs to be dropped (i.e., if it is holding
  /// onto memory resources).
  #[inline(always)]
  pub const fn on_heap(self) -> bool {
    self.kind() == Self::HEAP
  }

  /// Returns whether this `RawYarn` is SSO.
  #[inline(always)]
  pub const fn is_small(self) -> bool {
    self.kind() == Self::SMALL
  }

  /// Returns whether this `RawYarn` is SSO.
  #[inline(always)]
  pub const fn is_immortal(self) -> bool {
    self.kind() != Self::ALIASED
  }

  /// Frees heap memory owned by this raw yarn.
  ///
  /// # Safety
  ///
  /// This function must be called at most once, when the raw yarn is being
  /// disposed of.
  #[inline(always)]
  pub unsafe fn destroy(self) {
    if !self.on_heap() {
      return;
    }

    debug_assert!(self.len() > 0);
    let layout = alloc::Layout::for_value(self.as_slice());
    alloc::dealloc(self.ptr.ptr as *mut u8, layout)
  }

  /// Returns a pointer into the data for this raw yarn.
  #[inline(always)]
  pub const fn as_ptr(&self) -> *const u8 {
    match self.layout() {
      Layout::Small(s) => s.data.as_ptr().cast(),
      Layout::Slice(s) => s.ptr,
    }
  }

  /// Returns a pointer into the data for this raw yarn.
  #[inline(always)]
  pub fn as_mut_ptr(&mut self) -> *mut u8 {
    match self.layout_mut() {
      LayoutMut::Small(s) => s.data.as_mut_ptr().cast(),
      LayoutMut::Slice(s) => s.ptr.cast_mut(),
    }
  }

  /// Converts this RawYarn into a byte slice.
  #[inline(always)]
  pub const fn as_slice(&self) -> &[u8] {
    unsafe {
      // SAFETY: the output lifetime ensures that `self` cannot move away.
      slice::from_raw_parts(self.as_ptr(), self.len())
    }
  }

  /// Converts this RawYarn into a mutable byte slice.
  ///
  /// # Safety
  ///
  /// This must only be called on `SMALL` or `HEAP` yarns.
  #[inline(always)]
  pub unsafe fn as_mut_slice(&mut self) -> &mut [u8] {
    debug_assert!(self.is_small() || self.on_heap());
    unsafe {
      // SAFETY: the output lifetime ensures that `self` cannot move away.
      slice::from_raw_parts_mut(self.as_mut_ptr(), self.len())
    }
  }

  /// Returns a `RawYarn` by making a copy of the given slice.
  #[inline(always)]
  pub fn copy_slice(s: &[u8]) -> Self {
    match Self::from_slice_inlined(s) {
      Some(inl) => inl,
      None => Self::from_heap(s.into()),
    }
  }

  /// Returns a `RawYarn` by making an alias of the given slice.
  ///
  /// # Safety
  ///
  /// `s` must outlive all uses of the returned yarn.
  #[inline(always)]
  pub const unsafe fn alias_slice(s: &[u8]) -> Self {
    if let Some(inlined) = Self::from_slice_inlined(s) {
      return inlined;
    }

    Self::from_ptr_len_tag(s.as_ptr(), s.len(), Self::ALIASED)
  }

  /// Returns a new `RawYarn` containing the contents of the given slice.
  ///
  /// # Safety
  ///
  /// `len < Self::SSO`, and `ptr` must be valid for reading `len` bytes.
  #[inline]
  pub const unsafe fn from_slice_inlined_unchecked(
    ptr: *const u8,
    len: usize,
  ) -> Self {
    debug_assert!(len <= Self::SSO_LEN);

    let mut small = Small {
      data: [0; Self::SSO_LEN],
      len: (len as u8) | Self::SMALL << Self::SHIFT8,
    };

    // There's no way to get an *mut to `small.data`, so we do an iteration,
    // instead. This loop can be trivially converted into a memcpy by the
    // optimizer.
    let mut i = 0;
    while i < len {
      small.data[i] = *ptr.add(i);
      i += 1;
    }

    // Small and RawYarn are both POD.
    mem::transmute::<Small, RawYarn>(small)
  }

  /// Returns a new `RawYarn` containing the contents of the given slice.
  ///
  /// This function will always return an inlined string.
  #[inline]
  pub const fn from_slice_inlined(s: &[u8]) -> Option<Self> {
    if s.len() > Self::SSO_LEN {
      return None;
    }

    unsafe {
      // SAFETY: s.len() is within bounds; we just checked it above.
      Some(Self::from_slice_inlined_unchecked(s.as_ptr(), s.len()))
    }
  }

  /// Returns a `RawYarn` containing a single UTF-8-encoded Unicode scalar.
  ///
  /// This function does not allocate: every `char` fits in an inlined `RawYarn`.
  #[inline(always)]
  pub const fn from_char(c: char) -> Self {
    let (data, len) = crate::utf8::encode_utf8(c);
    unsafe {
      // SAFETY: len is at most 4, 4 < Self::SSO_LEN.
      Self::from_slice_inlined_unchecked(data.as_ptr(), len)
    }
  }

  /// Returns a `RawYarn` containing a single byte, without allocating.
  #[inline(always)]
  pub const fn from_byte(c: u8) -> Self {
    unsafe {
      // SAFETY: 1 < Self::SSO_LEN.
      Self::from_slice_inlined_unchecked(&c, 1)
    }
  }

  /// Returns a `RawYarn` consisting of the concatenation of the given slices.
  ///
  /// Does not allocate if the resulting concatenation can be inlined.
  ///
  /// # Safety
  ///
  /// `total_len < Self::SSO_LEN`.
  pub unsafe fn concat<'a>(
    total_len: usize,
    iter: impl IntoIterator<Item = &'a [u8]>,
  ) -> Self {
    if total_len > Self::SSO_LEN {
      let mut buf = Vec::with_capacity(total_len);
      for b in iter {
        buf.extend_from_slice(b);
      }

      return Self::from_heap(buf.into());
    }

    let mut cursor = 0;
    let mut data = [0; Self::SSO_LEN];
    for b in iter {
      data[cursor..cursor + b.len()].copy_from_slice(b);
      cursor += b.len();
    }

    Self::from_slice_inlined(&data[..cursor]).unwrap_unchecked()
  }

  /// Returns a `RawYarn` by taking ownership of the given allocation.
  #[inline]
  pub fn from_heap(s: Box<[u8]>) -> Self {
    if let Some(inline) = Self::from_slice_inlined(&s) {
      return inline;
    }

    let len = s.len();
    let ptr = Box::into_raw(s) as *mut u8;
    unsafe {
      // SAFETY: s is a heap allocation of the appropriate layout for HEAP,
      // which we own uniquely because we dismantled it from a box.
      Self::from_ptr_len_tag(ptr, len, Self::HEAP)
    }
  }

  /// Builds a new yarn from the given formatting arguments, without allocating
  /// in the trival and small cases.
  pub fn from_fmt_args(args: fmt::Arguments) -> Self {
    if let Some(constant) = args.as_str() {
      return Self::new(constant.as_bytes());
    }

    enum Buf {
      Sso(usize, [u8; RawYarn::SSO_LEN]),
      Vec(Vec<u8>),
    }
    impl fmt::Write for Buf {
      fn write_str(&mut self, s: &str) -> fmt::Result {
        match self {
          Self::Sso(len, bytes) => {
            let new_len = *len + s.len();
            if new_len > RawYarn::SSO_LEN {
              let mut vec = Vec::from(&bytes[..*len]);
              vec.extend_from_slice(s.as_bytes());

              *self = Self::Vec(vec);
            } else {
              let _ = &bytes[*len..new_len].copy_from_slice(s.as_bytes());
              *len = new_len;
            }
          }
          Self::Vec(vec) => vec.extend_from_slice(s.as_bytes()),
        }

        Ok(())
      }
    }

    let mut w = Buf::Sso(0, [0; RawYarn::SSO_LEN]);
    let _ = w.write_fmt(args);
    match w {
      Buf::Sso(len, bytes) => Self::from_slice_inlined(&bytes[..len]).unwrap(),
      Buf::Vec(vec) => Self::from_heap(vec.into()),
    }
  }
}
