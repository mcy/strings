//! Conversion trait impls.

use std::borrow::Borrow;
use std::fmt;
use std::str::Utf8Error;

use crate::Yarn;
use crate::YarnRef;

#[derive(Clone, Debug)]
pub struct NonCopy(());

impl fmt::Display for NonCopy {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.write_str("cannot convert yarn to non-owning yarn")
  }
}

impl<'a, Buf> TryFrom<Yarn<'a, Buf>> for YarnRef<'a, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  type Error = NonCopy;

  fn try_from(y: Yarn<'a, Buf>) -> Result<Self, NonCopy> {
    y.to_ref().ok_or(NonCopy(()))
  }
}

impl<'a> TryFrom<Yarn<'a, [u8]>> for Yarn<'a, str> {
  type Error = Utf8Error;

  fn try_from(y: Yarn<'a, [u8]>) -> Result<Self, Utf8Error> {
    y.to_utf8()
  }
}

impl<'a> TryFrom<YarnRef<'a, [u8]>> for YarnRef<'a, str> {
  type Error = Utf8Error;

  fn try_from(y: YarnRef<'a, [u8]>) -> Result<Self, Utf8Error> {
    y.to_utf8()
  }
}

impl<'a> From<Yarn<'a, str>> for Yarn<'a, [u8]> {
  fn from(y: Yarn<'a, str>) -> Self {
    y.into_bytes()
  }
}

impl<'a> From<YarnRef<'a, str>> for YarnRef<'a, [u8]> {
  fn from(y: YarnRef<'a, str>) -> Self {
    y.into_bytes()
  }
}

impl From<u8> for Yarn<'_, [u8]> {
  fn from(c: u8) -> Self {
    Self::from_byte(c)
  }
}

impl From<u8> for YarnRef<'_, [u8]> {
  fn from(c: u8) -> Self {
    Self::from_byte(c)
  }
}

impl<Buf> From<char> for Yarn<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  fn from(c: char) -> Self {
    Self::from_char(c)
  }
}

impl<Buf> From<char> for YarnRef<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  fn from(c: char) -> Self {
    Self::from_char(c)
  }
}

impl<'a, Slice, Buf> From<&'a Slice> for Yarn<'a, Buf>
where
  Buf: crate::Buf + ?Sized,
  Slice: AsRef<Buf> + ?Sized,
{
  fn from(s: &'a Slice) -> Self {
    Self::new(s)
  }
}

impl<'a, Slice, Buf> From<&'a Slice> for YarnRef<'a, Buf>
where
  Buf: crate::Buf + ?Sized,
  Slice: AsRef<Buf> + ?Sized,
{
  fn from(s: &'a Slice) -> Self {
    Self::new(s)
  }
}

impl From<Box<[u8]>> for Yarn<'_, [u8]> {
  fn from(s: Box<[u8]>) -> Self {
    Self::from_box(s)
  }
}

impl From<Vec<u8>> for Yarn<'_, [u8]> {
  fn from(s: Vec<u8>) -> Self {
    Self::from_vec(s)
  }
}

impl<Buf> From<Box<str>> for Yarn<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  fn from(s: Box<str>) -> Self {
    Self::from_str_box(s)
  }
}

impl<Buf> From<String> for Yarn<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  fn from(s: String) -> Self {
    Self::from_string(s)
  }
}

impl<Buf> From<Yarn<'_, Buf>> for Box<[u8]>
where
  Buf: crate::Buf + ?Sized,
{
  fn from(y: Yarn<Buf>) -> Self {
    y.into_box()
  }
}

impl<Buf> From<YarnRef<'_, Buf>> for Box<[u8]>
where
  Buf: crate::Buf + ?Sized,
{
  fn from(y: YarnRef<Buf>) -> Self {
    y.to_box()
  }
}

impl<Buf> From<Yarn<'_, Buf>> for Vec<u8>
where
  Buf: crate::Buf + ?Sized,
{
  fn from(y: Yarn<Buf>) -> Self {
    y.into_vec()
  }
}

impl<Buf> From<YarnRef<'_, Buf>> for Vec<u8>
where
  Buf: crate::Buf + ?Sized,
{
  fn from(y: YarnRef<Buf>) -> Self {
    y.to_vec()
  }
}

impl From<Yarn<'_, str>> for Box<str> {
  fn from(y: Yarn<str>) -> Self {
    y.into_str_box()
  }
}

impl From<YarnRef<'_, str>> for Box<str> {
  fn from(y: YarnRef<str>) -> Self {
    y.to_str_box()
  }
}

impl From<Yarn<'_, str>> for String {
  fn from(y: Yarn<str>) -> Self {
    y.into_string()
  }
}

impl From<YarnRef<'_, str>> for String {
  fn from(y: YarnRef<str>) -> Self {
    y.to_string()
  }
}

// AsRef / Borrow

impl<Buf> AsRef<Buf> for Yarn<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  fn as_ref(&self) -> &Buf {
    self.as_slice()
  }
}

impl<Buf> AsRef<Buf> for YarnRef<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  fn as_ref(&self) -> &Buf {
    self.as_slice()
  }
}

impl<Buf> Borrow<Buf> for Yarn<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  fn borrow(&self) -> &Buf {
    self.as_slice()
  }
}

impl<Buf> Borrow<Buf> for YarnRef<'_, Buf>
where
  Buf: crate::Buf + ?Sized,
{
  fn borrow(&self) -> &Buf {
    self.as_slice()
  }
}
