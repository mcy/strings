//! Readable test output generating from tree-structured data.

use std::io;
use std::io::Write;

use byteyarn::YarnBox;

mod json;
mod yaml;

/// A tree-shaped document that can be pretty-printed, for generating goldens.
///
/// Golden tests that output tree-shaped data can use `Doc` to generate
/// diff-friendly, readable output.
pub struct Doc<'a> {
  entries: Vec<(Option<YarnBox<'a, str>>, Elem<'a>)>,
}

/// The format output to use when rendering a document.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Format {
  /// Output as YAML.
  Yaml,
  /// Output as JSON.
  Json,
}

impl Default for Format {
  fn default() -> Self {
    Self::Yaml
  }
}

/// Options for rendering a [`Doc`] as a string.
pub struct Options {
  // The format to output in; defaults to YAML.
  pub format: Format,
  // The number of spaces to use for indentation.
  pub tab_width: usize,

  // The maximum number of columns to have before wrapping occurs.
  pub max_columns: usize,
  // The maximum number of columns for a one-line array.
  pub max_array_width: usize,
  // The maximum number of columns for a one-line object.
  pub max_object_width: usize,
}

impl Default for Options {
  fn default() -> Self {
    Self {
      format: Format::default(),
      tab_width: 2,
      max_columns: 80,
      max_array_width: 50,
      max_object_width: 40,
    }
  }
}

/// A type which can be an element of a [`Doc`].
///
/// All of the primitive number types and types which convert to `YarnBox<[u8]>`
/// can be used as `Doc` values. `Option<T>` for `T: DocValue` can also be
/// used, and will only be inserted if it is `Some`.
pub trait Value<'a> {
  fn append_to(self, doc: &mut Doc<'a>);
}

impl<'a> Doc<'a> {
  /// Returns a new, empty `Doc`.
  pub fn new() -> Self {
    Self { entries: Vec::new() }
  }

  /// Returns a new `Doc` with a single entry.
  pub fn single(
    name: impl Into<YarnBox<'a, str>>,
    value: impl Value<'a>,
  ) -> Self {
    Self::new().entry(name, value)
  }

  /// Appends a sequence of values to this document.
  pub fn push(mut self, elements: impl IntoIterator<Item: Value<'a>>) -> Self {
    for e in elements {
      e.append_to(&mut self);
    }
    self
  }

  /// Appends an entry with the given name to this document.
  pub fn entry(
    mut self,
    name: impl Into<YarnBox<'a, str>>,
    value: impl Value<'a>,
  ) -> Self {
    let prev = self.entries.len();
    value.append_to(&mut self);
    if prev < self.entries.len() {
      self.entries.last_mut().unwrap().0 = Some(name.into());
    }
    self
  }

  /// Appends an entry which is an array with the given elements.
  pub fn array(
    self,
    name: impl Into<YarnBox<'a, str>>,
    elements: impl IntoIterator<Item: Value<'a>>,
  ) -> Self {
    self.entry(name, Self::new().push(elements))
  }

  // Converts this document into a string, using the given options.
  pub fn to_string(&self, options: &Options) -> String {
    let mut out = Vec::new();
    let _ = self.render(&mut out, options);
    String::from_utf8(out).unwrap()
  }

  /// Converts this document into a string, writing it to the given output with
  /// the given options.
  pub fn render(
    &self,
    out: &mut dyn Write,
    options: &Options,
  ) -> io::Result<()> {
    let mut doc = allman::Doc::new();

    match options.format {
      Format::Yaml => yaml::build(
        yaml::Args { options, root: true, in_list: false },
        self,
        &mut doc,
      ),
      Format::Json => json::build(options, self, &mut doc),
    }

    doc.render(out, &allman::Options { max_columns: options.max_columns })
  }
}

impl Default for Doc<'_> {
  fn default() -> Self {
    Self::new()
  }
}

enum Elem<'a> {
  Bool(bool),
  Int(i128),
  UInt(u128),
  Fp(f64),
  String(YarnBox<'a>),
  Doc(Doc<'a>),
}

impl<'a, T: Value<'a>> Value<'a> for Option<T> {
  fn append_to(self, doc: &mut Doc<'a>) {
    if let Some(v) = self {
      v.append_to(doc)
    }
  }
}
impl<'a> Value<'a> for Doc<'a> {
  fn append_to(self, doc: &mut Doc<'a>) {
    doc.entries.push((None, Elem::Doc(self)))
  }
}

macro_rules! impl_from {
  ($({$($T:ty),*} => $V:ident,)*) => {$($(
    impl<'a> Value<'a> for $T {
      fn append_to(self, doc: &mut Doc<'a>) {
        doc.entries.push((None, Elem::$V(self as _)))
      }
    }
  )*)*}
}

impl_from! {
  {bool} => Bool,
  {i8, i16, i32, i64, i128, isize} => Int,
  {u8, u16, u32, u64, u128, usize} => UInt,
  {f32, f64} => Fp,
}

macro_rules! impl_from_yarn {
  ($(for<$lt:lifetime> $($T:ty),* => $U:ty,)*) => {$($(
    impl<$lt> Value<$lt> for $T {
      fn append_to(self, doc: &mut Doc<$lt>) {
        doc.entries.push((None, Elem::String(<$U>::from(self).into_bytes())))
      }
    }
  )*)*}
}

impl_from_yarn! {
  for<'a> &'a [u8], Vec<u8>, YarnBox<'a, [u8]> => YarnBox<'a, [u8]>,
  for<'a> char, &'a str, String, YarnBox<'a, str> => YarnBox<'a, str>,
}
