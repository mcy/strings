//! Diagnostics and error reports.
//!
//! This module contains types for generating an *error report*: a collection of
//! diagnostics that describe why an operation failed in detail. Diagnostics
//! are basically fancy compiler errors: they use [`Span`]s to present faulty
//! input in context.
//!
//! The [`Report`] type is a reference-counted list of diagnostics, which is
//! typically passed by reference into functions, but can be copied to simplify
//! lifetimes, since it's reference-counted.

use std::backtrace::Backtrace;
use std::cell::Cell;
use std::fmt;
use std::io;
use std::io::Write;
use std::panic;
use std::panic::Location;
use std::process;
use std::sync::Arc;
use std::thread;

use crate::file::Context;
#[cfg(doc)]
use crate::file::Span;

mod builtin;
mod diagnostic;
mod render;

pub use builtin::Builtins;
pub use builtin::Expected;
pub use diagnostic::Diagnostic;
use diagnostic::Kind;
pub use diagnostic::Loc;
pub use diagnostic::ToLoc;

/// A collection of errors can may built up over the course of an operation.
///
/// To construct a report, see [`Context::new_report()`]. The context that
/// constructs a report is the only one whose [`Span`]s should be passed into
/// it; doing otherwise will result in unspecified output (or probably a panic).
#[derive(Clone)]
pub struct Report {
  ctx: u32,
  state: Arc<render::State>,
}

/// Options for a [`Report`].
pub struct Options {
  /// Whether to color the output when rendered.
  pub color: bool,
  /// Whether to add a note to each diagnostic showing where in the source
  /// code it was reported. `ilex` makes a best-case effort to ensure this
  /// location is in *your* code.
  pub show_report_locations: bool,
}

impl Default for Options {
  fn default() -> Self {
    Self {
      color: true,
      show_report_locations: cfg!(debug_assertions),
    }
  }
}

impl Report {
  /// Returns a wrapper for accessing commonly-used, built-in message types.
  ///
  /// See [`Builtins`].
  pub fn builtins(&self) -> Builtins {
    Builtins(self.clone())
  }

  /// Adds a new error to this report.
  ///
  /// The returned [`Diagnostic`] object can be used to add spans, notes, and
  /// remarks, to generate a richer diagnostic.
  #[track_caller]
  pub fn error(&self, message: impl fmt::Display) -> Diagnostic {
    self.new_diagnostic(Kind::Error, message.to_string())
  }

  /// Like [`Report::error()`], but accepts a closure for generating the
  /// diagnostic message.
  #[track_caller]
  pub fn error_by(
    &self,
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Diagnostic {
    self.new_diagnostic(Kind::Error, display_by(fmt).to_string())
  }

  /// Adds a new warning to this report.
  ///
  /// The returned [`Diagnostic`] object can be used to add spans, notes, and
  /// remarks, to generate a richer diagnostic.
  #[track_caller]
  pub fn warn(&self, message: impl fmt::Display) -> Diagnostic {
    self.new_diagnostic(Kind::Warning, message.to_string())
  }

  /// Like [`Report::warn()`], but accepts a closure for generating the
  /// diagnostic message.
  #[track_caller]
  pub fn warn_by(
    &self,
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Diagnostic {
    self.new_diagnostic(Kind::Warning, display_by(fmt).to_string())
  }

  /// Adds a new top-level note to this report.
  ///
  /// The returned [`Diagnostic`] object can be used to add spans, notes, and
  /// remarks, to generate a richer diagnostic.
  #[track_caller]
  pub fn note(&self, message: impl fmt::Display) -> Diagnostic {
    self.new_diagnostic(Kind::Note, message.to_string())
  }

  /// Like [`Report::note()`], but accepts a closure for generating the
  /// diagnostic message.
  #[track_caller]
  pub fn note_by(
    &self,
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Diagnostic {
    self.new_diagnostic(Kind::Note, display_by(fmt).to_string())
  }

  #[track_caller]
  fn new_diagnostic(&self, kind: Kind, message: String) -> Diagnostic {
    Diagnostic::new(self.clone(), kind, message).reported_at(Location::caller())
  }

  /// Returns a [`Fatal`] regardless of whether this report contains any errors.
  pub fn fatal<T>(&self) -> Result<T, Fatal> {
    Err(Fatal(self.clone()))
  }

  /// If this report contains any errors, returns [`Err(Fatal)`][Fatal];
  /// otherwise, it returns `Ok(ok)`.
  ///
  /// This is a useful function for completing some operation that could have
  /// generated error diagnostics.
  ///
  /// See [`Fatal`].
  pub fn fatal_or<T>(&self, ok: T) -> Result<T, Fatal> {
    if !self.state.has_error() {
      return Ok(ok);
    }

    self.fatal()
  }

  /// Collates all of the "unsorted diagnostics" into the "sorted diagnostics",
  /// sorting them by thread id.
  ///
  /// This ensures that all diagnostics coming from a particular thread are
  /// together.
  pub fn collate(&self) {
    self.state.collate()
  }

  /// Writes out the contents of this diagnostic to `sink`.
  pub fn write_out(&self, sink: impl io::Write) -> io::Result<()> {
    self.in_context(|ctx| render::finish(self, ctx, sink))
  }

  pub(crate) fn new(ctx: &Context, opts: Options) -> Self {
    Self {
      ctx: ctx.ctx_id(),
      state: Arc::new(render::State::new(opts)),
    }
  }

  /// Executes `cb` after looking up the context that "owns" this report.
  ///
  /// Danger: calling any diagnostic-generating function in the callback will
  /// self-deadlock.
  fn in_context<R>(&self, cb: impl FnOnce(&Context) -> R) -> R {
    Context::find_and_run(self.ctx, |ctx| {
      match ctx {
        Some(ctx) => cb(ctx),
        None => {
          let msg = "ilex: attempted to operate on a report, but ilex::Context that owns it has disappeared; this is probably a bug";

          // It is highly probable this will be called while handling a panic.
          // Instead of double panicking (which is an instant abort) we print,
          // flush, print a backtrace, and *then* panic.
          if thread::panicking() {
            eprintln!("{msg}");
            let bt = Backtrace::capture();
            eprintln!("{bt}");
            std::io::stderr().flush().unwrap();
            panic!("double panic!");
          }

          panic!("{msg}")
        }
      }
    })
  }
}

/// An error type for making returning a [`Result`] that will trigger
/// diagnostics printing when unwrapped.
///
/// This is useful for functions that are [`Result`]-ey, like reading a file,
/// but which want to generate diagnostics, too.
pub struct Fatal(Report);

impl Fatal {
  /// Prints all diagnostics to stderr and terminates the program.
  pub fn terminate(self) -> ! {
    eprintln!("{self}");
    process::exit(1);
  }

  /// Panics with the [`Report`]'s diagnostics as the panic message.
  pub fn panic(self) -> ! {
    panic::panic_any(self.to_string())
  }
}

impl fmt::Debug for Fatal {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.in_context(|ctx| render::render_fmt(&self.0, ctx, f))
  }
}

impl fmt::Display for Fatal {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt::Debug::fmt(self, f)
  }
}

/// Returns a `Display`-able value that displays itself by executing a closure.
fn display_by(
  body: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
) -> impl fmt::Display {
  use std::fmt::*;

  struct By<F>(Cell<Option<F>>);
  impl<F: FnOnce(&mut Formatter) -> Result> Display for By<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
      self.0.take().unwrap()(f)
    }
  }

  By(Cell::new(Some(body)))
}
