//! Error printing facilities.
//!
//! These functions are used to simplify the display of various errors to
//! the user.

use std::cell::Cell;
use std::cell::RefCell;
use std::fmt;
use std::io;
use std::mem;
use std::panic;
use std::process;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering::SeqCst;
use std::sync::Arc;
use std::sync::Mutex;
use std::thread;

use crate::file::Context;

mod builtin;
mod diagnostic;
mod render;

pub use builtin::builtins;
pub use builtin::Builtins;
pub use diagnostic::Diagnostic;

/// Adds a new error to [`report::current()`][current].
#[track_caller]
pub fn error(fcx: &Context, message: impl fmt::Display) -> Diagnostic {
  current().error(fcx, message)
}

/// Adds a new warning to [`report::current()`][current].
#[track_caller]
pub fn warn(fcx: &Context, message: impl fmt::Display) -> Diagnostic {
  current().warn(fcx, message)
}

/// A collection of errors that may built up over the course of an operation.
#[derive(Clone)]
pub struct Report {
  id: u32,
  state: Arc<State>,
}

struct State {
  opts: RenderOptions,
  has_error: AtomicBool,
  next_id: AtomicU32,
  sorted_diagnostics: Mutex<Vec<diagnostic::Info>>,
  recent_diagnostics: Mutex<Vec<(u32, diagnostic::Info)>>,
}

/// Options for a [`Report`].
pub struct RenderOptions {
  /// Whether to color the output.
  pub color: bool,
  /// Whether to add a note to each diagnostic showing where it was
  /// reported.
  pub show_report_locations: bool,
}

impl Default for RenderOptions {
  fn default() -> Self {
    Self {
      color: true,
      show_report_locations: cfg!(debug_assertions),
    }
  }
}

impl Report {
  /// Creates a new report.
  pub fn new() -> Self {
    Self::with_options(RenderOptions::default())
  }

  /// Creates a report with the given options for rendering.
  pub fn with_options(opts: RenderOptions) -> Self {
    Self {
      id: 0,
      state: Arc::new(State {
        opts,
        has_error: AtomicBool::new(false),
        next_id: AtomicU32::new(1),
        sorted_diagnostics: Default::default(),
        recent_diagnostics: Default::default(),
      }),
    }
  }

  /// Returns a wrapper for accessing commonly-used, built-in message types.
  pub fn builtins(self) -> Builtins {
    Builtins(self)
  }

  /// Adds a new error to this report.
  #[track_caller]
  pub fn error(self, fcx: &Context, message: impl fmt::Display) -> Diagnostic {
    Diagnostic {
      rcx: self,
      fcx,
      info: diagnostic::Info {
        message: message.to_string(),
        kind: Some(diagnostic::Kind::Error),
        snippets: Vec::new(),
        notes: Vec::new(),
        reported_at: Some(panic::Location::caller()),
      },
    }
  }

  /// Like [`Report::error()`], but accepts a closure for generating the
  /// diagnostic message.
  #[track_caller]
  pub fn error_by(
    self,
    fcx: &Context,
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Diagnostic {
    self.error(fcx, display_by(fmt))
  }

  /// Adds a new warning to this report.
  #[track_caller]
  pub fn warn(self, fcx: &Context, message: impl fmt::Display) -> Diagnostic {
    Diagnostic {
      rcx: self,
      fcx,
      info: diagnostic::Info {
        message: message.to_string(),
        kind: Some(diagnostic::Kind::Warning),
        snippets: Vec::new(),
        notes: Vec::new(),
        reported_at: Some(panic::Location::caller()),
      },
    }
  }

  /// Like [`Report::warn()`], but accepts a closure for generating the
  /// diagnostic message.
  #[track_caller]
  pub fn warn_by(
    self,
    fcx: &Context,
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Diagnostic {
    self.warn(fcx, display_by(fmt))
  }

  /// Returns a `Fatal` regardless of whether this report contains any errors.
  pub fn fatal<T>(self) -> Result<T, Fatal> {
    Err(Fatal(self))
  }

  /// If this report contains any errors, return s `Err(Fatal)`; otherwise,
  /// it returns `Ok(ok)`.
  ///
  /// This is a useful function for completing some operation that could have
  /// generated error diagnostics.
  pub fn fatal_or<T>(self, ok: T) -> Result<T, Fatal> {
    if !self.state.has_error.load(SeqCst) {
      return Ok(ok);
    }

    self.fatal()
  }

  /// Collates all of the "unsorted diagnostics" into the "sorted diagnostics",
  /// sorting them by thread id. This ensures that all diagnostics coming from
  /// a particular thread are together.
  pub fn collate(&mut self) {
    render::collate(self)
  }

  /// Consumes this `Report` and dumps its diagnostics to `sink`.
  pub fn finish(self, fcx: &Context, sink: impl io::Write) -> io::Result<()> {
    render::finish(self, fcx, sink)
  }
}

thread_local! {
  static REPORT: RefCell<Option<Report>> = RefCell::new(None);
}

pub(crate) fn try_current() -> Option<Report> {
  REPORT.with(|rcx| rcx.borrow().clone())
}

/// Installs a `Report` as this thread's current report.
///
/// Returns a cleanup object that places the previous report back in place
/// when it goes out of scope.
pub fn install(mut rcx: Report) -> impl Drop {
  rcx.id = rcx.state.next_id.fetch_add(1, SeqCst);

  REPORT.with(|tls| {
    let mut tls = tls.borrow_mut();
    let old = mem::replace(&mut *tls, Some(rcx));

    struct Replacer(Option<Report>);
    impl Drop for Replacer {
      fn drop(&mut self) {
        if let Some(old) = self.0.take() {
          mem::forget(old);
        }
      }
    }

    Replacer(old)
  })
}

/// Returns this thread's `Report`.
///
/// # Panics
///
/// If this thread did not have a report initialized with [`install()`], this
/// function will panic.
pub fn current() -> Report {
  match try_current() {
    Some(rcx) => rcx,
    None => {
      const MSG: &str =
        "called Report::with_current() on a thread without a report installed";
      let current = thread::current();

      match current.name() {
        Some(name) => panic!("{MSG} ({name:?})"),
        None => panic!("{MSG} ({:?})", current.id()),
      }
    }
  }
}

impl Default for Report {
  fn default() -> Self {
    Self::new()
  }
}

/// Returned by functions that take a [`Report`] for writing errors to, if any
/// errors were written to it.
pub struct Fatal(Report);

impl Fatal {
  /// Prints all diagnostics to stderr and terminates the program.
  pub fn terminate(self, fcx: &Context) -> ! {
    eprintln!("{}", self.to_string(fcx));
    process::exit(1);
  }

  /// Panics with the [`Report`]'s diagnostics as the panic message.
  pub fn panic(self, fcx: &Context) -> ! {
    panic::panic_any(self.to_string(fcx))
  }

  /// Panics with the [`Report`]'s diagnostics as the panic message.
  pub fn to_string(self, fcx: &Context) -> String {
    display_by(|f| render::render_fmt(&self.0, fcx, f)).to_string()
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
