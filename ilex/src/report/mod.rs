//! Error printing facilities.
//!
//! These functions are used to simplify the display of various errors to
//! the user.

use std::backtrace::Backtrace;
use std::cell::Cell;
use std::cell::RefCell;
use std::fmt;
use std::io;
use std::io::Write;
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
pub use builtin::Expected;
pub use diagnostic::Diagnostic;

/// Adds a new error to [`report::current()`][current].
#[track_caller]
pub fn error(message: impl fmt::Display) -> Diagnostic {
  current().error(message)
}

/// Adds a new warning to [`report::current()`][current].
#[track_caller]
pub fn warn(message: impl fmt::Display) -> Diagnostic {
  current().warn(message)
}

/// Adds a new top-level note to [`report::current()`][current].
#[track_caller]
pub fn note(message: impl fmt::Display) -> Diagnostic {
  current().note(message)
}

/// A collection of errors that may built up over the course of an operation.
#[derive(Clone)]
pub struct Report {
  id: u32,
  ctx: u32,
  state: Arc<State>,
}

struct State {
  opts: Options,
  has_error: AtomicBool,
  next_id: AtomicU32,
  sorted_diagnostics: Mutex<Vec<diagnostic::Info>>,
  recent_diagnostics: Mutex<Vec<(u32, diagnostic::Info)>>,
}

/// Options for a [`Report`].
pub struct Options {
  /// Whether to color the output.
  pub color: bool,
  /// Whether to add a note to each diagnostic showing where it was
  /// reported.
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
  /// Creates a report with the given options for rendering.
  pub(crate) fn new(ctx: &Context, opts: Options) -> Self {
    Self {
      id: 0,
      ctx: ctx.ctx_id(),
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
  pub fn error(self, message: impl fmt::Display) -> Diagnostic {
    Diagnostic {
      report: self,
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
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Diagnostic {
    self.error(display_by(fmt))
  }

  /// Adds a new warning to this report.
  #[track_caller]
  pub fn warn(self, message: impl fmt::Display) -> Diagnostic {
    Diagnostic {
      report: self,
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
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Diagnostic {
    self.warn(display_by(fmt))
  }

  /// Adds a new top-level note to this report.
  #[track_caller]
  pub fn note(self, message: impl fmt::Display) -> Diagnostic {
    Diagnostic {
      report: self,
      info: diagnostic::Info {
        message: message.to_string(),
        kind: Some(diagnostic::Kind::Note),
        snippets: Vec::new(),
        notes: Vec::new(),
        reported_at: Some(panic::Location::caller()),
      },
    }
  }

  /// Like [`Report::note()`], but accepts a closure for generating the
  /// diagnostic message.
  #[track_caller]
  pub fn note_by(
    self,
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Diagnostic {
    self.warn(display_by(fmt))
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
  pub fn collate(&self) {
    render::collate(self)
  }

  /// Consumes this `Report` and dumps its diagnostics to `sink`.
  pub fn finish(self, sink: impl io::Write) -> io::Result<()> {
    self.in_context(|this, ctx| render::finish(this, ctx, sink))
  }

  /// Executes `cb` after looking up the context that "owns" this report.
  ///
  /// Danger: calling any diagnostic-generating function in the callback will
  /// self-deadlock.
  fn in_context<R>(self, cb: impl FnOnce(Report, &Context) -> R) -> R {
    Context::find_and_run(self.ctx, |ctx| {
      match ctx {
        Some(ctx) => cb(self, ctx),
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

thread_local! {
  static REPORT: RefCell<Option<Report>> = RefCell::new(None);
}

pub(crate) fn try_current() -> Option<Report> {
  REPORT.with(|report| report.borrow().clone())
}

/// An RAII type that undoes a call to `report::install()`.
pub struct Installation(Option<Report>);
impl Drop for Installation {
  fn drop(&mut self) {
    if let Some(old) = self.0.take() {
      mem::forget(old);
    }
  }
}

/// Installs a `Report` as this thread's current report.
///
/// Returns a cleanup object that places the previous report back in place
/// when it goes out of scope.
pub fn install(mut report: Report) -> Installation {
  report.id = report.state.next_id.fetch_add(1, SeqCst);
  REPORT.with(|tls| {
    Installation(mem::replace(&mut *tls.borrow_mut(), Some(report)))
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
    Some(report) => report,
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

/// Returned by functions that take a [`Report`] for writing errors to, if any
/// errors were written to it.
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
    self
      .0
      .clone()
      .in_context(|this, ctx| render::render_fmt(&this, ctx, f))
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
