//! Helpers for working with internal compiler errors (ICEs).
//!
//! This module provides types and other things to make sure you can provide
//! useful crash reports for your users.

use std::backtrace::Backtrace;
use std::backtrace::BacktraceStatus;
use std::io;
use std::panic;
use std::panic::AssertUnwindSafe;
use std::panic::PanicInfo;
use std::panic::UnwindSafe;
use std::sync::Mutex;
use std::thread;

use crate::file::Context;
use crate::report;
use crate::report::Fatal;
use crate::report::Report;

/// Executes a "compiler main function".
///
/// This function takes care of setting up a panic hook for us that will catch
/// any [`Ice`]s for us.
///
/// Generally, the way using this function would look is something like this:
///
// Delete "should_panic" to see what the ICE errors look like.
/// ```should_panic
/// use ilex::ice;
/// use ilex::report;
///
/// fn compile(ctx: &mut ilex::Context) -> Result<(), report::Fatal> {
///   panic!("its not done yet, im too busy writing a lexer library !!! 😡")
/// }
///
/// fn main() {
///   let mut ctx = ilex::Context::new();
/// # report::install(ctx.new_report_with(report::Options {
/// #   color: true,
/// #   show_report_locations: false,
/// # }));
///
///   let opts = ice::Options {
///     what_panicked: Some("my test".to_string()),
///     report_bugs_at: Some("https://github.com/mcy/strings/issues".into()),
///     extra_notes: vec![format!("ilex {}", env!("CARGO_PKG_VERSION"))],
///     ..ice::Options::default()
///   };
///
///   let result = ice::handle(&mut ctx, opts, |ctx| {
///     // Business logic that may panic.
///     compile(ctx)
///   });
///
///   if let Err(fatal) = result {
///     fatal.terminate();
///   }
/// }
/// ```
#[allow(clippy::needless_doctest_main)]
pub fn handle<R, Cb>(
  ctx: &mut Context,
  options: Options,
  callback: Cb,
) -> Result<R, Fatal>
where
  Cb: FnOnce(&mut Context) -> Result<R, Fatal>,
  Cb: UnwindSafe,
{
  static ICE: Mutex<Option<Ice>> = Mutex::new(None);

  let options2 = options.clone();
  let hook = panic::take_hook();
  panic::set_hook(Box::new(move |panic| {
    // Only generate ICEs in threads that have a report, i.e., threads that
    // belong to the compiler directly and not some library's worker pool.
    if report::try_current().is_none() {
      return hook(panic);
    };

    // Generate an ICE and save it for later, if this panic actually makes it
    // out to the main function.
    *ICE.lock().unwrap() = Some(Ice::generate(panic, options2.clone()));
  }));

  let result = panic::catch_unwind(AssertUnwindSafe(|| callback(ctx)));

  // If we caught a panic, add the ICE to our report. There may be an ICE in the
  // global from some other panic that didn't make it all the way out here.
  if result.is_err() {
    let ice = ICE
      .lock()
      .unwrap()
      .take()
      .unwrap_or_else(|| Ice::with_no_context(options));
    ice.report(report::current());
  }

  // We have to do this here, and not in, say, the panic hook, because we want
  // the report to be silently dropped.
  let _ignored = report::current().finish(io::stderr());

  result.unwrap_or_else(|e| panic::resume_unwind(e))
}

/// An internal compiler error (ICE), captured from a panic handler.
///
/// This is a separate type that can be ferried around between locations,
/// because the panic hook executes *before* unwinding, but you may not want to
/// print that as a diagnostic unless that panic bubbles all the way up to your
/// main function.
#[derive(Default)]
pub struct Ice {
  what: Option<String>,
  where_: Option<(String, Option<String>)>,
  why: Option<Backtrace>,
  options: Options,
}

/// Options for generating an ICE.
#[derive(Default, Clone)]
pub struct Options {
  /// Whether to show a backtrace. By default, uses the same rules as normal
  /// Rust (i.e. `RUST_BACKTRACE`). You may want to override it with something
  /// more in-style for your project.
  pub show_backtrace: Option<bool>,

  /// Configures what "unexpectedly panicked" in the output. Defaults to
  /// something generic like "the compiler".
  pub what_panicked: Option<String>,

  /// Configures a link to show users after the "unexpectedly panicked" message.
  /// This should probably look like `https://github.com/me/my-project/issues`.
  pub report_bugs_at: Option<String>,

  /// A static list of notes to append to an error before the backtrace.
  /// For example, rustc's ICE handler shows a GitHub link for filing issues,
  /// the version, git commit, and date the compiler was built at, and some
  /// subset of the flags of the compiler.
  pub extra_notes: Vec<String>,
}

impl Ice {
  /// Generates an ICE with no context. Useful for when you caught a panic but
  /// didn't stow an ICE as expected.
  pub fn with_no_context(options: Options) -> Self {
    Self {
      what: None,
      where_: None,
      why: None,
      options,
    }
  }

  /// Generates an ICE from a panic message.
  ///
  /// The results are "best effort". The Rust backtrace API is incomplete, so we
  /// make do with some... cleverness around parsing the backtrace itself.
  pub fn generate(panic: &PanicInfo, options: Options) -> Self {
    let msg = panic.payload();
    let msg = Option::or(
      msg.downcast_ref::<&str>().copied().map(str::to_string),
      msg.downcast_ref::<String>().cloned(),
    );

    let thread = thread::current();
    let thread_name = match thread.name() {
      Some(name) => name.into(),
      _ => format!("{:?}", thread.id()),
    };
    let location = panic.location().map(ToString::to_string);

    let backtrace = if options.show_backtrace.is_none() {
      Some(Backtrace::capture())
        .filter(|bt| bt.status() == BacktraceStatus::Captured)
    } else if options.show_backtrace == Some(true) {
      Some(Backtrace::force_capture())
    } else {
      None
    };

    Self {
      what: msg,
      where_: Some((thread_name, location)),
      why: backtrace,
      options,
    }
  }

  /// Dumps this ICE into a report.
  pub fn report(self, report: Report) {
    use format_args as f;

    report.clone().error(f!(
      "internal compiler error: {}",
      self.what.as_deref().unwrap_or("unknown panic")
    ));

    report.clone().note(f!(
      "{} unexpectedly panicked. this is a bug",
      self
        .options
        .what_panicked
        .as_deref()
        .unwrap_or("the compiler"),
    ));

    if let Some(at) = self.options.report_bugs_at {
      report.clone().note(f!("please file a bug at: {at}"));
    }

    for note in self.options.extra_notes {
      report.clone().note(f!("{note}"));
    }

    if let Some(bt) = self.why {
      match self.where_ {
        Some((thread, Some(loc))) => report
          .clone()
          .note(f!("thread \"{thread}\" panicked at {loc}\n{bt}")),
        Some((thread, _)) => report
          .clone()
          .note(f!("thread \"{thread}\" panicked\n{bt}")),
        None => report.clone().note(f!("backtrace:\n{bt}")),
      };
    }
  }
}
