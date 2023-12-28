use std::backtrace::Backtrace;
use std::backtrace::BacktraceStatus;
use std::io;
use std::panic;
use std::panic::AssertUnwindSafe;
use std::panic::PanicInfo;
use std::panic::UnwindSafe;
use std::process;
use std::thread;

use std::format_args as f;

use crate::file::FileCtx;
use crate::report::Fatal;
use crate::report::ReportCtx;

/// Executes a "compiler main function".
///
/// If the main function panics, this is caught, errs are printed, and
/// then the panic resumes. Otherwise, on successful return of the main
/// function, errs are printed to stderr and the program exits.
pub fn main<Compiler>(rcx: ReportCtx, compiler: Compiler) -> !
where
  Compiler: FnOnce(&mut FileCtx) -> Result<(), Fatal>,
  Compiler: UnwindSafe,
{
  let hook = panic::take_hook();
  panic::set_hook(Box::new(move |panic| {
    FileCtx::run(|fcx| ilex_panic(fcx, panic, &hook))
  }));

  rcx.clone().install();

  FileCtx::run(|fcx| {
    let result = panic::catch_unwind(AssertUnwindSafe(|| compiler(fcx)))
      .map(|r| r.is_ok());
    let _ignored = rcx.finish(fcx, io::stderr());
    match result {
      Ok(true) => process::exit(0),
      Ok(false) => process::exit(1),
      Err(e) => panic::resume_unwind(e),
    }
  })
}

fn ilex_panic(fcx: &FileCtx, panic: &PanicInfo, hook: &dyn Fn(&PanicInfo)) {
  let Some(report) = ReportCtx::try_current() else {
    return hook(panic);
  };

  let msg = panic.payload();
  let msg = if let Some(&s) = msg.downcast_ref::<&'static str>() {
    s.to_string()
  } else if let Some(s) = msg.downcast_ref::<String>() {
    s.clone()
  } else {
    "<no message>".to_string()
  };

  let thread = thread::current();
  let mut err =
    report.error(fcx, f!("internal compiler error: panicked at '{msg}'",));

  if let Some(location) = panic.location() {
    err = err.note(f!(
      "thread '{}' panicked at {location}",
      match thread.name() {
        Some(name) => name.into(),
        _ => format!("{:?}", thread.id()),
      }
    ));
  }

  let bt = Backtrace::capture();
  if bt.status() == BacktraceStatus::Captured {
    err = err.note("stack backtrace");

    let mut prev_line = None;
    let bt = bt.to_string();
    for mut line in bt.lines() {
      line = line.trim();
      if let Some(prev) = prev_line.take() {
        if line.starts_with("at ") {
          let buf;
          let mut line = line;
          if line.starts_with("at /rustc/") {
            if let Some(idx) = line.find("/library/") {
              buf = format!("at <rust>/{}", &line[idx + "/library/".len()..]);
              line = &buf;
            }
          }

          err = err.note(f!("{} {}", prev, line));
        } else {
          err = err.note(prev);
          prev_line = Some(line);
        }
      } else {
        prev_line = Some(line);
      }
    }

    if let Some(prev) = prev_line.take() {
      err.note(prev);
    }
  }
}
