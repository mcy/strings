use std::fmt;
use std::io;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;
use std::sync::Mutex;

use annotate_snippets::renderer::AnsiColor;
use annotate_snippets::renderer::Style;
use annotate_snippets::Annotation;
use annotate_snippets::AnnotationType;
use annotate_snippets::Renderer;
use annotate_snippets::Slice;
use annotate_snippets::Snippet;
use annotate_snippets::SourceAnnotation;

use crate::report::diagnostic;
use crate::report::diagnostic::Info;
use crate::report::diagnostic::Kind;
use crate::report::Options;
use crate::report::Report;

use super::diagnostic::Loc;

pub struct State {
  pub opts: Options,
  has_error: AtomicBool,
  sorted_diagnostics: Mutex<Vec<diagnostic::Info>>,
  recent_diagnostics: Mutex<Vec<(u64, diagnostic::Info)>>,
}

impl State {
  pub fn new(opts: Options) -> Self {
    Self {
      opts,
      has_error: AtomicBool::new(false),
      sorted_diagnostics: Default::default(),
      recent_diagnostics: Default::default(),
    }
  }

  pub fn has_error(&self) -> bool {
    self.has_error.load(Ordering::SeqCst)
  }

  /// Collates all of the "unsorted diagnostics" into the "sorted diagnostics",
  /// sorting them by thread id. This ensures that all diagnostics coming from
  /// a particular thread are together.
  pub fn collate(&self) {
    let mut recent = self.recent_diagnostics.lock().unwrap();
    let mut sorted = self.sorted_diagnostics.lock().unwrap();

    recent.sort_by_key(|&(id, _)| id);
    sorted.extend(recent.drain(..).map(|(_, i)| i));
  }

  pub fn insert_diagnostic(&self, info: Info) {
    if let Some(Kind::Error) = info.kind {
      self.has_error.store(true, Ordering::SeqCst);
    }

    static COUNTER: AtomicU64 = AtomicU64::new(0);
    thread_local! {
      static ID: u64 = COUNTER.fetch_add(1, Ordering::Relaxed);
    };

    let mut recent = self.recent_diagnostics.lock().unwrap();
    recent.push((ID.with(|&x| x), info))
  }
}

/// Consumes this `Report` and dumps its diagnostics to `sink`.
pub fn finish(report: &Report, sink: impl io::Write) -> io::Result<()> {
  struct Writer<W: io::Write> {
    sink: W,
    error: Option<io::Error>,
  }

  impl<W: io::Write> fmt::Write for Writer<W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
      self.sink.write_all(s.as_bytes()).map_err(|e| {
        self.error = Some(e);
        fmt::Error
      })
    }
  }

  let mut out = Writer { sink, error: None };
  render_fmt(report, &report.state.opts, &mut out).map_err(|_| {
    if let Some(e) = out.error.take() {
      return e;
    }

    io::Error::new(io::ErrorKind::Other, "formatter error")
  })
}

/// Dumps this collection of errors as user-displayable text into `sink`.
pub fn render_fmt(
  report: &Report,
  opts: &Options,
  sink: &mut dyn fmt::Write,
) -> fmt::Result {
  report.state.collate();
  let mut errors = 0;

  let mut renderer = Renderer::plain();
  #[rustfmt::skip]
  #[allow(clippy::let_unit_value)]
  let _ = if opts.color {
    renderer = Renderer::styled()
      .error(Style::new().fg_color(Some(AnsiColor::BrightRed.into())).bold())
      .warning(Style::new().fg_color(Some(AnsiColor::BrightYellow.into())).bold())
      .note(Style::new().fg_color(Some(AnsiColor::BrightGreen.into())).bold())
      .info(Style::new().fg_color(Some(AnsiColor::BrightBlue.into())).bold())
      .help(Style::new().fg_color(Some(AnsiColor::BrightCyan.into())).bold());
  };

  for e in report.state.sorted_diagnostics.lock().unwrap().iter() {
    let kind = match e.kind.unwrap() {
      Kind::Note => AnnotationType::Note,
      Kind::Warning => AnnotationType::Warning,
      Kind::Error => {
        errors += 1;
        AnnotationType::Error
      }
    };

    let mut snippet = Snippet {
      title: Some(Annotation {
        id: None,
        label: Some(&e.message),
        annotation_type: kind,
      }),
      footer: Vec::new(),
      slices: Vec::new(),
    };

    for snips in &e.snippets {
      let mut cur_file = None;
      let mut cur_slice = None;
      for (span, text, is_remark) in snips {
        let file = report.ctx.file(span.file).unwrap();
        if cur_file != Some(file) {
          cur_file = Some(file);
          if let Some(slice) = cur_slice.take() {
            snippet.slices.push(slice);
          }

          cur_slice = Some(Slice {
            source: file.text(),
            line_start: 1,
            origin: Some(file.path().as_str()),
            annotations: Vec::new(),
            fold: true,
          });
        }

        let slice = cur_slice.as_mut().unwrap();
        let Loc {
          mut start, mut end, ..
        } = span;

        if start == end && !slice.source.is_empty() {
          // Normalize the range so that it is never just one space long.
          // If this would cause range.1 to go past the end of the input length,
          // we swap them around instead.
          if end == slice.source.len() {
            start = end - 1;
          } else {
            end = start + 1;
          }
        }

        slice.annotations.push(SourceAnnotation {
          range: (start, end),
          label: text,
          annotation_type: if *is_remark {
            AnnotationType::Info
          } else {
            kind
          },
        });
      }

      if let Some(slice) = cur_slice.take() {
        snippet.slices.push(slice);
      }
    }

    // Crop the starts of each slice to only incorporate the annotations.
    for slice in &mut snippet.slices {
      let earliest_start = slice
        .annotations
        .iter()
        .map(|a| a.range.0)
        .min()
        .unwrap_or(0);
      let (count, start_idx) = slice.source[..earliest_start]
        .bytes()
        .enumerate()
        .filter_map(|(i, c)| (c == b'\n').then_some(i + 1))
        .enumerate()
        .map(|(i, j)| (i + 1, j))
        .last()
        .unwrap_or_default();

      slice.line_start = count + 1;
      slice.source = &slice.source[start_idx..];
      for a in &mut slice.annotations {
        a.range.0 -= start_idx;
        a.range.1 -= start_idx;
      }
    }

    for note in &e.notes {
      snippet.footer.push(Annotation {
        id: None,
        label: Some(note),
        annotation_type: AnnotationType::Note,
      });
    }

    let footer;
    if opts.show_report_locations {
      footer = format!("reported at: {}", e.reported_at.unwrap());
      snippet.footer.push(Annotation {
        id: None,
        label: Some(&footer),
        annotation_type: AnnotationType::Note,
      });
    }

    write!(sink, "{}\n\n", renderer.render(snippet))?;
  }

  if errors != 0 {
    let message = match errors {
      1 => "aborting due to previous error".into(),
      n => format!("aborting due to {n} errors"),
    };

    let aborting = Snippet {
      title: Some(Annotation {
        id: None,
        label: Some(&message),
        annotation_type: AnnotationType::Error,
      }),
      footer: Vec::new(),
      slices: Vec::new(),
    };

    writeln!(sink, "{}", renderer.render(aborting))?;
  }

  Ok(())
}
