use std::fmt;
use std::io;
use std::ops::Range;
use std::sync::atomic::Ordering::SeqCst;
use std::sync::Arc;

use annotate_snippets::renderer::AnsiColor;
use annotate_snippets::renderer::Style;
use annotate_snippets::Annotation;
use annotate_snippets::AnnotationType;
use annotate_snippets::Renderer;
use annotate_snippets::Slice;
use annotate_snippets::Snippet;
use annotate_snippets::SourceAnnotation;

use crate::file::Context;
use crate::file::Spanned;

use crate::report::diagnostic::Info;
use crate::report::diagnostic::Kind;
use crate::report::Report;

/// Collates all of the "unsorted diagnostics" into the "sorted diagnostics",
/// sorting them by thread id. This ensures that all diagnostics coming from
/// a particular thread are together.
pub fn collate(report: &Report) {
  let mut recent = report.state.recent_diagnostics.lock().unwrap();
  let mut sorted = report.state.sorted_diagnostics.lock().unwrap();

  recent.sort_by_key(|&(id, _)| id);
  sorted.extend(recent.drain(..).map(|(_, i)| i));
}

pub(in crate::report) fn insert_diagnostic(report: &mut Report, info: Info) {
  if let Some(Kind::Error) = info.kind {
    report.state.has_error.store(true, SeqCst);
  }

  let mut lock;
  let recent_diagnostics = match Arc::get_mut(&mut report.state) {
    Some(state) => state.recent_diagnostics.get_mut().unwrap(),
    None => {
      lock = report.state.recent_diagnostics.lock().unwrap();
      &mut *lock
    }
  };

  recent_diagnostics.push((report.id, info))
}

/// Consumes this `Report` and dumps its diagnostics to `sink`.
pub fn finish(
  report: Report,
  fcx: &Context,
  sink: impl io::Write,
) -> io::Result<()> {
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

  collate(&report);
  let mut out = Writer { sink, error: None };
  render_fmt(&report, fcx, &mut out).map_err(|_| {
    if let Some(e) = out.error.take() {
      return e;
    }

    io::Error::new(io::ErrorKind::Other, "formatter error")
  })
}

/// Dumps this collection of errors as user-displayable text into `sink`.
pub fn render_fmt(
  report: &Report,
  fcx: &Context,
  sink: &mut dyn fmt::Write,
) -> fmt::Result {
  collate(report);
  let mut errors = 0;

  let mut renderer = Renderer::plain();
  #[rustfmt::skip]
  #[allow(clippy::let_unit_value)]
  let _ = if report.state.opts.color {
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
        let file = span.file(fcx);
        if cur_file != Some(file) {
          cur_file = Some(file);
          if let Some(slice) = cur_slice.take() {
            snippet.slices.push(slice);
          }

          cur_slice = Some(Slice {
            source: file.text(),
            line_start: 1,
            origin: Some(file.name().as_str()),
            annotations: Vec::new(),
            fold: true,
          });
        }

        let slice = cur_slice.as_mut().unwrap();
        let Range { mut start, mut end } = span
          .range(fcx)
          .expect("synthetic spans are not supported in diagnostics yet");

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
    if report.state.opts.show_report_locations {
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
