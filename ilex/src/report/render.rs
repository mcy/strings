use std::fmt;
use std::io;
use std::ops::Range;
use std::sync::atomic::Ordering::SeqCst;
use std::sync::Arc;

use annotate_snippets::display_list::DisplayList;
use annotate_snippets::display_list::FormatOptions;
use annotate_snippets::snippet;

use crate::file::Context;
use crate::file::Spanned;

use crate::report::diagnostic::Info;
use crate::report::diagnostic::Kind;
use crate::report::Report;

/// Collates all of the "unsorted diagnostics" into the "sorted diagnostics",
/// sorting them by thread id. This ensures that all diagnostics coming from
/// a particular thread are together.
pub fn collate(report: &mut Report) {
  let (mut lock1, mut lock2);
  let (recent, sorted) = match Arc::get_mut(&mut report.state) {
    Some(state) => (
      state.recent_diagnostics.get_mut().unwrap(),
      state.sorted_diagnostics.get_mut().unwrap(),
    ),
    None => {
      lock1 = report.state.recent_diagnostics.lock().unwrap();
      lock2 = report.state.sorted_diagnostics.lock().unwrap();
      (&mut *lock1, &mut *lock2)
    }
  };

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
  mut report: Report,
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

  collate(&mut report);
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
  let mut errors = 0;
  for (i, e) in report
    .state
    .sorted_diagnostics
    .lock()
    .unwrap()
    .iter()
    .enumerate()
  {
    let kind = match e.kind.unwrap() {
      Kind::Note => snippet::AnnotationType::Note,
      Kind::Warning => snippet::AnnotationType::Warning,
      Kind::Error => {
        errors += 1;
        snippet::AnnotationType::Error
      }
    };

    let mut snippet = snippet::Snippet {
      title: Some(snippet::Annotation {
        id: None,
        label: Some(&e.message),
        annotation_type: kind,
      }),
      opt: FormatOptions {
        color: report.state.opts.color,
        anonymized_line_numbers: false,
        margin: None,
      },
      ..Default::default()
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

          cur_slice = Some(snippet::Slice {
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

        slice.annotations.push(snippet::SourceAnnotation {
          range: (start, end),
          label: text,
          annotation_type: if *is_remark {
            snippet::AnnotationType::Info
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
      snippet.footer.push(snippet::Annotation {
        id: None,
        label: Some(note),
        annotation_type: snippet::AnnotationType::Note,
      });
    }

    let footer;
    if report.state.opts.show_report_locations {
      footer = format!("reported at: {}", e.reported_at.unwrap());
      snippet.footer.push(snippet::Annotation {
        id: None,
        label: Some(&footer),
        annotation_type: snippet::AnnotationType::Note,
      });
    }

    if i != 0 {
      writeln!(sink)?;
    }
    writeln!(sink, "{}", DisplayList::from(snippet))?;
  }

  if errors != 0 {
    writeln!(sink)?;
    let message = match errors {
      1 => "aborting due to previous error".into(),
      n => format!("aborting due to {n} errors"),
    };

    writeln!(
      sink,
      "{}",
      DisplayList::from(snippet::Snippet {
        title: Some(snippet::Annotation {
          id: None,
          label: Some(&message),
          annotation_type: snippet::AnnotationType::Error,
        }),
        opt: FormatOptions {
          color: report.state.opts.color,
          ..Default::default()
        },
        ..Default::default()
      })
    )?;
  }

  Ok(())
}
