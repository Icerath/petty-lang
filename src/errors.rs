use std::path::Path;

use miette::{Error, LabeledSpan, NamedSource};

use crate::{source::SourceId, span::Span};

#[inline(never)]
#[cold]
pub fn error<S: Into<String>>(error: &str, labels: impl IntoIterator<Item = (Span, S)>) -> Error {
    error_with(error, labels, None)
}

#[inline(never)]
#[cold]
pub fn error_with<S: Into<String>>(
    error: &str,
    labels: impl IntoIterator<Item = (Span, S)>,
    help: Option<&str>,
) -> Error {
    let mut id = None;
    let labels: Vec<_> = labels
        .into_iter()
        .inspect(|(span, _)| id = Some(id.unwrap_or(span.source())))
        .map(|(span, msg)| LabeledSpan::at(span.into_range(), msg))
        .collect();
    error_inner(error, id.unwrap(), labels, help)
}

#[inline(never)]
#[cold]
fn error_inner(error: &str, src: SourceId, labels: Vec<LabeledSpan>, extra: Option<&str>) -> Error {
    let suggest = extra.map(str::to_string);
    let (path, contents) = src.get();
    miette::Report::from({
        let mut diag = miette::MietteDiagnostic::new(error.to_string());
        diag.help = suggest;
        diag.labels = Some(labels);
        diag
    })
    .with_source_code(source(&path, contents))
}

fn source(path: &Path, src: String) -> NamedSource<String> {
    NamedSource::new(path.display().to_string(), src)
}
