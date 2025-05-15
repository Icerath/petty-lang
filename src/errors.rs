use std::path::Path;

use miette::{Error, LabeledSpan, NamedSource};

use crate::span::Span;

#[inline(never)]
#[cold]
pub fn error<S: Into<String>>(
    error: &str,
    path: Option<&Path>,
    src: &str,
    labels: impl IntoIterator<Item = (Span, S)>,
) -> Error {
    error_with(error, path, src, labels, None)
}

#[inline(never)]
#[cold]
pub fn error_with<S: Into<String>>(
    error: &str,
    path: Option<&Path>,
    src: &str,
    labels: impl IntoIterator<Item = (Span, S)>,
    help: Option<&str>,
) -> Error {
    let labels: Vec<_> = labels
        .into_iter()
        .map(|(span, msg)| LabeledSpan::at(offset_span(span).into_range_usize(), msg))
        .collect();
    error_inner(error, path, src, labels, help)
}

#[inline(never)]
#[cold]
fn error_inner(
    error: &str,
    path: Option<&Path>,
    src: &str,
    labels: Vec<LabeledSpan>,
    extra: Option<&str>,
) -> Error {
    let suggest = extra.map(str::to_string);
    miette::Report::from({
        let mut diag = miette::MietteDiagnostic::new(error.to_string());
        diag.help = suggest;
        diag.labels = Some(labels);
        diag
    })
    .with_source_code(source(src, path))
}

fn source(src: &str, path: Option<&Path>) -> NamedSource<String> {
    let path = path.and_then(|path| path.to_str()).unwrap_or("");
    let src = src[crate::STD.len()..].to_string();
    NamedSource::new(path, src)
}

fn offset_span(span: Span) -> Span {
    if span == Span::ZERO {
        return span;
    }
    let offset: u32 = crate::STD.len().try_into().unwrap();
    Span::from(span.start().saturating_sub(offset)..span.end().saturating_sub(offset))
}
