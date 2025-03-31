use std::{borrow::Cow, path::Path};

use miette::{Error, LabeledSpan, NamedSource};

use crate::span::Span;

#[inline(never)]
#[cold]
pub fn error(error: &str, path: Option<&Path>, src: &str, labels: &[(Span, Cow<str>)]) -> Error {
    let labels: Vec<_> = labels
        .iter()
        .map(|(span, msg)| LabeledSpan::at(offset_span(*span).into_range_usize(), msg.as_ref()))
        .collect();
    miette::miette!(labels = labels, "{error}").with_source_code(source(src, path))
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
    Span::from(span.start() - offset..span.end() - offset)
}
