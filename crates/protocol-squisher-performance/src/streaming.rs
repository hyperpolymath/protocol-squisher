// SPDX-License-Identifier: PMPL-1.0-or-later

use serde::de::DeserializeOwned;
use serde::Serialize;
use std::fmt::{Display, Formatter};
use std::io::{BufRead, Write};

#[derive(Debug)]
pub enum StreamingError {
    Io(std::io::Error),
    Deserialize {
        line: usize,
        source: serde_json::Error,
    },
    Serialize {
        line: usize,
        source: serde_json::Error,
    },
}

impl Display for StreamingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StreamingError::Io(source) => write!(f, "stream I/O error: {source}"),
            StreamingError::Deserialize { line, source } => {
                write!(f, "failed to deserialize line {line}: {source}")
            },
            StreamingError::Serialize { line, source } => {
                write!(f, "failed to serialize line {line}: {source}")
            },
        }
    }
}

impl std::error::Error for StreamingError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            StreamingError::Io(source) => Some(source),
            StreamingError::Deserialize { source, .. } => Some(source),
            StreamingError::Serialize { source, .. } => Some(source),
        }
    }
}

impl From<std::io::Error> for StreamingError {
    fn from(value: std::io::Error) -> Self {
        StreamingError::Io(value)
    }
}

/// Stream-transform an iterator in bounded chunks without materializing all output at once.
pub fn transform_in_chunks<I, T, U, F>(
    input: I,
    chunk_size: usize,
    mut transform: F,
) -> impl Iterator<Item = Vec<U>>
where
    I: IntoIterator<Item = T>,
    F: FnMut(T) -> U,
{
    assert!(chunk_size > 0, "chunk_size must be > 0");

    let mut iter = input.into_iter();

    std::iter::from_fn(move || {
        let mut chunk = Vec::with_capacity(chunk_size);
        for _ in 0..chunk_size {
            match iter.next() {
                Some(item) => chunk.push(transform(item)),
                None => break,
            }
        }

        if chunk.is_empty() { None } else { Some(chunk) }
    })
}

/// Stream JSONL records from `reader` to `writer` while transforming each record.
pub fn transform_json_lines<R, W, T, U, F>(
    reader: R,
    mut writer: W,
    mut transform: F,
) -> Result<usize, StreamingError>
where
    R: BufRead,
    W: Write,
    T: DeserializeOwned,
    U: Serialize,
    F: FnMut(T) -> U,
{
    let mut processed = 0usize;

    for (idx, line_result) in reader.lines().enumerate() {
        let line_no = idx + 1;
        let line = line_result?;
        if line.trim().is_empty() {
            continue;
        }

        let record = serde_json::from_str::<T>(&line).map_err(|source| StreamingError::Deserialize {
            line: line_no,
            source,
        })?;

        let mapped = transform(record);
        serde_json::to_writer(&mut writer, &mapped).map_err(|source| StreamingError::Serialize {
            line: line_no,
            source,
        })?;
        writer.write_all(b"\n")?;
        processed += 1;
    }

    Ok(processed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};
    use std::io::Cursor;

    #[derive(Debug, Deserialize)]
    struct InRecord {
        id: u32,
        score: u32,
    }

    #[derive(Debug, Serialize)]
    struct OutRecord {
        id: u32,
        score: u32,
    }

    #[test]
    fn transforms_in_fixed_chunks() {
        let input = 0..10;
        let chunks: Vec<Vec<u32>> = transform_in_chunks(input, 3, |v| v * 2).collect();

        assert_eq!(chunks.len(), 4);
        assert_eq!(chunks[0], vec![0, 2, 4]);
        assert_eq!(chunks[1], vec![6, 8, 10]);
        assert_eq!(chunks[2], vec![12, 14, 16]);
        assert_eq!(chunks[3], vec![18]);
    }

    #[test]
    fn streams_json_lines_without_buffering_whole_dataset() {
        let input = r#"{"id":1,"score":10}
{"id":2,"score":20}
"#;
        let reader = Cursor::new(input.as_bytes());
        let mut output = Vec::new();

        let count =
            transform_json_lines::<_, _, InRecord, OutRecord, _>(reader, &mut output, |record| {
                OutRecord {
                    id: record.id,
                    score: record.score + 1,
                }
            })
            .expect("stream transform");

        assert_eq!(count, 2);
        let out = String::from_utf8(output).expect("utf8");
        assert!(out.contains(r#"{"id":1,"score":11}"#));
        assert!(out.contains(r#"{"id":2,"score":21}"#));
    }

    #[test]
    fn returns_line_aware_error_on_bad_json() {
        let input = r#"{"id":1,"score":10}
not-json
"#;
        let reader = Cursor::new(input.as_bytes());
        let mut output = Vec::new();

        let err = transform_json_lines::<_, _, InRecord, OutRecord, _>(reader, &mut output, |record| {
            OutRecord {
                id: record.id,
                score: record.score,
            }
        })
        .expect_err("expected parse error");

        match err {
            StreamingError::Deserialize { line, .. } => assert_eq!(line, 2),
            other => panic!("expected deserialize error, got {other:?}"),
        }
    }
}
