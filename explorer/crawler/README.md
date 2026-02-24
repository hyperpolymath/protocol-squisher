# Protocol Squisher Explorer Crawler

Elixir OTP crawler for discovering schema files on GitHub and producing
normalized NDJSON records for the continuous-learning pipeline.

## What It Does

- Queries GitHub Code Search for schema-like files.
- Fetches file content through the GitHub API.
- Detects Protocol Squisher format identifiers from file extensions.
- Parses fetched schemas in parallel (heuristic parser stage).
- Emits one NDJSON record per crawled schema.
- Optionally invokes `protocol-squisher corpus-analyze` for each file.

## Run

```bash
cd explorer/crawler
mix crawler.run --max-pages 1
```

With corpus analysis enabled:

```bash
mix crawler.run \
  --with-corpus \
  --corpus-cli ../../target/debug/protocol-squisher \
  --parser-concurrency 16 \
  --max-pages 1
```

## Output

Default output path:

```text
../../target/explorer/schemas.ndjson
```

Each line is JSON and contains metadata, detected format, fetched content,
`parse_summary` metadata, and optional `corpus_analysis` payload.

## Notes

- Provide `GITHUB_TOKEN` to improve API limits.
- Tune parser parallelism with `--parser-concurrency`.
- Supported extension mapping currently includes:
  `rs, py, proto, thrift, avsc, avdl, capnp, fbs, bop, msgpack, res, resi, json`.
