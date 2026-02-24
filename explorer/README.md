# Explorer Subsystem

Continuous-learning subsystem for Protocol Squisher.

## Layout

- `crawler/`: Elixir OTP GitHub schema crawler (`mix crawler.run`)
- `parser/`: Parallel schema parsing stage and parser-related docs
- `database/`: Placeholder for empirical compatibility database artifacts

## Quick Start

```bash
cd explorer/crawler
mix test
mix crawler.run --max-pages 1
```

For corpus integration, pass:

```bash
mix crawler.run --with-corpus --corpus-cli ../../target/debug/protocol-squisher
```
