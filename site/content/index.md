---
title: About
slug: index
order: 1
date: 2026-02-28
tags: [about, hyperpolymath]
---

# About protocol-squisher

**protocol-squisher** is a universal protocol analysis substrate created by **Jonathan D.A. Jewell**, an independent researcher and software engineer working under the name **hyperpolymath**.

This project exists because data does not live in one format. Every day, systems exchange information through dozens of serialisation protocols: Protocol Buffers for microservices, Avro for data pipelines, JSON Schema for web APIs, FlatBuffers for games, Cap'n Proto for embedded systems, and many more. Each protocol makes different trade-offs between size, speed, safety, and evolvability. When two systems need to talk, someone has to write the glue code that translates between them — and get it right.

protocol-squisher asks a different question: **what if the computer could figure out the translation automatically, and prove it correct?**

## The idea in brief

Give protocol-squisher two schemas in any supported format. It analyses both, computes a formal compatibility assessment, identifies what can be translated losslessly and what cannot, and generates the adapter code to make it happen. The entire pipeline is backed by formal proofs: if it compiles, it carries.

## Who this is for

- **Backend engineers** integrating services that speak different protocols
- **Data engineers** migrating pipelines between serialisation formats
- **Platform teams** evaluating protocol choices for new infrastructure
- **Researchers** studying type theory applied to real-world serialisation
- **Anyone** who has written a Protobuf-to-JSON adapter by hand and wished they hadn't

## The broader context

protocol-squisher is one of five pillars in a larger effort to build a complete, formally verified developer tool suite. The pillars are:

- **Languages** — PanLL, a neurosymbolic IDE for polyglot development
- **Databases** — VeriSimDB, QuandleDB, and LithoGlyph for verified data storage
- **Protocols** — protocol-squisher (you are here)
- **Containers** — stapeln for container stack analysis
- **Quality** — panic-attacker, hypatia, and echidna for testing and verification

All five pillars are free and open-source software under the Palimpsest License.
