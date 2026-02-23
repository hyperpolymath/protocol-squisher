# SPDX-License-Identifier: PMPL-1.0-or-later
# Reproducible Podman development image for protocol-squisher.

FROM docker.io/library/rust:1.89-bookworm

ENV DEBIAN_FRONTEND=noninteractive \
    PIP_DISABLE_PIP_VERSION_CHECK=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    CARGO_TERM_COLOR=always \
    VIRTUAL_ENV=/opt/venv \
    PATH=/opt/venv/bin:$PATH

# Python + pydantic are required for protocol-squisher Python analyzer paths.
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        clang \
        git \
        libssl-dev \
        pkg-config \
        python3 \
        python3-dev \
        python3-venv \
        python3-pip \
    && python3 -m venv /opt/venv \
    && /opt/venv/bin/pip install --no-cache-dir --upgrade pip \
    && /opt/venv/bin/pip install --no-cache-dir "pydantic>=2,<3" \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /workspace

CMD ["bash"]
