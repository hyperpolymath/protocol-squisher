# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# pyo3_integration_test - Python package for maturin mixed layout.
#
# Re-export all symbols from the compiled Rust extension (.so/.pyd)
# so that `from pyo3_integration_test import Status, ...` works.
from .pyo3_integration_test import *  # noqa: F401,F403
