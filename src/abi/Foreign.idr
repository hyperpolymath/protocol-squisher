-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Protocol Squisher ABI Foreign Function Declarations
--
-- Declares the C ABI functions implemented by the Zig FFI layer.
-- These functions provide the external interface for protocol
-- compatibility analysis and adapter generation.

module ProtocolSquisher.ABI.Foreign

import ProtocolSquisher.ABI.Types

-- | Initialize the protocol squisher engine
-- Returns a handle (>0) on success, -1 on failure
%foreign "C:squisher_init,libprotocol_squisher_ffi"
export
squisher_init : PrimIO Int

-- | Free resources associated with a squisher handle
%foreign "C:squisher_free,libprotocol_squisher_ffi"
export
squisher_free : Int -> PrimIO ()

-- | Analyze compatibility between two protocol formats
-- handle: squisher handle from squisher_init
-- source_format: source ProtocolFormat enum value (0-9)
-- target_format: target ProtocolFormat enum value (0-9)
-- Returns: TransportClass enum value (0-3), or -1 on error
%foreign "C:squisher_analyze_compatibility,libprotocol_squisher_ffi"
export
squisher_analyze_compatibility : Int -> Int -> Int -> PrimIO Int

-- | Generate an adapter between two protocol schemas
-- handle: squisher handle from squisher_init
-- source_schema: source schema definition as string
-- target_schema: target schema definition as string
-- source_format: source ProtocolFormat enum value (0-9)
-- target_format: target ProtocolFormat enum value (0-9)
-- Returns: number of field mappings generated, or -1 on error
%foreign "C:squisher_generate_adapter,libprotocol_squisher_ffi"
export
squisher_generate_adapter : Int -> String -> String -> Int -> Int -> PrimIO Int

-- | Get the number of field mappings in the last generated adapter
-- handle: squisher handle from squisher_init
-- Returns: mapping count, or -1 on error
%foreign "C:squisher_get_mapping_count,libprotocol_squisher_ffi"
export
squisher_get_mapping_count : Int -> PrimIO Int

-- | Get the overall transport class for the last generated adapter
-- handle: squisher handle from squisher_init
-- Returns: TransportClass enum value (0-3), or -1 on error
%foreign "C:squisher_get_transport_class,libprotocol_squisher_ffi"
export
squisher_get_transport_class : Int -> PrimIO Int

-- | Get the number of supported protocol formats
-- Always returns 10 (Protobuf through Python)
%foreign "C:squisher_format_count,libprotocol_squisher_ffi"
export
squisher_format_count : PrimIO Int
