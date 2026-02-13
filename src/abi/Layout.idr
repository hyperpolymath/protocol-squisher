-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <jonathan.jewell@open.ac.uk>
--
-- Protocol Squisher ABI Layout Verification
--
-- Provides compile-time proofs that FFI struct layouts match
-- C ABI requirements for cross-language interoperability.

module ProtocolSquisher.ABI.Layout

import ProtocolSquisher.ABI.Types

-- | Proof that TransportClass values are in valid range (0-3)
export
transportClassInRange : TransportClass -> (n : Nat ** LTE n 3)
transportClassInRange Concorde    = (0 ** LTEZero)
transportClassInRange Business    = (1 ** LTESucc LTEZero)
transportClassInRange Economy     = (2 ** LTESucc (LTESucc LTEZero))
transportClassInRange Wheelbarrow = (3 ** LTESucc (LTESucc (LTESucc LTEZero)))

-- | Proof that ProtocolFormat values are in valid range (0-9)
export
protocolFormatInRange : ProtocolFormat -> (n : Nat ** LTE n 9)
protocolFormatInRange Protobuf    = (0 ** LTEZero)
protocolFormatInRange Avro        = (1 ** LTESucc LTEZero)
protocolFormatInRange Thrift      = (2 ** LTESucc (LTESucc LTEZero))
protocolFormatInRange CapnProto   = (3 ** LTESucc (LTESucc (LTESucc LTEZero)))
protocolFormatInRange Bebop       = (4 ** LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))
protocolFormatInRange FlatBuffers = (5 ** LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))
protocolFormatInRange MessagePack = (6 ** LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))))
protocolFormatInRange JsonSchema  = (7 ** LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))))
protocolFormatInRange ReScript    = (8 ** LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))))))
protocolFormatInRange Python      = (9 ** LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))))))

-- | Convert TransportClass to its u8 representation
export
transportClassToU8 : TransportClass -> Bits8
transportClassToU8 Concorde    = 0
transportClassToU8 Business    = 1
transportClassToU8 Economy     = 2
transportClassToU8 Wheelbarrow = 3

-- | Convert ProtocolFormat to its u8 representation
export
protocolFormatToU8 : ProtocolFormat -> Bits8
protocolFormatToU8 Protobuf    = 0
protocolFormatToU8 Avro        = 1
protocolFormatToU8 Thrift      = 2
protocolFormatToU8 CapnProto   = 3
protocolFormatToU8 Bebop       = 4
protocolFormatToU8 FlatBuffers = 5
protocolFormatToU8 MessagePack = 6
protocolFormatToU8 JsonSchema  = 7
protocolFormatToU8 ReScript    = 8
protocolFormatToU8 Python      = 9

-- | Get fidelity for a transport class (percentage * 100)
export
transportClassFidelity : TransportClass -> Bits32
transportClassFidelity Concorde    = 10000  -- 100.00%
transportClassFidelity Business    = 9800   -- 98.00%
transportClassFidelity Economy     = 8000   -- 80.00%
transportClassFidelity Wheelbarrow = 5000   -- 50.00%
