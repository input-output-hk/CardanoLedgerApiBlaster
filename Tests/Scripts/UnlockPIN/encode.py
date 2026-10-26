"""Wrap Pebble's raw Flat output once in CBOR and write hex without a newline."""

from pathlib import Path

root = Path(__file__).resolve().parent
flat = (root / "out/out.flat").read_bytes()
if flat[:3] != bytes([1, 0, 0]):
    raise SystemExit("Expected UPLC 1.0.0 for the Plutus V2 validator")
size = len(flat)
if size < 24:
    header = bytes([0x40 + size])
elif size < 256:
    header = bytes([0x58, size])
elif size < 65536:
    header = b"\x59" + size.to_bytes(2, "big")
else:
    raise SystemExit("Unexpectedly large UnlockPIN script")
(root / "unlock_pin.flat").write_text((header + flat).hex(), encoding="ascii")
