import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  -- Execution costs, the symbolic log2 workaround and shared SMT model decoding.
  -- Blaster requires Z3 5.3.1 with the recfun-finder simplifier.
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "0de84aad0446464ad46763140931de9be95b2035"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "31347517f50bb765e4a3ad0a85c7a3f79efd5c84"

@[default_target]
lean_lib «CardanoLedgerApi» where
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here
