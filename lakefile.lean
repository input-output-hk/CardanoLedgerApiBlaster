import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "b5c1af7af64a20c69f80f179487c0146c255e164"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "bc03bb402ce702984875bbf8ba51216bd6f843d7"

@[default_target]
lean_lib «CardanoLedgerApi» where
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here
