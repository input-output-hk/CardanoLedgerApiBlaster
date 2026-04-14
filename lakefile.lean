import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "main"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "main"

@[default_target]
lean_lib «CardanoLedgerApi» where
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here
