import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "e37843f02b7d47fd940b01b92eb26ca0a98b83bd"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "1cb5a63e0416f336caa3104c2654718e6f971bc9"

@[default_target]
lean_lib «CardanoLedgerApi» where
   globs := #[.andSubmodules `CardanoLedgerApi]
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here
