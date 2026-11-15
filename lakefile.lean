import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  -- PlutusCoreBlaster PR #93; its extension API comes from Lean-blaster PR #472.
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "07584be44ba1d4fe70c95a8e219d7e2a6d2245d9"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "fe7a8fbe001594d8275ebb1783af8dea305f2bdd"

@[default_target]
lean_lib «CardanoLedgerApi» where
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here
