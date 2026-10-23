import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  -- Use execution-cost support from cek-machine-exunits. Keep Blaster pinned
  -- to the revision tested with Z3 4.15.2.
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "7a5a0b1ce37defc343640d985bab62e63f7744eb"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "bafdd4f7976037cd7bd8e443df04af096dc5b96e"

@[default_target]
lean_lib «CardanoLedgerApi» where
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--memory=8192"]
  extraDepTargets := #[`uplc_equiv]

lean_lib «UplcEquivalence» where
  srcDir := "equivalence"
  roots := #[`Equivalence]
  globs := #[.one `Equivalence, .submodules `Equivalence]

lean_exe uplc_equiv where
  srcDir := "equivalence"
  root := `Equivalence.Cli
