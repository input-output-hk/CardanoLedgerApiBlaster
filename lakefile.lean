import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  -- Execution costs from cek-machine-exunits; Fin translation from split/285-fin.
  -- Blaster requires Z3 5.3.1 with the recfun-finder simplifier.
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "7a5a0b1ce37defc343640d985bab62e63f7744eb"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "01ae099a4e84e4e82f68394e9f57e180d0b85d84"

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
