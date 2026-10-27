import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  -- Execution costs and the symbolic log2 workaround; custom Blaster integration.
  -- Blaster requires Z3 5.3.1 with the recfun-finder simplifier.
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "c91fa7070bbc69e17b6396c83bf11311e237af75"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "934f0c31f0e283a309fb07c1a612607dca0ca4f6"

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
