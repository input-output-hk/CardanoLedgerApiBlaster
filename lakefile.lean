import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  -- Execution costs and the symbolic log2 workaround; custom Blaster integration.
  -- Blaster requires Z3 5.3.1 with the recfun-finder simplifier.
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "1d5478ed3009e7dfa34d6c471ae140f379b7f5eb"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "18bfc1c54d1f0908dd2f33c78c909a0020a54c21"

@[default_target]
lean_lib «CardanoLedgerApi» where
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--memory=8192"]
  -- Test #eval commands launch this native executable during elaboration.
  needs := #[`@/uplc_equiv]

lean_lib «UplcEquivalence» where
  srcDir := "equivalence"
  roots := #[`Equivalence]
  globs := #[.one `Equivalence, .submodules `Equivalence]

lean_exe uplc_equiv where
  srcDir := "equivalence"
  root := `Equivalence.Cli
  -- Blaster evaluates Lean expressions in the native worker process.
  supportInterpreter := true
