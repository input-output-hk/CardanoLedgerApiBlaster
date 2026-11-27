import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  -- Execution costs, the symbolic log2 workaround and shared SMT model decoding.
  -- Blaster includes constructor-value caching and early list lookups.
  -- Blaster requires Z3 with the recfun-finder simplifier.
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "6aa4ad745990a504ec28d9da87ff62ba7c9f7f90"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "e3813921d1a16872fe16b4a5f3a68430a7105e54"

@[default_target]
lean_lib «CardanoLedgerApi» where
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--memory=8192"]
  -- Semantic tests use an isolated worker that calls the checker library.
  needs := #[`@/equivalence_test_worker]

target uplcInterrupt.o pkg : System.FilePath := do
  let source ← inputTextFile (pkg.dir / "equivalence" / "interrupt.c")
  let includes := #["-I", (← getLeanIncludeDir).toString]
  buildO (pkg.buildDir / "ir" / "uplcInterrupt.o") source includes #["-fPIC"] "cc" getLeanTrace

lean_lib «UplcEquivalence» where
  srcDir := "equivalence"
  roots := #[`Equivalence]
  globs := #[.one `Equivalence, .submodules `Equivalence]
  moreLinkObjs := #[uplcInterrupt.o]

lean_exe uplc_equiv where
  srcDir := "equivalence"
  root := `Equivalence.Cli
  -- Blaster evaluates Lean expressions in the native worker process.
  supportInterpreter := true

lean_lib EquivalenceTestSupport where
  srcDir := "test-support"
  roots := #[`EquivalenceTest.Protocol]

lean_exe equivalence_test_worker where
  srcDir := "test-support"
  root := `EquivalenceTest.Worker
  supportInterpreter := true

-- Isolated corpus measurements use the checker library and a process watchdog.
lean_exe equivalence_benchmark_worker where
  srcDir := "equivalence/benchmarks"
  root := `CorpusWorker
  supportInterpreter := true
