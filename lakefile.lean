import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  -- These revisions are tested together with Z3 4.15.2 in CI. Moving branch
  -- heads may require solver extensions absent from that release.
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "5249a39bd39c854ce5cef1b70113c51aac1e4f0a"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "bafdd4f7976037cd7bd8e443df04af096dc5b96e"

@[default_target]
lean_lib «CardanoLedgerApi» where
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  moreLeanArgs := #["--memory=8192"]

lean_lib «UplcEquivalence» where
  srcDir := "equivalence"
  roots := #[`Equivalence]
  globs := #[.one `Equivalence, .submodules `Equivalence]

