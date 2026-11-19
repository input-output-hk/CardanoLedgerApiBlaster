import Lake
open Lake DSL

package «CardanoLedgerApi» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]
  require PlutusCore from git "https://github.com/input-output-hk/PlutusCoreBlaster" @ "main"
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "beta-lambda-cache-optimization"

@[default_target]
lean_lib «CardanoLedgerApi» where
   -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here

-- Standalone mapping experiments, including the editable Playground entry point.
lean_lib MappingExamples where
  roots := #[`equivalence.proofs.mappings.Structural,
             `equivalence.proofs.mappings.Relational,
             `equivalence.proofs.mappings.Playground,
             `equivalence.proofs.mappings.MappingSupport,
             `equivalence.proofs.mappings.MappingSupportTests,
             `equivalence.proofs.mappings.AutomaticMapping]
