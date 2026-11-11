import Lake
open Lake DSL

package WscTractability where
  moreLeanArgs := #["--threads=2", "-s65536"]

meta if (get_config? blasterPath).isSome then
  require Blaster from (get_config? blasterPath |>.getD ".")
else
  require Blaster from git
    (get_config? blasterUrl |>.getD "https://github.com/input-output-hk/Lean-blaster") @
    (get_config? blasterRev |>.getD "beta-lambda-cache-optimization")
require PlutusCore from git
  (get_config? plutusUrl |>.getD "https://github.com/input-output-hk/PlutusCoreBlaster") @
  (get_config? plutusRev |>.getD "d85df0512fbc556a095a2d4c6276b528395eb06c")
require CardanoLedgerApi from git
  "https://github.com/input-output-hk/CardanoLedgerApiBlaster" @
  (get_config? ledgerRev |>.getD "5dab3c43f042b8735b6d067223baaa8d32ed28a1")

-- Build the fixture and definitions without attempting either expensive proof.
@[default_target]
lean_lib WscContainment where
  roots := #[`WscContainment.Specification]
  globs := #[.one `WscContainment.Script, .one `WscContainment.Specification]

-- Decode and state the older DX workload without running its expensive prep.
lean_lib WscDx where
  roots := #[`WscDx.Specification]
  globs := #[.one `WscDx.Script, .one `WscDx.Specification]
