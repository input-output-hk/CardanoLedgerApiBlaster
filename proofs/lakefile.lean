import Lake
open Lake DSL

package CardanoLedgerApiFacts where
  moreLeanArgs := #["--threads=2", "-s65536"]

require Blaster from git "https://github.com/colll78/Lean-blaster" @ "08002278c0fe6e8042c5e1380a12fb4511c79777"
require PlutusCore from git "https://github.com/colll78/PlutusCoreBlaster" @ "37e1fd9119116e6dfefd002d4a895c52f0dc01c0"
require PlutusCoreFacts from git "https://github.com/colll78/PlutusCoreBlaster" @ "37e1fd9119116e6dfefd002d4a895c52f0dc01c0" / "proofs"
require CardanoLedgerApi from ".."

@[default_target]
lean_lib CardanoLedgerApiFacts

@[test_driver]
lean_lib FactTests
