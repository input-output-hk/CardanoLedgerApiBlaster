import PlutusCore.UPLC
import CardanoLedgerApi.V2

namespace Tests.Scripts.HelloWorld
open CardanoLedgerApi.V2 (spendingInputs)

#import_uplc helloWorld PlutusV2 single_cbor_hex "Tests/Scripts/HelloWorld/hello_world.flat"

#prep_uplc (stats-file: "helloworld_prep.jsonl") (stats-interval: 100000) appliedHelloWorld helloWorld spendingInputs 10000

end Tests.Scripts.HelloWorld
