import Equivalence.Checker

namespace EquivalenceTest

open Lean

-- Test transport instances stay outside the production library.
deriving instance ToJson, FromJson for Equivalence.ValidContext.Limits
deriving instance ToJson, FromJson for Equivalence.Checker.Config

namespace Protocol

structure Script where
  source : String
  format : String
  deriving ToJson, FromJson

structure Request where
  options : Equivalence.Checker.Config
  old : Script
  new : Script
  deriving ToJson, FromJson

def decode (script : Script) : Except String PlutusCore.UPLC.Term.Program :=
  match script.format with
  | "textual" => PlutusCore.UPLC.TextEncoding.programFromString script.source
  | "single_cbor_hex" =>
    PlutusCore.UPLC.ScriptEncoding.Internal.singleCborEncodedScriptFromHex? script.source.trim
  | format => .error s!"Unsupported test fixture format: {format}"

end Protocol
end EquivalenceTest
