import Equivalence.Model

namespace Tests.Equivalence.Model

open Lean (Json)

def decoded (s : String) : Option Json :=
  (_root_.Equivalence.Model.dataBinding s).map (fun (_, value) => _root_.Equivalence.Model.dataJson value)

#guard decoded "datum: (Data.I (- 42))" == (Json.parse "{\"int\":-42}").toOption

-- Colons inside strings must not split bindings. Quotes and Unicode escapes use
-- SMT-LIB conventions; the output is lossless Plutus detailed-schema JSON.
#guard decoded "datum: (Data.B (ByteString.mk \"a: \"\"q\"\"\\u{0}\\u{ff}\"))" ==
  (Json.parse "{\"bytes\":\"613a2022712200ff\"}").toOption

#guard decoded "datum: (Data.Constr 0 (List.cons (Data.I 3) List.nil))" ==
  (Json.parse "{\"constructor\":0,\"fields\":[{\"int\":3}]}").toOption

#guard decoded "datum: (Data.Map (List.cons (Prod.mk (Data.I 1) (Data.List (List.cons (Data.B (ByteString.mk \"x\")) List.nil))) List.nil))" ==
  (Json.parse "{\"map\":[{\"k\":{\"int\":1},\"v\":{\"list\":[{\"bytes\":\"78\"}]}}]}").toOption

#guard (decoded "datum: (Data.I 3) trailing").isNone
#guard (decoded "datum: (Data.I not_an_integer)").isNone
#guard (decoded "datum: (Data.B (ByteString.mk \"\\u{100}\"))").isNone

-- Typed vesting parameters appear without their enclosing Data constructors.
#guard (_root_.Equivalence.Model.integerBinding "fee: (- 98765432101234567890)") ==
  some ("fee", -98765432101234567890)
#guard ((_root_.Equivalence.Model.listBinding
    "referenceInputs: (List.cons_Data (Data.I 42) List.nil_Data)").map
    (fun (_, xs) => _root_.Equivalence.Model.dataJson (.List xs))) ==
  (Json.parse "{\"list\":[{\"int\":42}]}").toOption
#guard ((_root_.Equivalence.Model.mapBinding
    "mint: (List.cons_Prod (Prod.mk_Data (Data.I 1) (Data.I 2)) List.nil_Prod)").map
    (fun (_, xs) => _root_.Equivalence.Model.dataJson (.Map xs))) ==
  (Json.parse "{\"map\":[{\"k\":{\"int\":1},\"v\":{\"int\":2}}]}").toOption
#guard ((_root_.Equivalence.Model.byteStringBinding "txId: (ByteString.mk \"a: \\u{ff}\")").map
    (fun (_, bytes) => _root_.Equivalence.Model.dataJson (.B bytes))) ==
  (Json.parse "{\"bytes\":\"613a20ff\"}").toOption
#guard (_root_.Equivalence.Model.listBinding "inputs: List.nil_Data trailing").isNone
#guard (_root_.Equivalence.Model.mapBinding "mint: (List.cons (Data.I 1) List.nil)").isNone

-- Z3 qualifies polymorphic empty lists with their sort in real model values.
#guard ((_root_.Equivalence.Model.listBinding
    "referenceInputs: (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I 42) (as List.nil (@List @PlutusCore.Data.PlutusCore.DataInternal.Data)))").map
    (fun (_, xs) => _root_.Equivalence.Model.dataJson (.List xs))) ==
  (Json.parse "{\"list\":[{\"int\":42}]}").toOption
#guard ((_root_.Equivalence.Model.mapBinding
    "mint: (List.cons (Prod.mk (Data.I 1) (Data.I 2)) (as List.nil MapEntryList))").map
    (fun (_, xs) => _root_.Equivalence.Model.dataJson (.Map xs))) ==
  (Json.parse "{\"map\":[{\"k\":{\"int\":1},\"v\":{\"int\":2}}]}").toOption

end Tests.Equivalence.Model
