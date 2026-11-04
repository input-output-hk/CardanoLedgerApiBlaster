import Lean
import Blaster
import PlutusCore

-- Check the symbolic boundaries, including the transparent CEK adapters.
open Lean Elab Command in
run_elab do
  for n in #[``PlutusCore.String.encodeUtf8, ``PlutusCore.String.decodeUtf8,
      ``PlutusCore.Cbor.encodeData] do
    unless (← getEnv).find? n |>.any (fun c => match c with
      | .opaqueInfo _ => true
      | _ => false) do
      throwError "Expected opaque declaration: {n}"
  for n in #[``PlutusCore.UPLC.BuiltinFunctions.String.encodeUtf8,
      ``PlutusCore.UPLC.BuiltinFunctions.String.decodeUtf8,
      ``PlutusCore.UPLC.BuiltinFunctions.Data.serializeData] do
    unless (← getEnv).find? n |>.any (fun c => match c with
      | .defnInfo _ => true
      | _ => false) do
      throwError "Expected transparent adapter: {n}"

open PlutusCore.String PlutusCore.Cbor

-- These proofs use Blaster's symbolic path, without executing primitive bodies.
example (s t : String) : s = t → encodeUtf8 s = encodeUtf8 t := by blaster
example (x y : PlutusCore.ByteString.ByteString) :
    x = y → decodeUtf8 x = decodeUtf8 y := by blaster
example (x y : PlutusCore.Data.Data) :
    x = y → encodeData x = encodeData y := by blaster

open PlutusCore.UPLC.CekValue PlutusCore.UPLC.Term

example (s : String) :
    PlutusCore.UPLC.BuiltinFunctions.String.encodeUtf8 [.VCon (.String s)] =
      some (.VCon (.ByteString (encodeUtf8 s))) := by blaster

example (bs : PlutusCore.ByteString.ByteString) :
    PlutusCore.UPLC.BuiltinFunctions.String.decodeUtf8 [.VCon (.ByteString bs)] =
      PlutusCore.UPLC.BuiltinFunctions.Utils.tryCatchSome
        (decodeUtf8 bs) (CekValue.VCon ∘ Const.String) := by blaster

example (d : PlutusCore.Data.Data) :
    PlutusCore.UPLC.BuiltinFunctions.Data.serializeData [.VCon (.Data d)] =
      (fun s => CekValue.VCon (.ByteString ⟨s⟩))
        <$> encodeData d := by blaster

-- CEK argument checks still reduce without opening the primitive bodies.
example : PlutusCore.UPLC.BuiltinFunctions.String.encodeUtf8 [] = none := rfl
example : PlutusCore.UPLC.BuiltinFunctions.String.decodeUtf8 [] = none := rfl
example : PlutusCore.UPLC.BuiltinFunctions.Data.serializeData [] = none := rfl
