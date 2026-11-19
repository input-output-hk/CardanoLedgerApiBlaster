import Equivalence.Checker

open PlutusCore.UPLC.Term

-- Check the corpus adapter against expected GCD values, so agreement on two
-- evaluation errors cannot accidentally validate an inappropriate input ABI.
#eval show IO Unit from do
  let files ← System.FilePath.readDir "equivalence/examples/ecd"
  let mut checks := 0
  for file in files do
    if file.path.extension == some "cbor_hex" then
      let program ← IO.ofExcept <|
        PlutusCore.UPLC.ScriptEncoding.Internal.singleCborEncodedScriptFromHex?
          (← IO.FS.readFile file.path).trim
      let .Program version body := program
      let adapted := Program.Program version
        (.Lam (.Apply (.Apply body (.Var 0)) (.Const (.Integer 462))))
      for (n, expected) in [(-12, 6), (0, 462), (6, 6), (48, 6), (1071, 21)] do
        let run p args := Equivalence.Function.execute p args 0 0 true false 20000
        match run program [.Const (.Integer n), .Const (.Integer 462)],
            run adapted [.Const (.Integer n)] with
        | .success (.VCon (.Integer a)) _, .success (.VCon (.Integer b)) _ =>
            unless a == expected && b == expected do
              throw <| IO.userError s!"Unexpected GCD: {file.path}, {n}, {a}, {b}"
        | _, _ => throw <| IO.userError s!"ECD did not return an integer: {file.path}, {n}"
        checks := checks + 1
  IO.println s!"ECD adapter: {checks} expected-value checks passed"
