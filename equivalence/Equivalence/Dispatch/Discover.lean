import Equivalence.Dispatch.Pattern
import PlutusCore.UPLC.BuiltinFunctions.Evaluate

/-! Bounded abstract execution discovers equality dispatch through UPLC closures,
forces, projections and decoders. Discoveries are hints, never proof assumptions.
The same paths and Data kinds apply to both datum and redeemer, including nested
constructors, lists, maps, byte strings and integer payloads. -/

namespace Equivalence.Dispatch
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term Program Const BuiltinFun BuiltinType)
open PlutusCore.UPLC.Builtins (ExpectedBuiltinArgs ExpectedBuiltinArg expectedArgs)

private structure Scan where
  fuel : Nat := 10000
  facts : Array Fact := #[]
  limited : Bool := false
  limitReasons : Array String := #[]
  decisions : List Nat := []
  taken : Array Nat := #[]
  pending : Array (Nat × List Nat) := #[]

private abbrev M := StateM Scan

private def addReason (reasons : Array String) (reason : String) : Array String :=
  if reasons.contains reason then reasons else reasons.push reason

private def reachLimit (reason : String) : M Unit :=
  modify fun s => { s with limited := true, limitReasons := addReason s.limitReasons reason }

private def tick (depth : Nat) : M Bool := do
  let state ← get
  if state.fuel == 0 then
    reachLimit "trace fuel limit"
    return false
  if depth > 1024 then
    reachLimit "evaluation depth limit"
    return false
  modify fun s => { s with fuel := s.fuel - 1 }
  return true

private def note (fact : Fact) : M Unit := do
  let path := fact.path
  if path.root == .context then return
  if path.steps.length > 6 then reachLimit "data path depth limit"
  else if (← get).facts.size ≥ 256 then reachLimit "fact limit"
  else if !(← get).facts.contains fact then modify fun s => { s with facts := s.facts.push fact }

private inductive Scalar where
  | integer (p : Path)
  | tag (p : Path)
  | bytes (p : Path)
  | text (p : Path)

private inductive Value where
  | constant (c : Const)
  | data (p : Path)
  | node (tag : Int) (fields : List Value)
  | dataList (items : List Value)
  | dataMap (entries : List (Value × Value))
  | pair (a b : Value)
  | list (elemTy : BuiltinType) (items : List Value)
  | sequence (p : Path) (s : Sequence) (offset : Nat)
  | scalar (s : Scalar)
  | closure (body : Term) (env : List Value) (delayed : Bool)
  | builtin (b : BuiltinFun) (args : List Value) (remaining : ExpectedBuiltinArgs)
  | ctor (tag : Nat) (fields : List Value)
  | test (fact : Fact)
  | unknown

private instance : Inhabited Value := ⟨.unknown⟩

private def dataTy : BuiltinType := .AtomicType .TypeData
private def dataPairTy : BuiltinType := .TypeOperator (.TypePair dataTy dataTy)

private partial def ofConst : Const → Value
  | .Data (.Constr tag fields) => .node tag (fields.map (fun d => ofConst (.Data d)))
  | .ConstDataList items => .list dataTy (items.map (fun d => ofConst (.Data d)))
  | .ConstPairDataList items => .list dataPairTy (items.map fun (k,v) => .pair (ofConst (.Data k)) (ofConst (.Data v)))
  | .ConstList elemTy items => .list elemTy (items.map ofConst)
  | .Pair (a,b) => .pair (ofConst a) (ofConst b)
  | .PairData (a,b) => .pair (ofConst (.Data a)) (ofConst (.Data b))
  | c => .constant c

private partial def toConst : Value → Option Const
  | .constant c => some c
  | .node tag fields => return .Data (.Constr tag (← fields.mapM data))
  | .dataList items => return .Data (.List (← items.mapM data))
  | .dataMap entries => return .Data (.Map (← entries.mapM fun (k,v) => do
      return (← data k, ← data v)))
  | .pair a b => return .Pair (← toConst a, ← toConst b)
  | .list elemTy items => do
    if elemTy == dataTy then return .ConstDataList (← items.mapM data)
    if elemTy == dataPairTy then
      return .ConstPairDataList (← items.mapM fun
        | .pair a b => return (← data a, ← data b)
        | _ => none)
    return .ConstList elemTy (← items.mapM toConst)
  | _ => none
where
  data (v : Value) : Option Data := do
    let some (.Data d) := toConst v | none
    return d

private def prioritize (pending : Array (Nat × List Nat)) : Array (Nat × List Nat) :=
  (pending.toList.mergeSort (fun a b => a.1 ≤ b.1)).toArray

private def branchPriority (p : Path) : Nat :=
  match p.root with | .redeemer => 0 | .datum => 1 | .context => 2

/-- Replay a decision prefix, then queue its siblings. Dispatch decisions take
priority over unrelated transaction branches; all exploration remains bounded. -/
private def pick (count : Nat) (priority := 2) : M Nat := do
  let state ← get
  let (index, remaining) := match state.decisions with
    | next :: rest => (next, rest)
    | [] => (0, [])
  if state.decisions.isEmpty then
    let decisionPrefix := state.taken.toList
    let siblings := ((List.range count).drop 1).map (fun i => (priority, decisionPrefix ++ [i])) |>.toArray
    let pending := prioritize (state.pending ++ siblings)
    modify fun s => { s with pending := pending.take 128 }
    if pending.size > 128 then reachLimit "pending branch limit"
  modify fun s => { s with decisions := remaining, taken := s.taken.push index }
  return index

private def choose (values : List Value) : M Value := do
  let index ← pick values.length
  return values[index]?.getD .unknown

private def scalarEquality (a b : Value) : Option Fact :=
  match a, toConst b with
  | .data p, some (.Data d) => some (.equal p d)
  | .scalar (.integer p), some (.Integer n) => some (.equal p (.I n))
  | .scalar (.tag p), some (.Integer n) => some (.tag p n)
  | .scalar (.bytes p), some (.ByteString b) => some (.equal p (.B b))
  | .scalar (.text p), some (.String s) => some (.equal p (.B (PlutusCore.String.encodeUtf8 s)))
  | _, _ => none

private def opposite : Fact → Fact
  | .equal p d => .notEqual p d | .notEqual p d => .equal p d
  | .tag p n => .notTag p n | .notTag p n => .tag p n
  | .length p t n => .need p t (n + 1)
  | fact => fact

private def known (test fact : Fact) : Option Bool :=
  if test.path != fact.path then none else
  match test, fact with
  | .equal _ a, .equal _ b => some (a == b)
  | .tag _ a, .tag _ b => some (a == b)
  | .kind _ a, .kind _ b => some (a == b)
  | .notEqual _ a, .equal _ b => some (a != b)
  | .notTag _ a, .tag _ b => some (a != b)
  | .equal _ a, .notEqual _ b => if a == b then some false else none
  | .tag _ a, .notTag _ b => if a == b then some false else none
  | .length _ t n, .length _ u m => if t == u then some (n == m) else none
  | .need _ t n, .length _ u m => if t == u then some (m ≥ n) else none
  | _, _ => if test == fact then some true else none

private def assume (fact : Fact) : M Bool := do
  if let some yes := (← get).facts.toList.findSome? (known fact) then
    note (if yes then fact else opposite fact)
    return yes
  let yes := (← pick 2 (branchPriority fact.path)) == 0
  note (if yes then fact else opposite fact)
  return yes

private def sequenceHead (p : Path) (s : Sequence) (offset : Nat) : M Value := do
  if offset ≥ 8 then reachLimit "collection prefix limit"; return .unknown
  note (.need p s (offset + 1))
  return match s with
    | .fields => .data (p.child (.field offset))
    | .items => .data (p.child (.item offset))
    | .entries => .pair (.data (p.child (.key offset))) (.data (p.child (.value offset)))

private def native (b : BuiltinFun) (args : List Value) : Value := (do
  let constants ← args.mapM toConst
  let value ← PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction
    .defaultFunSemanticsVariantE b (constants.reverse.map PlutusCore.UPLC.CekValue.CekValue.VCon)
  let .VCon c := value | none
  return ofConst c).getD .unknown

mutual
  private partial def builtin (b : BuiltinFun) (args : List Value) (depth : Nat) : M Value := do
    unless ← tick depth do return .unknown
    match b, args with
    | .UnIData, [.data p] => note (.kind p .integer); return .scalar (.integer p)
    | .UnBData, [.data p] => note (.kind p .bytes); return .scalar (.bytes p)
    | .UnConstrData, [.data p] =>
      note (.kind p .constr)
      return .pair (.scalar (.tag p)) (.sequence p .fields 0)
    | .UnConstrData, [.node tag fields] => return .pair (.constant (.Integer tag)) (.list dataTy fields)
    | .UnListData, [.dataList items] => return .list dataTy items
    | .UnMapData, [.dataMap entries] => return .list dataPairTy (entries.map fun (k,v) => .pair k v)
    | .UnListData, [.data p] => note (.kind p .list); return .sequence p .items 0
    | .UnMapData, [.data p] => note (.kind p .map); return .sequence p .entries 0
    | .UnListData, [.constant (.Data (.List xs))] => return .list dataTy (xs.map fun d => ofConst (.Data d))
    | .UnMapData, [.constant (.Data (.Map xs))] =>
      return .list dataPairTy (xs.map fun (k,v) => .pair (ofConst (.Data k)) (ofConst (.Data v)))
    | .FstPair, [.pair a _] => return a
    | .SndPair, [.pair _ b] => return b
    | .HeadList, [.list _ (x :: _)] => return x
    | .TailList, [.list elemTy (_ :: xs)] => return .list elemTy xs
    | .HeadList, [.sequence p s offset] => sequenceHead p s offset
    | .TailList, [.sequence p s offset] =>
      note (.need p s (offset + 1))
      return .sequence p s (offset + 1)
    | .NullList, [.list _ xs] => return .constant (.Bool xs.isEmpty)
    | .NullList, [.sequence p s offset] => return .test (.length p s offset)
    | .MkCons, [head, .list elemTy tail] => return .list elemTy (head :: tail)
    | .MkPairData, [a,b] => return .pair a b
    | .MkNilData, _ => return .list dataTy []
    | .MkNilPairData, _ => return .list dataPairTy []
    | .EqualsInteger, [a,z] | .EqualsByteString, [a,z] | .EqualsString, [a,z] | .EqualsData, [a,z] =>
      if let some fact := scalarEquality a z <|> scalarEquality z a then return .test fact
      return native b args
    | .IfThenElse, [.constant (.Bool yes), a, z] => return if yes then a else z
    | .IfThenElse, [.test fact,a,z] => return if ← assume fact then a else z
    | .IfThenElse, [_, a,z] => choose [a,z]
    | .ChooseList, [.list _ xs,a,z] => return if xs.isEmpty then a else z
    | .ChooseList, [.sequence p s offset,a,z] => return if ← assume (.length p s offset) then a else z
    | .ChooseList, [_,a,z] => choose [a,z]
    | .ChooseData, [.node _ _,a,_,_,_,_] => return a
    | .ChooseData, [.dataMap _,_,m,_,_,_] => return m
    | .ChooseData, [.dataList _,_,_,l,_,_] => return l
    | .ChooseData, [.data p,a,m,l,i,b] =>
      let index ← pick 5 (branchPriority p)
      let some kind := [Kind.constr,.map,.list,.integer,.bytes][index]? | return .unknown
      note (.kind p kind)
      return [a,m,l,i,b][index]?.getD .unknown
    | .ChooseUnit, [_,v] | .Trace, [_,v] => return v
    | .IData, [.scalar (.integer p)] | .BData, [.scalar (.bytes p)] => return .data p
    | .ConstrData, [.constant (.Integer tag), .list elemTy fields] =>
      return if elemTy == dataTy then .node tag fields else .unknown
    | .DecodeUtf8, [.scalar (.bytes p)] => return .scalar (.text p)
    | .EncodeUtf8, [.scalar (.text p)] => return .scalar (.bytes p)
    | _, _ => return native b args

  private partial def apply (f arg : Value) (depth : Nat) : M Value := do
    unless ← tick depth do return .unknown
    match f with
    | .closure body env false => eval body (arg :: env) (depth + 1)
    | .builtin b args (.More .ArgV rest) => return .builtin b (arg :: args) rest
    | .builtin b args (.One .ArgV) => builtin b (arg :: args).reverse (depth + 1)
    | _ => return .unknown

  private partial def force (v : Value) (depth : Nat) : M Value := do
    unless ← tick depth do return .unknown
    match v with
    | .closure body env true => eval body env (depth + 1)
    | .builtin b args (.More .ArgQ rest) => return .builtin b args rest
    | .builtin b args (.One .ArgQ) => builtin b args.reverse (depth + 1)
    | _ => return .unknown

  private partial def caseValue (v : Value) (handlers : List Term) (env : List Value) (depth : Nat) : M Value := do
    unless ← tick depth do return .unknown
    let run := fun index values => do
      let some body := handlers[index]? | return Value.unknown
      let f ← eval body env (depth + 1)
      values.foldlM (fun f arg => apply f arg (depth + 1)) f
    match v with
    | .ctor tag values => run tag values
    | .constant (.Integer n) => if n < 0 then return .unknown else run n.toNat []
    | .constant (.Bool b) => run (if b then 1 else 0) []
    | .constant .Unit => run 0 []
    | .pair a b => run 0 [a,b]
    | .list _ [] => run 1 []
    | .list elemTy (x :: xs) => run 0 [x,.list elemTy xs]
    | .scalar s =>
      let path := match s with | .integer p | .tag p | .bytes p | .text p => p
      let index ← pick handlers.length (branchPriority path)
      if let some fact := scalarEquality (.scalar s) (.constant (.Integer index)) then note fact
      run index []
    | .test fact => run (if ← assume fact then 1 else 0) []
    | .sequence p s offset =>
      if ← assume (.length p s offset) then run 1 []
      else run 0 [← sequenceHead p s offset, .sequence p s (offset + 1)]
    | _ =>
      let index ← pick handlers.length
      let some body := handlers[index]? | return .unknown
      eval body env (depth + 1)

  private partial def eval (term : Term) (env : List Value) (depth : Nat) : M Value := do
    unless ← tick depth do return .unknown
    match term with
    | .Var index => return env[index]?.getD .unknown
    | .Const c => return ofConst c
    | .Builtin b => return .builtin b [] (expectedArgs b)
    | .Lam body => return .closure body env false
    | .Delay body => return .closure body env true
    | .Force body => force (← eval body env (depth + 1)) (depth + 1)
    | .Apply f arg =>
      let f ← eval f env (depth + 1)
      let arg ← eval arg env (depth + 1)
      apply f arg (depth + 1)
    | .Constr tag fields => return .ctor tag (← fields.mapM fun f => eval f env (depth + 1))
    | .Case scrutinee handlers => caseValue (← eval scrutinee env (depth + 1)) handlers env (depth + 1)
    | .Error => return .unknown
end

private def products {α : Type} (parts : List (List α)) (limit : Nat := 16) : List (List α) :=
  parts.foldl (fun acc next => ((acc.flatMap fun xs => next.map (xs ++ [·])).take limit)) [[]]

private def sequenceSizes (facts : Array Fact) (p : Path) (s : Sequence) : List (Nat × Bool) := Id.run do
  let exact := facts.toList.filterMap fun f => match f with
    | .length q t n => if p == q && s == t && n ≤ 8 then some (n,true) else none
    | _ => none
  let needed := facts.foldl (fun n f => match f with
    | .need q t k => if p == q && s == t then max n (min k 8) else n
    | _ => n) 0
  return (exact ++ [(needed,true),(needed,false)]).eraseDups

private partial def variants (facts : Array Fact) (p : Path) (depth : Nat := 0) : List Pattern := Id.run do
  if depth > 6 then return [.any]
  let literals := facts.toList.filterMap fun f => match f with
    | .equal q d => if p == q then some (Pattern.literal d) else none
    | _ => none
  let kinds := (facts.toList.filterMap fun f => match f with
    | .kind q k => if p == q then some k else none
    | _ => none).eraseDups
  -- Facts within one trace are conjunctive; a literal is not an alternative
  -- to the broader type information learned while decoding it.
  if !literals.isEmpty then return literals.eraseDups
  let mut result := []
  for k in kinds do
    match k with
    | .integer => result := result ++ [.integer]
    | .bytes => result := result ++ [.bytes]
    | .constr =>
      let tags := (facts.toList.filterMap fun f => match f with
        | .tag q n => if p == q then some (some n) else none
        | _ => none).eraseDups
      let tags := if tags.isEmpty then [none] else tags
      for (size,exact) in sequenceSizes facts p .fields do
        let choices := (List.range size).map fun i => variants facts (p.child (.field i)) (depth + 1)
        for children in products choices do
          for tag in tags do result := result ++ [.constr tag children exact]
    | .list =>
      for (size,exact) in sequenceSizes facts p .items do
        let choices := (List.range size).map fun i => variants facts (p.child (.item i)) (depth + 1)
        result := result ++ (products choices).map (fun xs => .list xs exact)
    | .map =>
      for (size,exact) in sequenceSizes facts p .entries do
        let choices := (List.range size).map fun i =>
          (variants facts (p.child (.key i)) (depth + 1)).flatMap fun k =>
            (variants facts (p.child (.value i)) (depth + 1)).map (k, ·)
        result := result ++ (products choices).map (fun xs => .map xs exact)
  return if result.isEmpty then [.any] else result.eraseDups.take 16

structure Discovery where
  cases : Array Case := #[]
  limited : Bool := false
  factCount : Nat := 0
  limitReasons : Array String := #[]
  deriving Repr

/-- Optional collection tails are variants of the same dispatch alternative. -/
private partial def selectorKey : Pattern → Pattern
  | .constr tag fields _ => .constr tag (fields.map selectorKey) true
  | .list items _ => .list (items.map selectorKey) true
  | .map entries _ => .map (entries.map fun (k,v) => (selectorKey k, selectorKey v)) true
  | pattern => pattern

private def groupCase (groups : Array (Pattern × Array Case)) (candidate : Case) : Array (Pattern × Array Case) :=
  let key := selectorKey candidate.redeemer
  match groups.findIdx? (fun (redeemer,_) => redeemer == key) with
  | none => groups.push (key, #[candidate])
  | some index => groups.modify index fun (redeemer,cases) =>
    (redeemer, if cases.contains candidate then cases else cases.push candidate)

/-- Analyze each implementation along separate bounded decision traces. Never
combine datum facts from one branch with redeemer facts from another. -/
def discover (limits : ValidContext.Limits) (oldProgram newProgram : Program) (caseLimit : Nat := 16) : Discovery := Id.run do
  let datum := limits.datum.map (fun d => ofConst (.Data d)) |>.getD (.data ⟨.datum,[]⟩)
  let redeemer := limits.redeemer.map (fun d => ofConst (.Data d)) |>.getD (.data ⟨.redeemer,[]⟩)
  -- Some validators read datum/redeemer through the own input or redeemer
  -- map instead of ScriptInfo. Preserve those aliases in a one-own-input
  -- discovery scaffold; this does not restrict the eventual solver context.
  let external := fun i => Value.data ⟨.context,[.field i]⟩
  let reference := ofConst (.Data (Context.outputReference ({} : ValidContext.Fields).scriptTxId))
  let ownOutput := Value.node 0 [external 16, external 17, .node 2 [datum], .node 1 []]
  let ownInput := Value.node 0 [reference, ownOutput]
  let txFields := (List.range 16).map external
  let txFields := txFields.set 0 (.dataList (if limits.maxInputs > 0 then [ownInput] else []))
  let txFields := txFields.set 9 (.dataMap [(.node 1 [reference], redeemer)])
  let context := Value.node 0 [.node 0 txFields,redeemer,.node 1 [reference,.node 0 [datum]]]
  let mut groups : Array (Pattern × Array Case) := #[]
  let mut facts : Array Fact := #[]
  let mut limited := false
  let mut limitReasons := #[]
  for program in [oldProgram, newProgram] do
    let mut pending := #[(0, ([] : List Nat))]
    let mut remaining := 200000
    let mut seen : Array (List Nat) := #[]
    while !pending.isEmpty && remaining > 0 && seen.size < 32 do
      let decisions := pending[0]!.2
      pending := pending.extract 1 pending.size
      seen := seen.push decisions
      let scan : M Unit := do
        let .Program _ body := program
        discard (apply (← eval body [] 0) context 0)
      let fuel := min remaining 10000
      let (_, state) := scan.run { fuel, decisions }
      remaining := remaining - (fuel - state.fuel)
      let queued := prioritize (pending ++ state.pending)
      let queued := queued.foldl (fun acc item =>
        if seen.contains item.2 || acc.any (fun existing => existing.2 == item.2) then acc else acc.push item) #[]
      pending := queued.take 128
      limited := limited || queued.size > 128 || state.limited
      if queued.size > 128 then limitReasons := addReason limitReasons "pending branch limit"
      limitReasons := state.limitReasons.foldl addReason limitReasons
      for fact in state.facts do
        if !facts.contains fact then facts := facts.push fact
      if state.facts.any (fun fact => state.facts.any (fun other => known fact other == some false)) then continue
      let datums := limits.datum.map (fun d => [Pattern.literal d]) |>.getD (variants state.facts ⟨.datum,[]⟩)
      let redeemers := limits.redeemer.map (fun d => [Pattern.literal d]) |>.getD (variants state.facts ⟨.redeemer,[]⟩)
      limited := limited || datums.length ≥ 16 || redeemers.length ≥ 16
      if datums.length ≥ 16 || redeemers.length ≥ 16 then
        limitReasons := addReason limitReasons "pattern variant limit"
      let conditions := state.facts.toList
      for r in redeemers do
        for d in datums do
          let datumRestricted := d != .any || conditions.any (·.path.root == .datum)
          let redeemerRestricted := r != .any || conditions.any (·.path.root == .redeemer)
          if (limits.datum.isNone && datumRestricted) || (limits.redeemer.isNone && redeemerRestricted) then
            if let some candidate := ({ datum := d, redeemer := r, conditions } : Case).normalize then
              groups := groupCase groups candidate
    limited := limited || !pending.isEmpty
    if !pending.isEmpty then
      limitReasons := addReason limitReasons (if remaining == 0 then "total scan fuel limit" else "branch trace limit")
  -- Both implementations may test different literal selectors. Split broad
  -- alternatives at their union so "other" excludes all named values, while
  -- each named value retains datum requirements from either implementation.
  let literals := groups.toList.flatMap (fun (_,cases) => cases.toList.filterMap fun c =>
    match c.redeemer with | .literal value => some value | _ => none) |>.eraseDups
  let mut partitioned : Array (Pattern × Array Case) := #[]
  for (_,cases) in groups do
    for candidate in cases do
      if candidate.redeemer matches .literal _ then
        partitioned := groupCase partitioned candidate
      else
        for value in literals do
          if let some refined := candidate.withRedeemer value then
            partitioned := groupCase partitioned refined
        let exclusions := literals.map (Fact.notEqual ⟨.redeemer,[]⟩)
        let residual := { candidate with conditions := candidate.conditions ++ exclusions }
        if let some residual := residual.normalize then partitioned := groupCase partitioned residual
  groups := partitioned
  -- Try each redeemer group's first useful datum before further alternatives.
  -- Broad prefixes remain available afterwards.
  let alternatives := groups.map fun (_,cases) =>
    cases.filter (fun (c : Case) => c.datum != Pattern.any) ++ cases.filter (fun (c : Case) => c.datum == Pattern.any)
  let rounds := alternatives.foldl (fun n cases => max n cases.size) 0
  let mut candidates : Array Case := #[]
  for i in [:rounds] do
    for cases in alternatives do
      if let some candidate := cases[i]? then candidates := candidates.push candidate
  if candidates.size > caseLimit then limitReasons := addReason limitReasons "case limit"
  return {
    cases := candidates.take caseLimit
    limited := limited || candidates.size > caseLimit
    factCount := facts.size
    limitReasons }

end Equivalence.Dispatch
