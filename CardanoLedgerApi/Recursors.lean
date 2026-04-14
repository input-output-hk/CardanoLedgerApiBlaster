import Lean
open Lean Elab Term Meta

namespace CardanoLedgerApi.Recursors

/-! This module introduces a set of macros that specialize recursors on List. -/

/--
  "Recursor.map `x` in `xs` with `body`"
   Expands into a local recursive function that maps each element `x` in `xs` with `body`.

   Example usage:
     Recursor.map n in [1, 2, 3, 4, 5] with n + 10  -- [11, 12, 13, 14, 15]
-/
syntax (name := recursorMap) "Recursor.map " ident " in " term " with " term : term

@[term_elab recursorMap]
def elabRecursorMap : TermElab := fun stx expectedType? => do
  let `(Recursor.map $x in $xs with $body) := stx
    | throwUnsupportedSyntax
  elabTerm (← `(
    let rec go : List _ → List _ :=
      fun
        | [] => []
        | $x :: t => $body :: go t
    go $xs
  )) expectedType?

/--
  "Recursor.find? `x` in `xs => `pred`"
   Expands into a local recursive function that traverses `xs` and returns
   `some x` for the first element satisfying `pred`.
    Return `none` if no element matches.

   Example usage:
     Recursor.find? n in [1, 2, 3, 4, 5] => n % 2 = 0  -- some 2
-/
syntax (name := recursorFind) "Recursor.find? " ident " in " term " => " term : term

@[term_elab recursorFind]
def elabRecursorFind : TermElab := fun stx expectedType? => do
  let `(Recursor.find? $x in $xs => $pred) := stx
    | throwUnsupportedSyntax
  elabTerm (← `(
    let rec go : List _ → Option _ :=
      fun
        | [] => none
        | $x :: t => if $pred then some $x else go t
    go $xs
  )) expectedType?

/--
  "Recursor.findMap? `x` in `xs` => `pred` with `body`"
   Expands into a local recursive function that traverses `xs` and returns
   `some body` for the first element satisfying `pred`.
    Return `none` if no element matches.

   Example usage:
     Recursor.findMap? n in [1, 2, 3, 4, 5] => n % 2 = 0 with n + 10 -- some 12
-/
syntax (name := recursorFindMap) "Recursor.findMap? " ident " in " term " => " term " with " term : term

@[term_elab recursorFindMap]
def elabRecursorFindMap : TermElab := fun stx expectedType? => do
  let `(Recursor.findMap? $x in $xs => $pred with $body) := stx
    | throwUnsupportedSyntax
  elabTerm (← `(
    let rec go : List _ → Option _ :=
      fun
        | [] => none
        | $x :: t => if $pred then some $body else go t
    go $xs
  )) expectedType?


/--
  "Recursor.findAll `x` in `xs` => `pred`"
   Expands into a local recursive function that traverses `xs` and returns
   all elements satisfying `pred`.

   Example usage:
     Recursor.findAll n in [1, 2, 3, 4, 5] => n > 2  -- [3, 4, 5]
     Recursor.findAll n in [1, 2, 3, 4, 5] => n > 5  -- []
-/
syntax (name := recursorFindAll) "Recursor.findAll " ident " in " term " => " term : term

@[term_elab recursorFindAll]
def elabRecursorFindAll : TermElab := fun stx expectedType? => do
  let `(Recursor.findAll $x in $xs => $pred) := stx
    | throwUnsupportedSyntax
  elabTerm (← `(
    let rec go : List _ → List _ :=
      fun
        | [] => []
        | $x :: t => if $pred then $x :: go t else go t
    go $xs
  )) expectedType?

/--
  "Recursor.any `x` in `xs` => `pred`"
   Expands into a local recursive function that traverses `xs` and returns `true`
   for the first element satisfying `pred`.
   Return `false` if no element matches.

   Example usage:
     Recursor.any n in [1, 2, 3, 4, 5] => n ≥ 10  -- false
     Recursor.any n in [1, 2, 3, 4, 5] => n < 4  -- true
-/
syntax (name := recursorAny) "Recursor.any " ident " in " term " => " term : term

@[term_elab recursorAny]
def elabRecursorAny : TermElab := fun stx expectedType? => do
  let `(Recursor.any $x in $xs => $pred) := stx
    | throwUnsupportedSyntax
  elabTerm (← `(
    let rec go : List _ → Bool :=
      fun
        | [] => false
        | $x :: t => $pred || go t
    go $xs
  )) expectedType?

/--
  "Recursor.all `x` in `xs` => `pred`"
   Expands into a local recursive function that traverses `xs` and returns `true`
   when all elements satisfy `pred`. Return `false` on the first element not satisfying `pred`.

   Example usage:
     Recursor.all n in [1, 2, 3, 4, 5] => n < 5  -- true
     Recursor.all n in [1, 2, 3, 4, 5] => n < 3  -- false
-/
syntax (name := recursorAll) "Recursor.all " ident " in " term " => " term : term

@[term_elab recursorAll]
def elabRecursorAll : TermElab := fun stx expectedType? => do
  let `(Recursor.all $x in $xs => $pred) := stx
    | throwUnsupportedSyntax
  elabTerm (← `(
    let rec go : List _ → Bool :=
      fun
        | [] => true
        | $x :: t => $pred && go t
    go $xs
  )) expectedType?

end CardanoLedgerApi.Recursors
