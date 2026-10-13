import TinyZF.Cantor

/-! The 15 axiom-producing clauses, in logical then protected order.
Imported from the current candidate settings, including reversed binary payloads,
per-schema parameter permutations, protected safety guards and selected rewrites. -/
namespace TinyZF.Source
open Cantor

/-- Equality constructor in the reversed payload convention. -/
def weq (a b : Nat) := pair (pair b a) 0
/-- Membership constructor. -/
def wel (a b : Nat) := pair (pair b a) 1
/-- Implication constructor. -/
def wim (a b : Nat) := pair (pair b a) 2
/-- Negation constructor (its payload is unary). -/
def wn (a : Nat) := pair a 3
/-- Universal quantification constructor. -/
def wal (x a : Nat) := pair (pair a x) 4
/-- Existential quantification expands as not-forall-not. -/
def wex (x a : Nat) := wn (wal x (wn a))
/-- Conjunction expands as not-implication-not. -/
def wa (a b : Nat) := wn (wim a (wn b))
/-- Avoid capture at the protected phase, exactly as the source does. -/
def safe (a b : Nat) := if a = b then a + 1 else a

/-- The current source axiom instances. Numeric parameters are unrestricted.
The protected guards are part of the instance definition. -/
def schema (k : Fin 15) (p1 p2 p3 : Nat) : Nat :=
  match k.val with
  | 0 => -- B1
    (wim (wim p3 p2) (wim (wim p2 p1) (wim p3 p1)))
  | 1 => -- B2
    (wim (wim (wn p1) p1) p1)
  | 2 => -- B3
    (wim p2 (wim (wn p2) p1))
  | 3 => -- B4
    (wim (wal p2 (wim p1 p3)) (wim (wal p2 p1) (wal p2 p3)))
  | 4 => -- B6b
    (wim (wal p2 (wal p1 p3)) (wal p1 (wal p2 p3)))
  | 5 => -- B6c
    (wim (wex p2 (wal p2 p1)) p1)
  | 6 => -- B7
    (wex p1 (weq p1 p2))
  | 7 => -- B8a
    (wim (weq p1 p3) (wim (weq p1 p2) (weq p3 p2)))
  | 8 => -- B8b
    (wim (weq p1 p2) (wim (wel p1 p3) (wel p2 p3)))
  | 9 => -- B8c
    (wim (weq p1 p3) (wim (wel p2 p1) (wel p2 p3)))
  | 10 => -- POW
    let p1 := safe p1 p2
    let p3 := safe p3 p2
    (wex p3 (wal p2 (wim (wal p3 (wim (wel p3 p2) (wel p3 p1))) (wel p2 p3))))
  | 11 => -- UNI
    let p1 := safe p1 p2
    let p3 := safe p3 p2
    (wex p3 (wal p2 (wim (wn (wal p3 (wim (wel p2 p3) (wn (wel p3 p1))))) (wel p2 p3))))
  | 12 => -- ICS
    let p1 := safe p1 p2
    let p3 := safe p3 p2
    (wn (wal p3 (wim (wal p2 (wa (wim (wel p2 p3) (wex p1 p3)) (wim (wel p2 p1) (wim (wex p1 p3) (wel p2 p3))))) (wn (wal p1 (wim (wn (wal p2 (wim p3 (wn (wal p2 (wim p3 (wn (wel p2 p3)))))))) (wn (wel p1 p3))))))))
  | 13 => -- B6a1
    let p1 := safe p1 p2
    let p3 := safe p3 p2
    (wim (weq p1 p3) (wal p2 (weq p1 p3)))
  | _ => -- B6a2
    let p1 := safe p1 p2
    let p3 := safe p3 p2
    (wim (wel p1 p3) (wal p2 (wel p1 p3)))

/-- Inference clauses and schema instances are kept distinct. -/
inductive Clause where
  | moot | detach | generalize | axiom (k : Fin 15)
  deriving DecidableEq

/-- Actual candidate selector order; large positive selectors saturate at the last clause. -/
def dispatch : Nat → Clause
  | 0 => .moot
  | 1 => .axiom 8
  | 2 => .axiom 5
  | 3 => .axiom 1
  | 4 => .axiom 6
  | 5 => .axiom 0
  | 6 => .axiom 2
  | 7 => .detach
  | 8 => .axiom 7
  | 9 => .axiom 3
  | 10 => .generalize
  | 11 => .axiom 9
  | 12 => .axiom 4
  | 13 => .axiom 14
  | 14 => .axiom 11
  | 15 => .axiom 10
  | 16 => .axiom 12
  | _ => .axiom 13

/-- Each schema has a selectable code in the compiled clause order. -/
def schemaSelector (k : Fin 15) : Nat :=
  (⟨#[5, 3, 6, 9, 12, 2, 4, 8, 1, 11, 15, 14, 16, 17, 13], by decide⟩ : Vector Nat 15).get k

end TinyZF.Source
