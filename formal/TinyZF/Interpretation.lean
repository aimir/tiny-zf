import TinyZF.Formulas
import TinyZF.Source
import TinyZF.ProtectedOriginal

/-! # First-order meaning of the numeric calculus

The selected Boolean rewrites preserve first-order truth in every domain and
valuation. This is semantic equivalence, not yet a derivation of their
interchangeability inside the source Hilbert calculus.
-/
namespace TinyZF.Source

-- Keep constructor names intact while rewriting their decoding laws. Expanding
-- nested Cantor arithmetic during propositional normalization is unnecessary.
attribute [local irreducible] weq wel wim wn wal wex wa

/-- All source derivations are valid in every structure satisfying its explicit
schemas. Invalid formula codes and stack defaults are covered by total decoding. -/
theorem derivation_valid {α : Type} (membership : α → α → Prop)
    (model : ModelsSource membership) {n : Nat} (h : Provable n) : Valid membership n := by
  induction h with
  | moot => intro env; simp [Formula.eval]
  | «axiom» k p1 p2 p3 => exact model k p1 p2 p3
  | @detachment a b hab ha ihab iha =>
    intro env
    have hh := ihab env
    simp only [decode_wim, Formula.eval] at hh
    exact hh (iha env)
  | @generalization x a ha ih =>
    intro env
    simp only [decode_wal, Formula.eval]
    exact fun v => ih (Function.update env x v)

set_option maxHeartbeats 2000000 in
/-- The exact five protected rewrite choices preserve truth for arbitrary numeric
parameters, arbitrary membership structures, and every variable assignment. -/
theorem protected_rewrites_correct {α : Type} (membership : α → α → Prop)
    (env : Nat → α) (k : Fin 5) (p1 p2 p3 : Nat) :
    (decodeFormula (schema ⟨k.val + 10, by omega⟩ p1 p2 p3)).eval membership env ↔
      (decodeFormula (originalProtected k p1 p2 p3)).eval membership env := by
  classical
  fin_cases k <;> try rfl
  all_goals
    simp only [schema, originalProtected, wex, wa, decode_wn, decode_wal,
      decode_wim, decode_wel, Formula.eval]
    simp only [imp_iff_not_or, not_or, not_and_or, not_not,
      not_forall, not_exists, and_comm, or_comm]

end TinyZF.Source
