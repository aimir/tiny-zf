import Mathlib.Tactic

/-! # The machine's Cantor arithmetic

This is the diagonal pairing `a + (a+b)*(a+b+1)/2`, not mathlib's square pairing.
The inverse follows the same diagonal walk as the register program. All results
are for arbitrary natural numbers, without execution or tape-size bounds.
-/

namespace TinyZF.Cantor

/-- Triangular numbers, defined recursively to expose the loop invariant. -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => tri n + (n + 1)

/-- The recursive triangular number agrees with the source's integer formula. -/
theorem tri_formula (n : Nat) : tri n = n * (n + 1) / 2 := by
  have h : 2 * tri n = n * (n + 1) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [tri]; nlinarith
  omega

/-- Each completed diagonal has at least its index many cells. -/
theorem le_tri (n : Nat) : n ≤ tri n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [tri]; omega

/-- The exact pairing convention used in the candidate. -/
def pair (a b : Nat) : Nat := a + tri (a + b)

/-- Advance one position along the Cantor diagonals. -/
def advance : Nat × Nat → Nat × Nat
  | (a, 0) => (0, a + 1)
  | (a, b + 1) => (a + 1, b)

/-- The inverse algorithm starts at `(0,0)` and advances `n` times. -/
def unpair : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => advance (unpair n)

/-- The diagonal walk visits every position on each diagonal. -/
theorem unpair_diagonal (s a : Nat) (h : a ≤ s) :
    unpair (a + tri s) = (a, s - a) := by
  induction s generalizing a with
  | zero =>
    have : a = 0 := by omega
    subst a
    rfl
  | succ s ih =>
    induction a with
    | zero =>
      have eqn : 0 + tri (s + 1) = (s + tri s) + 1 := by simp only [tri]; omega
      rw [eqn, unpair, ih s (by omega)]
      simp [advance]
    | succ a ia =>
      have ha : a ≤ s + 1 := by omega
      have hs : s + 1 - a = (s - a) + 1 := by omega
      rw [show a + 1 + tri (s + 1) = (a + tri (s + 1)) + 1 by omega,
        unpair, ia ha, hs]
      simp [advance]

/-- Decoding an encoded pair recovers both arbitrary components. -/
@[simp] theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  unfold pair
  rw [unpair_diagonal (a + b) a (by omega)]
  simp

/-- Encoding the decoded components recovers every number, including garbage inputs. -/
@[simp] theorem pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    generalize h : unpair n = p at *
    obtain ⟨a,b⟩ := p
    cases b with
    | zero => simp only [unpair, h, advance, pair, tri, Nat.add_zero, Nat.zero_add] at *; omega
    | succ b => simp only [unpair, h, advance, pair] at *
                rw [show a + 1 + b = a + (b + 1) by omega]
                omega

/-- Injectivity prevents distinct stack or formula constructors sharing a code. -/
theorem pair_injective {a b c d : Nat} (h : pair a b = pair c d) : a = c ∧ b = d := by
  have hh := congrArg unpair h
  simpa using hh

/-- Bounds used to terminate the total formula decoder and proof-tail traversal. -/
theorem left_le (a b : Nat) : a ≤ pair a b := by unfold pair; omega

/-- The second component never exceeds the enclosing pair. -/
theorem right_le (a b : Nat) : b ≤ pair a b := by
  have := le_tri (a + b); unfold pair; omega

/-- A positive tag makes the payload strictly smaller than its formula code. -/
theorem left_lt (a b : Nat) (h : 0 < b) : a < pair a b := by
  have := le_tri (a + b); unfold pair; omega

/-- Both decoded components are bounded by their original code. -/
theorem unpair_le (n : Nat) : (unpair n).1 ≤ n ∧ (unpair n).2 ≤ n := by
  have hl := left_le (unpair n).1 (unpair n).2
  have hr := right_le (unpair n).1 (unpair n).2
  simpa using And.intro hl hr

end TinyZF.Cantor
