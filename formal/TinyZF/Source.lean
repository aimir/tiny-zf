import TinyZF.Enumeration
import TinyZF.Schemas

/-! # The candidate's numeric source calculus and stack interpreter

This specification is deliberately distinct from conventional ZF. It has the
exact candidate schema instances, two inference rules, and the harmless numeric
default 0. Its unbounded enumeration theorem does not assume tape/compiler
correctness or an interpretation between ICS and ZF.
-/
namespace TinyZF.Source
open Cantor

/-- Derivations in the exact numeric source calculus. Schema definitions expose
all guard, permutation and rewrite choices instead of trusting a compiler. -/
inductive Provable : Nat → Prop
  | moot : Provable 0
  | axiom (k : Fin 15) (p1 p2 p3 : Nat) : Provable (schema k p1 p2 p3)
  | detachment {a b : Nat} : Provable (wim a b) → Provable a → Provable b
  | generalization (x : Nat) {a : Nat} : Provable a → Provable (wal x a)

/-- Every schema can be selected; this finite certificate binds the inverse order. -/
theorem dispatch_schema (k : Fin 15) : dispatch (schemaSelector k) = .axiom k := by
  fin_cases k <;> decide

/-- Persistent theorem data: the current theorem and its Cantor-encoded stack. -/
abbrev Stack := Nat × Nat

/-- One source instruction. The old top is pushed before clause execution;
underflow decodes as zero, and failed detachment returns the default theorem. -/
def execute (i : Instruction) (s : Stack) : Stack :=
  let stack := pair s.1 s.2
  match dispatch i.selector with
  | .moot => (0, stack)
  | .axiom k => (schema k i.p1 i.p2 i.p3, stack)
  | .generalize =>
    let minor := unpair stack
    (wal i.p1 minor.1, minor.2)
  | .detach =>
    let minor := unpair stack
    let major := unpair minor.2
    (if wim minor.1 i.p1 = major.1 then i.p1 else 0, major.2)

/-- Every element of a zero-padded encoded stack is a theorem. -/
def GoodStack (w : Nat) : Prop :=
  ∀ k, Provable (unpair (iterate (fun n => (unpair n).2) k w)).1

/-- Popping preserves the stack invariant and produces a theorem, even on underflow. -/
theorem good_pop {w : Nat} (h : GoodStack w) :
    Provable (unpair w).1 ∧ GoodStack (unpair w).2 :=
  ⟨h 0, fun k => h (k + 1)⟩

/-- Pushing an arbitrary theorem preserves the infinite zero-padded stack invariant. -/
theorem good_push {x w : Nat} (hx : Provable x) (hw : GoodStack w) : GoodStack (pair x w) := by
  intro k
  cases k with
  | zero => simpa [iterate] using hx
  | succ k => simpa only [iterate, unpair_pair] using hw k

/-- Empty encoded stacks contain only the default theorem. -/
theorem good_zero : GoodStack 0 := by
  have h (k : Nat) : iterate (fun n => (unpair n).2) k 0 = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => exact ih
  intro k
  rw [h]
  exact Provable.moot

/-- The interpreter invariant includes both the top theorem and the encoded tail. -/
def Invariant (s : Stack) := Provable s.1 ∧ GoodStack s.2

/-- Every instruction, including malformed selectors and failed inferences,
preserves provability of every stack entry. -/
theorem execute_sound (i : Instruction) (s : Stack) (h : Invariant s) :
    Invariant (execute i s) := by
  have hw := good_push h.1 h.2
  unfold execute
  cases dispatch i.selector with
  | moot => exact ⟨Provable.moot, hw⟩
  | «axiom» k => exact ⟨Provable.axiom k i.p1 i.p2 i.p3, hw⟩
  | generalize =>
    have hh := good_pop hw
    exact ⟨Provable.generalization i.p1 hh.1, hh.2⟩
  | detach =>
    have h1 := good_pop hw
    have h2 := good_pop h1.2
    refine ⟨?_, h2.2⟩
    dsimp only
    split_ifs with eqn
    · rw [← eqn] at h2
      exact Provable.detachment h2.1 h1.1
    · exact Provable.moot

/-- A compiled derivation pushes exactly one new theorem, preserving every caller stack. -/
def Pushes (xs : List Instruction) (c : Nat) :=
  xs ≠ [] ∧ ∀ t w, executeList execute xs (t, w) = (c, pair t w)

/-- Every source derivation compiles into a nonempty list that works on any stack. -/
theorem compile {c : Nat} (h : Provable c) : ∃ xs, Pushes xs c := by
  induction h with
  | moot =>
    exact ⟨[⟨0,0,0,0⟩], by simp [Pushes, executeList, execute, dispatch]⟩
  | «axiom» k p1 p2 p3 =>
    exact ⟨[⟨schemaSelector k,p1,p2,p3⟩], by
      simp [Pushes, executeList, execute, dispatch_schema]⟩
  | @generalization x a ha ih =>
    obtain ⟨xs, hn, hx⟩ := ih
    refine ⟨xs ++ [⟨10,x,0,0⟩], ?_, ?_⟩
    · simp
    · intro t w
      rw [executeList_append, hx]
      simp [executeList, execute, dispatch]
  | @detachment a b hab ha ihab iha =>
    obtain ⟨xs, hn, hx⟩ := ihab
    obtain ⟨ys, hm, hy⟩ := iha
    refine ⟨xs ++ ys ++ [⟨7,b,0,0⟩], ?_, ?_⟩
    · simp
    · intro t w
      rw [executeList_append, executeList_append, hx, hy]
      simp [executeList, execute, dispatch]

/-- Initial source state: all persistent registers are zero. -/
def initial : SearchState Stack := ⟨0, 0, (0, 0)⟩

/-- The pure enumerator observes the same target code 1 after an instruction.
The pure function continues afterward; existence of the first hit models halting. -/
def FindsTarget : Prop := ∃ n, (iterate (searchStep execute) (n + 1) initial).payload.1 = 1

/-- Soundness applies at every arbitrary finite iteration, not merely tested examples. -/
theorem iteration_sound (n : Nat) : Invariant (iterate (searchStep execute) n initial).payload := by
  have preserve (s : SearchState Stack) (h : Invariant s.payload) :
      Invariant (searchStep execute s).payload := execute_sound _ _ h
  have all (n : Nat) (s : SearchState Stack) (h : Invariant s.payload) :
      Invariant (iterate (searchStep execute) n s).payload := by
    induction n generalizing s with
    | zero => exact h
    | succ n ih => exact ih _ (preserve s h)
  exact all n initial ⟨Provable.moot, good_zero⟩

/-- The numeric source enumerator finds its target exactly when that target has
a derivation in the explicitly defined current source calculus. This theorem
does not assert that the 308-state tape machine implements the enumerator. -/
theorem enumerator_correct : FindsTarget ↔ Provable 1 := by
  constructor
  · rintro ⟨n, hn⟩
    have h := (iteration_sound (n + 1)).1
    rwa [hn] at h
  · intro h
    obtain ⟨xs, hn, hx⟩ := compile h
    cases xs with
    | nil => exact False.elim (hn rfl)
    | cons i xs =>
      obtain ⟨n, he⟩ := every_program_runs execute (0, 0) i xs
      have hh := congrArg Prod.fst he
      rw [hx] at hh
      exact ⟨n + xs.length, by simpa [initial, Nat.add_assoc] using hh⟩

end TinyZF.Source
