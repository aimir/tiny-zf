import TinyZF.Tape.Cycles

/-! # Unbounded simulation and halting

Instruction contracts consume a positive, finite number of literal machine
steps. This module turns such contracts into equivalence of halting for whole
runs. Positivity matters: samples then pass every finite tape time, so the tape
cannot halt unnoticed between two interpreter boundaries.
-/
namespace TinyZF.Tape

/-- Tail-recursive iteration also permits taking its final step last. -/
theorem iterate_succ_last {α : Type} (f : α → α) (n : Nat) (a : α) :
    iterate f (n+1) a = f (iterate f n a) := by
  simpa only [iterate] using iterate_add f n 1 a

/-- An absorbing predicate remains true after any further finite execution. -/
theorem absorbing_later {α : Type} (f : α → α) (halt : α → Prop)
    (absorbing : ∀ a, halt a → halt (f a)) (a : α) (n k : Nat)
    (hn : halt (iterate f n a)) (hle : n ≤ k) : halt (iterate f k a) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [iterate_add]
  induction j with
  | zero => exact hn
  | succ j ih => rw [iterate_succ_last]; exact absorbing _ (ih (by omega))

/-- A progressing simulation preserves and reflects unbounded halting.
 The relation may include register encodings, pointer-space bounds, and other
 invariants. Each abstract step must provide an actual positive tape run. -/
theorem halting_iff_of_simulation {α β : Type}
    (concrete : α → α) (abstract : β → β) (haltA : α → Prop) (haltB : β → Prop)
    (a₀ : α) (b₀ : β) (rel : α → β → Prop)
    (initial : rel a₀ b₀)
    (absorbing : ∀ a, haltA a → haltA (concrete a))
    (halts : ∀ a b, rel a b → (haltA a ↔ haltB b))
    (expand : ∀ a b, rel a b →
      ∃ k, 0 < k ∧ rel (iterate concrete k a) (abstract b)) :
    (∃ n, haltA (iterate concrete n a₀)) ↔
      ∃ n, haltB (iterate abstract n b₀) := by
  have samples : ∀ n, ∃ k, n ≤ k ∧
      rel (iterate concrete k a₀) (iterate abstract n b₀) := by
    intro n
    induction n with
    | zero => exact ⟨0, le_rfl, initial⟩
    | succ n ih =>
      obtain ⟨k, hnk, hr⟩ := ih
      obtain ⟨j, hj, hs⟩ := expand _ _ hr
      refine ⟨k+j, by omega, ?_⟩
      simpa only [iterate_add, iterate_succ_last] using hs
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨k, hnk, hr⟩ := samples n
    exact ⟨n, (halts _ _ hr).mp (absorbing_later concrete haltA absorbing a₀ n k hn hnk)⟩
  · rintro ⟨n, hn⟩
    obtain ⟨k, _, hr⟩ := samples n
    exact ⟨k, (halts _ _ hr).mpr hn⟩

/-- Once a literal head-relative machine halts, every later sample is halted. -/
theorem halted_absorbing {n} (m : Machine n) (z : Zipper n) (h : z.state = none) :
    (step m z).state = none := by simp [step, h]

/-- Removing a proved finite startup prefix does not change halting.
 This lets the bootstrap certificate precede an unbounded instruction proof. -/
theorem halts_iff_after_exec {n} {m : Machine n} {a b : Zipper n} (h : Exec m a b) :
    (∃ k, (iterate (step m) k a).state = none) ↔
      ∃ k, (iterate (step m) k b).state = none := by
  obtain ⟨j, hj⟩ := h
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hl := absorbing_later (step m) (fun z => z.state = none)
      (halted_absorbing m) a k (j+k) hk (by omega)
    simpa only [iterate_add, hj] using hl
  · rintro ⟨k, hk⟩
    exact ⟨j+k, by simpa only [iterate_add, hj] using hk⟩

end TinyZF.Tape
