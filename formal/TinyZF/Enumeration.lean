import TinyZF.Cantor

/-! # Exact proof-field coding and exhaustive enumeration

The 308-state candidate decodes fields in the order `param1,param3,param2,axiomcode`.
The control lemmas below hold for every instruction interpreter and every payload:
the enumeration mechanism cannot omit a finite instruction sequence. It is not
assumed that the binary tape implements this mechanism; that is a separate goal.
-/

namespace TinyZF
open Cantor

/-- One proof instruction, with semantic names independent of its wire order. -/
structure Instruction where
  selector : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  deriving DecidableEq, Repr

/-- The candidate's four nested pairs, in its actual allocation order. -/
def encodeInstruction (i : Instruction) (tail : Nat) : Nat :=
  pair i.p1 (pair i.p3 (pair i.p2 (pair i.selector tail)))

/-- Decode exactly four fields; the remaining tail belongs to later instructions. -/
def decodeInstruction (n : Nat) : Instruction × Nat :=
  let a := unpair n
  let b := unpair a.2
  let c := unpair b.2
  let d := unpair c.2
  (⟨d.1, a.1, c.1, b.1⟩, d.2)

/-- Reordering the proof fields loses no instruction or tail. -/
@[simp] theorem decode_encode (i : Instruction) (tail : Nat) :
    decodeInstruction (encodeInstruction i tail) = (i, tail) := by
  cases i
  simp [decodeInstruction, encodeInstruction]

/-- Every number has a unique decomposition into the four fields and a tail. -/
@[simp] theorem encode_decode (n : Nat) :
    encodeInstruction (decodeInstruction n).1 (decodeInstruction n).2 = n := by
  simp [decodeInstruction, encodeInstruction]

/-- The remainder after four splits never exceeds the input. -/
theorem decode_tail_le (n : Nat) : (decodeInstruction n).2 ≤ n := by
  have h1 := (unpair_le n).2
  have h2 := (unpair_le (unpair n).2).2
  have h3 := (unpair_le (unpair (unpair n).2).2).2
  have h4 := (unpair_le (unpair (unpair (unpair n).2).2).2).2
  exact le_trans h4 (le_trans h3 (le_trans h2 h1))

/-- The pair of proof-control registers and an arbitrary interpreter payload. -/
structure SearchState (α : Type) where
  remaining : Nat
  next : Nat
  payload : α

/-- A zero tail reloads the next integer; a positive tail is decremented first. -/
def searchStep {α : Type} (execute : Instruction → α → α) (s : SearchState α) : SearchState α :=
  let input := if s.remaining = 0 then s.next else s.remaining - 1
  let parts := decodeInstruction input
  ⟨parts.2, if s.remaining = 0 then s.next + 1 else s.next,
    execute parts.1 s.payload⟩

/-- Iteration is total: halting is observed separately as an event. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, s => s
  | n + 1, s => iterate f n (f s)

/-- Iterations concatenate, which lets the completeness proof join search phases. -/
theorem iterate_add {α : Type} (f : α → α) (n m : Nat) (s : α) :
    iterate f (n + m) s = iterate f m (iterate f n s) := by
  induction n generalizing s with
  | zero => simp [iterate]
  | succ n ih => simpa [iterate, Nat.succ_add] using ih (f s)

/-- A finite positive proof tail always drains, regardless of interpreter behavior. -/
theorem drain {α : Type} (execute : Instruction → α → α) (s : SearchState α) :
    ∃ n, (iterate (searchStep execute) n s).remaining = 0 ∧
      (iterate (searchStep execute) n s).next = s.next := by
  generalize h : s.remaining = k
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    by_cases hz : s.remaining = 0
    · exact ⟨0, hz, rfl⟩
    · have hn : (searchStep execute s).next = s.next := by simp [searchStep, hz]
      have hl : (searchStep execute s).remaining < k := by
        have hb := decode_tail_le (s.remaining - 1)
        simp only [searchStep, hz, ↓reduceIte]
        omega
      obtain ⟨n, he, hc⟩ := ih _ hl (searchStep execute s) rfl
      exact ⟨n + 1, he, hc.trans hn⟩

/-- From blank proof control, every natural number is eventually loaded. -/
theorem reach_counter {α : Type} (execute : Instruction → α → α) (initial : α) (m : Nat) :
    ∃ n, (iterate (searchStep execute) n ⟨0, 0, initial⟩).remaining = 0 ∧
      (iterate (searchStep execute) n ⟨0, 0, initial⟩).next = m := by
  induction m with
  | zero => exact ⟨0, rfl, rfl⟩
  | succ m ih =>
    obtain ⟨n, he, hc⟩ := ih
    let s := iterate (searchStep execute) n ⟨0, 0, initial⟩
    have hn : (searchStep execute s).next = m + 1 := by
      simp only [searchStep, show s.remaining = 0 from he, ↓reduceIte]
      exact congrArg (· + 1) hc
    obtain ⟨k, ht, hk⟩ := drain execute (searchStep execute s)
    refine ⟨n + (k + 1), ?_, ?_⟩
    · rw [iterate_add]; exact ht
    · rw [iterate_add]; exact hk.trans hn

/-- A stored continuation uses a positive tag so tail traversal strictly descends. -/
def encodeTail : List Instruction → Nat
  | [] => 0
  | i :: rest => encodeInstruction i (encodeTail rest) + 1

/-- Execute a finite instruction list without interpreting its numerical encoding. -/
def executeList {α : Type} (execute : Instruction → α → α) : List Instruction → α → α
  | [], s => s
  | i :: rest, s => executeList execute rest (execute i s)

/-- List execution composes in the expected order. -/
theorem executeList_append {α : Type} (execute : Instruction → α → α)
    (xs ys : List Instruction) (s : α) :
    executeList execute (xs ++ ys) s = executeList execute ys (executeList execute xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (execute x s)

/-- Decoding a stored continuation executes exactly that list and preserves the counter. -/
theorem run_tail {α : Type} (execute : Instruction → α → α) (xs : List Instruction)
    (s : SearchState α) (h : s.remaining = encodeTail xs) :
    iterate (searchStep execute) xs.length s =
      ⟨0, s.next, executeList execute xs s.payload⟩ := by
  induction xs generalizing s with
  | nil => cases s; simp_all [encodeTail, iterate, executeList]
  | cons i xs ih =>
    have hs : searchStep execute s =
        ⟨encodeTail xs, s.next, execute i s.payload⟩ := by
      simp [searchStep, h, encodeTail, decode_encode]
    simp only [List.length_cons, iterate, hs]
    exact ih _ rfl

/-- Reloading a coded proof executes its first instruction and the entire continuation. -/
theorem run_loaded {α : Type} (execute : Instruction → α → α) (i : Instruction)
    (xs : List Instruction) (s : SearchState α)
    (he : s.remaining = 0) (hc : s.next = encodeInstruction i (encodeTail xs)) :
    (iterate (searchStep execute) (xs.length + 1) s).payload =
      executeList execute (i :: xs) s.payload := by
  have hs : searchStep execute s =
      ⟨encodeTail xs, s.next + 1, execute i s.payload⟩ := by
    simp [searchStep, he, hc]
  rw [iterate, hs, run_tail execute xs ⟨encodeTail xs, s.next + 1, execute i s.payload⟩ rfl]
  rfl

/-- Every nonempty list runs from some reachable payload. This is the exhaustive-search
property needed after compiling a derivation into instructions that work on any stack. -/
theorem every_program_runs {α : Type} (execute : Instruction → α → α) (initial : α)
    (i : Instruction) (xs : List Instruction) :
    ∃ n, (iterate (searchStep execute) (n + (xs.length + 1)) ⟨0, 0, initial⟩).payload =
      executeList execute (i :: xs)
        (iterate (searchStep execute) n ⟨0, 0, initial⟩).payload := by
  obtain ⟨n, he, hc⟩ := reach_counter execute initial (encodeInstruction i (encodeTail xs))
  exact ⟨n, by rw [iterate_add]; exact run_loaded execute i xs _ he hc⟩

end TinyZF
