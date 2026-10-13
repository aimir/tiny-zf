import TinyZF.Machine
import TinyZF.Enumeration

/-! # Exact tape views and finite executions

This file connects a convenient head-relative tape view to the literal,
integer-indexed semantics. Finite lists are extended by infinitely many blank
cells; no bound on either tape length or running time is introduced.
-/
namespace TinyZF.Tape

abbrev Stream := Nat → Bool

def cons (b : Bool) (s : Stream) : Stream
  | 0 => b
  | n + 1 => s n

def tail (s : Stream) : Stream := fun n => s (n + 1)
def pref (l : List Bool) (s : Stream) : Stream := l.foldr cons s
def blanks : Stream := fun _ => false

/-- Prefixes compose in tape order. -/
@[simp] theorem pref_append (a b : List Bool) (s : Stream) :
    pref (a ++ b) s = pref a (pref b s) := by simp [pref, List.foldr_append]

/-- A stream is determined by its first cell and tail. -/
@[simp] theorem cons_tail (s : Stream) : cons (s 0) (tail s) = s := by
  funext n; cases n <;> rfl

/-- Adding a blank before an infinite blank suffix has no effect. -/
@[simp] theorem cons_blanks : cons false blanks = blanks := by
  funext n; cases n <;> rfl

/-- A finite blank suffix is absorbed into the infinite blank tape. -/
@[simp] theorem pref_blanks (n : Nat) : pref (List.replicate n false) blanks = blanks := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cons false (pref (List.replicate n false) blanks) = blanks
    rw [ih, cons_blanks]

/-- Left cells are nearest first; the right stream includes the scanned cell. -/
@[ext] structure Zipper (n : Nat) where
  state : Option (Fin n)
  left : Stream
  right : Stream

def step {n} (m : Machine n) (z : Zipper n) : Zipper n :=
  match z.state with
  | none => z
  | some q =>
    match m q (z.right 0) with
    | none => { z with state := none }
    | some t =>
      if t.right then ⟨t.next, cons t.write z.left, tail z.right⟩
      else ⟨t.next, tail z.left, cons (z.left 0) (cons t.write (tail z.right))⟩

def ofConfiguration {n} (c : Configuration n) : Zipper n :=
  ⟨c.state, fun k => c.tape (c.head - (k + 1)), fun k => c.tape (c.head + k)⟩

/-- Head-relative and absolute tapes perform exactly the same single step,
including the two kinds of halting transition. -/
theorem ofConfiguration_step {n} (m : Machine n) (c : Configuration n) :
    ofConfiguration (m.step c) = step m (ofConfiguration c) := by
  cases hs : c.state with
  | none => simp [Machine.step, step, ofConfiguration, hs]
  | some q =>
    cases ht : m q (c.tape c.head) with
    | none => simp [Machine.step, step, ofConfiguration, hs, ht]
    | some t =>
      cases hd : t.right
      · apply Zipper.ext
        · simp [ofConfiguration, Machine.step, step, hs, ht, hd]
        · funext k
          simp only [ofConfiguration, Machine.step, step, hs, Nat.cast_zero, Int.add_zero,
            ht, hd, Bool.false_eq_true, ↓reduceIte, tail]
          have h : c.head + -1 - (k + 1 : Int) ≠ c.head := by omega
          simp only [Function.update_of_ne h]
          congr 1; omega
        · funext k
          cases k with
          | zero =>
            simp [ofConfiguration, Machine.step, step, hs, ht, hd, cons,
              show c.head + -1 ≠ c.head by omega, sub_eq_add_neg]
          | succ k =>
            cases k with
            | zero => simp [ofConfiguration, Machine.step, step, hs, ht, hd, cons]
            | succ k =>
              simp only [ofConfiguration, Machine.step, step, hs, Nat.cast_zero, Int.add_zero,
                ht, hd, Bool.false_eq_true, ↓reduceIte, cons, tail]
              have h : c.head + -1 + (k + 1 + 1 : Nat) ≠ c.head := by omega
              simp only [Function.update_of_ne h]
              congr 1; omega
      · apply Zipper.ext
        · simp [ofConfiguration, Machine.step, step, hs, ht, hd]
        · funext k
          cases k with
          | zero => simp [ofConfiguration, Machine.step, step, hs, ht, hd, cons]
          | succ k =>
            simp only [ofConfiguration, Machine.step, step, hs, Nat.cast_zero, Int.add_zero,
              ht, hd, ↓reduceIte, cons]
            have h : c.head + 1 - ((k + 1 : Nat) + 1 : Int) ≠ c.head := by omega
            simp only [Function.update_of_ne h]
            congr 1; omega
        · funext k
          simp only [ofConfiguration, Machine.step, step, hs, Nat.cast_zero, Int.add_zero,
            ht, hd, ↓reduceIte, tail]
          have h : c.head + 1 + (k : Int) ≠ c.head := by omega
          simp only [Function.update_of_ne h]
          congr 1; omega

/-- The change of tape coordinates commutes with every finite execution. -/
theorem ofConfiguration_run {n} (m : Machine n) (k : Nat) (c : Configuration n) :
    ofConfiguration (m.run k c) = iterate (step m) k (ofConfiguration c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih => rw [Machine.run, ih, ofConfiguration_step]; rfl

/-- Consequently halting in the convenient view is exactly literal halting. -/
theorem halts_iff {n} (m : Machine n) (c : Configuration n) :
    m.halts c ↔ ∃ k, (iterate (step m) k (ofConfiguration c)).state = none := by
  unfold Machine.halts
  apply exists_congr
  intro k
  rw [← ofConfiguration_run]
  rfl

/-- An arbitrary finite execution, used to compose scans and primitive routines. -/
def Exec {n} (m : Machine n) (a b : Zipper n) : Prop := ∃ k, iterate (step m) k a = b

/-- A finite execution that consumes at least one step. Progress is needed to
exclude a spurious implementation halt between abstract simulation boundaries. -/
def Progress {n} (m : Machine n) (a b : Zipper n) : Prop :=
  ∃ k, 0 < k ∧ iterate (step m) k a = b

/-- Zero steps preserve a configuration. -/
theorem Exec.refl {n} (m : Machine n) (a : Zipper n) : Exec m a a := ⟨0, rfl⟩

/-- Finite executions compose by addition of their lengths. -/
theorem Exec.trans {n} {m : Machine n} {a b c : Zipper n}
    (h : Exec m a b) (j : Exec m b c) : Exec m a c := by
  obtain ⟨k, hk⟩ := h; obtain ⟨l, hl⟩ := j
  exact ⟨k + l, by rw [iterate_add, hk, hl]⟩

/-- A progressing execution is in particular finite. -/
theorem Progress.exec {n} {m : Machine n} {a b : Zipper n}
    (h : Progress m a b) : Exec m a b := by obtain ⟨k, _, hk⟩ := h; exact ⟨k, hk⟩

/-- A checked first transition establishes progress, followed by any finite tail. -/
theorem Progress.prepend {n} {m : Machine n} {a b c : Zipper n}
    (h : step m a = b) (j : Exec m b c) : Progress m a c := by
  obtain ⟨k, hk⟩ := j
  exact ⟨k + 1, by omega, by simpa only [iterate, h] using hk⟩

/-- Prefix a finite execution by one checked transition. -/
theorem Exec.prepend {n} {m : Machine n} {a b c : Zipper n}
    (h : step m a = b) (j : Exec m b c) : Exec m a c := (Progress.prepend h j).exec

/-- Progress is retained when a finite execution is appended. -/
theorem Progress.trans_exec {n} {m : Machine n} {a b c : Zipper n}
    (h : Progress m a b) (j : Exec m b c) : Progress m a c := by
  obtain ⟨k, hp, hk⟩ := h; obtain ⟨l, hl⟩ := j
  exact ⟨k + l, by omega, by rw [iterate_add, hk, hl]⟩

/-- Progress is retained when a finite execution is prepended. -/
theorem Exec.trans_progress {n} {m : Machine n} {a b c : Zipper n}
    (h : Exec m a b) (j : Progress m b c) : Progress m a c := by
  obtain ⟨k, hk⟩ := h; obtain ⟨l, hp, hl⟩ := j
  exact ⟨k + l, by omega, by rw [iterate_add, hk, hl]⟩

/-- Two progressing routines compose. -/
theorem Progress.trans {n} {m : Machine n} {a b c : Zipper n}
    (h : Progress m a b) (j : Progress m b c) : Progress m a c := h.trans_exec j.exec

/-- Finite tape prefes with infinite blank suffixes. -/
def zc {n} (q : Fin n) (l r : List Bool) : Zipper n :=
  ⟨some q, pref l blanks, pref r blanks⟩

/-- The same split with the head on the left side's leading cell. -/
def zl {n} (q : Fin n) (l r : List Bool) : Zipper n :=
  ⟨some q, tail (pref l blanks), cons (pref l blanks 0) (pref r blanks)⟩

/-- Moving the split left exposes the last written cell. -/
@[simp] theorem zl_cons {n} (q : Fin n) (b : Bool) (l r : List Bool) :
    zl q (b :: l) r = zc q l (b :: r) := rfl

/-- To the left of a finite tape pref the next cell is blank. -/
@[simp] theorem zl_nil {n} (q : Fin n) (r : List Bool) :
    zl q [] r = zc q [] (false :: r) := rfl

/-- Explicit blank padding on the left has no effect. -/
@[simp] theorem zc_padl {n} (q : Fin n) (l r : List Bool) (k : Nat) :
    zc q (l ++ List.replicate k false) r = zc q l r := by simp [zc]

/-- Explicit blank padding on the right has no effect. -/
@[simp] theorem zc_padr {n} (q : Fin n) (l r : List Bool) (k : Nat) :
    zc q l (r ++ List.replicate k false) = zc q l r := by simp [zc]

/-- Blank padding also has no effect when the head faces the left pref. -/
@[simp] theorem zl_padr {n} (q : Fin n) (l r : List Bool) (k : Nat) :
    zl q l (r ++ List.replicate k false) = zl q l r := by simp [zl]

/-- A right-moving table entry acts on arbitrary surrounding tape prefes. -/
theorem moveR {n} {m : Machine n} (q q' : Fin n) (b w : Bool) (l r : List Bool)
    (h : m q b = some ⟨w, true, some q'⟩) :
    step m (zc q l (b :: r)) = zc q' (w :: l) r := by
  simp only [step, zc, pref, List.foldr_cons, cons, h, ↓reduceIte]; rfl

/-- A left-moving table entry acts on arbitrary surrounding tape prefes. -/
theorem moveL {n} {m : Machine n} (q q' : Fin n) (b w : Bool) (l r : List Bool)
    (h : m q b = some ⟨w, false, some q'⟩) :
    step m (zc q l (b :: r)) = zl q' l (w :: r) := by
  simp only [step, zc, zl, pref, List.foldr_cons, cons, h, Bool.false_eq_true, ↓reduceIte]; rfl

/-- Identical cells may be placed on either end of their own run. -/
theorem replicate_comm (b : Bool) (k : Nat) (l : List Bool) :
    List.replicate k b ++ b :: l = b :: List.replicate k b ++ l := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] using ih

/-- A self-loop scans an arbitrary finite run to the right. -/
theorem scanR {n} {m : Machine n} (q : Fin n) (b : Bool) (k : Nat) (l r : List Bool)
    (h : m q b = some ⟨b, true, some q⟩) :
    Exec m (zc q l (List.replicate k b ++ r)) (zc q (List.replicate k b ++ l) r) := by
  induction k generalizing l with
  | zero => exact .refl _ _
  | succ k ih =>
    apply Exec.prepend (moveR q q b b l _ h)
    convert ih (b :: l) using 1 <;> simp [List.replicate_succ, replicate_comm]

/-- A self-loop scans an arbitrary finite run to the left. -/
theorem scanL {n} {m : Machine n} (q : Fin n) (b : Bool) (k : Nat) (l r : List Bool)
    (h : m q b = some ⟨b, false, some q⟩) :
    Exec m (zl q (List.replicate k b ++ l) r) (zl q l (List.replicate k b ++ r)) := by
  induction k generalizing r with
  | zero => exact .refl _ _
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, zl_cons]
    apply Exec.prepend (moveL q q b b _ r h)
    convert ih (b :: r) using 1 <;> simp [List.replicate_succ, replicate_comm]

/-- A finite description of a tape with blank tails. This is used only for
 certifying the fixed bootstrap; the simulation itself uses unbounded streams. -/
structure Snapshot (n : Nat) where
  state : Option (Fin n)
  left : List Bool
  right : List Bool
  deriving DecidableEq

/-- Interpret a finite snapshot as an infinite tape. -/
def Snapshot.view {n} (s : Snapshot n) : Zipper n :=
  ⟨s.state, pref s.left blanks, pref s.right blanks⟩

/-- A computable presentation of the same literal step. Empty lists read blank. -/
def Snapshot.step {n} (m : Machine n) (s : Snapshot n) : Snapshot n :=
  match s.state with
  | none => s
  | some q =>
    match m q (s.right.headD false) with
    | none => { s with state := none }
    | some t => if t.right then ⟨t.next, t.write :: s.left, s.right.tail⟩
      else ⟨t.next, s.left.tail, s.left.headD false :: t.write :: s.right.tail⟩

/-- Finite snapshots step exactly as their infinite-tape interpretations. -/
theorem Snapshot.view_step {n} (m : Machine n) (s : Snapshot n) :
    (s.step m).view = Tape.step m s.view := by
  obtain ⟨q, l, r⟩ := s
  cases q with
  | none => rfl
  | some q =>
    cases l <;> cases r <;>
      simp only [Snapshot.step, Snapshot.view, List.headD, List.head?, List.tail,
        Option.getD, pref, List.foldr_nil, List.foldr_cons, Tape.step, cons, blanks]
    all_goals split
    all_goals first | rfl | (split <;> rfl)

/-- Snapshot evaluation remains sound for arbitrarily many steps. -/
theorem Snapshot.view_run {n} (m : Machine n) (k : Nat) (s : Snapshot n) :
    (iterate (Snapshot.step m) k s).view = iterate (Tape.step m) k s.view := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [iterate, ih, Snapshot.view_step]; rfl

/-- Force the finite configuration constructor at every step. This computes
 the same run while avoiding repeated projections through unevaluated runs
 during kernel reduction of long finite certificates. -/
def Snapshot.run {n} (m : Machine n) : Nat → Snapshot n → Snapshot n
  | 0, s => s
  | k+1, ⟨none, l, r⟩ => Snapshot.run m k ⟨none, l, r⟩
  | k+1, ⟨some q, l, r⟩ =>
    match m q (r.headD false) with
    | none => Snapshot.run m k ⟨none, l, r⟩
    | some t => if t.right then Snapshot.run m k ⟨t.next, t.write :: l, r.tail⟩
      else Snapshot.run m k ⟨t.next, l.tail, l.headD false :: t.write :: r.tail⟩

/-- The efficient certificate evaluator is definitionally faithful to the
 finite step function at each stage, hence computes exactly its iteration. -/
theorem Snapshot.run_eq_iterate {n} (m : Machine n) (k : Nat) (s : Snapshot n) :
    Snapshot.run m k s = iterate (Snapshot.step m) k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    obtain ⟨q, l, r⟩ := s
    cases q with
    | none => exact ih _
    | some q =>
      simp only [Snapshot.run, iterate, Snapshot.step]
      split
      · exact ih _
      · split <;> exact ih _

/-- Endpoint of a finite list of proposed execution checkpoints. -/
def traceEnd {n} (s : Snapshot n) : List (Nat × Snapshot n) → Snapshot n
  | [] => s
  | (_, t) :: rest => traceEnd t rest

/-- Check every proposed segment with the literal machine. Checkpoints keep
 reduction depth small, and are evidence only after this check is proved true. -/
def checkTrace {n} (m : Machine n) (s : Snapshot n) : List (Nat × Snapshot n) → Bool
  | [] => true
  | (k, t) :: rest => decide (Snapshot.run m k s = t) && checkTrace m t rest

/-- A successful checkpoint check entails an actual finite tape execution.
 In particular, an untrusted generator cannot invent intermediate snapshots. -/
theorem checkTrace_sound {n} (m : Machine n) (s : Snapshot n) (trace : List (Nat × Snapshot n))
    (h : checkTrace m s trace = true) : Exec m s.view (traceEnd s trace).view := by
  induction trace generalizing s with
  | nil => exact Exec.refl _ _
  | cons entry rest ih =>
    obtain ⟨k, t⟩ := entry
    simp only [checkTrace, Bool.and_eq_true, decide_eq_true_eq] at h
    apply Exec.trans (b := t.view) _ (ih t h.2)
    exact ⟨k, by rw [← Snapshot.view_run, ← Snapshot.run_eq_iterate, h.1]⟩

end TinyZF.Tape
