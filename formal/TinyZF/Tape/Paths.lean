import TinyZF.Tape.Control

/-! # Instruction paths through the literal transition table

A path certificate records the finite sequence of rightward dispatcher edges
leading to an instruction. Every edge is checked against the literal table.
This interface lets a finite control-flow certificate use shared DAG nodes
without assuming the Python compiler is correct.
-/
namespace TinyZF.Tape.Framework

/-- The abstract operations implemented by dispatcher leaves. -/
inductive Operation where
  | reg (decrement : Bool) (register : Fin 10)
  | breakOp (levels : Fin 3)
  | continueOp (levels : Fin 5)
  | halt
  deriving DecidableEq

/-- Literal final edge for an instruction. Break, continue and halt occur on
 right branches in this candidate. The instruction graph must certify this. -/
def leafEdge : Operation → Bool → Option (Transition 308)
  | .reg d r, b => some ⟨b, true, some (regState d r.val)⟩
  | .breakOp k, true => some ⟨false, false, some (breakState k.val)⟩
  | .continueOp k, true => some ⟨false, false, some (continueState (k.val-1))⟩
  | .halt, true => some ⟨true, true, none⟩
  | _, false => none

/-- A path certificate ends at the given instruction edge. Interior edges
 preserve their bit and move right. The initial state is the literal DAG root. -/
inductive Path : Fin 308 → List Bool → Operation → Prop where
  | leaf (q : Fin 308) (b : Bool) (op : Operation)
      (present : (leafEdge op b).isSome = true)
      (edge : m q b = leafEdge op b) : Path q [b] op
  | node (q q' : Fin 308) (b : Bool) (P : List Bool) (op : Operation)
      (edge : m q b = some ⟨b, true, some q'⟩)
      (rest : Path q' P op) : Path q (b :: P) op

/-- An instruction path consumes at least one cell. -/
theorem Path.nonempty {q P op} (h : Path q P op) : P ≠ [] := by cases h <;> simp

/-- Executing a certified register path reaches precisely its physical address
 chain, with the consumed path preserved to the left of the head. -/
theorem Path.to_register {q P d r} (h : Path q P (.reg d r)) (L Y : List Bool) :
    Progress m (zc q L (P ++ Y))
      (zc (regState d r.val) (P.reverse ++ L) Y) := by
  generalize he : Operation.reg d r = op at h
  induction h generalizing L with
  | leaf q b op present edge =>
    subst op
    apply Progress.prepend (moveR _ _ _ _ _ _ edge)
    exact Exec.refl _ _
  | node q q' b P op edge rest ih =>
    apply Progress.prepend (moveR _ _ _ _ _ _ edge)
    convert (ih (b :: L) he).exec using 1 <;> first | rfl |
      simp only [List.append_eq, List.reverse_cons, List.append_assoc,
        List.cons_append, List.nil_append]

/-- A non-register path ends in a one bit; its final transition can be executed
 with arbitrary tape after the instruction. The prefix walk is explicit. -/
theorem Path.to_right_leaf {q P op} (h : Path q P op)
    (hreg : ∀ d r, op ≠ .reg d r) (L Y : List Bool) :
    ∃ pre q', P = pre ++ [true] ∧ m q' true = leafEdge op true ∧
      Exec m (zc q L (P ++ Y)) (zc q' (pre.reverse ++ L) (true :: Y)) := by
  induction h generalizing L with
  | leaf q b op present edge =>
    cases op <;> cases b <;> simp only [leafEdge, Option.isSome_none, Bool.false_eq_true] at present
    · exact False.elim (hreg _ _ rfl)
    · exact False.elim (hreg _ _ rfl)
    all_goals exact ⟨[], q, rfl, edge, Exec.refl _ _⟩
  | node q q' b P op edge rest ih =>
    obtain ⟨pre, last, hp, he, hx⟩ := ih hreg (b :: L)
    refine ⟨b :: pre, last, by rw [hp]; rfl, he, ?_⟩
    apply Exec.prepend (moveR _ _ _ _ _ _ edge)
    convert hx using 1 <;> first | rfl |
      simp only [List.append_eq, List.reverse_cons, List.append_assoc,
        List.cons_append, List.nil_append]

/-- Halting remains stable in the head-relative representation. -/
theorem halted_step (z : Zipper 308) (h : z.state = none) : step m z = z := by
  simp [step, h]

/-- A certified halt path reaches a halted literal configuration. -/
theorem Path.to_halt {q P} (h : Path q P .halt) (L Y : List Bool) :
    ∃ z, Progress m (zc q L (P ++ Y)) z ∧ z.state = none := by
  obtain ⟨pre, last, _, edge, hx⟩ := h.to_right_leaf (by intro d r h; cases h) L Y
  refine ⟨⟨none, cons true (pref (pre.reverse ++ L) blanks), pref Y blanks⟩, ?_, rfl⟩
  apply Exec.trans_progress hx
  apply Progress.prepend (b := ⟨none, cons true (pref (pre.reverse ++ L) blanks), pref Y blanks⟩)
  · simp only [step, zc, pref, List.foldr_cons, cons, leafEdge] at edge ⊢
    rw [edge]; rfl
  · exact Exec.refl _ _

/-- A certified break path performs the encoded ancestor jump. The inequality
 accounts for all erased path cells becoming reusable gap cells. -/
theorem Path.to_break {q P} (k : Fin 3) (h : Path q P (.breakOp k))
    (hk : 0 < k.val) (hnz : nz 0 P.reverse) (Y : List Bool) :
    ∃ g, Progress m (zc q [true] (P ++ Y))
      (zc root [true] ((incRev (stripRev false k.val P.reverse)).reverse ++ zeros g ++ Y)) ∧
      P.length ≤ (stripRev false k.val P.reverse).length + g := by
  obtain ⟨pre, last, hp, edge, hx⟩ := h.to_right_leaf (by intro d r h; cases h) [true] Y
  have hnz' : nz 0 pre.reverse := by simpa [hp, List.reverse_append, nz] using hnz
  obtain ⟨g, hg, hlen⟩ := break_ip pre.reverse k.val (false :: Y) (by omega) hnz'
  have hstrip : stripRev false k.val P.reverse = stripRev false k.val pre.reverse := by
    cases hv : k.val with
    | zero => omega
    | succ j => simp [hp, List.reverse_append, stripRev, hv]
  rw [hstrip]
  refine ⟨g+1, ?_, ?_⟩
  · apply Exec.trans_progress hx
    apply Progress.prepend (moveL _ _ _ _ _ _ edge)
    convert hg.exec using 1 <;> first | rfl |
      simp [hp, List.reverse_append, stripRev, show k.val ≠ 0 by omega,
        List.append_assoc, List.replicate_succ, replicate_comm]
  · have hlen' : P.length = pre.length + 1 := by simp [hp]
    simp only [List.length_reverse] at hlen
    omega

/-- A certified continue path returns to its selected loop ancestor. The
 count condition prevents erasing the initial tape marker. -/
theorem Path.to_continue {q P} (k : Fin 5) (h : Path q P (.continueOp k))
    (hk : 0 < k.val) (hnz : nz 0 P.reverse) (hc : k.val ≤ P.count true)
    (Y : List Bool) :
    ∃ g, Progress m (zc q [true] (P ++ Y))
      (zc root [true] ((stripRev true k.val P.reverse).reverse ++ zeros g ++ Y)) ∧
      P.length ≤ (stripRev true k.val P.reverse).length + g := by
  obtain ⟨pre, last, hp, edge, hx⟩ := h.to_right_leaf (by intro d r h; cases h) [true] Y
  have hnz' : nz 0 pre.reverse := by simpa [hp, List.reverse_append, nz] using hnz
  have hc' : k.val - 1 ≤ pre.reverse.count true := by
    simp [hp] at hc
    simp only [List.count_reverse]
    omega
  obtain ⟨g, hg, hlen⟩ := continue_ip pre.reverse (k.val-1) (false :: Y) (by omega) hnz' hc'
  have hstrip : stripRev true k.val P.reverse = stripRev true (k.val-1) pre.reverse := by
    cases hv : k.val with
    | zero => omega
    | succ j => simp [hp, List.reverse_append, stripRev, hv]
  rw [hstrip]
  refine ⟨g+1, ?_, ?_⟩
  · apply Exec.trans_progress hx
    apply Progress.prepend (moveL _ _ _ _ _ _ edge)
    convert hg.exec using 1 <;> first | rfl |
      simp [List.append_assoc, List.replicate_succ, replicate_comm]
  · have hlen' : P.length = pre.length + 1 := by simp [hp]
    simp only [List.length_reverse] at hlen
    omega

/-- A small executable checker for instruction paths. Its input can be
 produced by any tool; soundness checks the literal table, not that tool. -/
def checkPath (q : Fin 308) (P : List Bool) (op : Operation) : Bool :=
  match P with
  | [] => false
  | [b] => (leafEdge op b).isSome && decide (Machine308.fastLookup q b = leafEdge op b)
  | b :: c :: U => match Machine308.fastLookup q b with
    | some ⟨w, true, some q'⟩ => (w == b) && checkPath q' (c :: U) op
    | _ => false

/-- Passing the finite checker supplies an unbounded tape-execution contract
 through `Path`, valid for arbitrary data after the path. -/
theorem checkPath_sound (q : Fin 308) (P : List Bool) (op : Operation)
    (h : checkPath q P op = true) : Path q P op := by
  induction P generalizing q with
  | nil => simp [checkPath] at h
  | cons b P ih =>
    cases P with
    | nil =>
      simp only [checkPath, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .leaf q b op h.1 (by simpa only [Machine308.fastLookup_eq_machine] using h.2)
    | cons c U =>
      unfold checkPath at h
      split at h <;> try contradiction
      rename_i w q' edge
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨rfl, hrest⟩
      exact .node q q' _ (c :: U) op
        (by simpa only [Machine308.fastLookup_eq_machine] using edge) (ih q' hrest)

end TinyZF.Tape.Framework
