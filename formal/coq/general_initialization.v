(** Completeness from any finite enumerator state, and exact equivalence from
    a clean formula stack. Padding the encoded halting program avoids a finite
    initial segment of candidate numbers. No finite-prefix restriction remains. *)
From Coq Require Import Arith Lia Lists.List.
From M254L Require Import Codes254 Enum254 Thm254 L1_Comp254 L1_Sound254.
Import ListNotations.

(** Concatenate a finite execution prefix with a halting execution. This is
    the transport step used when reaching a later candidate number. *)
Lemma lift_halts n s t : run n s = Some t -> halts_from t -> halts_from s.
Proof.
  intros E [k [u [R H]]]. exists (n+k), u. split; [|exact H].
  rewrite run_add, E. exact R.
Qed.

(** Every candidate at or above the current counter is eventually reached,
    unless execution halts first. The induction drains the current proof list
    before advancing the counter, so the initial proof list may be arbitrary. *)
Lemma reach_offset d s : halts_from s \/ exists n t,
  run n s = Some t /\ pl t = 0 /\ np t = np s + d.
Proof.
  induction d as [|d [Hh|[n [t [R [P0 N0]]]]]].
  - destruct (drain (pl s) s (le_n _)) as [H|[n [t [R [P0 N0]]]]].
    + now left.
    + right. exists n,t. repeat split; auto; lia.
  - now left.
  - destruct (enum_step t) as [u|] eqn:E.
    + pose proof (step_pl t u E) as [HP HN]. rewrite P0 in HP,HN. cbn in HP,HN.
      destruct (drain (pl u) u (le_n _)) as [Hh|[k [v [R2 [P2 N2]]]]].
      * left. apply (lift_halts n s t R). apply (halts_from_step t u E Hh).
      * right. exists (n+S k),v. split.
        -- rewrite run_add,R. cbn. now rewrite E.
        -- split; [exact P2|lia].
    + left. exists n,t. now split.
Qed.

(** Encoding more command fields never decreases the numeric tail. *)
Lemma fields_ge_r fs r : r <= enc_fields fs r.
Proof.
  induction fs as [|x fs IH]; [reflexivity|].
  cbn [enc_fields fold_right]. eapply Nat.le_trans; [exact IH|apply P_ge_r].
Qed.

(** A command-list code is at least its length. Appending inert commands after
    an already halting prefix therefore produces arbitrarily large codes. *)
Lemma tail_ge_length L : length L <= enc_tail L.
Proof.
  induction L as [|k L IH]; [reflexivity|].
  cbn [length enc_tail]. pose proof (fields_ge_r (fields k) (enc_tail L)). lia.
Qed.

(** A derivation of contradiction gives a program that halts from every
    retained register state. Pad its unused suffix beyond the initial counter,
    then use reach_offset and the pinned compiler-completeness theorem. *)
Theorem complete_from_any s : thm254 1 -> halts_from s.
Proof.
  intro H. destruct (compile 1 H) as [L HL].
  set (rest := (L ++ SUFFIX) ++ repeat CNIP (np s)).
  set (N := enc_fields (fields START) (enc_tail rest)).
  assert (HN : np s <= N).
  { unfold N. eapply Nat.le_trans; [|apply fields_ge_r].
    eapply Nat.le_trans; [|apply tail_ge_length].
    unfold rest. rewrite !length_app,repeat_length. lia. }
  destruct (reach_offset (N-np s) s) as [Hh|[n [t [R [P0 N0]]]]]; [exact Hh|].
  apply (lift_halts n s t R). apply (run_first START rest t P0); [lia|].
  change (exec ((START :: L ++ SUFFIX) ++ repeat CNIP (np s)) (tupof t) = None).
  rewrite exec_app, (program_halts L HL (tupof t)). reflexivity.
Qed.

(** Combine universal completeness with the pinned soundness invariant:
    the current formula, cached formula and stack entries are all theorems. *)
Theorem good_state_halts_iff s : Inv s -> (halts_from s <-> thm254 1).
Proof.
  intro H. split.
  - intros [n [t [R E]]]. apply (halt_step t); [eapply Inv_run; eauto|exact E].
  - apply complete_from_any.
Qed.

(** Search entry point: zero current formula, cache and stack satisfy Inv.
    The proof-list value, candidate counter and additive parameter are arbitrary.
    A machine using this lemma still needs its exact tape-to-source proof. *)
Theorem clean_state_halts_iff pl0 np0 d0 :
  halts_from (mkState pl0 np0 0 0 d0 0) <-> thm254 1.
Proof.
  apply good_state_halts_iff. split; [constructor|].
  split; [constructor|apply good_0].
Qed.
Print Assumptions clean_state_halts_iff.
