(** * Protected startup: the literal 250-state machine implements contradiction search

    Headline [tm250_thm]: [halts tm c0 <-> thm254 1]. The left side is the
    exact blank binary-tape machine; the right side is the pinned source
    calculus deriving contradiction. The end-to-end module transports this
    result to the conventional ZF, ZFC and SIR statements already proved
    upstream, without changing those mathematical bridges.

    Proof flow: finite RM prefixes; transport at an arbitrary bisimulation
    entry; a closed structured AX suffix; return to enumeration at candidate
    zero; stack protection. The suffix constructs an enormous stack, whose
    exact value is irrelevant because the initial tail is never popped.
    Boot, Sim and the instruction-site proofs establish the preceding literal
    tape-to-RM equivalence, including the exact inactive register tail. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia NArith.
From BusyCoq Require Import TM.
From M254 Require Import RM RMEquiv Prog254 TM254 Boot Sim Main.
From M254P Require Import Bisim Dag254 Cert254 Bisim254 ProgLib254 L2Root254.
From M254L Require Import Codes254 Enum254 Thm254 GeneralInit StackProtection.
Import ListNotations.
Opaque P.

(** ** Finite runs and entry transport *)
(** A configuration that takes an RM step is not a halt leaf. *)
Lemma rm_step_not_halt p c c' : rm_step p c = Some c' -> ~ at_halt p c.
Proof.
  destruct c as [P R]. intros E [d W]. unfold rm_step in E. cbn [fst] in W.
  rewrite W in E. discriminate.
Qed.

(** One actual nonhalting step preserves halting in both directions. *)
Lemma rm_step_halts_iff p c c' : rm_step p c = Some c' ->
  rm_halts p c <-> rm_halts p c'.
Proof.
  intros E. split.
  - intros ([|n] & z & Run & Halt).
    + injection Run as <-. exfalso. exact (rm_step_not_halt p c c' E Halt).
    + cbn [rm_run] in Run. rewrite E in Run. exists n,z. auto.
  - apply (halts_pre p 1 c c'). cbn [rm_run]. rewrite E. reflexivity.
Qed.

(** A checked finite RM prefix preserves halting, regardless of its length. *)
Lemma rm_run_halts_iff p n c c' : rm_run p n c = Some c' ->
  rm_halts p c <-> rm_halts p c'.
Proof.
  revert c. induction n as [|n IH]; intros c Run.
  - injection Run as <-. reflexivity.
  - cbn [rm_run] in Run. destruct (rm_step p c) as [c1|] eqn:E; [|discriminate].
    rewrite (rm_step_halts_iff p c c1 E). exact (IH c1 Run).
Qed.

(** Use the already checked bisimulation at any related test entry, with equal registers. *)
Lemma entry_one_way p1 p2 C
  (F : forallb (entry_ok (ptree p1) (ptree p2) C) C = true)
  P1 P2 j k R :
  In (P1,P2,j,k) C -> rm_halts p1 (P1,R) -> rm_halts p2 (P2,R).
Proof.
  intros Hi [n [c [Hr Ha]]].
  exact (Bisim.sim p1 p2 C F n P1 P2 j k R R Hi
    (fun i => @eq_refl nat (R i)) (ex_intro _ c (conj Hr Ha))).
Time Qed.

(** Extract the per-entry checks from the full certificate check. *)
Lemma check_entries p1 p2 C : check (ptree p1) (ptree p2) C = true ->
  forallb (entry_ok (ptree p1) (ptree p2) C) C = true.
Proof. unfold check. intro H. exact (proj2 (andb_prop _ _ H)). Time Qed.

(** Membership is preserved when swapping the programs and their two entry paths. *)
Lemma entry_mirror P1 P2 j k C :
  In (P1,P2,j,k) C -> In (P2,P1,j,k) (mirror C).
Proof.
  intro H. unfold mirror.
  exact (in_map (fun '(a,b,j,k) => (b,a,j,k)) C (P1,P2,j,k) H).
Time Qed.

(** The forward and mirrored certificates give halting equivalence at an arbitrary entry. *)
Lemma checked_entry_iff p1 p2 C
  (Forward : check (ptree p1) (ptree p2) C = true)
  (Backward : check (ptree p2) (ptree p1) (mirror C) = true)
  P1 P2 j k R :
  In (P1,P2,j,k) C -> rm_halts p1 (P1,R) <-> rm_halts p2 (P2,R).
Proof.
  intro Hi. split.
  - exact (entry_one_way p1 p2 C (check_entries p1 p2 C Forward) P1 P2 j k R Hi).
  - exact (entry_one_way p2 p1 (mirror C) (check_entries p2 p1 (mirror C) Backward)
      P2 P1 j k R (entry_mirror P1 P2 j k C Hi)).
Time Qed.
(** Specialize that general transport to the exact candidate and original source trees. *)
Lemma certificate_entry_iff P1 P2 j k R :
  In (P1,P2,j,k) cert254 ->
  rm_halts p254 (P1,R) <-> rm_halts dag254 (P2,R).
Proof. exact (checked_entry_iff p254 dag254 cert254 cert_fwd cert_bwd P1 P2 j k R). Qed.

Local Notation t := true.
Local Notation f := false.
(** Literal 29-bit program counter established by the binary-tape bootstrap. *)
Definition seed_pc : list bool := [t;t;t;f;t;f;f;t;f;f;t;f;t;f;f;f;t;f;f;f;f;t;t;f;t;t;f;t;t].
(** The first test PC reached after the two-step normalizing prefix. *)
Definition test_pc : list bool := [t;t;t;f;t;f;f;t;f;f;t;f;t;f;f;f;t;f;f;f;f;t;t;f;t;t;f;t].
(** Original 219-node source entry related to that test by certificate entry 148. *)
Definition source_pc : list bool := [t;t;t;f;t;f;f;t;f;f;t;f;t;t;f;f;t;t;f;t;t;f;t].

(** The boot entry takes an increment and a control step before the certified test site. *)
Lemma seed_two_steps R : rm_run p254 2 (seed_pc,R) =
  Some (test_pc,upd R 1 (S (R 1))).
Proof. vm_compute. reflexivity. Qed.

(** The exact test/source pair is entry 148 of the checked certificate. *)
Lemma seed_certificate_entry : In (test_pc,source_pc,148%N,3001%N) cert254.
Proof. apply nth_error_In with (n:=148). vm_compute. reflexivity. Qed.

(** Transport the actual nonempty startup PC to its matching original-source entry. *)
Theorem seed_source_bridge R :
  rm_halts p254 (seed_pc,R) <->
  rm_halts dag254 (source_pc,upd R 1 (S (R 1))).
Proof.
  rewrite (rm_run_halts_iff p254 2 _ _ (seed_two_steps R)).
  apply certificate_entry_iff with (j:=148%N) (k:=3001%N), seed_certificate_entry.
Qed.


(** ** Complete structured AX suffix *)
(** The nine logical registers after the 347-step source prefix. *)
Definition suffix_start : St := mkSt 0 1 38 1 1 0 0 0 0.
(** Execute the entire remaining AX suffix with opaque pairing arithmetic. Its stack result may be arbitrary; every other active register is zero. *)
Lemma suffix24_sem : exists w,
  sem (ENode 24) suffix_start XNormal (mkSt 0 0 w 0 0 0 0 0 0).
Proof.
  eexists. unfold suffix_start. run_seq.
  apply sx_nil_eq. rewrite ?iter_unP, ?unP_P. cbn [fst snd]. reflexivity.
Qed.

(** ** Exact source entry and return to enumeration *)
(** Exact PC left by the computed prefix, including its trailing zero bits. *)
Definition suffix_pc : list bool := [t;t;t;f;t;f;f;t;f;f;t;f;t;t;t;f;f].
(** Structured prefix of node 24, the remaining AX construction. *)
Definition suffix_node_pc : list bool := [t;t;t;f;t;f;f;t;f;f;t;f;t;t;t].
(** The startup register file after its first increment. *)
Definition initial_source_regs : regs := upd seed_regs 1 (S (seed_regs 1)).

(** Compute exactly 347 small source steps to the start of the remaining structured AX suffix. *)
Lemma seed_prefix : exists R',
  rm_run dag254 347 (source_pc,initial_source_regs) = Some (suffix_pc,R') /\
  approx R' suffix_start.
Proof.
  eexists. split.
  - vm_compute. reflexivity.
  - intros i. do 9 (destruct i as [|i]; [vm_compute; reflexivity|]). vm_compute. reflexivity.
Qed.

(** The original source DAG satisfies the structured-program well-formedness checker. *)
Lemma dag_wf : wf dag254.
Proof. apply wf_check_sound. vm_compute. reflexivity. Qed.

(** The designated source prefix points to the complete suffix node 24. *)
Lemma suffix_node_path : fol dag254 (ENode (root dag254)) suffix_node_pc = Some (ENode 24).
Proof. vm_compute. reflexivity. Qed.

(** The finite prefix leaves two trailing zero PC bits, which do not change the selected instruction. *)
Lemma suffix_pc_ipeq : ipeq suffix_pc suffix_node_pc.
Proof. change (ipeq ((suffix_node_pc ++ [f]) ++ [f]) suffix_node_pc). eapply ipeq_trans; apply ipeq_app_false. Qed.

(** After the structured suffix returns, exactly three control steps reach a root-equivalent PC. *)
Lemma suffix_control R : rm_run dag254 3 (inc_path suffix_node_pc,R) = Some ([f;f;f],R).
Proof. vm_compute. reflexivity. Qed.

(** Equivalent PC encodings have the same first step and therefore the same positive-length run. *)
Lemma run_positive_ipeq p n P1 P2 R : ipeq P1 P2 ->
  rm_run p (S n) (P1,R) = rm_run p (S n) (P2,R).
Proof. intro E. cbn [rm_run]. rewrite (step_ipeq p P1 P2 R E). reflexivity. Qed.

(** The control-step result also holds for the trailing-zero encoding returned by structured execution. *)
Lemma suffix_control_ipeq P' R : ipeq P' (inc_path suffix_node_pc) ->
  rm_run dag254 3 (P',R) = Some ([f;f;f],R).
Proof. intro E. rewrite (run_positive_ipeq dag254 2 _ _ R E). apply suffix_control. Qed.

(** Trailing-zero equivalence of program counters preserves halting. *)
Lemma halts_ipeq p P1 P2 R : ipeq P1 P2 ->
  rm_halts p (P1,R) <-> rm_halts p (P2,R).
Proof.
  intro E. split; intros [n H].
  - exists n. exact (hn_ipeq p n P1 P2 R E H).
  - exists n. exact (hn_ipeq p n P2 P1 R (ipeq_sym _ _ E) H).
Qed.

(** Three zero PC bits select the same instructions as the empty root counter. *)
Lemma root_zero_ipeq : ipeq [f;f;f] [].
Proof. change (ipeq ((([] ++ [f]) ++ [f]) ++ [f]) []). eapply ipeq_trans; [apply ipeq_app_false|]. eapply ipeq_trans; apply ipeq_app_false. Qed.

(** Compose the finite prefix, unbounded structured suffix and return steps. The protected-stack theorem then proves the exact calculus endpoint without calculating the enormous stack. *)
Theorem source_seed_halts :
  rm_halts dag254 (source_pc,initial_source_regs) <-> thm254 1.
Proof.
  destruct seed_prefix as (Rpre & Prefix & Apre).
  rewrite (rm_run_halts_iff dag254 347 _ _ Prefix).
  destruct suffix24_sem as (w & Sem).
  destruct (Sem Rpre Apre) as (Rfinal & Run & Afinal).
  pose proof (RMEquiv.fwd dag254 dag_wf (ENode 24) Rpre XNormal Rfinal Run
    suffix_node_pc suffix_pc suffix_node_path suffix_pc_ipeq) as Reach.
  cbn [reaches target] in Reach. destruct Reach as (n & P' & Prefix' & E).
  rewrite (rm_run_halts_iff dag254 n _ _ Prefix').
  rewrite (rm_run_halts_iff dag254 3 _ _ (suffix_control_ipeq P' Rfinal E)).
  rewrite (halts_ipeq dag254 [f;f;f] [] Rfinal root_zero_ipeq).
  rewrite (rm_halts_iff_iter dag254 dag_wf).
  assert (Enc : approx Rfinal (enc (mkState 0 0 0 w 0 0))) by exact Afinal.
  rewrite (iter_halts_dag (mkState 0 0 0 w 0 0) Rfinal Enc).
  exact (arbitrary_stack_zero_head_halts_iff w 0).
Qed.

(** The complete literal blank-tape machine halts exactly when the source calculus derives contradiction. *)
Theorem tm250_thm : halts tm c0 <-> thm254 1.
Proof.
  rewrite tm254_rm.
  change (rm_halts p254 (seed_pc,seed_regs) <-> thm254 1).
  rewrite (seed_source_bridge seed_regs). exact source_seed_halts.
Qed.

Print Assumptions tm250_thm.
