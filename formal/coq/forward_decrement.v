(** Forward-streaming positive decrement proof fragments.

    candidate.py installs these lemmas in the pinned Box.v and changes
    SymExec.decp_exit to 48. Coq checks their literal machine transitions.
    The input is an arbitrary marked register file, with arbitrary left
    context and arbitrary register values; the output decrements the chosen
    positive register, appends one zero block, and returns in state 48.
    The fragments replace the old reverse-shift lemmas, so the removed state
    131 is not required. They cover both the split and merged stream loop. *)

(** Positive decrement carries the erased cell rightward through the suffix. *)
(* Move the erased-cell gap across one positive run. *)
Lemma forward_dec_block m K X :
  zc (st 112) K (false :: ones (S m) ++ false :: X) -->*
  zc (st 112) (false :: ones (S m) ++ K) (false :: X).
Proof.
  go. go.
  eapply evstep_trans; [apply (scanR _ true true m), tm_st; reflexivity|].
  go. rewrite rep_comm. rewrite zl_c. go.
  apply eq_ev. f_equal. rewrite rep_comm. reflexivity.
Qed.

(* Expose a separator even when the remaining file is empty. *)
Lemma sepsR_pad_forward rest : exists W, sepsR rest ++ [false] = false :: W.
Proof. destruct rest; eexists; reflexivity. Qed.

(* Induct over the suffix; the final blank becomes a new zero block. *)
Lemma forward_dec rest K :
  zc (st 112) K (sepsR rest) -->*
  zl (st 63) (rev (sepsL rest ++ [true]) ++ K) [].
Proof.
  revert K. induction rest as [|m rest IH]; intros K.
  - change (sepsR []) with (@nil bool).
    rewrite zc_blank. go. rewrite zc_blank. go.
    apply eq_ev. rewrite zl_blank. reflexivity.
  - rewrite sepsR_cons.
    rewrite <- (zc_padr _ _ _ 1). change (zeros 1) with [false].
    cbn [app]. rewrite <- app_assoc.
    destruct (sepsR_pad_forward rest) as [W EW]. rewrite EW.
    eapply evstep_trans; [apply forward_dec_block|].
    rewrite <- EW, (zc_padr _ _ (sepsR rest) 1).
    eapply evstep_trans; [apply IH|].
    apply eq_ev. f_equal.
    change (sepsL (m :: rest)) with ((ones (S m) ++ [false]) ++ sepsL rest).
    rewrite !rev_app_distr, rev_ones.
    cbn [rev app]. rewrite <- !app_assoc. reflexivity.
Qed.

(* Identify the streamed tape with the ordinary register encoding. *)
Lemma sepsL_forward vs X : false :: sepsL vs ++ X = sepsR vs ++ false :: X.
Proof.
  induction vs as [|v vs IH]; [reflexivity|].
  rewrite sepsL_cons, sepsR_cons. cbn [app].
  rewrite <- !app_assoc. cbn [app]. rewrite IH. reflexivity.
Qed.

(* The public positive-decrement contract used by the symbolic executor. *)
Lemma box_decp r l vs : r < 9 -> 9 <= length vs -> nth r vs 0 <> 0 ->
  zc (st 43) l (sepsM r vs) -->* zl (st (decp_exit r)) l (sepsR (decr r vs ++ [0])).
Proof.
  intros Hr Hl Hz. destruct (split_at vs r) as (pre & v & rest & -> & <-); [lia|].
  rewrite nth_split in Hz. destruct v as [|v']; [congruence|]. clear Hz.
  rewrite sepsM_split, decr_split. simpl pred.
  eapply evstep_trans; [apply (fwd 43 59); reflexivity|].
  go. go. go. rewrite zl_c.
  change (false :: true :: ones v' ++ sepsR rest) with (sepsR (v' :: rest)).
  eapply evstep_trans; [apply (forward_dec (v' :: rest) (false :: rev (sepsR pre) ++ l))|].
  assert (E : rev (sepsL (v' :: rest) ++ [true]) ++ false :: rev (sepsR pre) ++ l =
              rev (sepsR ((pre ++ v' :: rest) ++ [0])) ++ l).
  { rewrite !sepsR_app.
    change (sepsR [0]) with [false; true].
    rewrite <- app_assoc. rewrite <- (sepsL_forward (v' :: rest) [true]).
    rewrite !rev_app_distr. cbn [rev app]. rewrite !rev_app_distr.
    cbn [rev app]. rewrite <- !app_assoc. reflexivity. }
  rewrite E. unfold decp_exit.
  eapply evstep_trans; [apply (ret_file 63 48); try reflexivity; destruct pre; discriminate|].
  rewrite app_nil_r. apply evstep_refl.
Qed.

