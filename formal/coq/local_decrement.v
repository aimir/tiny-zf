(* Carry the erased cell rightward through a run of ones by local swaps.
   Each iteration preserves the run and moves the erased cell one place.
   This avoids a separate state for scanning to the end of the run. *)
Lemma local_dec_ones m K X :
  zc (st 112) (false :: K) (ones m ++ X) -->*
  zc (st 112) (false :: ones m ++ K) X.
Proof.
  revert K. induction m as [|m IH]; intros K; [apply evstep_refl|].
  cbn [repeat app]. go. rewrite zl_c. go. go.
  eapply evstep_trans; [apply IH|].
  apply eq_ev. f_equal. rewrite rep_comm. reflexivity.
Qed.

(* The same block contract as the forward scan, using the local swap loop. *)
Lemma forward_dec_block m K X :
  zc (st 112) K (false :: ones (S m) ++ false :: X) -->*
  zc (st 112) (false :: ones (S m) ++ K) (false :: X).
Proof.
  go. go.
  eapply evstep_trans; [apply (local_dec_ones m (true :: K) (false :: X))|].
  apply eq_ev. f_equal. rewrite rep_comm. reflexivity.
Qed.
