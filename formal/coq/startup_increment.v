(** The increment carry uses the decrement scanner for its final blank-tape
    detour. It returns to the last one in state 48; the unchanged register-file
    return proof then applies. This induction covers arbitrary register values
    and arbitrary later blocks, not a bounded execution sample. *)
Lemma shift_inc rest a K :
  zc (st 95) K (ones a ++ sepsR rest) -->* zl (st 48) (rev (ones (S a) ++ sepsR rest) ++ K) [].
Proof.
  revert a K. induction rest as [|m rest IH]; intros a K.
  - change (sepsR []) with (@nil bool).
    eapply evstep_trans; [apply (scanR _ true true a), tm_st; reflexivity|].
    rewrite zc_blank. go. rewrite zc_blank. go. rewrite zc_blank. go. rewrite zl_c. go.
    apply eq_ev. rewrite app_nil_r, rev_ones. cbn [repeat app]. unfold zl. cbn [tl hd].
    change (zc (st 48) (ones a ++ K) ([true] ++ zeros 2) = zc (st 48) (ones a ++ K) [true]).
    apply zc_padr.
  - rewrite sepsR_cons.
    eapply evstep_trans; [apply (scanR _ true true a), tm_st; reflexivity|].
    go. go. eapply evstep_trans; [apply IH|].
    apply eq_ev. f_equal.
    change (ones (S a) ++ false :: true :: ones m ++ sepsR rest) with (ones (S a) ++ [false] ++ (ones (S m) ++ sepsR rest)).
    rewrite !rev_app_distr, !rev_ones. rewrite <- !app_assoc. reflexivity.
Qed.
