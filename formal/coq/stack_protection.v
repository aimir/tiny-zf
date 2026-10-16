(** * Stack protection for the source enumerator

    Headline: [arbitrary_initial_stack_halts_iff] proves

      thm254 t -> thm254 hh ->
      (halts_from (mkState 0 0 t base dd hh) <-> thm254 1).

    The stack [base] and additive parameter [dd] are arbitrary. The candidate
    counter and remaining proof list start at zero. The zero-head corollary
    requires no derivability hypotheses. This is a source theorem; a binary
    machine still needs a checked initialization and interpreter simulation.

    Proof flow: exact command coding; an earlier injective DROP partner for
    each NIP; finite-prefix credit; source cursor correspondence; preservation
    of a derivable stack prefix above the arbitrary old tail. Completeness
    comes from GeneralInit.complete_from_any. No theory bridge is assumed. *)
From Coq Require Import Lists.List Arith Lia Bool.
From M254L Require Import Codes254 Enum254 Thm254 L1_Sound254 L1_Comp254.
Require Import GeneralInit.
Import ListNotations.

(** ** Exact candidate coding *)

Inductive rawcmd := RMP (x:nat) | RDROP (x:nat) | RNIP (x:nat)
  | RAX (c x y u:nat).
Definition raw_fields k := match k with
  | RMP x => [0;x] | RDROP x => [1;x] | RNIP x => [2;x]
  | RAX c x y u => [3+c;x;y;u] end.
Definition pack fs r := fold_right P r fs.
Fixpoint raw_tail L := match L with
  | [] => 0 | k::ks => S (pack (raw_fields k) (raw_tail ks)) end.
Definition program_code L := match L with
  | [] => 0 | k::ks => pack (raw_fields k) (raw_tail ks) end.
Definition read_command n : rawcmd * nat :=
  let '(a,r) := unP n in let '(x,r) := unP r in
  match a with
  | 0 => (RMP x,r) | 1 => (RDROP x,r) | 2 => (RNIP x,r)
  | S(S(S c)) => let '(y,r) := unP r in let '(u,r) := unP r in
    (RAX c x y u,r) end.

(** Strict growth of triangular numbers makes smaller selector fields produce smaller codes. *)
Lemma tri_strict n m : n<m -> tri n<tri m.
Proof.
  revert n. induction m as [|m IH]; intros n H; [lia|].
  rewrite tri_S. destruct (Nat.eq_dec n m) as [->|N]; [lia|].
  specialize (IH n ltac:(lia)). lia.
Qed.
(** Increasing the first pairing coordinate strictly increases its code. *)
Lemma pair_strict_left a b c : a<b -> P a c<P b c.
Proof. intro H. unfold P. pose proof (tri_strict (a+c) (b+c) ltac:(lia)). lia. Qed.
(** Increasing the tail coordinate strictly increases its code. *)
Lemma pair_strict_right a b c : b<c -> P a b<P a c.
Proof. intro H. unfold P. pose proof (tri_strict (a+b) (a+c) ltac:(lia)). lia. Qed.

(** A fixed field prefix preserves strict ordering of encoded tails. *)
Lemma pack_strict fs r s : r<s -> pack fs r<pack fs s.
Proof. induction fs as [|x fs IH]; intro H; cbn [pack fold_right]; [exact H|].
 apply pair_strict_right, IH, H. Qed.

(** Decoding a packed command recovers both the command and its remaining tail. *)
Lemma read_pack k r : read_command (pack (raw_fields k) r) = (k,r).
Proof. destruct k; unfold raw_fields, pack; cbn [fold_right];
 unfold read_command; rewrite !unP_P; reflexivity. Qed.
(** The decoder distinguishes different commands and tails. *)
Lemma pack_injective k l r s : pack (raw_fields k) r = pack (raw_fields l) s -> k=l /\ r=s.
Proof. intro E. apply (f_equal read_command) in E. rewrite !read_pack in E.
 now injection E. Qed.

(** The positive tail terminator makes complete command tails uniquely encoded. *)
Lemma raw_tail_injective L : forall K, raw_tail L=raw_tail K -> L=K.
Proof.
 induction L as [|k L IH]; intros [|l K] E; try discriminate; [reflexivity|].
 cbn [raw_tail] in E. injection E as E.
 apply pack_injective in E as [-> E]. f_equal. exact (IH K E).
Qed.
(** Every nonempty candidate has a unique command sequence. *)
Lemma program_code_injective k L l K : program_code (k::L)=program_code(l::K) -> k::L=l::K.
Proof.
 cbn [program_code]. intro E. apply pack_injective in E as [-> E].
 f_equal. apply raw_tail_injective, E.
Qed.

(** Changing a NIP to DROP lowers a tail code, including under any preceding commands. *)
Lemma nip_drop_tail pre x post :
 raw_tail (pre++RDROP x::post)<raw_tail(pre++RNIP x::post).
Proof.
 induction pre as [|k pre IH]; cbn [app raw_tail].
 - cbn [raw_fields pack fold_right].
   pose proof (pair_strict_left 1 2 (P x (raw_tail post)) ltac:(lia)). lia.
 - pose proof (pack_strict (raw_fields k) _ _ IH). lia.
Qed.
(** The same replacement strictly lowers the full candidate number. *)
Lemma nip_drop_program pre x post :
 program_code (pre++RDROP x::post)<program_code(pre++RNIP x::post).
Proof.
 destruct pre as [|k pre]; cbn [app program_code].
 - cbn [raw_fields pack fold_right]. apply pair_strict_left; lia.
 - apply pack_strict, nip_drop_tail.
Qed.

Definition toggle k := match k with RDROP x=>RNIP x | RNIP x=>RDROP x | k=>k end.
Fixpoint toggle_at n L := match n,L with
 | _,[]=>[] | 0,k::ks=>toggle k::ks | S n,k::ks=>k::toggle_at n ks end.
(** The position-specific toggle replaces the selected NIP and preserves its context. *)
Lemma toggle_at_append pre x post :
 toggle_at (length pre) (pre++RNIP x::post)=pre++RDROP x::post.
Proof. induction pre; cbn; [reflexivity|]. now rewrite IHpre. Qed.

(** A command consumes a tail no larger than its input; this bounds recursive decoding. *)
Lemma read_rest_le n : snd (read_command n)<=n.
Proof.
 unfold read_command.
 pose proof (unP_le n) as [_ A]. destruct (unP n) as [a r] eqn:E; cbn in A.
 pose proof (unP_le r) as [_ B]. destruct (unP r) as [x t] eqn:F; cbn in B.
 destruct a as [|[|[|c]]]; cbn; try lia.
 pose proof (unP_le t) as [_ C]. destruct (unP t) as [y u] eqn:G; cbn in C.
 pose proof (unP_le u) as [_ D]. destruct (unP u) as [z v] eqn:H; cbn in D. cbn. lia.
Qed.
(** Repacking a decoded command gives its exact input code. *)
Lemma pack_read n : pack (raw_fields (fst(read_command n))) (snd(read_command n))=n.
Proof.
 unfold read_command.
 pose proof (P_unP n) as A. destruct (unP n) as [a r] eqn:E; cbn in A.
 pose proof (P_unP r) as B. destruct (unP r) as [x t] eqn:F; cbn in B.
 destruct a as [|[|[|c]]].
 - cbn [fst snd raw_fields pack fold_right]. subst n r. reflexivity.
 - cbn [fst snd raw_fields pack fold_right]. subst n r. reflexivity.
 - cbn [fst snd raw_fields pack fold_right]. subst n r. reflexivity.
 - pose proof (P_unP t) as C. destruct (unP t) as [y u] eqn:G; cbn in C.
   pose proof (P_unP u) as D. destruct (unP u) as [z v] eqn:H; cbn in D.
   cbn [fst snd raw_fields pack fold_right]. subst n r t u. reflexivity.
Qed.

Fixpoint decode_tail_fuel fuel n := match fuel,n with
 | S fuel,S m => fst(read_command m)::decode_tail_fuel fuel (snd(read_command m))
 | _,_ => [] end.

(** Fuel equal to the tail code suffices to decode it exactly. *)
Lemma decode_tail_exact fuel : forall n, n<=fuel -> raw_tail(decode_tail_fuel fuel n)=n.
Proof.
 induction fuel as [|fuel IH]; intros [|n] H; cbn [decode_tail_fuel raw_tail]; try lia; try reflexivity.
 rewrite IH by (pose proof (read_rest_le n); lia).
 rewrite pack_read. reflexivity.
Qed.
Definition decode_program n := fst(read_command n)::decode_tail_fuel (snd(read_command n)) (snd(read_command n)).
(** Every natural candidate number decodes to a program with that exact code. *)
Lemma decode_program_exact n : program_code(decode_program n)=n.
Proof.
 unfold decode_program. cbn [program_code]. rewrite decode_tail_exact by lia. apply pack_read.
Qed.
(** Every candidate executes at least its first command. *)
Lemma decode_program_nonempty n : decode_program n<>[].
Proof. discriminate. Qed.

(** Encoding and decoding a nonempty program preserves the entire program. *)
Lemma decode_program_inverse k L : decode_program(program_code(k::L))=k::L.
Proof.
 unfold decode_program at 1. apply program_code_injective.
 fold (decode_program (program_code (k::L))). apply decode_program_exact.
Qed.

(** ** Earlier partners and finite-prefix credit *)

Definition event := (nat*nat)%type.
Definition events n : list event := map (fun j=>(n,j)) (seq 0 (length(decode_program n))).
Fixpoint past n := match n with 0=>[] | S n=>past n++events n end.
Definition event_prefix n k := past n++firstn k (events n).
Definition partner (e:event) := (program_code(toggle_at (snd e) (decode_program(fst e))),snd e).
Definition is_drop (e:event) := match nth_error(decode_program(fst e))(snd e) with
 | Some(RDROP _) => true | _=>false end.
Definition is_nip (e:event) := match nth_error(decode_program(fst e))(snd e) with
 | Some(RNIP _) => true | _=>false end.

(** A list-form inverse convenient for position-specific replacements. *)
Lemma decode_nonempty L : L<>[] -> decode_program(program_code L)=L.
Proof. destruct L; [contradiction|]. intro H. apply decode_program_inverse. Qed.
(** Toggling the corresponding DROP restores the original NIP. *)
Lemma toggle_drop_append pre x post :
 toggle_at(length pre)(pre++RDROP x::post)=pre++RNIP x::post.
Proof. induction pre; cbn; [reflexivity|]. now rewrite IHpre. Qed.
(** A program containing the selected command is nonempty, so the inverse applies. *)
Lemma app_cons_nonempty {A}(pre:list A) x post : pre++x::post<>[].
Proof. destruct pre; discriminate. Qed.
(** Compute the exact earlier candidate and position corresponding to a NIP event. *)
Lemma partner_nip pre x post :
 partner(program_code(pre++RNIP x::post),length pre)=
 (program_code(pre++RDROP x::post),length pre).
Proof.
 unfold partner; cbn [fst snd]. rewrite decode_nonempty by apply app_cons_nonempty.
 rewrite toggle_at_append. reflexivity.
Qed.
(** The DROP partner uniquely recovers its original NIP event. *)
Lemma partner_drop pre x post :
 partner(program_code(pre++RDROP x::post),length pre)=
 (program_code(pre++RNIP x::post),length pre).
Proof.
 unfold partner; cbn [fst snd]. rewrite decode_nonempty by apply app_cons_nonempty.
 rewrite toggle_drop_append. reflexivity.
Qed.

(** Every NIP has an earlier DROP partner, and the partnership is injective. *)
Lemma nip_partner e : is_nip e=true ->
 fst(partner e)<fst e /\ is_drop(partner e)=true /\ partner(partner e)=e.
Proof.
 destruct e as [n j]. unfold is_nip; cbn [fst snd].
 destruct(nth_error(decode_program n) j)as [k|]eqn:E; [|discriminate].
 destruct k as [x|x|x|c x y u]; try discriminate. intros _.
 destruct(nth_error_split (decode_program n) j E)as [pre [post [L J]]].
 assert(N: n=program_code(pre++RNIP x::post)).
 { rewrite <-L. symmetry. apply decode_program_exact. }
 subst n j. rewrite partner_nip. cbn [fst snd].
 split; [apply nip_drop_program|]. split.
 - unfold is_drop; cbn [fst snd]. rewrite decode_nonempty by apply app_cons_nonempty.
   rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
 - rewrite partner_drop. reflexivity.
Qed.

(** An event belongs to a candidate exactly when its position is in range. *)
Lemma events_member n m j : In(m,j)(events n) <-> m=n /\ j<length(decode_program n).
Proof.
 unfold events. rewrite in_map_iff. split.
 - intros [i [E H]]. injection E as -> ->. apply in_seq in H. lia.
 - intros [-> H]. exists j. split; [reflexivity|]. apply in_seq. lia.
Qed.
(** Completed candidates contain every valid event whose candidate number is smaller. *)
Lemma past_member n m j : In(m,j)(past n) <-> m<n /\ j<length(decode_program m).
Proof.
 induction n as [|n IH]; cbn [past]; [split; [contradiction|lia]|].
 rewrite in_app_iff,IH,events_member. split.
 - intros [[A B]|[-> B]]; split; try lia; exact B.
 - intros [A B]. destruct(Nat.eq_dec m n)as [->|N]; [right; auto|left; split; auto; lia].
Qed.
(** A current-candidate prefix contains only events of that candidate. *)
Lemma firstn_In {A} k (l:list A) x : In x(firstn k l)->In x l.
Proof. intro H. rewrite <-(firstn_skipn k l). apply in_or_app; auto. Qed.
(** Events in an execution prefix have valid positions and bounded candidate numbers. *)
Lemma prefix_member n k m j : In(m,j)(event_prefix n k) ->
 m<=n /\ j<length(decode_program m).
Proof.
 unfold event_prefix. rewrite in_app_iff. intros [H|H].
 - apply past_member in H. lia.
 - apply firstn_In,events_member in H. destruct H as [-> H]. auto.
Qed.

(** An injective event transformation preserves distinct occurrences. *)
Lemma map_injective_nodup {A B}(f:A->B) l :
 (forall x y,In x l->In y l->f x=f y->x=y)->NoDup l->NoDup(map f l).
Proof.
 intros Inj H. induction H as [|x l Hnot Hdup IH]; cbn; constructor.
 - intro E. apply in_map_iff in E as [y [E Hy]].
   assert(x=y)by(apply Inj; simpl; auto). subst y. contradiction.
 - apply IH. intros u v Hu Hv E. apply Inj; simpl; auto.
Qed.
(** Positions distinguish the events of one candidate. *)
Lemma events_nodup n : NoDup(events n).
Proof.
 unfold events. apply map_injective_nodup; [intros x y _ _ H; now injection H|apply seq_NoDup].
Qed.
(** Taking a finite event prefix preserves distinct occurrences. *)
Lemma firstn_nodup {A} k (l:list A) : NoDup l->NoDup(firstn k l).
Proof.
 revert l. induction k; intros l H; [constructor|]. destruct l; [constructor|].
 cbn. inversion H; subst. constructor; [intro E; apply H2; now apply firstn_In in E|auto].
Qed.
(** Different candidate numbers distinguish completed-candidate events. *)
Lemma past_nodup n : NoDup(past n).
Proof.
 induction n; cbn [past]; [constructor|]. apply NoDup_app; [exact IHn|apply events_nodup|].
 intros [m j] H K. apply past_member in H. apply events_member in K. lia.
Qed.
(** No event is repeated in the complete execution prefix. *)
Lemma prefix_nodup n k : NoDup(event_prefix n k).
Proof.
 unfold event_prefix. apply NoDup_app; [apply past_nodup|apply firstn_nodup,events_nodup|].
 intros [m j] H K. apply past_member in H. apply firstn_In,events_member in K. lia.
Qed.

(** Every NIP partner already occurs among the prefix's DROP events. *)
Lemma prefix_partner_in n k e : In e(event_prefix n k)->is_nip e=true ->
 In(partner e)(filter is_drop(event_prefix n k)).
Proof.
 intros H N. pose proof(nip_partner e N)as [A [B C]].
 apply filter_In. split; [|exact B]. unfold event_prefix. apply in_or_app. left.
 destruct e as [m j]. pose proof(prefix_member _ _ _ _ H)as [M J].
 destruct(partner(m,j))as [u v]eqn:E. cbn [fst snd]in A.
 apply past_member. split; [lia|].
 unfold is_drop in B. cbn [fst snd]in B.
 destruct(nth_error(decode_program u)v)eqn:F; [apply nth_error_Some; congruence|discriminate].
Qed.
(** Injectivity bounds NIP occurrences by the number of preceding DROP occurrences. *)
Theorem drop_pays_nip n k :
 length(filter is_nip(event_prefix n k))<=length(filter is_drop(event_prefix n k)).
Proof.
 rewrite <-(length_map partner(filter is_nip(event_prefix n k))).
 apply NoDup_incl_length.
 - apply map_injective_nodup; [|apply NoDup_filter,prefix_nodup].
   intros e f E F H. apply filter_In in E as [_ E]. apply filter_In in F as [_ F].
   pose proof(nip_partner e E)as [_ [_ A]]. pose proof(nip_partner f F)as [_ [_ B]].
   rewrite <-A,<-B,H. reflexivity.
 - intros e H. apply in_map_iff in H as [f [<- F]].
   apply filter_In in F as [F N]. now apply prefix_partner_in.
Qed.

(** Advancing a valid list prefix appends its next element. *)
Lemma firstn_next {A}(l:list A) j x : nth_error l j=Some x ->
 firstn(S j)l=firstn j l++[x].
Proof.
 revert l. induction j; intros [|y ys] H; cbn in *; try discriminate.
 - now injection H as <-.
 - now rewrite(IHj ys H).
Qed.
(** The event at a valid candidate position carries exactly that candidate and position. *)
Lemma events_nth n j : j<length(decode_program n)->nth_error(events n)j=Some(n,j).
Proof.
 intro H. unfold events. rewrite nth_error_map,nth_error_seq.
 replace(j <? length(decode_program n))with true by(symmetry; apply Nat.ltb_lt; exact H).
 reflexivity.
Qed.
(** One more command appends exactly the current event to the execution history. *)
Lemma prefix_extend n j : j<length(decode_program n)->
 event_prefix n(S j)=event_prefix n j++[(n,j)].
Proof.
 intro H. unfold event_prefix. rewrite(firstn_next _ _ _ (events_nth n j H)),app_assoc. reflexivity.
Qed.
(** The current NIP contributes no DROP credit. *)
Lemma nip_not_drop e : is_nip e=true -> is_drop e=false.
Proof.
 unfold is_nip,is_drop. destruct(nth_error(decode_program(fst e))(snd e))as[k|]; [destruct k|];
 discriminate || reflexivity.
Qed.

(** Immediately before NIP, earlier DROP events exceed earlier NIP events by at least one. *)
Theorem nip_has_credit n j : j<length(decode_program n)->is_nip(n,j)=true ->
 S(length(filter is_nip(event_prefix n j)))<=length(filter is_drop(event_prefix n j)).
Proof.
 intros V N. pose proof(drop_pays_nip n(S j))as H.
 rewrite(prefix_extend n j V),!filter_app,!length_app in H.
 cbn [filter]in H. rewrite N,(nip_not_drop _ N)in H. cbn [length]in H. lia.
Qed.

(** ** Correspondence with the frozen source decoder *)

Definition raw_source k r np1 s :=
 let dd:=d s in let hh:=h s in let t:=tw s in let w:=ws s in
 match k with
 | RMP x => let dd:=dd+x in Some(if Nat.eqb(wim t dd)hh
   then mkState r np1 dd (P 0 w) dd 0 else mkState r np1 0 w dd 0)
 | RDROP x => Some(mkState r np1 hh (P t w) (dd+x) hh)
 | RNIP x => if Nat.eqb hh 1 then None else
   let '(v,w):=unP w in Some(mkState r np1 t w (dd+x) v)
 | RAX c x y u => Some(mkState r np1 (gate(dd+x)(hh+y)c)
   (ax_stack(dd+x)hh(hh+y)c u t w) 0 0)
 end.

(** The frozen source decoder executes exactly the encoded raw command and fields. *)
Lemma enum_raw s k r np1 :
 (pl s=S(pack(raw_fields k)r) /\ np1=np s) \/
 (pl s=0 /\ np s=pack(raw_fields k)r /\ np1=S(np s)) ->
 enum_step s=raw_source k r np1 s.
Proof.
 intro H. unfold enum_step.
 assert(E:(if Nat.eqb(pl s)0 then(np s,S(np s))else(pred(pl s),np s))
  =(pack(raw_fields k)r,np1)).
 { destruct H as [[-> ->]|[-> [-> ->]]]; reflexivity. }
 rewrite E. destruct k; unfold raw_fields,pack; cbn [fold_right];
 rewrite !unP_P; reflexivity.
Qed.

Definition cursor n j s :=
 if Nat.eqb j 0 then pl s=0 /\ np s=n
 else pl s=raw_tail(skipn j(decode_program n)) /\ np s=S n.
Definition valid_cursor n j := j<length(decode_program n).
Definition next_cursor n j :=
 if Nat.ltb(S j)(length(decode_program n))then(n,S j)else(S n,0).

(** A valid cursor has a command remaining to execute. *)
Lemma skipn_nonempty {A}(l:list A)j : j<length l -> exists x xs,skipn j l=x::xs.
Proof.
 revert l. induction j; intros [|x xs] H; cbn in *; try lia.
 - eauto.
 - apply IHj. lia.
Qed.
(** Executing a command advances to the remainder of its candidate. *)
Lemma skipn_succ_cons {A}(l:list A)j x xs : skipn j l=x::xs -> skipn(S j)l=xs.
Proof. revert l. induction j; intros [|y ys] H; cbn in *; try discriminate.
 - now injection H.
 - now apply IHj in H.
Qed.

(** Source counters select the same command as the fixed candidate enumeration. *)
Lemma cursor_read s n j : cursor n j s -> valid_cursor n j ->
 exists k rest,skipn j(decode_program n)=k::rest /\
 enum_step s=raw_source k (raw_tail rest)(S n)s.
Proof.
 intros C V. unfold valid_cursor in V.
 destruct(skipn_nonempty _ _ V)as[k[rest E]]. exists k,rest. split; [exact E|].
 apply enum_raw. destruct j as[|j].
 - unfold cursor in C; cbn in C. destruct C as[P0 N0].
   right. split; [exact P0|]. cbn in E.
   pose proof(decode_program_exact n)as H. rewrite E in H. cbn [program_code]in H.
   split; congruence.
 - change(pl s=raw_tail(skipn(S j)(decode_program n)) /\ np s=S n)in C. destruct C as[P0 N0].
   left. rewrite E in P0. cbn [raw_tail]in P0. auto.
Qed.
(** Successful command execution stores its exact remaining code and candidate counter. *)
Lemma raw_source_fields k r n s s' : raw_source k r n s=Some s' -> pl s'=r /\ np s'=n.
Proof.
 destruct k as[x|x|x|c x y u]; cbn [raw_source].
 - destruct(Nat.eqb(wim(tw s)(d s+x))(h s)); intro E; injection E as <-; split; reflexivity.
 - intro E; injection E as <-; split; reflexivity.
 - destruct(Nat.eqb(h s)1); [discriminate|].
   destruct(unP(ws s))as[v w]. intro E; injection E as <-; split; reflexivity.
 - intro E; injection E as <-; split; reflexivity.
Qed.

(** The source cursor advances within its candidate or to the next candidate. *)
Lemma cursor_step s s' n j : cursor n j s -> valid_cursor n j -> enum_step s=Some s' ->
 cursor(fst(next_cursor n j))(snd(next_cursor n j))s' /\
 valid_cursor(fst(next_cursor n j))(snd(next_cursor n j)).
Proof.
 intros C V H. destruct(cursor_read _ _ _ C V)as[k[rest[E R]]].
 rewrite R in H. apply raw_source_fields in H as[P0 N0].
 unfold next_cursor. destruct(Nat.ltb(S j)(length(decode_program n)))eqn:B; cbn[fst snd].
 - apply Nat.ltb_lt in B. split; [|exact B].
   change(pl s'=raw_tail(skipn(S j)(decode_program n)) /\ np s'=S n).
   rewrite(skipn_succ_cons _ _ _ _ E). auto.
 - apply Nat.ltb_ge in B. split.
   + unfold cursor; cbn. split; [|exact N0].
     assert(Len:S j=length(decode_program n))by(unfold valid_cursor in V; lia).
     assert(rest=[])by(pose proof(skipn_succ_cons _ _ _ _ E)as F;
       rewrite Len,skipn_all in F; congruence).
     now subst rest.
   + unfold valid_cursor. destruct(decode_program(S n))eqn:D; [exfalso; apply(decode_program_nonempty(S n)),D|cbn;lia].
Qed.

(** The next source cursor represents the next event prefix, including candidate boundaries. *)
Lemma next_prefix n j : valid_cursor n j ->
 event_prefix(fst(next_cursor n j))(snd(next_cursor n j))=event_prefix n(S j).
Proof.
 intro V. unfold next_cursor. destruct(S j <? length(decode_program n))eqn:B; cbn[fst snd]; [reflexivity|].
 apply Nat.ltb_ge in B. unfold event_prefix.
 change((past n++events n)++[]=past n++firstn(S j)(events n)). rewrite app_nil_r.
 rewrite firstn_all2; [reflexivity|]. unfold events. rewrite length_map,length_seq. exact B.
Qed.
(** The head of a remaining command list is the command at its cursor position. *)
Lemma skipn_command {A}(l:list A)j x xs : skipn j l=x::xs -> nth_error l j=Some x.
Proof.
 intro E. pose proof(hd_error_skipn j l)as H. rewrite E in H. cbn[hd_error]in H. symmetry; exact H.
Qed.
Definition drop_count n j := length(filter is_drop(event_prefix n j)).
Definition nip_count n j := length(filter is_nip(event_prefix n j)).
(** Advancing the source cursor updates the two event counts by the current command. *)
Lemma next_counts n j : valid_cursor n j ->
 drop_count(fst(next_cursor n j))(snd(next_cursor n j))=
   drop_count n j+(if is_drop(n,j)then 1 else 0) /\
 nip_count(fst(next_cursor n j))(snd(next_cursor n j))=
   nip_count n j+(if is_nip(n,j)then 1 else 0).
Proof.
 intro V. unfold drop_count,nip_count. rewrite(next_prefix n j V),(prefix_extend n j V).
 rewrite !filter_app,!length_app. cbn[filter].
 destruct(is_drop(n,j)),(is_nip(n,j)); cbn[length]; split; reflexivity.
Qed.

(** ** The protected prefix and headline source theorem *)

Opaque P.
Definition stack_on xs w := fold_right P w xs.
Definition rows a h b c u t := [rho1 a b;rho2 a b c;rho3 a b c;rho4 a b c;
 rho5 a b c;rho6 a b;rho7 a b c;rho8 a b c u;wal a h;t].
(** The AX command pushes ten derivable formulas when the current formula and cache are derivable. *)
Lemma rows_good a h b c u t : thm254 t->thm254 h->Forall thm254(rows a h b c u t).
Proof.
 intros T H. unfold rows.
 apply Forall_cons; [exact(T_r1 a b)|].
 apply Forall_cons; [exact(T_r2 a b c)|].
 apply Forall_cons; [exact(T_r3 a b c)|].
 apply Forall_cons; [exact(T_r4 a b c)|].
 apply Forall_cons; [exact(T_r5 a b c)|].
 apply Forall_cons; [exact(T_r6 a b)|].
 apply Forall_cons; [exact(T_r7 a b c)|].
 apply Forall_cons; [exact(T_r8 a b c u)|].
 apply Forall_cons; [exact(T_gen a h H)|].
 apply Forall_cons; [exact T|constructor].
Qed.
(** A newly pushed formula list composes with the existing certified prefix. *)
Lemma stack_on_app xs ys w : stack_on(xs++ys)w=stack_on xs(stack_on ys w).
Proof. unfold stack_on. apply fold_right_app. Qed.
(** The frozen AX stack expression is exactly the ten-formula prefix used in the invariant. *)
Lemma ax_stack_rows a h b c u t w : ax_stack a h b c u t w=stack_on(rows a h b c u t)w.
Proof. reflexivity. Qed.
Definition protected base n j s := cursor n j s /\ valid_cursor n j /\
 thm254(tw s) /\ thm254(h s) /\ exists xs,
 ws s=stack_on xs base /\ Forall thm254 xs /\
 drop_count n j<=nip_count n j+length xs.

(** Each source command preserves the certified stack prefix; the credit bound makes NIP safe. *)
Lemma protected_step base n j s s' : protected base n j s->enum_step s=Some s'->
 protected base(fst(next_cursor n j))(snd(next_cursor n j))s'.
Proof.
 intros[C[V[T[H[xs[W[G K]]]]]]] Step.
 pose proof(cursor_step _ _ _ _ C V Step)as[C' V'].
 destruct(cursor_read _ _ _ C V)as[k[rest[E R]]].
 pose proof(skipn_command _ _ _ _ E)as At.
 pose proof(next_counts n j V)as[DC NC].
 unfold is_drop,is_nip in DC,NC. cbn[fst snd]in DC,NC. rewrite At in DC,NC.
 split; [exact C'|]. split; [exact V'|].
 rewrite R in Step. destruct k as[x|x|x|c x y u]; cbn beta iota zeta in DC,NC;
 cbn[raw_source]in Step.
 - destruct(Nat.eqb(wim(tw s)(d s+x))(h s))eqn:B.
   + injection Step as <-. cbn[tw h ws].
     split.
     * apply Nat.eqb_eq in B. exact(T_mp(tw s)(d s+x)T(eq_ind_r thm254 H B)).
     * split; [exact T_true|]. exists(0::xs). split.
       -- cbn[stack_on fold_right]. now rewrite W.
       -- split; [constructor; [exact T_true|exact G]|]. cbn[length]. lia.
   + injection Step as <-. cbn[tw h ws]. split; [exact T_true|]. split; [exact T_true|].
     exists xs. repeat split; auto; lia.
 - injection Step as <-. cbn[tw h ws]. split; [exact H|]. split; [exact H|].
   exists(tw s::xs). split; [cbn[stack_on fold_right]; now rewrite W|].
   split; [constructor; assumption|]. cbn[length]. lia.
 - assert(N:is_nip(n,j)=true)by(unfold is_nip;cbn[fst snd];rewrite At;reflexivity).
   pose proof(nip_has_credit n j V N)as Credit. fold(drop_count n j)(nip_count n j)in Credit.
   destruct xs as[|v xs]; [cbn[length]in K;lia|].
   inversion G as[|? ? Tv Gs]; subst.
   destruct(Nat.eqb(h s)1)eqn:B; [discriminate|].
   rewrite W in Step. cbn[stack_on fold_right]in Step. rewrite unP_P in Step.
   injection Step as <-. cbn[tw h ws]. split; [exact T|]. split; [exact Tv|].
   exists xs. split; [reflexivity|]. split; [exact Gs|]. cbn[length]in K. lia.
 - injection Step as <-. cbn[tw h ws]. split; [apply gate_thm|]. split; [exact T_true|].
   exists(rows(d s+x)(h s)(h s+y)c u(tw s)++xs). split.
   + rewrite stack_on_app,<-W. apply ax_stack_rows.
   + split; [apply Forall_app; split; [apply rows_good; assumption|exact G]|].
     rewrite length_app. cbn[rows length]. lia.
Qed.

(** Candidate zero starts with no debt and needs no assumptions about the old stack tail. *)
Lemma protected_initial base t dd hh : thm254 t->thm254 hh->
 protected base 0 0 (mkState 0 0 t base dd hh).
Proof.
 intros T H. split; [split;reflexivity|]. split.
 - unfold valid_cursor. vm_compute. lia.
 - split; [exact T|]. split; [exact H|]. exists []. split; [reflexivity|].
   split; [constructor|]. unfold drop_count,nip_count,event_prefix,past. cbn. lia.
Qed.

(** Induction extends prefix protection through any finite successful source run. *)
Lemma protected_run base m : forall s n j,protected base n j s->
 forall s',run m s=Some s'->exists n' j',protected base n' j' s'.
Proof.
 induction m as[|m IH];intros s n j Inv s' E.
 - cbn[run]in E. injection E as <-. eauto.
 - cbn[run]in E. destruct(enum_step s)as[u|]eqn:Step;[|discriminate].
   pose proof(protected_step _ _ _ _ _ Inv Step)as I.
   eapply IH;[exact I|exact E].
Qed.

(** A halting NIP obtains contradiction from the certified cache, independently of the old tail. *)
Lemma protected_halt base n j s : protected base n j s->enum_step s=None->thm254 1.
Proof.
 intros[C[V[T[H Rest]]]] Stop.
 destruct(cursor_read _ _ _ C V)as[k[rest[E R]]]. rewrite R in Stop.
 destruct k as[x|x|x|c x y u];cbn[raw_source]in Stop;try discriminate.
 destruct(Nat.eqb(h s)1)eqn:B.
 - apply Nat.eqb_eq in B. now rewrite B in H.
 - destruct(unP(ws s));discriminate.
Qed.

(** The complete source endpoint: arbitrary initial stack, candidate zero, and derivable current formula/cache. *)
Theorem arbitrary_initial_stack_halts_iff t base dd hh :
 thm254 t->thm254 hh->
 (halts_from(mkState 0 0 t base dd hh)<->thm254 1).
Proof.
 intros T H. split.
 - intros[m[s'[E Stop]]].
   destruct(protected_run base m _ 0 0 (protected_initial base t dd hh T H) _ E)as[n[j I]].
   exact(protected_halt base n j s' I Stop).
 - apply complete_from_any.
Qed.
(** Zero current formula and cache discharge both derivability hypotheses without assumptions. *)
Corollary arbitrary_stack_zero_head_halts_iff base dd :
 halts_from(mkState 0 0 0 base dd 0)<->thm254 1.
Proof. apply arbitrary_initial_stack_halts_iff;exact T_true. Qed.

Print Assumptions arbitrary_initial_stack_halts_iff.
Print Assumptions arbitrary_stack_zero_head_halts_iff.
