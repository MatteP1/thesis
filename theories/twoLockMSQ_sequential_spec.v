From stdpp Require Import countable.
From iris.algebra Require Import excl.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants.
From iris.unstable.heap_lang Require Import interpreter.
From MSQueue Require Import twoLockMSQ_impl.
From MSQueue Require Import twoLockMSQ_common.

Local Existing Instance spin_lock.

Section proofs.

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!inG Σ (exclR unitO)}.

Let N := nroot .@ "twoLockMSQ".

(* ===== Sequential Specification for Two-lock M&S Queue ===== *)

(* 
	isLL is short for: 'is Linked List'.
	isLL_chain states that every node x in xs satisfies 
		n_in x ↦□ (n_val x, #(n_out x)).
   	Further, all adjacent pairs, [x ; x'], are connected by x' pointing to x.
	Example:
	The list
	[(l_5_in, x_5, l_5_out); 
	 (l_4_in, x_4, l_4_out); 
	 (l_3_in, x_3, l_3_out); 
	 (l_2_in, x_2, l_2_out); 
	 (l_1_in, x_1, l_1_out)] 
	generates:
	(x_5, l_5_out) <- l_5_in 	∗	l_5_in <- l_4_out	∗
	(x_4, l_4_out) <- l_4_in 	∗	l_4_in <- l_3_out	∗
	(x_3, l_3_out) <- l_3_in 	∗	l_3_in <- l_2_out	∗
	(x_2, l_2_out) <- l_2_in 	∗	l_2_in <- l_1_out	∗
	(x_1, l_1_out) <- l_1_in

 *)

Fixpoint isLL_chain (xs : list (loc * val * loc) ) : iProp Σ :=
	match xs with
	| [] => True
	| [x] => n_in x ↦□ (n_val x, #(n_out x))
	| x :: ((x' :: xs'') as xs') =>
				n_in x ↦□ (n_val x, #(n_out x)) ∗
				n_out x' ↦□ #(n_in x) ∗
				isLL_chain xs'
	end.

(* isLL_chain is persistent for all xs *)
Global Instance isLL_chain_persistent xs : Persistent (isLL_chain xs).
Proof.
	induction xs as [|x [|x' xs']]; apply _.
Qed.

(* xs defines a linked list, when the tail (the first element of the list) points to NONEV, and all the nodes form a linked list chain. *)
Definition isLL (xs : list (loc * val * loc) ) : iProp Σ :=
	match xs with
	| [] => True
	| x :: xs' => (n_out x) ↦ NONEV ∗ isLL_chain xs
	end.

(* Since isLL_chain is persistent, we can always extract it from isLL. *)
Lemma isLL_and_chain : forall xs,
	isLL xs -∗
	isLL xs ∗ isLL_chain xs.
Proof.
	iIntros (xs) "HisLLxs".
	destruct xs as [| x' xs']; first done.
	unfold isLL.
	iPoseProof "HisLLxs" as "[Hx'_out #HisLLxs]".
	iFrame.
	by iSplit.
Qed.

(* If x is an element in an isLL_chain, then it is a node. *)
Lemma isLL_chain_node : forall xs_1 x xs_2,
	isLL_chain (xs_1 ++ x :: xs_2) -∗
	n_in x ↦□ (n_val x, #(n_out x)).
Proof.
	iIntros (xs_1 x xs_2) "#HisLL_chain".
	iInduction xs_1 as [| y xs'_1] "IH".
	- destruct xs_2.
	  + done.
	  + by iDestruct "HisLL_chain" as "(Hx & _ & _)".
	- iApply "IH". 
	  destruct xs'_1 as [| y' xs''_1];
	  iDestruct "HisLL_chain" as "(_ & _ & H)"; done.
Qed.

Lemma isLL_chain_split : forall xs ys,
	isLL_chain (xs ++ ys) -∗
	isLL_chain xs ∗ isLL_chain ys.
Proof.
	iIntros (xs ys) "#HisLL_chain_xs_ys".
	iInduction xs as [|x' xs'] "IH".
	- by iSplit.
	- destruct xs' as [| x'' xs''].
	  + destruct ys as [| y' ys'].
		* by iSplit.
		* iDestruct "HisLL_chain_xs_ys" as "(Hx' & Hy'_out & HIsLL_chain_ys')".
		  fold isLL_chain. iSplit; done.
	  + iAssert (isLL_chain (x'' :: xs'') ∗ isLL_chain ys)%I as "[IHxs' IHys]".
	  	{
			iApply "IH". iDestruct "HisLL_chain_xs_ys" as "(_ & _ & Hchain)"; done.
		}
		iSplit; try done.
		iDestruct "HisLL_chain_xs_ys" as "(Hx'_in & Hx''_out & _)".
		unfold isLL_chain; auto.
Qed.


(* Fist and Last of lists *)
Definition isFirst {A} (x : A) xs := ∃ xs_rest, xs = xs_rest ++ [x].
Definition isLast {A} (x : A) xs := ∃ xs_rest, xs = x :: xs_rest.
Definition isSndLast {A} (x : A) xs := ∃ x_first xs_rest, xs = x_first :: x :: xs_rest.

Lemma exists_first {A} : forall (xs : list A),
	~(xs = nil) ->
	∃x_first, isFirst x_first xs.
Proof.
	induction xs as [|x xs' IH]; first done.
	intros _.
	destruct xs' as [|x' xs'']; first by exists x, [].
	destruct IH as [x_first [xs_rest H_eq]]; first done.
	exists x_first, (x :: xs_rest).
	by rewrite H_eq.
Qed.

Lemma exists_last {A} : forall (xs : list A),
	~(xs = nil) ->
	∃x_last, isLast x_last xs.
Proof.
	intros [|x xs']; first done.
	intros _.
	by exists x, xs'.
Qed.


Record SeqQgnames := {γ_Hlock_seq 	: gname;
					  γ_Tlock_seq 	: gname;
					 }.

Definition is_queue_seq (q : val) (xs_v: list val) (Q_γ: SeqQgnames) : iProp Σ :=
	∃ l_queue l_head l_tail : loc, ∃ H_lock T_lock : val,
	⌜q = #l_queue⌝ ∗
	l_queue ↦□ ((#l_head, #l_tail), (H_lock, T_lock)) ∗
	∃ (xs_queue : list (loc * val * loc)), ∃x_head x_tail : (loc * val * loc),
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	isLL (xs_queue ++ [x_head]) ∗
	l_head ↦ #(n_in x_head) ∗
	l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail (xs_queue ++ [x_head])⌝ ∗
	is_lock Q_γ.(γ_Hlock_seq) H_lock (True) ∗
	is_lock Q_γ.(γ_Tlock_seq) T_lock (True).

Lemma initialize_spec_seq : 
	{{{ True }}} 
		initialize #() 
	{{{ v Q_γ, RET v; is_queue_seq v [] Q_γ }}}.
Proof.
	iIntros (Φ _) "HΦ".
	wp_lam.
	wp_alloc l_1_out as "Hl_1_out".
	wp_alloc l_1_in as "Hl_1_in".
	wp_pures.
	iMod (pointsto_persist with "Hl_1_in") as "#Hl_1_in".
	wp_apply (newlock_spec True); first done.
	iIntros (hlock γ_Hlock) "Hγ_Hlock".
	wp_let.
	wp_apply (newlock_spec True); first done.
	iIntros (tlock γ_Tlock) "Hγ_Tlock".
	set (Queue_gnames := {| γ_Hlock_seq := γ_Hlock;
							γ_Tlock_seq := γ_Tlock;
					|}).
	wp_let.
	wp_alloc l_tail as "Hl_tail".
	wp_alloc l_head as "Hl_head".
	wp_alloc l_queue as "Hl_queue".
	iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
	iApply ("HΦ" $! #l_queue Queue_gnames).
	iModIntro.
	iExists l_queue, l_head, l_tail, hlock, tlock.
	do 2(iSplit; first done).
	iFrame.
	iExists [].
	do 2 iExists (l_1_in, NONEV, l_1_out).
	iFrame.
	do 2 (iSplit; first done).
	by iExists [].
Qed.

Lemma enqueue_spec_seq Q (v : val) (xs_v : list val) (qg : SeqQgnames) :
	{{{ is_queue_seq Q xs_v qg }}}
		enqueue Q v 
	{{{w, RET w; is_queue_seq Q (v :: xs_v) qg }}}.
Proof.
	iIntros (Φ) "(%l_queue & %l_head & %l_tail & %H_lock & %T_lock & -> &
				 #Hl_queue & %xs_q & %x_head & %x_tail & %Hproj & H_isLL_xs &
				  Hl_head & Hl_tail & %HisLast_x_tail & #H_hlock &
				  #H_tlock) HΦ".
	destruct HisLast_x_tail as [xs_rest Hxs_split].
	rewrite Hxs_split.
	iDestruct "H_isLL_xs" as "[Hn_out_x_tail #H_isLL_chain_xs]".
	wp_lam.
	wp_let.
	wp_pures.
	wp_alloc l_new_out as "Hl_new_out".
	wp_alloc l_new_in as "Hl_new_in".
	iMod (pointsto_persist with "Hl_new_in") as "#Hl_new_in".
	wp_let.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "H_tlock").
	iIntros "(Hlocked_γ_Tlock & _)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_load.
	iPoseProof (isLL_chain_node [] x_tail xs_rest with "[H_isLL_chain_xs]") as "Hn_in_x_tail"; first done.
	wp_load.
	wp_pures.
	wp_store.
	iMod (pointsto_persist with "Hn_out_x_tail") as "#Hn_out_x_tail".
	wp_load.
	wp_pures.
	wp_store.
	wp_load.
	wp_pures.
	wp_apply (release_spec with "[$H_tlock $Hlocked_γ_Tlock]").
	iIntros (_).
	iApply ("HΦ" $! #()).
	iExists l_queue, l_head, l_tail, H_lock, T_lock.
	do 2 (iSplit; first done).
	iExists ((l_new_in, SOMEV v, l_new_out) :: xs_q), x_head, (l_new_in, SOMEV v, l_new_out).
	iSplit. { iPureIntro. simpl. f_equal. done. }
	iFrame.
	iSplit.
	{
		iSimpl.
		rewrite Hxs_split.
		repeat iSplit; done.
	}
	iSplit; first by iExists (xs_q ++ [x_head]).
	by iSplit.
Qed.

Lemma dequeue_spec_seq Q (xs_v : list val) (qg : SeqQgnames) : 
	{{{ is_queue_seq Q xs_v qg }}}
		dequeue Q
	{{{ v, RET v; (⌜xs_v = []⌝ ∗ ⌜v = NONEV⌝ ∗ is_queue_seq Q xs_v qg) ∨
				  (∃x_v xs'_v, ⌜xs_v = xs'_v ++ [x_v]⌝ ∗ 
				  		⌜v = SOMEV x_v⌝ ∗ is_queue_seq Q xs'_v qg) }}}.
Proof.
	iIntros (Φ) "(%l_queue & %l_head & %l_tail & %H_lock & %T_lock & -> &
				 #Hl_queue & %xs_q & %x_head & %x_tail & %Hproj & H_isLL_xs &
				  Hl_head & Hl_tail & %HisLast_x_tail & #H_hlock &
				  #H_tlock) HΦ".
	iPoseProof (isLL_and_chain with "H_isLL_xs") as "[H_isLL_xs #H_isLL_chain_xs]".
	wp_lam.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "H_hlock").
	iIntros "(Hlocked_γ_Hlock & _)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_load.
	wp_let.
	iPoseProof (isLL_chain_node xs_q x_head [] with "[H_isLL_chain_xs]") as "Hn_in_x_head"; first done.
	wp_load.
	wp_pures.
	(* Is the queue empty? *)
	destruct xs_q as [| x' xs_q' ].
	- (* Queue is empty *)
	  iDestruct "H_isLL_xs" as "[Hn_out_x_head _]".
	  wp_load.
	  wp_let.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_apply (release_spec with "[$H_hlock $Hlocked_γ_Hlock]").
	  iIntros (_).
	  wp_seq.
	  iModIntro.
	  iApply ("HΦ" $! NONEV).
	  iLeft.
	  destruct xs_v; last inversion Hproj.
	  do 2 (iSplit; first done).
	  iExists l_queue, l_head, l_tail, H_lock, T_lock.
	  do 2 (iSplit; first done).
	  iExists [], x_head, x_tail.
	  iFrame.
	  repeat iSplit; done.
	- (* Queue is not empty *)
	  destruct (exists_first (x' :: xs_q')) as [x_head_next [xs_q'' Hxs_q_eq]]; first done.
	  rewrite Hxs_q_eq.
	  iPoseProof (isLL_chain_split xs_q'' [x_head_next; x_head] with "[H_isLL_chain_xs]") as "[_ H_isLL_chain_x_head_next]"; first by rewrite <- app_assoc.
	  iDestruct "H_isLL_chain_x_head_next" as "(H_x_head_next_in & H_x_head_out & _)".
	  wp_load.
	  wp_let.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_store.
	  wp_load.
	  wp_pures.
	  wp_apply (release_spec with "[$H_hlock $Hlocked_γ_Hlock]").
	  iIntros (_).
	  wp_seq.
	  iModIntro.
	  iApply ("HΦ" $! (n_val x_head_next)).
	  iRight.
	  destruct xs_v; first inversion Hproj.
	  destruct (exists_first (v :: xs_v)) as [x_head_next_val [xs_val_rest Hxs_val_rest_eq]]; first done.
	  rewrite Hxs_val_rest_eq.
	  iExists x_head_next_val, xs_val_rest.
	  iSplit; first done.
	  rewrite Hxs_val_rest_eq in Hproj.
	  rewrite Hxs_q_eq in Hproj.
	  rewrite (proj_val_split xs_q'' [x_head_next]) in Hproj.
	  rewrite (wrap_some_split xs_val_rest [x_head_next_val]) in Hproj.
	  simpl in Hproj.
	  iSplit; first by iPureIntro; eapply list_last_eq.
	  iExists l_queue, l_head, l_tail, H_lock, T_lock.
	  do 2 (iSplit; first done).
	  iExists xs_q'', x_head_next, x_tail.
	  iSplit; first by iPureIntro; apply (list_last_eq (proj_val xs_q'') (wrap_some xs_val_rest) (n_val x_head_next) (InjRV x_head_next_val) Hproj).
	  iFrame.
	  iSplitL "H_isLL_xs".
	  {
		rewrite <- Hxs_q_eq.
		iDestruct "H_isLL_xs" as "[H_x_tail_out _]".
		iFrame.
		iPoseProof (isLL_chain_split (x' :: xs_q') [x_head] with "H_isLL_chain_xs") as "[HisLL_chain_no_head _]".
		done.
	  }
	  iSplit.
	  {
		iPureIntro.
		rewrite <- Hxs_q_eq.
		exists (xs_q').
		destruct HisLast_x_tail as [xs' Heq].
		inversion Heq.
		reflexivity.
	  }
	  by iSplit.
Qed.

End proofs.