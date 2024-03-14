From stdpp Require Import countable.
From iris.algebra Require Import excl.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants.
From MSQueue Require Import twoLockMSQ_impl.
From MSQueue Require Import twoLockMSQ_common.

Local Existing Instance spin_lock.

Section proofs.

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!inG Σ (exclR unitO)}.

Let N := nroot .@ "twoLockMSQ".

(* ===== Sequential Specification for Two-lock M&S Queue ===== *)

Record SeqQgnames := {γ_Hlock_seq 	: gname;
					  γ_Tlock_seq 	: gname;
					 }.

Definition is_queue_seq (v_q : val) (xs_v: list val) (Q_γ: SeqQgnames) : iProp Σ :=
	∃ l_queue l_head l_tail : loc, ∃ h_lock t_lock : val,
	⌜v_q = #l_queue⌝ ∗
	l_queue ↦□ ((#l_head, #l_tail), (h_lock, t_lock)) ∗
	∃ (xs_queue : list (loc * val * loc)), ∃x_head x_tail : (loc * val * loc),
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	isLL (xs_queue ++ [x_head]) ∗
	l_head ↦ #(n_in x_head) ∗
	l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail (xs_queue ++ [x_head])⌝ ∗
	is_lock Q_γ.(γ_Hlock_seq) h_lock (True) ∗
	is_lock Q_γ.(γ_Tlock_seq) t_lock (True).

Lemma initialize_spec_seq :
	{{{ True }}} 
		initialize #() 
	{{{ v_q Q_γ, RET v_q; is_queue_seq v_q [] Q_γ }}}.
Proof.
	iIntros (Φ _) "HΦ".
	wp_lam.
	wp_alloc l_1_out as "Hl_1_out".
	wp_alloc l_1_in as "Hl_1_in".
	wp_pures.
	iMod (pointsto_persist with "Hl_1_in") as "#Hl_1_in".
	wp_apply (newlock_spec True); first done.
	iIntros (h_lock γ_Hlock) "Hγ_Hlock".
	wp_let.
	wp_apply (newlock_spec True); first done.
	iIntros (t_lock γ_Tlock) "Hγ_Tlock".
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
	iExists l_queue, l_head, l_tail, h_lock, t_lock.
	do 2(iSplit; first done).
	iFrame.
	iExists [].
	do 2 iExists (l_1_in, NONEV, l_1_out).
	iFrame.
	do 2 (iSplit; first done).
	by iExists [].
Qed.

Lemma enqueue_spec_seq v_q (v : val) (xs_v : list val) (Q_γ : SeqQgnames) :
	{{{ is_queue_seq v_q xs_v Q_γ }}}
		enqueue v_q v 
	{{{w, RET w; is_queue_seq v_q (v :: xs_v) Q_γ }}}.
Proof.
	iIntros (Φ) "(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> &
				 #Hl_queue & %xs_queue & %x_head & %x_tail & %Hproj & HisLL_xs &
				  Hl_head & Hl_tail & %HisLast_x_tail & #Hh_lock &
				  #Ht_lock) HΦ".
	destruct HisLast_x_tail as [xs_rest Hxs_split].
	rewrite Hxs_split.
	iDestruct "HisLL_xs" as "[Hn_out_x_tail #HisLL_chain_xs]".
	wp_lam.
	wp_let.
	wp_pures.
	wp_alloc l_new_out as "Hl_new_out".
	wp_alloc l_new_in as "Hl_new_in".
	iMod (pointsto_persist with "Hl_new_in") as "#Hl_new_in".
	wp_let.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "Ht_lock").
	iIntros "(Hlocked_γ_Tlock & _)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_load.
	iPoseProof (isLL_chain_node [] x_tail xs_rest with "[HisLL_chain_xs]") as "Hn_in_x_tail"; first done.
	wp_load.
	wp_pures.
	wp_store.
	iMod (pointsto_persist with "Hn_out_x_tail") as "#Hn_out_x_tail".
	wp_load.
	wp_pures.
	wp_store.
	wp_load.
	wp_pures.
	wp_apply (release_spec with "[$Ht_lock $Hlocked_γ_Tlock]").
	iIntros (_).
	iApply ("HΦ" $! #()).
	iExists l_queue, l_head, l_tail, h_lock, t_lock.
	do 2 (iSplit; first done).
	iExists ((l_new_in, SOMEV v, l_new_out) :: xs_queue), x_head, (l_new_in, SOMEV v, l_new_out).
	iSplit. { iPureIntro. simpl. f_equal. done. }
	iFrame.
	iSplit.
	{
		iSimpl.
		rewrite Hxs_split.
		repeat iSplit; done.
	}
	iSplit; first by iExists (xs_queue ++ [x_head]).
	by iSplit.
Qed.

Lemma dequeue_spec_seq v_q (xs_v : list val) (Q_γ : SeqQgnames) : 
	{{{ is_queue_seq v_q xs_v Q_γ }}}
		dequeue v_q
	{{{ v, RET v; (⌜xs_v = []⌝ ∗ ⌜v = NONEV⌝ ∗ is_queue_seq v_q xs_v Q_γ) ∨
				  (∃x_v xs'_v, ⌜xs_v = xs'_v ++ [x_v]⌝ ∗ 
				  		⌜v = SOMEV x_v⌝ ∗ is_queue_seq v_q xs'_v Q_γ) }}}.
Proof.
	iIntros (Φ) "(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> &
				 #Hl_queue & %xs_queue & %x_head & %x_tail & %Hproj & HisLL_xs &
				  Hl_head & Hl_tail & %HisLast_x_tail & #Hh_lock &
				  #Ht_lock) HΦ".
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	wp_lam.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "Hh_lock").
	iIntros "(Hlocked_γ_Hlock & _)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_load.
	wp_let.
	iPoseProof (isLL_chain_node xs_queue x_head [] with "[HisLL_chain_xs]") as "Hn_in_x_head"; first done.
	wp_load.
	wp_pures.
	(* Is the queue empty? *)
	destruct xs_queue as [| x' xs_queue' ].
	- (* Queue is empty *)
	  iDestruct "HisLL_xs" as "[Hn_out_x_head _]".
	  wp_load.
	  wp_let.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_apply (release_spec with "[$Hh_lock $Hlocked_γ_Hlock]").
	  iIntros (_).
	  wp_seq.
	  iModIntro.
	  iApply ("HΦ" $! NONEV).
	  iLeft.
	  destruct xs_v; last inversion Hproj.
	  do 2 (iSplit; first done).
	  iExists l_queue, l_head, l_tail, h_lock, t_lock.
	  do 2 (iSplit; first done).
	  iExists [], x_head, x_tail.
	  iFrame.
	  repeat iSplit; done.
	- (* Queue is not empty *)
	  destruct (exists_first (x' :: xs_queue')) as [x_head_next [xs_queue'' Hxs_queue_eq]]; first done.
	  rewrite Hxs_queue_eq.
	  iPoseProof (isLL_chain_split xs_queue'' [x_head_next; x_head] with "[HisLL_chain_xs]") as "[_ HisLL_chain_x_head_next]"; first by rewrite <- app_assoc.
	  iDestruct "HisLL_chain_x_head_next" as "(Hx_head_next_in & Hx_head_out & _)".
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
	  wp_apply (release_spec with "[$Hh_lock $Hlocked_γ_Hlock]").
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
	  rewrite Hxs_queue_eq in Hproj.
	  rewrite (proj_val_split xs_queue'' [x_head_next]) in Hproj.
	  rewrite (wrap_some_split xs_val_rest [x_head_next_val]) in Hproj.
	  simpl in Hproj.
	  iSplit; first by iPureIntro; eapply list_last_eq.
	  iExists l_queue, l_head, l_tail, h_lock, t_lock.
	  do 2 (iSplit; first done).
	  iExists xs_queue'', x_head_next, x_tail.
	  iSplit; first by iPureIntro; apply (list_last_eq (proj_val xs_queue'') (wrap_some xs_val_rest) (n_val x_head_next) (InjRV x_head_next_val) Hproj).
	  iFrame.
	  iSplitL "HisLL_xs".
	  {
		rewrite <- Hxs_queue_eq.
		iDestruct "HisLL_xs" as "[Hx_tail_out _]".
		iFrame.
		iPoseProof (isLL_chain_split (x' :: xs_queue') [x_head] with "HisLL_chain_xs") as "[HisLL_chain_no_head _]".
		done.
	  }
	  iSplit.
	  {
		iPureIntro.
		rewrite <- Hxs_queue_eq.
		exists (xs_queue').
		destruct HisLast_x_tail as [xs' Heq].
		inversion Heq.
		reflexivity.
	  }
	  by iSplit.
Qed.

End proofs.