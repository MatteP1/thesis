From stdpp Require Import countable.
From iris.algebra Require Import excl list agree lib.frac_auth.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants token.
From MSQueue Require Import twoLockMSQ_impl.
From MSQueue Require Import twoLockMSQ_common.

Local Existing Instance spin_lock.

Section proofs.

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!tokenG Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Let N := nroot .@ "twoLockMSQ".

(* ===== Concurrent Specification for Two-lock M&S Queue ===== *)

(* Ghost variable names *)
Record Qgnames := {γ_Abst 	: gname;
				   γ_Hlock 	: gname;
				   γ_Tlock 	: gname;
				   γ_E 		: gname;
				   γ_nE 	: gname;
				   γ_D 		: gname;
				   γ_nD 	: gname;
				   γ_Before : gname;
				   γ_After 	: gname;
				  }.

(* Tokens *)
Definition TokHlock (g : Qgnames) := token g.(γ_Hlock).
Definition TokTlock (g : Qgnames) := token g.(γ_Tlock).
Definition TokE (g : Qgnames) := token g.(γ_E).
Definition ToknE (g : Qgnames) := token g.(γ_nE).
Definition TokD (g : Qgnames) := token g.(γ_D).
Definition ToknD (g : Qgnames) := token g.(γ_nD).
Definition TokBefore (g : Qgnames) := token g.(γ_Before).
Definition TokAfter (g : Qgnames) := token g.(γ_After).
Definition TokUpdated (g : Qgnames) := ((TokBefore g) ∗ (TokAfter g))%I.

Definition queue_invariant (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, own Q_γ.(γ_Abst) (●F (to_agree xs_v)) ∗ (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: (loc * val * loc)), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	(
		(* Static *)
		(
			l_head ↦ #(n_in x_head) ∗
			l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail xs⌝ ∗
			ToknE Q_γ ∗ ToknD Q_γ ∗ TokUpdated Q_γ
		)
		∨
		(* Enqueue *)
		(
			l_head ↦ #(n_in x_head) ∗
			l_tail ↦{#1/2} #(n_in x_tail) ∗
				(⌜isLast x_tail xs⌝ ∗ TokBefore Q_γ ∨
				 ⌜isSndLast x_tail xs⌝ ∗ TokAfter Q_γ) ∗
			TokE Q_γ ∗ ToknD Q_γ
		)
		∨
		(* Dequeue *)
		(
			l_head ↦{#1/2} #(n_in x_head) ∗
			l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail xs⌝ ∗
			ToknE Q_γ ∗ TokD Q_γ ∗ TokUpdated Q_γ
		)
		∨
		(* Both *)
		(
			l_head ↦{#1/2} #(n_in x_head) ∗
			l_tail ↦{#1/2} #(n_in x_tail) ∗
				(⌜isLast x_tail xs⌝ ∗ TokBefore Q_γ ∨
				 ⌜isSndLast x_tail xs⌝ ∗ TokAfter Q_γ) ∗
			TokE Q_γ ∗ TokD Q_γ
		)
	).

Definition queue_invariant_simple (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, own Q_γ.(γ_Abst) (●F (to_agree xs_v)) ∗ (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: (loc * val * loc)), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	(
		(
			(l_head ↦ #(n_in x_head) ∗ ToknD Q_γ) ∨ 
			(l_head ↦{#1/2} #(n_in x_head) ∗ TokD Q_γ)
		) ∗
		(
			(l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail xs⌝ ∗ ToknE Q_γ ∗ TokUpdated Q_γ) ∨
			(
				l_tail ↦{#1/2} #(n_in x_tail) ∗ TokE Q_γ ∗
				(
					(⌜isLast x_tail xs⌝ ∗ TokBefore Q_γ) ∨
				 	(⌜isSndLast x_tail xs⌝ ∗ TokAfter Q_γ)
				)
			)
		)
	).

Lemma queue_invariant_equiv_simple : forall l_head l_tail Q_γ,
	(queue_invariant l_head l_tail Q_γ) ∗-∗
	(queue_invariant_simple l_head l_tail Q_γ).
Proof.
	iIntros (l_head l_tail Q_γ).
	iSplit.
	- iIntros "(%xs_v & HAbst_auth & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_split & HisLL_xs & %Hconc_abst_eq & [HStatic | [HEnqueue | [HDequeue | HBoth]]])"; 
	iExists xs_v; iFrame; iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
	  + iDestruct "HStatic" as "(Hl_head & Hl_tail & HisLast & HTokne & HToknD & HTokUpdated)".
	  	iSplit; first done.
		iSplitL "Hl_head HToknD"; first (iLeft; iFrame).
		iLeft. iFrame.
	  + iDestruct "HEnqueue" as "(Hl_head & Hl_tail & [[HisLast HTokAfter] | [HisSndLast HAfter]] & HToke & HToknD)".
	    * iSplit; first done.
		  iSplitL "Hl_head HToknD"; first (iLeft; iFrame). 
		  iRight. iFrame. iLeft. iFrame.
		* iSplit; first done.
		  iSplitL "Hl_head HToknD"; first (iLeft; iFrame). 
		  iRight. iFrame. iRight. iFrame.
	  + iDestruct "HDequeue" as "(Hl_head & Hl_tail & HisLast & HTokne & HTokD & HTokUpdated)".
	    iSplit; first done.
		iSplitL "Hl_head HTokD"; first (iRight; iFrame).
		iLeft. iFrame.
	  + iDestruct "HBoth" as "(Hl_head & Hl_tail & [[HisLast HTokAfter] | [HisSndLast HAfter]] & HToke & HTokD)".
	    * iSplit; first done.
		  iSplitL "Hl_head HTokD"; first (iRight; iFrame). 
		  iRight. iFrame. iLeft. iFrame.
		* iSplit; first done.
		  iSplitL "Hl_head HTokD"; first (iRight; iFrame). 
		  iRight. iFrame. iRight. iFrame.
	- iIntros "(%xs_v & HAbst_auth & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_split & HisLL_xs & %Hconc_abst_eq & [[Hl_head HToknD] | [Hl_head HTokD]] & [(Hl_tail & HisLast & HToknE & HTokUpdated) | (Hl_tail & HTokE & [[HisLast HTokBefore] | [HisSndLast HTokAfter]])])";
	iExists xs_v; iFrame; iExists xs, xs_queue, xs_old, x_head, x_tail; eauto 10 with iFrame.
Qed.

Definition is_queue (v_q : val) (Q_γ: Qgnames) : iProp Σ :=
	∃ l_queue l_head l_tail : loc, ∃ h_lock T_lock : val,
	⌜v_q = #l_queue⌝ ∗
	l_queue ↦□ ((#l_head, #l_tail), (h_lock, T_lock)) ∗
	inv N (queue_invariant l_head l_tail Q_γ) ∗
	is_lock Q_γ.(γ_Hlock) h_lock (TokD Q_γ) ∗
	is_lock Q_γ.(γ_Tlock) T_lock (TokE Q_γ).

(* is_queue is persistent *)
Global Instance is_queue_persistent v_q Q_γ : Persistent (is_queue v_q Q_γ).
Proof. apply _. Qed.

Lemma initialize_spec:
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γ, RET v_q; is_queue v_q Q_γ ∗
						  own Q_γ.(γ_Abst) (◯F (to_agree [])) }}}.
Proof.
	iIntros (Φ) "_ HΦ".
	wp_lam.
	wp_pures.
	wp_alloc l_1_out as "Hl_1_out".
	wp_alloc l_1_in as "Hl_1_in".
	wp_pures.
	iMod (pointsto_persist with "Hl_1_in") as "#Hl_1_in".
	wp_pures.
	iMod token_alloc as (γ_D) "Hγ_D".
	wp_apply (newlock_spec with "Hγ_D").
	iIntros (h_lock γ_Hlock) "Hγ_Hlock".
	wp_let.
	iMod token_alloc as (γ_E) "Hγ_E".
	wp_apply (newlock_spec with "Hγ_E").
	iIntros (t_lock γ_Tlock) "Hγ_Tlock".
	wp_let.
	wp_alloc l_tail as "Hl_tail".
	wp_alloc l_head as "Hl_head".
	iMod token_alloc as (γ_nE) "Hγ_nE".
	iMod token_alloc as (γ_nD) "Hγ_nD".
	iMod token_alloc as (γ_Before) "Hγ_Before".
	iMod token_alloc as (γ_After) "Hγ_After".
	iMod (own_alloc (●F (to_agree []) ⋅ ◯F (to_agree []))) as (γ_Abst) "[Hγ_Abst_auth Hγ_Abst_frac]"; first by apply frac_auth_valid.
	set (Queue_gnames := {| γ_Abst := γ_Abst;
							γ_Hlock := γ_Hlock;
							γ_Tlock := γ_Tlock;
							γ_E := γ_E;
							γ_nE := γ_nE;
							γ_D := γ_D;
							γ_nD := γ_nD;
							γ_Before := γ_Before;
							γ_After := γ_After
					|}).
	iMod (inv_alloc N _ (queue_invariant l_head l_tail Queue_gnames) with "[Hγ_Abst_auth Hl_head Hl_tail Hl_1_in Hl_1_out Hγ_nE Hγ_nD Hγ_Before Hγ_After]") as "#HqueueInv".
	{
		iNext. iExists []. iFrame. iExists [(l_1_in, NONEV, l_1_out)], [], [], (l_1_in, NONEV, l_1_out), (l_1_in, NONEV, l_1_out). cbn. iSplit; first done. iSplitL "Hl_1_in Hl_1_out"; first auto. iSplit; first done.
		iLeft. iFrame. iPureIntro. by exists [].
	}
	wp_alloc l_queue as "Hl_queue".
	iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
	iApply ("HΦ" $! #l_queue Queue_gnames).
	iModIntro.
	iFrame.
	iExists l_queue, l_head, l_tail, h_lock, t_lock.
	by repeat iSplit.
Qed.

Lemma enqueue_spec v_q (v : val) (Q_γ : Qgnames) (P Q : iProp Σ) :
	□(∀xs_v, (own Q_γ.(γ_Abst) (●F (to_agree xs_v)) ∗ P
				={⊤ ∖ ↑N}=∗ own Q_γ.(γ_Abst) (●F (to_agree (v :: xs_v))) ∗ Q))
	-∗
	{{{ is_queue v_q Q_γ ∗ P}}}
		enqueue v_q v
	{{{ w, RET w; Q }}}.
Proof.
	(* CHANGE: START *)
	iIntros "#Hvs". 
	(* NOTE: The proof below should work even if the viewshift isn't persistent, as it is only used once. TODO: REMOVE THIS COMMENT WHEN YOU KNOW IF VIEWSHIFT SHOULD BE IN PRECONDITION. *)
	iIntros (Φ) "!> [(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> &
				 #Hl_queue & #Hqueue_inv & #Hh_lock & #Ht_lock) HP] HΦ".
	(* CHANGE: END *)
	wp_lam.
	wp_let.
	wp_pures.
	wp_alloc l_new_out as "Hl_new_out".
	wp_alloc l_new_in as "Hl_new_in".
	iMod (pointsto_persist with "Hl_new_in") as "#Hl_new_in".
	set x_new := (l_new_in, SOMEV v, l_new_out).
	change l_new_in with (n_in x_new).
	change l_new_out with (n_out x_new).
	change (SOMEV v) with (n_val x_new).
	wp_let.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "Ht_lock").
	iIntros "(Hlocked_γ_Tlock & HTokE)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (! #l_tail)%E.
	(* Open in Static / Dequeue *)
	iInv "Hqueue_inv" as "Hqueue_inv_open".
	(* CHANGE: START *)
	iPoseProof (queue_invariant_equiv_simple l_head l_tail Q_γ with "Hqueue_inv_open") as "Hqueue_inv_open".
	iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail & >%Heq_xs & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( [Hl_tail1 Hl_tail2] & >[%xs_fromtail %HisLast] & HToknE & HTokUpdated ) | (_ & >HTokE' & _) ])"; last by iCombine "HTokE HTokE'" gives "%H". (* Impossible: TokE *)
	(* CHANGE: END *)
	wp_load.
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	iPoseProof (isLL_chain_node [] x_tail xs_fromtail with "[HisLL_chain_xs]") as "#Hx_tail"; first by rewrite HisLast.
	iDestruct "HTokUpdated" as "[HTokBefore HTokAfter]".
	iModIntro.
	(* Close in Enqueue / Both : Before *)
	(* CHANGE: START *)
	iSplitL "Hhead Hl_tail1 HTokE HTokBefore HisLL_xs HAbst".
	(* CHANGE: END *)
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		(* CHANGE: START *)
		iExists xs_v; iFrame; iExists xs, xs_queue, xs_old, x_head, x_tail.
		(* CHANGE: END *)
		iFrame.
		do 2 (iSplit; first done).
		iRight.
		iFrame.
		iLeft.
		iFrame.
		by iExists xs_fromtail.
	}
	iClear (HisLast xs_fromtail Hconc_abst_eq xs_v Heq_xs xs xs_queue x_head xs_old) "HisLL_chain_xs".
	wp_load.
	wp_pures.
	wp_bind (#(n_out x_tail) <- #l_new_in)%E.
	(* Open in Enqueue / Both : Before *)
	iInv "Hqueue_inv" as "Hqueue_inv_open".
	(* CHANGE: START *)
	iPoseProof (queue_invariant_equiv_simple l_head l_tail Q_γ with "Hqueue_inv_open") as "Hqueue_inv_open".
	iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail' & >%Heq_xs & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( _ & _ & >HToknE' & _ ) | (>Hl_tail1 & HTokE & [[>[%xs_fromtail %HisLast] HTokBefore] | [_ >HTokAfter']]) ])"; 
	[ by iCombine "HToknE HToknE'" gives "%H" | | (* Impossible: ToknE *)
	  by iCombine "HTokAfter HTokAfter'" gives "%H" ]. (* Impossible: TokAfter *)
	(* CHANGE: END *)
	iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]".
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	rewrite HisLast.
	iAssert (▷⌜x_tail' = x_tail⌝)%I as ">->".
	{
		iNext.
		iPoseProof (isLL_chain_node [] x_tail' xs_fromtail with "[HisLL_chain_xs]") as "#Hx_tail'"; first done.
		by iApply n_in_equal.
	}
	iDestruct "HisLL_xs" as "[Hx_tail_null _]".
	wp_store.
	iMod (pointsto_persist with "Hx_tail_null") as "#Hx_tail_out".
	iDestruct "Hl_tail" as "[Hl_tail1 Hl_tail2]".
	set xs_new := x_new :: xs.
	iAssert (isLL xs_new) with "[Hl_new_out HisLL_chain_xs]" as "HisLL_xs_new".
	{
		unfold xs_new, isLL. iFrame. rewrite HisLast. unfold isLL_chain; auto.
	}
	iPoseProof (isLL_and_chain with "HisLL_xs_new") as "[HisLL_xs_new #HisLL_chain_xs_new]".
	(* CHANGE: START *)
	(* Update the abstract state using the viewshift *)
	iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[HAbst_new HQ]"; first by iFrame.
	(* CHANGE: END *)
	iModIntro.
	(* Close in Enqueue / Both: After *)
	(* CHANGE: START *)
	iSplitL "Hhead Hl_tail1 HTokE HTokAfter HisLL_xs_new HAbst_new".
	(* CHANGE: END *)
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		(* CHANGE: START *)
		iExists (v :: xs_v); iFrame; iExists xs_new, (x_new :: xs_queue), xs_old, x_head, x_tail.
		(* CHANGE: END *)
		iSplit. { iPureIntro. unfold xs_new. cbn. rewrite Heq_xs. auto. }
		iFrame.
		iSplit. { iPureIntro. simpl. f_equal. done. }
		iRight.
		iFrame.
		iRight.
		iFrame.
		iExists x_new, xs_fromtail. 
		unfold xs_new.
		by rewrite HisLast.
	}
	iClear (HisLast xs_fromtail Hconc_abst_eq xs_v Heq_xs xs_new xs xs_queue x_head xs_old Htail_eq) "HisLL_chain_xs HisLL_chain_xs_new".
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (#l_tail <- #l_new_in)%E.
	(* Open in Enqueue / Both : After *)
	iInv "Hqueue_inv" as "Hqueue_inv_open".
	(* CHANGE: START *)
	iPoseProof (queue_invariant_equiv_simple l_head l_tail Q_γ with "Hqueue_inv_open") as "Hqueue_inv_open".
	iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail'' & >%Heq_xs & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( _ & _ & >HToknE' & _ ) | (>Hl_tail1 & HTokE & [[_ >HTokBefore'] | [>(%x_new' & %xs_fromtail & %HisSndLast) HTokAfter]])])"; 
	[ by iCombine "HToknE HToknE'" gives "%H" | (* Impossible: ToknE *)
	  by iCombine "HTokBefore HTokBefore'" gives "%H" | ]. (* Impossible: TokBefore *)
	(* CHANGE: END *)
	iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]".
	rewrite dfrac_op_own.
	rewrite Qp.half_half.
	wp_store.
	iModIntro.
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	iAssert (⌜x_tail'' = x_tail⌝)%I as "->".
	{
		iPoseProof (isLL_chain_node [x_new'] x_tail'' xs_fromtail with "[HisLL_chain_xs]") as "#Hx_tail''"; first by rewrite HisSndLast.
		by iApply n_in_equal.
	}
	iAssert (⌜x_new' = x_new⌝)%I as "->".
	{
		rewrite HisSndLast.
		iPoseProof (isLL_chain_node [] x_new' (x_tail :: xs_fromtail) with "[HisLL_chain_xs]") as "#Hx_tail''"; first done.
		iDestruct "HisLL_chain_xs" as "(_ & Hx_tail_out' & _)".
		iCombine "Hx_tail_out Hx_tail_out'" gives "[_ %H]".
		by iApply n_in_equal.
	}
	(* Close in Static / Dequeue *)
	(* CHANGE: START *)
	iSplitR "HTokE Hlocked_γ_Tlock HΦ HQ".
	(* CHANGE: END *)
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		(* CHANGE: START *)
		iExists xs_v; iFrame; iExists xs, xs_queue, xs_old, x_head, x_new.
		(* CHANGE: END *)
		iSplit; first done.
		iFrame.
		iSplit; first done.
		iLeft.
		iFrame.
		by iExists (x_tail :: xs_fromtail).
	}
	wp_seq.
	wp_load.
	wp_pures.
	wp_apply (release_spec with "[$Ht_lock $HTokE $Hlocked_γ_Tlock]").
	iIntros (_).
	by iApply "HΦ".
Qed.

Lemma dequeue_spec v_q (Q_γ : Qgnames) (P : iProp Σ) (Q : val -> iProp Σ):
	□(∀xs_v, (own Q_γ.(γ_Abst) (●F (to_agree xs_v)) ∗ P
				={⊤ ∖ ↑N}=∗
		      	(( ⌜xs_v = []⌝ ∗ own Q_γ.(γ_Abst) (●F (to_agree (xs_v))) ∗ Q NONEV) ∨
				(∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗ own Q_γ.(γ_Abst) (●F (to_agree (xs_v'))) ∗ Q (SOMEV x_v)))
			)
	 )
	-∗
	{{{ is_queue v_q Q_γ ∗ P}}}
		dequeue v_q
	{{{ v, RET v; Q v }}}.
Proof.
	Admitted.

End proofs.
