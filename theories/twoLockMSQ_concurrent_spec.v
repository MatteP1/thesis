From stdpp Require Import countable.
From iris.algebra Require Import excl.
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

Let N := nroot .@ "twoLockMSQ".

(* ===== Concurrent Specification for Two-lock M&S Queue ===== *)

(* Ghost variable names *)
Record Qgnames := {γ_Hlock 	: gname;
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

Definition queue_invariant (Ψ : val -> iProp Σ) (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: (loc * val * loc)), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	All xs_v Ψ ∗
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

Definition queue_invariant_simple (Ψ : val -> iProp Σ) (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: (loc * val * loc)), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	All xs_v Ψ ∗
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

Lemma queue_invariant_equiv_simple : forall Ψ l_head l_tail Q_γ,
	(queue_invariant Ψ l_head l_tail Q_γ) ∗-∗
	(queue_invariant_simple Ψ l_head l_tail Q_γ).
Proof.
	iIntros (Ψ l_head l_tail Q_γ).
	iSplit.
	- iIntros "(%xs_v & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_split & HisLL_xs & %Hconc_abst_eq & HAll & [H_Static | [H_Enqueue | [H_Dequeue | H_Both]]])"; 
	iExists xs_v, xs, xs_queue, xs_old, x_head, x_tail; iFrame.
	  + iDestruct "H_Static" as "(Hl_head & Hl_tail & HisLast & HTokne & HToknD & HTokUpdated)".
	  	iSplit; first done.
		iSplitL "Hl_head HToknD"; first (iLeft; iFrame).
		iLeft. iFrame.
	  + iDestruct "H_Enqueue" as "(Hl_head & Hl_tail & [[HisLast HTokAfter] | [HisSndLast HAfter]] & HToke & HToknD)".
	    * iSplit; first done.
		  iSplitL "Hl_head HToknD"; first (iLeft; iFrame). 
		  iRight. iFrame. iLeft. iFrame.
		* iSplit; first done.
		  iSplitL "Hl_head HToknD"; first (iLeft; iFrame). 
		  iRight. iFrame. iRight. iFrame.
	  + iDestruct "H_Dequeue" as "(Hl_head & Hl_tail & HisLast & HTokne & HTokD & HTokUpdated)".
	    iSplit; first done.
		iSplitL "Hl_head HTokD"; first (iRight; iFrame).
		iLeft. iFrame.
	  + iDestruct "H_Both" as "(Hl_head & Hl_tail & [[HisLast HTokAfter] | [HisSndLast HAfter]] & HToke & HTokD)".
	    * iSplit; first done.
		  iSplitL "Hl_head HTokD"; first (iRight; iFrame). 
		  iRight. iFrame. iLeft. iFrame.
		* iSplit; first done.
		  iSplitL "Hl_head HTokD"; first (iRight; iFrame). 
		  iRight. iFrame. iRight. iFrame.
	- iIntros "(%xs_v & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_split & HisLL_xs & %Hconc_abst_eq & HAll & [[Hl_head HToknD] | [Hl_head HTokD]] & [(Hl_tail & HisLast & HToknE & HTokUpdated) | (Hl_tail & HTokE & [[HisLast HTokBefore] | [HisSndLast HTokAfter]])])";
	iExists xs_v, xs, xs_queue, xs_old, x_head, x_tail; eauto 10 with iFrame.
Qed.

Definition is_queue (Ψ : val -> iProp Σ) (v_q : val) (Q_γ: Qgnames) : iProp Σ :=
	∃ l_queue l_head l_tail : loc, ∃ H_lock T_lock : val,
	⌜v_q = #l_queue⌝ ∗
	l_queue ↦□ ((#l_head, #l_tail), (H_lock, T_lock)) ∗
	inv N (queue_invariant Ψ l_head l_tail Q_γ) ∗
	is_lock Q_γ.(γ_Hlock) H_lock (TokD Q_γ) ∗
	is_lock Q_γ.(γ_Tlock) T_lock (TokE Q_γ).

(* is_queue is persistent *)
Global Instance is_queue_persistent Ψ v_q Q_γ : Persistent (is_queue Ψ v_q Q_γ).
Proof. apply _. Qed.

Lemma initialize_spec (Ψ : val -> iProp Σ):
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γ, RET v_q; is_queue Ψ v_q Q_γ }}}.
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
	iIntros (hlock γ_Hlock) "Hγ_Hlock".
	wp_let.
	iMod token_alloc as (γ_E) "Hγ_E".
	wp_apply (newlock_spec with "Hγ_E").
	iIntros (tlock γ_Tlock) "Hγ_Tlock".
	wp_let.
	wp_alloc l_tail as "Hl_tail".
	wp_alloc l_head as "Hl_head".
	iMod token_alloc as (γ_nE) "Hγ_nE".
	iMod token_alloc as (γ_nD) "Hγ_nD".
	iMod token_alloc as (γ_Before) "Hγ_Before".
	iMod token_alloc as (γ_After) "Hγ_After".
	set (Queue_gnames := {| γ_Hlock := γ_Hlock;
							γ_Tlock := γ_Tlock;
							γ_E := γ_E;
							γ_nE := γ_nE;
							γ_D := γ_D;
							γ_nD := γ_nD;
							γ_Before := γ_Before;
							γ_After := γ_After
					|}).
	iMod (inv_alloc N _ (queue_invariant Ψ l_head l_tail Queue_gnames) with "[Hl_head Hl_tail Hl_1_in Hl_1_out Hγ_nE Hγ_nD Hγ_Before Hγ_After]") as "#HqueueInv".
	{
		iNext. iExists [], [(l_1_in, NONEV, l_1_out)], [], [], (l_1_in, NONEV, l_1_out), (l_1_in, NONEV, l_1_out). cbn. iSplit; first done. iSplitL "Hl_1_in Hl_1_out"; first auto. do 2 (iSplit; first done).
		iLeft. iFrame. iPureIntro. by exists [].
	}
	wp_alloc l_queue as "Hl_queue".
	iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
	iApply ("HΦ" $! #l_queue Queue_gnames).
	iModIntro.
	iExists l_queue, l_head, l_tail, hlock, tlock.
	by repeat iSplit.
Qed.

Lemma enqueue_spec v_q Ψ (v : val) (Q_γ : Qgnames) :
	{{{ is_queue Ψ v_q Q_γ ∗ Ψ v }}}
		enqueue v_q v
	{{{ w, RET w; True }}}.
Proof.
	iIntros (Φ) "[(%l_queue & %l_head & %l_tail & %H_lock & %T_lock & -> &
				 #Hl_queue & #H_queue_inv & #H_hlock & #H_tlock) HΨ_v] HΦ".
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
	wp_apply (acquire_spec with "H_tlock").
	iIntros "(Hlocked_γ_Tlock & HTokE)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (! #l_tail)%E.
	(* Open in Static / Dequeue *)
	iInv "H_queue_inv" as "H_queue_inv_open".
	iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail Q_γ with "H_queue_inv_open") as "H_queue_inv_open".
	iDestruct "H_queue_inv_open" as "(%xs_v & %xs & %xs_queue & %xs_old & %x_head & %x_tail & >%H_eq_xs & HisLL_xs & >%Hconc_abst_eq & HAll_xs & H_head & [ ( [Hl_tail1 Hl_tail2] & >[%xs_fromtail %H_isLast] & HToknE & HTokUpdated ) | (_ & >HTokE2 & _) ])"; last by iCombine "HTokE HTokE2" gives "%H". (* Impossible: TokE *)
	wp_load.
	iModIntro.
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	iPoseProof (isLL_chain_node [] x_tail xs_fromtail with "[HisLL_chain_xs]") as "#Hx_tail"; first by rewrite H_isLast.
	iDestruct "HTokUpdated" as "[HTokBefore HTokAfter]".
	(* Close in Enqueue / Both : Before *)
	iSplitL "H_head Hl_tail1 HTokE HTokBefore HisLL_xs HAll_xs".
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists xs_v, xs, xs_queue, xs_old, x_head, x_tail.
		iFrame.
		do 2 (iSplit; first done).
		iRight.
		iFrame.
		iLeft.
		iFrame.
		by iExists xs_fromtail.
	}
	wp_load.
	wp_pures.
	wp_bind (#(n_out x_tail) <- #l_new_in)%E.
	(* Open in Enqueue / Both : Before *)
	iInv "H_queue_inv" as "H_queue_inv_open".
	iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail Q_γ with "H_queue_inv_open") as "H_queue_inv_open".
	iDestruct "H_queue_inv_open" as "(%xs_v_2 & %xs_2 & %xs_queue_2 & %xs_old_2 & %x_head_2 & %x_tail_2 & >%H_eq_xs_2 & HisLL_xs_2 & >%Hconc_abst_eq_2 & HAll_xs_2 & H_head & [ ( _ & _ & >HToknE2 & _ ) | (>Hl_tail1 & HTokE & [[>[%xs_fromtail_2 %H_isLast_2] HTokBefore] | [_ >HTokAfter2]]) ])"; 
	[ by iCombine "HToknE HToknE2" gives "%H" | | (* Impossible: ToknE *)
	  by iCombine "HTokAfter HTokAfter2" gives "%H" ]. (* Impossible: TokAfter *)
	iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]".
	iPoseProof (isLL_and_chain with "HisLL_xs_2") as "[HisLL_xs_2 #HisLL_chain_xs_2]".
	rewrite H_isLast_2.
	iAssert (▷⌜x_tail_2 = x_tail⌝)%I as ">->".
	{
		iNext.
		iPoseProof (isLL_chain_node [] x_tail_2 xs_fromtail_2 with "[HisLL_chain_xs_2]") as "#Hx_tail_2"; first by rewrite H_isLast.
		iApply n_in_equal; done.
	}
	iDestruct "HisLL_xs_2" as "[Hx_tail_null _]".
	wp_store.
	iMod (pointsto_persist with "Hx_tail_null") as "#Hx_tail_out".
	iDestruct "Hl_tail" as "[Hl_tail1 Hl_tail2]".
	iModIntro.
	set xs_new := x_new :: xs_2.
	iAssert (isLL xs_new) with "[Hl_new_out HisLL_chain_xs_2]" as "HisLL_xs_new".
	{
		unfold xs_new, isLL. iFrame. rewrite H_isLast_2. unfold isLL_chain; auto.
	}
	iPoseProof (isLL_and_chain with "HisLL_xs_new") as "[HisLL_xs_new #HisLL_chain_xs_new]".
	(* Close in Enqueue / Both: After *)
	iSplitL "H_head Hl_tail1 HTokE HTokAfter HisLL_xs_new HAll_xs_2 HΨ_v".
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists (v :: xs_v_2), xs_new, (x_new :: xs_queue_2), xs_old_2, x_head_2, x_tail.
		iSplit. { iPureIntro. unfold xs_new. cbn. rewrite H_eq_xs_2. auto. }
		iFrame.
		iSplit. { iPureIntro. simpl. f_equal. done. }
		iRight.
		iFrame.
		iRight.
		iFrame.
		iExists x_new, xs_fromtail_2. 
		unfold xs_new.
		by rewrite H_isLast_2.
	}
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (#l_tail <- #l_new_in)%E.
	(* Open in Enqueue / Both : After *)
	iInv "H_queue_inv" as "H_queue_inv_open".
	iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail Q_γ with "H_queue_inv_open") as "H_queue_inv_open".
	iDestruct "H_queue_inv_open" as "(%xs_v_3 & %xs_3 & %xs_queue_3 & %xs_old_3 & %x_head_3 & %x_tail_3 & >%H_eq_xs_3 & HisLL_xs_3 & >%Hconc_abst_eq_3 & HAll_xs_3 & H_head & [ ( _ & _ & >HToknE2 & _ ) | (>Hl_tail1 & HTokE & [[_ >HTokBefore2] | [>(%x_new_2 & %xs_fromtail_3 & %H_isSndLast) HTokAfter]])])"; 
	[ by iCombine "HToknE HToknE2" gives "%H" | (* Impossible: ToknE *)
	  by iCombine "HTokBefore HTokBefore2" gives "%H" | ]. (* Impossible: TokBefore *)
	iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq2]".
	rewrite dfrac_op_own.
	rewrite Qp.half_half.
	wp_store.
	iModIntro.
	iPoseProof (isLL_and_chain with "HisLL_xs_3") as "[HisLL_xs_3 #HisLL_chain_xs_3]".
	iAssert (⌜x_tail_3 = x_tail⌝)%I as "->".
	{
		iApply (isLL_chain_agree x_tail_3 x_tail [x_new_2] [] [] []).
		- by simplify_eq.
		- rewrite H_isSndLast. iPoseProof (isLL_chain_split [x_new_2 ; x_tail_3] xs_fromtail_3 with "HisLL_chain_xs_3") as "[Hgoal _]". done.
		- rewrite H_isLast. iPoseProof (isLL_chain_split [x_tail] xs_fromtail with "HisLL_chain_xs") as "[Hgoal _]". done.
	}
	iAssert (⌜x_new_2 = x_new⌝)%I as "->".
	{
		iApply (isLL_chain_agree_next x_tail x_new_2 x_new [] [] [] []).
		- rewrite H_isSndLast. iPoseProof (isLL_chain_split [x_new_2; x_tail] xs_fromtail_3 with "HisLL_chain_xs_3") as "[Hgoal _]". done.
		- unfold xs_new. rewrite H_isLast_2. iPoseProof (isLL_chain_split [x_new; x_tail] xs_fromtail_2 with "HisLL_chain_xs_new") as "[Hgoal _]". done.
	}
	(* Close in Static / Dequeue *)
	iSplitR "HTokE Hlocked_γ_Tlock HΦ".
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists xs_v_3, xs_3, xs_queue_3, xs_old_3, x_head_3, x_new.
		iSplit; first done.
		iFrame.
		iSplit; first done.
		iLeft.
		iFrame.
		by iExists (x_tail :: xs_fromtail_3).
	}
	wp_seq.
	wp_load.
	wp_pures.
	wp_apply (release_spec with "[$H_tlock $HTokE $Hlocked_γ_Tlock]").
	done.
Qed.

Lemma dequeue_spec v_q Ψ (Q_γ : Qgnames) :
	{{{ is_queue Ψ v_q Q_γ }}}
		dequeue v_q
	{{{ v, RET v; ⌜v = NONEV⌝ ∨ (∃ x_v, ⌜v = SOMEV x_v⌝ ∗ Ψ x_v) }}}.
Proof.
	iIntros (Φ) "(%l_queue & %l_head & %l_tail & %H_lock & %T_lock & -> &
				 #Hl_queue & #H_queue_inv & #H_hlock & #H_tlock) HΦ".
	wp_lam.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "H_hlock").
	iIntros "(Hlocked_γ_Hlock & HTokD)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (! #l_head)%E.
	(* Open in Static / Enqueue *)
	iInv "H_queue_inv" as "H_queue_inv_open".
	iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail Q_γ with "H_queue_inv_open") as "H_queue_inv_open".
	iDestruct "H_queue_inv_open" as "(%xs_v & %xs & %xs_queue & %xs_old & %x_head & %x_tail & >%H_eq_xs & H_isLL_xs & >%Hconc_abst_eq & HAll_xs & [ [Hl_head HToknD] | [Hl_head >HTokD2] ] & H_tail)"; 
	last by iCombine "HTokD HTokD2" gives "%H". (* Impossible: TokD*)
	wp_load.
	iModIntro.
	iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
	iPoseProof (isLL_and_chain with "H_isLL_xs") as "[H_isLL_xs #H_isLL_chain_xs_1]".
	(* Close in Dequeue / Both *)
	iSplitL "Hl_head2 HTokD H_tail H_isLL_xs HAll_xs".
	{
		iNext. iApply queue_invariant_equiv_simple.
		iExists xs_v, xs, xs_queue, xs_old, x_head, x_tail. iFrame.
		do 2 (iSplit; first done). iRight. done.
	}
	wp_let.
	subst.
	iPoseProof (isLL_chain_node with "H_isLL_chain_xs_1") as "H_x_head_in".
	wp_load.
	wp_pures.
	wp_bind (! #(n_out x_head))%E.
	(* Open in Dequeue / Both *)
	iInv "H_queue_inv" as "H_queue_inv_open".
	iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail Q_γ with "H_queue_inv_open") as "H_queue_inv_open".
	iDestruct "H_queue_inv_open" as "(%xs_v_2 & %xs_2 & %xs_queue_2 & %xs_old_2 & %x_head_2 & %x_tail_2 & >%H_eq_xs_2 & H_isLL_xs_2 & >%Hconc_abst_eq_2 & HAll_xs_2 & [ [Hl_head >HToknD2] | [>Hl_head2 HTokD] ] & H_tail)";
	first by iCombine "HToknD HToknD2" gives "%H". (* Impossible: ToknD*)
	iPoseProof (isLL_and_chain with "H_isLL_xs_2") as "[H_isLL_xs_2 #HisLL_chain_xs_2]".
	iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq2]".
	iAssert (▷⌜x_head_2 = x_head⌝)%I as ">->".
	{
		iNext.
		simplify_eq.
		by iApply (isLL_chain_agree x_head_2 x_head xs_queue_2 xs_old_2 xs_queue xs_old).
	}
	subst.
	(* Case analysis: Is queue empty? *)
	destruct xs_queue_2 as [| x_tail_2_2 xs_queue_2'].
	- (* Queue is empty. *)
	  iDestruct "H_isLL_xs_2" as "[H_x_head_out _]".
	  wp_load.
	  iModIntro.
	  (* Close in Static / Enqueue *)
	  iSplitL "Hl_head HToknD H_tail H_x_head_out".
	  {
		iNext. iApply queue_invariant_equiv_simple.
		iExists [], ([] ++ [x_head] ++ xs_old_2), [], xs_old_2, x_head, x_tail_2.
		iFrame. do 3 (iSplit; first done). iLeft. iFrame.
		rewrite dfrac_op_own. rewrite Qp.half_half. done.
	  }
	  wp_let.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_apply (release_spec with "[$H_hlock $HTokD $Hlocked_γ_Hlock]").
	  iIntros (_).
	  wp_seq.
	  iModIntro.
	  iApply "HΦ".
	  by iLeft.
	- (* Queue is non-empty*)
	  destruct (exists_first (x_tail_2_2 :: xs_queue_2')) as [x_head_next [xs_rest Hxs_rest_eq]]; first done.
	  rewrite Hxs_rest_eq.
	  iAssert (▷(isLL_chain [x_head_next; x_head]))%I as "H_isLL_chain_x_head_next".
	  {
		iNext. iClear "H_isLL_chain_xs_1". rewrite <- app_assoc.
		iDestruct (isLL_chain_split with "HisLL_chain_xs_2") as "[_ H]".
		iClear "HisLL_chain_xs_2".
		rewrite -> app_assoc.
		iDestruct (isLL_chain_split with "H") as "[H' _]".
		done.
	  }
	  iDestruct "H_isLL_chain_x_head_next" as "(H_x_head_next_in & H_x_head_next_out & _)".
	  wp_load.
	  iModIntro.
	  iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
	  (* Close in Dequeue / Both *)
	  iSplitL "Hl_head2 H_isLL_xs_2 H_tail HTokD HAll_xs_2".
	  {
		iNext. iApply queue_invariant_equiv_simple.
		iExists xs_v_2, ((xs_rest ++ [x_head_next]) ++ [x_head] ++ xs_old_2), (xs_rest ++ [x_head_next]), xs_old_2, x_head, x_tail_2.
		iFrame. iSplit; first done. iSplit; first by rewrite <- Hxs_rest_eq.  iRight. done.
	  }
	  wp_let.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_bind (#l_head <- #(n_in x_head_next))%E.
	  (* Open in Dequeue / Both *)
	  iInv "H_queue_inv" as "H_queue_inv_open".
	  iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail Q_γ with "H_queue_inv_open") as "H_queue_inv_open".
	  iDestruct "H_queue_inv_open" as "(%xs_v_3 & %xs_3 & %xs_queue_3 & %xs_old_3 & %x_head_3 & %x_tail_3 & >%H_eq_xs_3 & H_isLL_xs_3 & >%Hconc_abst_eq_3 & HAll_xs_3 & [ [Hl_head >HToknD2] | [>Hl_head2 HTokD] ] & H_tail)";
	  first by iCombine "HToknD HToknD2" gives "%H". (* Impossible ToknD *)
	  iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq3]".
	  rewrite dfrac_op_own.
	  rewrite Qp.half_half.
	  wp_store.
	  iModIntro.
	  iPoseProof (isLL_and_chain with "H_isLL_xs_3") as "[H_isLL_xs_3 #H_isLL_chain_xs_3]".
	  iAssert (⌜x_head_3 = x_head⌝)%I as "->".
	  {
		iApply (isLL_chain_agree x_head_3 x_head xs_queue_3 xs_old_3 xs_queue xs_old); by simplify_eq.
	  }
	  subst.
	  (* Sync up xs_queue_3 with xs_queue_2 *)
	  destruct xs_queue_3 as [|x_tail_3_2 xs_queue_3'].
	  { (* Impossible case. xs_queue_3 must contain at least one element. *)
		iDestruct "H_isLL_xs_3" as "[H_x_head_3_null _]".
		iCombine "H_x_head_3_null H_x_head_next_out" gives "[_ %Hcontra]".
		simplify_eq.
	  }
	  destruct (exists_first (x_tail_3_2 :: xs_queue_3')) as [x_head_next_3 [xs_rest' Hxs_rest_eq']]; first done.
	  rewrite Hxs_rest_eq'.
	  rewrite <- app_assoc. rewrite <- app_assoc.
	  iAssert (⌜x_head_next = x_head_next_3⌝)%I as "->"; first by iApply isLL_chain_agree_next.
	  destruct xs_v_3 as [|x_v xs'_v_3]; 
	  	first inversion Hconc_abst_eq_3. (* Impossible case. xs_v_3 must contain at least one element. *)
	  destruct (exists_first (x_v :: xs'_v_3)) as [x_head_next_val [xs_val_rest Hxs_val_rest_eq]]; first done.
	  rewrite Hxs_val_rest_eq in Hconc_abst_eq_3.
	  rewrite Hxs_val_rest_eq.
	  rewrite Hxs_rest_eq' in Hconc_abst_eq_3.
	  rewrite (proj_val_split xs_rest' [x_head_next_3]) in Hconc_abst_eq_3.
	  rewrite (wrap_some_split xs_val_rest [x_head_next_val]) in Hconc_abst_eq_3.
	  simpl in Hconc_abst_eq_3.
	  apply (list_last_eq (proj_val xs_rest') (wrap_some xs_val_rest) (n_val x_head_next_3) (InjRV x_head_next_val)) in Hconc_abst_eq_3 as [Hxs_rest_val_eq Hx_head_next_eq].
	  iPoseProof (All_split with "HAll_xs_3") as "[HAll_xs_val_rest [Hx_head_next_val_Ψ _]]".
	  (* Close in Static / Enqueue *)
	  iSplitL "Hl_head H_tail HToknD H_isLL_xs_3 HAll_xs_val_rest".
	  {
		iNext. iApply queue_invariant_equiv_simple.
		iExists xs_val_rest, (xs_rest' ++ [x_head_next_3] ++ [x_head] ++ xs_old_3), xs_rest', ([x_head] ++ xs_old_3), x_head_next_3, x_tail_3.
		iFrame. iSplit; first done.
		iSplit; first done.
		iLeft.
		iFrame.
	  }
	  wp_seq.
	  wp_load.
	  wp_pures.
	  wp_apply (release_spec with "[$H_hlock $HTokD $Hlocked_γ_Hlock]").
	  iIntros (_).
	  wp_seq.
	  iModIntro.
	  iApply "HΦ".
	  iRight.
	  iExists x_head_next_val.
	  by iSplit.
Qed.

End proofs.