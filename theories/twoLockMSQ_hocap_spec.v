From stdpp Require Import countable.
From iris.algebra Require Import list agree lib.frac_auth.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants token.
From MSQueue Require Import twoLockMSQ_impl.
From MSQueue Require Import MSQ_common.

Local Existing Instance spin_lock.

Section proofs.

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!tokenG Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Variable N : namespace.
Notation Ni := (N .@ "internal").

(* ===== Hocap Specification for Two-lock M&S Queue ===== *)

(* ----- Ghost variable names ----- *)
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

(* ----- Tokens ----- *)
Definition TokHlock (g : Qgnames) := token g.(γ_Hlock).
Definition TokTlock (g : Qgnames) := token g.(γ_Tlock).
Definition TokE (g : Qgnames) := token g.(γ_E).
Definition ToknE (g : Qgnames) := token g.(γ_nE).
Definition TokD (g : Qgnames) := token g.(γ_D).
Definition ToknD (g : Qgnames) := token g.(γ_nD).
Definition TokBefore (g : Qgnames) := token g.(γ_Before).
Definition TokAfter (g : Qgnames) := token g.(γ_After).
Definition TokUpdated (g : Qgnames) := ((TokBefore g) ∗ (TokAfter g))%I.

(* ------ Notation for Abstract State of Queue ------ *)
Notation "Q_γ ⤇● xs_v" := (own Q_γ.(γ_Abst) (●F (to_agree xs_v)))
	(at level 20, format "Q_γ  ⤇●  xs_v") : bi_scope.
Notation "Q_γ ⤇◯ xs_v" := (own Q_γ.(γ_Abst) (◯F (to_agree xs_v)))
	(at level 20, format "Q_γ  ⤇◯  xs_v") : bi_scope.
Notation "Q_γ ⤇[ q ] xs_v" := (own Q_γ.(γ_Abst) (◯F{ q } (to_agree xs_v)))
	(at level 20, format "Q_γ  ⤇[ q ]  xs_v") : bi_scope.

(* ----- Queue Invariants ------ *)
Definition queue_invariant (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, Q_γ ⤇● xs_v ∗ (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: node), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	(* Relation between concrete and abstract state *)
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
	∃ xs_v, Q_γ ⤇● xs_v ∗ (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: node), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	(* Relation between concrete and abstract state *)
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

Lemma queue_invariant_equiv_simple : ∀ l_head l_tail Q_γ,
	(queue_invariant l_head l_tail Q_γ) ∗-∗
	(queue_invariant_simple l_head l_tail Q_γ).
Proof.
	iIntros (l_head l_tail Q_γ).
	iSplit.
	- iIntros "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_eq & HisLL_xs & %Hconc_abst_eq & [HStatic | [HEnqueue | [HDequeue | HBoth]]])";
	iExists xs_v; iFrame "HAbst"; iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
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
	- iIntros "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_eq & HisLL_xs & %Hconc_abst_eq & [[Hl_head HToknD] | [Hl_head HTokD]] & [(Hl_tail & HisLast & HToknE & HTokUpdated) | (Hl_tail & HTokE & [[HisLast HTokBefore] | [HisSndLast HTokAfter]])])";
	iExists xs_v; iFrame "HAbst"; iExists xs, xs_queue, xs_old, x_head, x_tail; eauto 10 with iFrame.
Qed.

(* ----- The 'is_queue' Predicate ------ *)
Definition is_queue (v_q : val) (Q_γ: Qgnames) : iProp Σ :=
	∃ l_queue l_head l_tail : loc, ∃ h_lock T_lock : val,
	⌜v_q = #l_queue⌝ ∗
	l_queue ↦□ ((#l_head, #l_tail), (h_lock, T_lock)) ∗
	inv Ni (queue_invariant l_head l_tail Q_γ) ∗
	is_lock Q_γ.(γ_Hlock) h_lock (TokD Q_γ) ∗
	is_lock Q_γ.(γ_Tlock) T_lock (TokE Q_γ).

(* is_queue is persistent *)
Global Instance is_queue_persistent v_q Q_γ : Persistent (is_queue v_q Q_γ).
Proof. apply _. Qed.


(* ----- Specification for Initialise ----- *)
Lemma initialize_spec:
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γ, RET v_q; is_queue v_q Q_γ ∗ Q_γ ⤇◯ [] }}}.
Proof.
	iIntros (Φ) "_ HΦ".
	wp_lam.
	wp_pures.
	wp_alloc l_1_out as "Hx1_to_none".
	wp_alloc l_1_in as "Hx1_node".
	wp_pures.
	set x_1 := (l_1_in, NONEV, l_1_out).
	change l_1_in with (n_in x_1).
	change l_1_out with (n_out x_1).
	pose proof (eq_refl : NONEV = n_val x_1) as Hx1_val.
	rewrite {2}Hx1_val.
	clearbody x_1.
	iMod (pointsto_persist with "Hx1_node") as "#Hx1_node".
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
	(* CHANGE: START: γ_Abst *)
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
	iMod (inv_alloc Ni _ (queue_invariant l_head l_tail Queue_gnames) with "[Hγ_Abst_auth Hl_head Hl_tail Hx1_to_none Hγ_nE Hγ_nD Hγ_Before Hγ_After]") as "#HqueueInv".
	(* CHANGE: END *)
	{
		iNext.
		(* CHANGE: START: framing instead of splitting *)
		iExists []; iFrame "Hγ_Abst_auth".
		(* CHANGE: END *)
		iExists [x_1], [], [], x_1, x_1; iFrame.
		do 3 (iSplit; first done).
		iLeft.
		iFrame.
		by iExists [].
	}
	wp_alloc l_queue as "Hl_queue".
	iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
	iApply ("HΦ" $! #l_queue Queue_gnames).
	iModIntro.
	iFrame "Hγ_Abst_frac".
	iExists l_queue, l_head, l_tail, h_lock, t_lock.
	by repeat iSplit.
Qed.

(* ----- Specification for Enqueue ----- *)
Lemma enqueue_spec v_q (v : val) (Q_γ : Qgnames) (P Q : iProp Σ) :
	□(∀xs_v, (Q_γ ⤇● xs_v ∗ P ={⊤ ∖ ↑Ni}=∗ ▷ (Q_γ ⤇● (v :: xs_v) ∗ Q))) -∗
	{{{ is_queue v_q Q_γ ∗ P}}}
		enqueue v_q v
	{{{ w, RET w; Q }}}.
Proof.
	(* CHANGE: START: intro viewshift *)
	iIntros "#Hvs".
	iIntros (Φ) "!> [(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> &
				 #Hl_queue & #Hqueue_inv & #Hh_lock & #Ht_lock) HP] HΦ".
	(* CHANGE: END *)
	wp_lam.
	wp_let.
	wp_pures.
	wp_alloc l_new_out as "Hxnew_to_none".
	wp_alloc l_new_in as "Hxnew_node".
	set x_new := (l_new_in, SOMEV v, l_new_out).
	change l_new_in with (n_in x_new).
	change l_new_out with (n_out x_new).
	change (SOMEV v) with (n_val x_new).
	pose proof (eq_refl : SOMEV v = n_val x_new) as Hxnew_val.
	clearbody x_new.
	iMod (pointsto_persist with "Hxnew_node") as "#Hxnew_node".
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
	(* CHANGE: START: remove Ψ, HAll -> HAbst *)
	iPoseProof (queue_invariant_equiv_simple l_head l_tail Q_γ with "Hqueue_inv_open") as "Hqueue_inv_open".
	iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( [Hl_tail1 Hl_tail2] & >[%xs_fromtail %HisLast] & HToknE & HTokUpdated ) | (_ & >HTokE' & _) ])"; last by iCombine "HTokE HTokE'" gives "%H". (* Impossible: TokE *)
	(* CHANGE: END *)
	wp_load.
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	iPoseProof (isLL_chain_node [] x_tail xs_fromtail with "[HisLL_chain_xs]") as "#Hxtail_node"; first by rewrite HisLast.
	iDestruct "HTokUpdated" as "[HTokBefore HTokAfter]".
	iModIntro.
	(* Close in Enqueue / Both : Before *)
	(* CHANGE: START: HAll -> HAbst *)
	iSplitL "Hhead Hl_tail1 HTokE HTokBefore HisLL_xs HAbst".
	(* CHANGE: END *)
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists xs_v; iFrame "HAbst".
		iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
		do 2 (iSplit; first done).
		iRight.
		iFrame.
		iLeft.
		iFrame.
		by iExists xs_fromtail.
	}
	iClear (HisLast xs_fromtail Hconc_abst_eq xs_v Hxs_eq xs xs_queue x_head xs_old) "HisLL_chain_xs".
	wp_load.
	wp_pures.
	wp_bind (#(n_out x_tail) <- #(n_in x_new))%E.
	(* Open in Enqueue / Both : Before *)
	iInv "Hqueue_inv" as "Hqueue_inv_open".
	(* CHANGE: START: remove Ψ, HAll -> HAbst *)
	iPoseProof (queue_invariant_equiv_simple l_head l_tail Q_γ with "Hqueue_inv_open") as "Hqueue_inv_open".
	iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail' & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( _ & _ & >HToknE' & _ ) | (>Hl_tail1 & HTokE & [[>[%xs_fromtail %HisLast] HTokBefore] | [_ >HTokAfter']]) ])";
	[ by iCombine "HToknE HToknE'" gives "%H" | | (* Impossible: ToknE *)
	  by iCombine "HTokAfter HTokAfter'" gives "%H" ]. (* Impossible: TokAfter *)
	(* CHANGE: END *)
	iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]".
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	rewrite HisLast.
	iAssert (▷⌜x_tail' = x_tail⌝)%I as ">->".
	{
		iNext.
		iPoseProof (isLL_chain_node [] x_tail' xs_fromtail with "[HisLL_chain_xs]") as "#Hxtail'_node"; first done.
		by iApply n_in_equal.
	}
	iDestruct "HisLL_xs" as "[Hxtail_to_none _]".
	wp_store.
	iMod (pointsto_persist with "Hxtail_to_none") as "#Hxtail_to_xnew".
	iDestruct "Hl_tail" as "[Hl_tail1 Hl_tail2]".
	set xs_new := x_new :: xs.
	iAssert (isLL xs_new) with "[Hxnew_to_none HisLL_chain_xs]" as "HisLL_xs_new".
	{
		rewrite /xs_new /isLL HisLast.
		iFrame.
		unfold isLL_chain; auto.
	}
	iPoseProof (isLL_and_chain with "HisLL_xs_new") as "[HisLL_xs_new #HisLL_chain_xs_new]".
	(* CHANGE: START: viewshift *)
	(* Update the abstract state using the viewshift *)
	iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[HAbst_new HQ]"; first by iFrame.
	(* CHANGE: END *)
	iModIntro.
	(* Close in Enqueue / Both: After *)
	(* CHANGE: START: HAll + HΨ_v -> HAbst_new *)
	iSplitL "Hhead Hl_tail1 HTokE HTokAfter HisLL_xs_new HAbst_new".
	(* CHANGE: END *)
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists (v :: xs_v); iFrame "HAbst_new".
		iExists xs_new, (x_new :: xs_queue), xs_old, x_head, x_tail.
		iSplit. { by rewrite /xs_new Hxs_eq. }
		iFrame.
		iSplit. { iPureIntro. simpl. f_equal; done. }
		iRight.
		iFrame.
		iRight.
		iFrame.
		iExists x_new, xs_fromtail.
		by rewrite /xs_new HisLast.
	}
	iClear (HisLast xs_fromtail Hconc_abst_eq xs_v Hxs_eq xs_new xs xs_queue x_head xs_old Htail_eq) "HisLL_chain_xs HisLL_chain_xs_new".
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (#l_tail <- #(n_in x_new))%E.
	(* Open in Enqueue / Both : After *)
	iInv "Hqueue_inv" as "Hqueue_inv_open".
	(* CHANGE: START: remove Ψ, HAll -> HAbst *)
	iPoseProof (queue_invariant_equiv_simple l_head l_tail Q_γ with "Hqueue_inv_open") as "Hqueue_inv_open".
	iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail'' & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( _ & _ & >HToknE' & _ ) | (>Hl_tail1 & HTokE & [[_ >HTokBefore'] | [>(%x_new' & %xs_fromtail & %HisSndLast) HTokAfter]])])";
	[ by iCombine "HToknE HToknE'" gives "%H" | (* Impossible: ToknE *)
	  by iCombine "HTokBefore HTokBefore'" gives "%H" | ]. (* Impossible: TokBefore *)
	(* CHANGE: END *)
	iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]".
	rewrite dfrac_op_own Qp.half_half.
	wp_store.
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	iAssert (⌜x_tail'' = x_tail⌝)%I as "->".
	{
		iPoseProof (isLL_chain_node [x_new'] x_tail'' xs_fromtail with "[HisLL_chain_xs]") as "#Hxtail''_node"; first by rewrite HisSndLast.
		by iApply n_in_equal.
	}
	iAssert (⌜x_new' = x_new⌝)%I as "->".
	{
		rewrite HisSndLast.
		iPoseProof (isLL_chain_node [] x_new' (x_tail :: xs_fromtail) with "[HisLL_chain_xs]") as "#Hxnew'_node"; first done.
		iDestruct "HisLL_chain_xs" as "(_ & Hxtail_to_xnew' & _)".
		iCombine "Hxtail_to_xnew Hxtail_to_xnew'" gives "[_ %H]".
		by iApply n_in_equal.
	}
	iModIntro.
	(* Close in Static / Dequeue *)
	(* CHANGE: START: save HQ *)
	iSplitR "HTokE Hlocked_γ_Tlock HΦ HQ".
	(* CHANGE: END *)
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists xs_v; iFrame "HAbst".
		iExists xs, xs_queue, xs_old, x_head, x_new; iFrame.
		do 2 (iSplit; first done).
		iLeft.
		iFrame.
		by iExists (x_tail :: xs_fromtail).
	}
	wp_seq.
	wp_load.
	wp_pures.
	wp_apply (release_spec with "[$Ht_lock $HTokE $Hlocked_γ_Tlock]").
	(* CHANGE: START: prove Q*)
	iIntros (_).
	by iApply "HΦ".
	(* CHANGE: END *)
Qed.

(* ----- Specification for Dequeue ----- *)
Lemma dequeue_spec v_q (Q_γ : Qgnames) (P : iProp Σ) (Q : val -> iProp Σ):
	□(∀xs_v, (Q_γ ⤇● xs_v ∗ P
				={⊤ ∖ ↑Ni}=∗
				▷ (( ⌜xs_v = []⌝ ∗ Q_γ ⤇● xs_v ∗ Q NONEV) ∨
				(∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗ Q_γ ⤇● xs_v' ∗ Q (SOMEV x_v)))
			)
	 )
	-∗
	{{{ is_queue v_q Q_γ ∗ P }}}
		dequeue v_q
	{{{ v, RET v; Q v }}}.
Proof.
	(* CHANGE: START: intro viewshift *)
	iIntros "#Hvs".
	iIntros (Φ) "!> [(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> &
				 #Hl_queue & #Hqueue_inv & #Hh_lock & #Ht_lock) HP] HΦ".
	(* CHANGE: END *)
	wp_lam.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "Hh_lock").
	iIntros "(Hlocked_γ_Hlock & HTokD)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (! #l_head)%E.
	(* Open in Static / Enqueue *)
	iInv "Hqueue_inv" as "Hqueue_inv_open".
	(* CHANGE: START: remove Ψ, HAll -> HAbst *)
	iPoseProof (queue_invariant_equiv_simple l_head l_tail Q_γ with "Hqueue_inv_open") as "Hqueue_inv_open".
	iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & [ [Hl_head HToknD] | [Hl_head >HTokD'] ] & Htail)";
	last by iCombine "HTokD HTokD'" gives "%H". (* Impossible: TokD*)
	(* CHANGE: END *)
	wp_load.
	iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	iModIntro.
	(* Close in Dequeue / Both *)
	(* CHANGE: START: HAll -> HAbst *)
	iSplitL "Hl_head1 HTokD Htail HisLL_xs HAbst".
	(* CHANGE: END *)
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists xs_v; iFrame "HAbst".
		iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
		do 2 (iSplit; first done).
		by iRight.
	}
	subst.
	iPoseProof (isLL_chain_node with "HisLL_chain_xs") as "Hxhead_node".
	iClear (Hconc_abst_eq xs_v xs_queue xs_old x_tail) "HisLL_chain_xs".
	wp_let.
	wp_load.
	wp_pures.
	wp_bind (! #(n_out x_head))%E.
	(* Open in Dequeue / Both *)
	iInv "Hqueue_inv" as "Hqueue_inv_open".
	(* CHANGE: START: remove Ψ, HAll -> HAbst *)
	iPoseProof (queue_invariant_equiv_simple l_head l_tail Q_γ with "Hqueue_inv_open") as "Hqueue_inv_open".
	iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head' & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & [ [Hl_head >HToknD'] | [>Hl_head1 HTokD] ] & Htail)";
	first by iCombine "HToknD HToknD'" gives "%H". (* Impossible: ToknD*)
	(* CHANGE: END *)
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq]".
	subst.
	iAssert (▷⌜x_head' = x_head⌝)%I as ">->".
	{
		iNext.
		iPoseProof (isLL_chain_node xs_queue x_head' xs_old with "[HisLL_chain_xs]") as "#Hxhead'_node"; first done.
		by iApply n_in_equal.
	}
	(* CASE ANALYSIS: Is queue empty? *)
	destruct (ll_case_first xs_queue) as [->|[x_head_next [xs_queue' ->]]].
	- (* Queue is empty. *)
	  iDestruct "HisLL_xs" as "[Hxhead_to_none _]".
	  wp_load.
	  (* CHANGE: START: viewshift *)
	  (* Update the abstract state using the viewshift *)
	  iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[(>-> & HAbst & HQ) | (%x_v & %xs_v' & >-> & HAbst_new & HQ) ]";
	  	[ by iFrame | |
		  (* The abstract state must be empty. Hence the second disjunct is impossible. *)
		  rewrite wrap_some_split in Hconc_abst_eq;
		  exfalso;
		  by apply (app_cons_not_nil (wrap_some xs_v') [] (SOMEV x_v))
		].
	  (* CHANGE: END *)
	  iModIntro.
	  (* Close in Static / Enqueue *)
	  (* CHANGE: START: Added HAbst *)
	  iSplitL "Hl_head HToknD Htail Hxhead_to_none HAbst".
	  (* CHANGE: END *)
	  {
		iNext.
		iApply queue_invariant_equiv_simple.
		(* CHANGE: START: framing instead of splitting *)
		iExists []; iFrame "HAbst".
		(* CHANGE: END *)
		iExists ([] ++ [x_head] ++ xs_old), [], xs_old, x_head, x_tail; iFrame. do 3 (iSplit; first done). iLeft. iFrame.
		by rewrite dfrac_op_own Qp.half_half.
	  }
	  wp_let.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_apply (release_spec with "[$Hh_lock $HTokD $Hlocked_γ_Hlock]").
	  iIntros (_).
	  wp_seq.
	  iModIntro.
	  (* CHANGE: START: prove Q *)
	  by iApply "HΦ".
	  (* CHANGE: END *)
	- (* Queue is non-empty*)
	  iAssert (▷(isLL_chain [x_head_next; x_head]))%I as "HisLL_chain_xheadnext".
	  {
		iNext.
		rewrite <- app_assoc.
		iDestruct (isLL_chain_split with "HisLL_chain_xs") as "[_ H]".
		iClear "HisLL_chain_xs".
		rewrite -> app_assoc.
		iDestruct (isLL_chain_split with "H") as "[H' _]".
		done.
	  }
	  iDestruct "HisLL_chain_xheadnext" as "(Hxheadnext_node & Hxhead_to_xheadnext & _)".
	  wp_load.
	  iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
	  iModIntro.
	  (* Close in Dequeue / Both *)
	  (* CHANGE: START: HAll -> HAbst *)
	  iSplitL "Hl_head1 HisLL_xs Htail HTokD HAbst".
	  (* CHANGE: END *)
	  {
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists xs_v; iFrame "HAbst".
		iExists ((xs_queue' ++ [x_head_next]) ++ [x_head] ++ xs_old), (xs_queue' ++ [x_head_next]), xs_old, x_head, x_tail; iFrame.
		do 2 (iSplit; first done).
		by iRight.
	  }
	  iClear (Hconc_abst_eq xs_v xs_queue' xs_old x_tail Hhead_eq) "HisLL_chain_xs".
	  wp_let.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_bind (#l_head <- #(n_in x_head_next))%E.
	  (* Open in Dequeue / Both *)
	  iInv "Hqueue_inv" as "Hqueue_inv_open".
	  (* CHANGE: START: remove Ψ, HAll -> HAbst *)
	  iPoseProof (queue_invariant_equiv_simple l_head l_tail Q_γ with "Hqueue_inv_open") as "Hqueue_inv_open".
	  iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head'' & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & [ [Hl_head >HToknD'] | [>Hl_head1 HTokD] ] & Htail)";
	  first by iCombine "HToknD HToknD'" gives "%H". (* Impossible ToknD *)
	  (* CHANGE: END *)
	  iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq]".
	  rewrite dfrac_op_own Qp.half_half.
	  subst.
	  wp_store.
	  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	  iAssert (⌜x_head'' = x_head⌝)%I as "->".
	  {
		iPoseProof (isLL_chain_node xs_queue x_head'' xs_old with "[HisLL_chain_xs]") as "#Hxhead''_node"; first done.
		by iApply n_in_equal.
	  }
	  (* Sync up xs_queue *)
	   destruct (ll_case_first xs_queue) as [->|[x_head_next' [xs_queue' ->]]].
	  { (* Impossible case. xs_queue must contain at least one element. *)
		iDestruct "HisLL_xs" as "[Hxhead_to_none _]".
		iCombine "Hxhead_to_none Hxhead_to_xheadnext" gives "[_ %Hcontra]".
		simplify_eq.
	  }
	  rewrite <- app_assoc.
	  iAssert (⌜x_head_next' = x_head_next⌝)%I as "->".
	  {
		iPoseProof (isLL_chain_split xs_queue' _ with "HisLL_chain_xs") as "(_ & Hxheadnext'_node & Hxhead_to_xheadnext' & _)".
		iCombine "Hxhead_to_xheadnext Hxhead_to_xheadnext'" gives "[_ %Heq]".
		by iApply n_in_equal.
	  }
	  (* CHANGE: START: destruct xs_v using viewshift *)
	  (* Update the abstract state using the viewshift *)
	  iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[(>-> & HAbst & HQ) | (%x_v & %xs_v' & >-> & HAbst_new & HQ) ]";
	  	[ by iFrame |
		  (* The abstract state cannot be empty. Hence the first disjunct is impossible *)
		  rewrite proj_val_split in Hconc_abst_eq;
		  exfalso;
		  by apply (app_cons_not_nil (proj_val xs_queue') [] (n_val x_head_next)) |
		].
	  (* CHANGE: END *)
	  rewrite proj_val_split wrap_some_split /= in Hconc_abst_eq.
	  apply list_last_eq in Hconc_abst_eq as [Hxs_rest_val_eq Hxheadnext_xv_eq].
	  (* CHANGE: Removed splitting All *)
	  iModIntro.
	  (* Close in Static / Enqueue *)
	  (* CHANGE: START: HAll -> HAbst_new *)
	  iSplitL "Hl_head Htail HToknD HisLL_xs HAbst_new".
	  (* CHANGE: END *)
	  {
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists xs_v'; iFrame "HAbst_new".
		iExists (xs_queue' ++ [x_head_next] ++ [x_head] ++ xs_old), xs_queue', ([x_head] ++ xs_old), x_head_next, x_tail; iFrame.
		do 2 (iSplit; first done).
		iLeft.
		iFrame.
	  }
	  wp_seq.
	  wp_load.
	  wp_pures.
	  wp_apply (release_spec with "[$Hh_lock $HTokD $Hlocked_γ_Hlock]").
	  iIntros (_).
	  wp_seq.
	  iModIntro.
	  iApply "HΦ".
	  (* CHANGE: START *)
	  by rewrite Hxheadnext_xv_eq.
	  (* CHANGE: END *)
Qed.

End proofs.

Notation "Q_γ ⤇● xs_v" := (own Q_γ.(γ_Abst) (●F (to_agree xs_v)))
	(at level 20, format "Q_γ  ⤇●  xs_v") : bi_scope.
Notation "Q_γ ⤇◯ xs_v" := (own Q_γ.(γ_Abst) (◯F (to_agree xs_v)))
	(at level 20, format "Q_γ  ⤇◯  xs_v") : bi_scope.
Notation "Q_γ ⤇[ q ] xs_v" := (own Q_γ.(γ_Abst) (◯F{ q } (to_agree xs_v)))
	(at level 20, format "Q_γ  ⤇[ q ]  xs_v") : bi_scope.
