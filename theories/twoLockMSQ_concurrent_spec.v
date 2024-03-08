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

(* ===== Concurrent Specification for Two-lock M&S Queue ===== *)

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

(* if two nodes have the same 'in' location, then it is the same node. *)
Lemma n_in_equal (x y : (loc * val * loc)) :
	⌜#(n_in x) = #(n_in y)⌝ -∗
	n_in x ↦□ (n_val x, #(n_out x)) -∗
	n_in y ↦□ (n_val y, #(n_out y)) -∗
	⌜x = y⌝.
Proof.
	iIntros (Heq_loc) "Hx Hy".
	simplify_eq.
	rewrite Heq_loc.
	iCombine "Hx Hy" gives "[_ %Heq_pair]".
	simplify_eq.
	iPureIntro.
	destruct x as [[lx1 vx] lx2], y as [[ly1 vy] ly2].
	cbn in *.
	by subst.
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

Lemma isLL_chain_agree : forall x y xs xs' ys ys',
	⌜n_in x = n_in y⌝ -∗
	isLL_chain (xs ++ [x] ++ xs') -∗
	isLL_chain (ys ++ [y] ++ ys') -∗
	⌜x = y⌝.
Proof.
	iIntros (x y xs xs' ys ys' Heqn_in_xy) "#HisLL_chainxs #HisLL_chainys".
	iApply n_in_equal.
	- iPureIntro. by rewrite Heqn_in_xy.
	- by iApply (isLL_chain_node xs x xs').
	- by iApply (isLL_chain_node ys y ys').
Qed.

Lemma isLL_chain_agree_next : forall x y z ys ys' zs zs',
	isLL_chain (ys ++ [y ; x] ++ ys') -∗
	isLL_chain (zs ++ [z ; x] ++ zs') -∗
	⌜y = z⌝.
Proof.
	iIntros (x y z ys ys' zs zs') "#HisLL_chainys #HisLL_chainzs".
	iPoseProof (isLL_chain_split ys ([y ; x] ++ ys') with "HisLL_chainys") as "[_ HisLL_chain_yxys']".
	iPoseProof (isLL_chain_split [y ; x] ys' with "HisLL_chain_yxys'") as "[HisLL_chain_yx _]".
	iPoseProof (isLL_chain_split zs ([z ; x] ++ zs') with "HisLL_chainzs") as "[_ HisLL_chain_zxzs']".
	iPoseProof (isLL_chain_split [z ; x] zs' with "HisLL_chain_zxzs'") as "[HisLL_chain_zx _]".
	iClear "HisLL_chainys HisLL_chainzs HisLL_chain_yxys' HisLL_chain_zxzs'".
	iDestruct "HisLL_chain_yx" as "(#Hy_in_2 & #Hy_out_1 & Hy_in_1)".
	iDestruct "HisLL_chain_zx" as "(#Hz_in_2 & #Hz_out_1 & Hz_in_1)".
	iCombine "Hy_out_1 Hz_out_1" gives "[_ %Heq_in]".
	simplify_eq.
	iApply n_in_equal; try done. by rewrite Heq_in.
Qed.

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
Definition TokHlock (g : Qgnames) := own g.(γ_Hlock) (Excl ()).
Definition TokTlock (g : Qgnames) := own g.(γ_Tlock) (Excl ()).
Definition TokE (g : Qgnames) := own g.(γ_E) (Excl ()).
Definition ToknE (g : Qgnames) := own g.(γ_nE) (Excl ()).
Definition TokD (g : Qgnames) := own g.(γ_D) (Excl ()).
Definition ToknD (g : Qgnames) := own g.(γ_nD) (Excl ()).
Definition TokBefore (g : Qgnames) := own g.(γ_Before) (Excl ()).
Definition TokAfter (g : Qgnames) := own g.(γ_After) (Excl ()).
Definition TokUpdated (g : Qgnames) := ((TokBefore g) ∗ (TokAfter g))%I.

Definition queue_invariant (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs xs_rest xs_old (x_head x_tail: (loc * val * loc)),
	⌜xs = xs_rest ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
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
	∃ xs xs_rest xs_old (x_head x_tail: (loc * val * loc)),
	⌜xs = xs_rest ++ [x_head] ++ xs_old⌝ ∗ isLL xs ∗
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
	- iIntros "(%xs & %xs_rest & %xs_old & %x_head & %x_tail & Hxs_split & HisLL_xs & [H_Static | [H_Enqueue | [H_Dequeue | H_Both]]])"; 
	iExists xs, xs_rest, xs_old, x_head, x_tail; iFrame.
	  + iDestruct "H_Static" as "(Hl_head & Hl_tail & HisLast & HTokne & HToknD & HTokUpdated)".
		iSplitL "Hl_head HToknD"; first (iLeft; iFrame).
		iLeft. iFrame.
	  + iDestruct "H_Enqueue" as "(Hl_head & Hl_tail & [[HisLast HTokAfter] | [HisSndLast HAfter]] & HToke & HToknD)".
	    * iSplitL "Hl_head HToknD"; first (iLeft; iFrame). 
		  iRight. iFrame. iLeft. iFrame.
		* iSplitL "Hl_head HToknD"; first (iLeft; iFrame). 
		  iRight. iFrame. iRight. iFrame.
	  + iDestruct "H_Dequeue" as "(Hl_head & Hl_tail & HisLast & HTokne & HTokD & HTokUpdated)".
		iSplitL "Hl_head HTokD"; first (iRight; iFrame).
		iLeft. iFrame.
	  + iDestruct "H_Both" as "(Hl_head & Hl_tail & [[HisLast HTokAfter] | [HisSndLast HAfter]] & HToke & HTokD)".
	    * iSplitL "Hl_head HTokD"; first (iRight; iFrame). 
		  iRight. iFrame. iLeft. iFrame.
		* iSplitL "Hl_head HTokD"; first (iRight; iFrame). 
		  iRight. iFrame. iRight. iFrame.
	- iIntros "(%xs & %xs_rest & %xs_old & %x_head & %x_tail & Hxs_split & HisLL_xs & [[Hl_head HToknD] | [Hl_head HTokD]] & [(Hl_tail & HisLast & HToknE & HTokUpdated) | (Hl_tail & HTokE & [[HisLast HTokBefore] | [HisSndLast HTokAfter]])])";
	iExists xs, xs_rest, xs_old, x_head, x_tail; eauto 10 with iFrame.
Qed.

Definition is_queue (q : val) (Q_γ: Qgnames) : iProp Σ :=
	∃ head tail : loc, ∃ H_lock T_lock : val,
	∃ l : loc , ⌜q = #l⌝ ∗
		l ↦□ ((#head, #tail), (H_lock, T_lock)) ∗
		inv N (queue_invariant head tail Q_γ) ∗
		is_lock Q_γ.(γ_Hlock) H_lock (TokD Q_γ) ∗
		is_lock Q_γ.(γ_Tlock) T_lock (TokE Q_γ).

Lemma initialize_spec :
	{{{ True }}}
		initialize #()
	{{{ v Q_γ, RET v; is_queue v Q_γ}}}.
Proof.
	iIntros (Φ) "_ HΦ".
	wp_lam.
	wp_pures.
	wp_alloc l_1_out as "Hl_1_out".
	wp_alloc l_1_in as "Hl_1_in".
	wp_pures.
	iMod (pointsto_persist with "Hl_1_in") as "#Hl_1_in".
	wp_pures.
	iMod (own_alloc (Excl ()) ) as (γ_D) "Hγ_D"; first done.
	wp_apply (newlock_spec with "Hγ_D").
	iIntros (hlock γ_Hlock) "Hγ_Hlock".
	wp_let.
	iMod (own_alloc (Excl ()) ) as (γ_E) "Hγ_E"; first done.
	wp_apply (newlock_spec with "Hγ_E").
	iIntros (tlock γ_Tlock) "Hγ_Tlock".
	wp_let.
	wp_alloc l_tail as "Hl_tail".
	wp_alloc l_head as "Hl_head".
	iMod (own_alloc (Excl ()) ) as (γ_nE) "Hγ_nE"; first done.
	iMod (own_alloc (Excl ()) ) as (γ_nD) "Hγ_nD"; first done.
	iMod (own_alloc (Excl ()) ) as (γ_Before) "Hγ_Before"; first done.
	iMod (own_alloc (Excl ()) ) as (γ_After) "Hγ_After"; first done.
	set (Queue_gnames := {| γ_Hlock := γ_Hlock;
							γ_Tlock := γ_Tlock;
							γ_E := γ_E;
							γ_nE := γ_nE;
							γ_D := γ_D;
							γ_nD := γ_nD;
							γ_Before := γ_Before;
							γ_After := γ_After
					|}).
	iMod (inv_alloc N _ (queue_invariant l_head l_tail Queue_gnames) with "[Hl_head Hl_tail Hl_1_in Hl_1_out Hγ_nE Hγ_nD Hγ_Before Hγ_After]") as "#HqueueInv".
	{
		iNext. iExists [(l_1_in, NONEV, l_1_out)], [], [], (l_1_in, NONEV, l_1_out), (l_1_in, NONEV, l_1_out). cbn. iSplitR; first done. iSplitL "Hl_1_in Hl_1_out"; first auto.
		iLeft. iFrame. iPureIntro. by exists [].
	}
	wp_alloc l_queue as "Hl_queue".
	iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
	iApply ("HΦ" $! #l_queue Queue_gnames).
	iModIntro.
	iExists l_head, l_tail, hlock, tlock, l_queue.
	by repeat iSplit.
Qed.

Lemma enqueue_spec Q (v : val) (qg : Qgnames) :
	{{{ is_queue Q qg }}}
		enqueue Q v 
	{{{w, RET w; True}}}.
Proof.
	iIntros (Φ) "(%l_head & %l_tail & %H_lock & %T_lock & %l_queue & -> &
				 #Hl_queue & #H_queue_inv & #H_hlock & #H_tlock) HΦ".
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
	iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_open") as "H_queue_inv_open".
	iDestruct "H_queue_inv_open" as "(%xs & %xs_rest & %xs_old & %x_head & %x_tail & >%H_eq_xs & HisLL_xs & H_head & [ ( [Hl_tail1 Hl_tail2] & >[%xs_fromtail %H_isLast] & HToknE & HTokUpdated ) | (_ & >HTokE2 & _) ])"; last by iCombine "HTokE HTokE2" gives "%H". (* Impossible: TokE *)
	wp_load.
	iModIntro.
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	iPoseProof (isLL_chain_node [] x_tail xs_fromtail with "[HisLL_chain_xs]") as "#Hx_tail"; first by rewrite H_isLast.
	iDestruct "HTokUpdated" as "[HTokBefore HTokAfter]".
	(* Close in Enqueue / Both : Before *)
	iSplitL "H_head Hl_tail1 HTokE HTokBefore HisLL_xs".
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists xs, xs_rest, xs_old, x_head, x_tail.
		iFrame.
		iSplitR; first done.
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
	iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_open") as "H_queue_inv_open".
	iDestruct "H_queue_inv_open" as "(%xs_2 & %xs_rest_2 & %xs_old_2 & %x_head_2 & %x_tail_2 & >%H_eq_xs_2 & HisLL_xs_2 & H_head & [ ( _ & _ & >HToknE2 & _ ) | (>Hl_tail1 & HTokE & [[>[%xs_fromtail_2 %H_isLast_2] HTokBefore] | [_ >HTokAfter2]]) ])"; 
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
	iSplitL "H_head Hl_tail1 HTokE HTokAfter HisLL_xs_new".
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists xs_new, (x_new :: xs_rest_2), xs_old_2, x_head_2, x_tail.
		iSplitR. { iPureIntro. unfold xs_new. cbn. rewrite H_eq_xs_2. auto. }
		iFrame.
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
	iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_open") as "H_queue_inv_open".
	iDestruct "H_queue_inv_open" as "(%xs_3 & %xs_rest_3 & %xs_old_3 & %x_head_3 & %x_tail_3 & >%H_eq_xs_3 & HisLL_xs_3 & H_head & [ ( _ & _ & >HToknE2 & _ ) | (>Hl_tail1 & HTokE & [[_ >HTokBefore2] | [>(%x_new_2 & %xs_fromtail_3 & %H_isSndLast) HTokAfter]])])"; 
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
		iExists xs_3, xs_rest_3, xs_old_3, x_head_3, x_new.
		iSplitR; first done.
		iFrame.
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

Lemma dequeue_spec Q (qg : Qgnames) : 
	{{{ is_queue Q qg}}} 
		dequeue Q 
	{{{v, RET v; True}}}.
Proof.
	iIntros (Φ) "(%l_head & %l_tail & %H_lock & %T_lock & %l_queue & -> &
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
	iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_open") as "H_queue_inv_open".
	iDestruct "H_queue_inv_open" as "(%xs & %xs_rest & %xs_old & %x_head & %x_tail & >%H_eq_xs & H_isLL_xs & [ [Hl_head HToknD] | [Hl_head >HTokD2] ] & H_tail)"; 
	last by iCombine "HTokD HTokD2" gives "%H". (* Impossible: TokD*)
	wp_load.
	iModIntro.
	iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
	iPoseProof (isLL_and_chain with "H_isLL_xs") as "[H_isLL_xs #H_isLL_chain_xs_1]".
	(* Close in Dequeue / Both *)
	iSplitL "Hl_head2 HTokD H_tail H_isLL_xs".
	{
		iNext. iApply queue_invariant_equiv_simple.
		iExists xs, xs_rest, xs_old, x_head, x_tail. iFrame.
		iSplitR; first done. iRight. done.
	}
	wp_let.
	subst.
	iPoseProof (isLL_chain_node with "H_isLL_chain_xs_1") as "H_x_head_in".
	wp_load.
	wp_pures.
	wp_bind (! #(n_out x_head))%E.
	(* Open in Dequeue / Both *)
	iInv "H_queue_inv" as "H_queue_inv_open".
	iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_open") as "H_queue_inv_open".
	iDestruct "H_queue_inv_open" as "(%xs_2 & %xs_rest_2 & %xs_old_2 & %x_head_2 & %x_tail_2 & >%H_eq_xs_2 & H_isLL_xs_2 & [ [Hl_head >HToknD2] | [>Hl_head2 HTokD] ] & H_tail)";
	first by iCombine "HToknD HToknD2" gives "%H". (* Impossible: ToknD*)
	iPoseProof (isLL_and_chain with "H_isLL_xs_2") as "[H_isLL_xs_2 #HisLL_chain_xs_2]".
	iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq2]".
	iAssert (▷⌜x_head_2 = x_head⌝)%I as ">->".
	{
		iNext.
		simplify_eq.
		by iApply (isLL_chain_agree x_head_2 x_head xs_rest_2 xs_old_2 xs_rest xs_old).
	}
	subst.
	(* Case analysis: Is queue empty? *)
	destruct xs_rest_2 as [| x_tail_2_2 xs_rest_2'].
	- (* Queue is empty. *)
	  iDestruct "H_isLL_xs_2" as "[H_x_head_out _]".
	  wp_load.
	  iModIntro.
	  (* Close in Static / Enqueue *)
	  iSplitL "Hl_head HToknD H_tail H_x_head_out".
	  {
		iNext. iApply queue_invariant_equiv_simple.
		iExists ([] ++ [x_head] ++ xs_old_2), [], xs_old_2, x_head, x_tail_2.
		iFrame. iSplitR; first done. iSplitR; first done. iLeft. iFrame.
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
	  done.
	- (* Queue is non-empty*)
	  destruct (exists_first (x_tail_2_2 :: xs_rest_2')) as [x_head_next [xs_rest_2'' Hxs_rest_eq]]; first done.
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
	  iSplitL "Hl_head2 H_isLL_xs_2 H_tail HTokD".
	  {
		iNext. iApply queue_invariant_equiv_simple.
		iExists ((xs_rest_2'' ++ [x_head_next]) ++ [x_head] ++ xs_old_2), (xs_rest_2'' ++ [x_head_next]), xs_old_2, x_head, x_tail_2.
		iFrame. iSplitR; first done. iRight. done.
	  }
	  wp_let.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_bind (#l_head <- #(n_in x_head_next))%E.
	  iInv "H_queue_inv" as "H_queue_inv_open".
	  iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_open") as "H_queue_inv_open".
	  iDestruct "H_queue_inv_open" as "(%xs_3 & %xs_rest_3 & %xs_old_3 & %x_head_3 & %x_tail_3 & >%H_eq_xs_3 & H_isLL_xs_3 & [ [Hl_head >HToknD2] | [>Hl_head2 HTokD] ] & H_tail)";
	  first by iCombine "HToknD HToknD2" gives "%H". (* Impossible ToknD *)
	  iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq3]".
	  rewrite dfrac_op_own.
	  rewrite Qp.half_half.
	  wp_store.
	  iModIntro.
	  (* Close in Static / Enqueue *)
	  iSplitL "Hl_head H_tail HToknD H_isLL_xs_3".
	  {
		iNext.
		iPoseProof (isLL_and_chain with "H_isLL_xs_3") as "[H_isLL_xs_3 #H_isLL_chain_xs_3]".
		subst.
		iAssert (⌜x_head_3 = x_head⌝)%I as "->".
		{
			iApply (isLL_chain_agree x_head_3 x_head xs_rest_3 xs_old_3 xs_rest xs_old); by simplify_eq.
		}
		(* Sync up xs_rest_2 with xs_rest_3 *)
		destruct xs_rest_3 as [|x_tail_3_2 xs_rest_3'].
		- (* Impossible case. xs_rest_3 must contain at least one element. *)
		  iDestruct "H_isLL_xs_3" as "[H_x_head_3_null _]".
		  iCombine "H_x_head_3_null H_x_head_next_out" gives "[_ %Hcontra]".
		  simplify_eq.
		- destruct (exists_first (x_tail_3_2 :: xs_rest_3')) as [x_head_next_3 [xs_rest_3'' Hxs_rest_eq_3]]; first done.
		  rewrite Hxs_rest_eq_3.
		  rewrite <- app_assoc. rewrite <- app_assoc.
		  iAssert (⌜x_head_next = x_head_next_3⌝)%I as "->"; first by iApply isLL_chain_agree_next.
		  iApply queue_invariant_equiv_simple.
		  iExists (xs_rest_3'' ++ [x_head_next_3] ++ [x_head] ++ xs_old_3), xs_rest_3'', ([x_head] ++ xs_old_3), x_head_next_3, x_tail_3.
		  iFrame. iSplitR; first done. iLeft. iFrame.
	  }
	  wp_seq.
	  wp_load.
	  wp_pures.
	  wp_apply (release_spec with "[$H_hlock $HTokD $Hlocked_γ_Hlock]").
	  iIntros (_).
	  wp_seq.
	  iModIntro.
	  iApply "HΦ".
	  done.
Qed.

End proofs.