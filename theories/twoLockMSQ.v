From stdpp Require Import countable.
From iris.algebra Require Import excl.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Export invariants.
From iris.unstable.heap_lang Require Import interpreter.

Local Existing Instance spin_lock.


Definition initialize : val :=
	rec: "initialize" <> :=
		let: "node" := ref (NONE, ref (NONE)) in
		let: "H_lock" := newlock #() in
		let: "T_lock" := newlock #() in
		ref ((ref "node", ref "node"), ("H_lock", "T_lock")).

Definition enqueue : val :=
	rec: "enqueue" "Q" "value" :=
		let: "node" := ref (SOME "value", ref(NONE)) in
		acquire (Snd (Snd (!"Q"))) ;; (* Acqurie T_lock *)
		Snd (!(!(Snd (Fst(!"Q"))))) <- "node" ;;
		Snd (Fst (!"Q")) <- "node" ;;
		release (Snd (Snd (!"Q"))).

Definition dequeue : val :=
	rec: "dequeue" "Q" :=
		acquire (Fst (Snd (!"Q")));; (* Acquire H_lock *)
		let: "node" := !(Fst (Fst (!"Q"))) in (* Get Head node *)
		let: "new_head" := !(Snd(!"node")) in (* Find Head.Next *)
		if: "new_head" = NONE then (* Check if Queue is empty *)
			(* No Next node. Queue is empty. *)
			release (Fst (Snd(!"Q"))) ;;
			NONEV
		else
			(* Queue not empty. Pop first element in Queue *)
			let: "value" := Fst (!"new_head") in (* Get its value *)
			Fst (Fst (!"Q")) <- "new_head" ;; (* Swing Head to next node *)
			release (Fst (Snd (!"Q"))) ;; (* Release H_lock *)
			"value". (* Return value *)

Section tests.

Definition test_initialize : expr :=
	let: "Q" := initialize #() in
	"Q".

Definition test_enqueue : expr :=
	let: "Q" := initialize #() in
	enqueue "Q" #5 ;;
	enqueue "Q" #7 ;;
	#().

Definition test_dequeue1 : expr :=
	let: "Q" := initialize #() in
	enqueue "Q" #5 ;;
	let: "v1" := dequeue "Q" in
	"v1".

Definition test_dequeue2 : expr :=
	let: "Q" := initialize #() in
	enqueue "Q" #5 ;;
	enqueue "Q" #7 ;;
	let: "v1" := dequeue "Q" in
	let: "v2" := dequeue "Q" in
	("v1", "v2").

Definition test_dequeue_empty1 : expr :=
	let: "Q" := initialize #() in
	let: "v1" := dequeue "Q" in
	"v1".

Definition test_dequeue_empty2 : expr :=
	let: "Q" := initialize #() in
	enqueue "Q" #5 ;;
	let: "v1" := dequeue "Q" in
	let: "v2" := dequeue "Q" in
	let: "v3" := dequeue "Q" in
	("v1", "v2", "v3").

Compute (exec 200 test_dequeue_empty2).

End tests.

Section proofs.

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!inG Σ (exclR unitO)}.

Let N := nroot .@ "twoLockMSQ".

Record Qgnames := {γ_Hlock 	: gname;
				   γ_Tlock 	: gname;
				   γ_E 		: gname;
				   γ_nE 	: gname;
				   γ_D 		: gname;
				   γ_nD 	: gname;
				   γ_Before : gname;
				   γ_After 	: gname;
				  }.

Definition TokHlock (g : Qgnames) := own g.(γ_Hlock) (Excl ()).
Definition TokTlock (g : Qgnames) := own g.(γ_Tlock) (Excl ()).
Definition TokE (g : Qgnames) := own g.(γ_E) (Excl ()).
Definition ToknE (g : Qgnames) := own g.(γ_nE) (Excl ()).
Definition TokD (g : Qgnames) := own g.(γ_D) (Excl ()).
Definition ToknD (g : Qgnames) := own g.(γ_nD) (Excl ()).
Definition TokBefore (g : Qgnames) := own g.(γ_Before) (Excl ()).
Definition TokAfter (g : Qgnames) := own g.(γ_After) (Excl ()).
Definition TokUpdated (g : Qgnames) := ((TokBefore g) ∗ (TokAfter g))%I.

(* Notaion for triples *)
(* TODO: rename fst to "in", snd to "n_val", and trd to "out". Maybe n_in *)
(* TODO: maybe "n_in" and "n_out" to avoid clashing with keywords *)
Definition fst {A B C} (x : A * B * C ) := (let '(a, b, c) := x in a).
Definition snd {A B C} (x : A * B * C ) := (let '(a, b, c) := x in b).
Definition trd {A B C} (x : A * B * C ) := (let '(a, b, c) := x in c).


Fixpoint isLL_chain (xs : list (loc * val * loc) ) : iProp Σ :=
	match xs with
	| [] => True
	| [x] => (fst x) ↦□ (snd x, #(trd x))
	| xᵢ₁ :: ((xᵢ :: xs'') as xs') =>
		fst(xᵢ₁) ↦□ (snd xᵢ₁, #(trd xᵢ₁)) ∗
		(trd xᵢ) ↦□ #(fst xᵢ₁) ∗ isLL_chain xs'
	end.

(* TODO: Prove this! *)
Global Instance isLL_chain_persistent xs : Persistent (isLL_chain xs).
Proof.
	Admitted.

Definition isLL (xs : list (loc * val * loc) ) : iProp Σ :=
	match xs with
	| [] => True
	| x :: xs' => (trd x) ↦ NONEV ∗ isLL_chain xs
	end.

Lemma isLL_and_chain : forall xs,
	isLL xs -∗
	isLL xs ∗ isLL_chain xs.
Proof.
	iIntros (xs) "HisLLxs".
	destruct xs as [| x' xs']; first done.
	unfold isLL.
	iPoseProof "HisLLxs" as "[Htrdx' #HisLLxs]".
	auto.
Qed.

Lemma fst_equal (x y : (loc * val * loc)) :
	⌜#(fst x) = #(fst y)⌝ -∗
	fst x ↦□ (snd x, #(trd x)) -∗
	fst y ↦□ (snd y, #(trd y)) -∗
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

Lemma isLL_chain_node : forall xs_1 x xs_2,
	isLL_chain (xs_1 ++ x :: xs_2) -∗
	fst(x) ↦□ (snd x, #(trd x)).
Proof.
	iIntros (xs_1 x xs_2) "#HisLL_chain".
	iInduction xs_1 as [| y xs'_1] "IH".
	- simpl.
	  destruct xs_2.
	  + done.
	  + iDestruct "HisLL_chain" as "(Hx & _ & _)"; auto.
	- iApply "IH". destruct xs'_1 as [| y' xs''_1];
	  	iDestruct "HisLL_chain" as "(_ & _ & H)"; done.
Qed.

Lemma isLL_chain_split : forall xs ys,
	isLL_chain (xs ++ ys) -∗
	isLL_chain xs ∗ isLL_chain ys.
Proof.
	iIntros (xs ys) "#HisLL_chain_xs_ys".
	iInduction xs as [|x' xs'] "IH".
	- auto.
	- destruct xs' as [| x'' xs''].
	  + destruct ys as [| y' ys'].
		* auto.
		* iDestruct "HisLL_chain_xs_ys" as "(Hx' & Htrdy' & HIsLL_chain_ys')".
		  fold isLL_chain. iSplitL; done.
	  + iAssert (isLL_chain (x'' :: xs'') ∗ isLL_chain ys)%I as "[IHxs' IHys]".
	  	{
			iApply "IH". iDestruct "HisLL_chain_xs_ys" as "(_ & _ & Hchain)"; done.
		}
		iSplitL; auto.
		iDestruct "HisLL_chain_xs_ys" as "(Hfstx' & Htrdx'' & _)".
		unfold isLL_chain; auto.
Qed.

Lemma isLL_chain_agree : forall x_1 y_1 xs xs' ys ys',
	⌜fst x_1 = fst y_1⌝ -∗
	isLL_chain (xs ++ [x_1] ++ xs') -∗
	isLL_chain (ys ++ [y_1] ++ ys') -∗
	⌜x_1 = y_1⌝.
Proof.
	iIntros (x_1 y_1 xs xs' ys ys' Heqfst_x1y1) "#HisLL_chainxs #HisLL_chainys".
	iApply fst_equal.
	- iPureIntro. by rewrite Heqfst_x1y1.
	- by iApply (isLL_chain_node xs x_1 xs').
	- by iApply (isLL_chain_node ys y_1 ys').
Qed.

(* TODO: make proof nicer *)
Lemma isLL_chain_agree_next : forall x y z ys ys' zs zs',
	isLL_chain (ys ++ [y ; x] ++ ys') -∗
	isLL_chain (zs ++ [z ; x] ++ zs') -∗
	⌜y = z⌝.
Proof.
	iIntros (x y z ys ys' zs zs') "#HisLL_chainys #HisLL_chainzs".
	iAssert (isLL_chain (ys ++ [y ; x]) ∗ isLL_chain ys')%I as "[HisLL_chainysyx _]".
	{ iApply isLL_chain_split. by rewrite app_assoc. }
	iAssert (isLL_chain ys ∗ isLL_chain ([y ; x]))%I as "[_ HisLL_chainy]".
	{ by iApply isLL_chain_split. }
	iAssert (isLL_chain (zs ++ [z ; x]) ∗ isLL_chain zs')%I as "[HisLL_chainzszx _]".
	{ iApply isLL_chain_split. iClear "HisLL_chainys". by rewrite app_assoc. }
	iAssert (isLL_chain zs ∗ isLL_chain ([z ; x]))%I as "[_ HisLL_chainz]".
	{ by iApply isLL_chain_split. }
	unfold isLL_chain.
	iDestruct "HisLL_chainy" as "(#Hfsty_2 & #Htrdy_1 & Hfsty_1)".
	iDestruct "HisLL_chainz" as "(#Hfsztz_2 & #Htrdz_1 & Hfstz_1)".
	iCombine "Htrdy_1 Htrdz_1" gives "[_ %Heq_fst]".
	simplify_eq.
	iApply fst_equal; auto. iPureIntro. by rewrite Heq_fst.
Qed.


(* Todo: consider removing *)
Lemma isLL_extend : forall xs (x y : (loc * val * loc)),
	{{{ isLL (x :: xs) ∗
		fst y ↦□ (snd y, #(trd y)) ∗
		trd y ↦ NONEV }}}
			#(trd x) <- #(fst y)
	{{{ w, RET w; isLL (y :: x :: xs) }}}.
Proof.
	iIntros (xs x y Φ) "([Hlₙ₁ HisLL_chain_xs] & Hfsty & Htrdy) HΦ".
	wp_store.
	iMod (pointsto_persist with "Hlₙ₁") as "Hlₙ₁".
	iApply "HΦ".
	iModIntro. iFrame.
Qed.

Lemma list_first_last {A} : forall (x_first : A) xs,
	∃x_last xs', x_first :: xs = xs' ++ [x_last].
Proof.
	intros x_first xs. generalize dependent x_first.
	induction xs as [|x' xs'' IH]; intros x_first.
	- exists x_first, []. done.
	- destruct (IH x') as [x_last' [xs' Hxs_eq]].
	  exists x_last', (x_first :: xs'). simpl. f_equal. done.
Qed.
	  

Definition isLast {A} (x : A) xs := ∃ xs_rest, xs = x :: xs_rest.
Definition isSndLast {A} (x : A) xs := ∃ x_first xs_rest, xs = x_first :: x :: xs_rest.

Definition queue_invariant (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs xs_rest xs_old (x_head x_tail: (loc * val * loc)),
	⌜xs = xs_rest ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	(
		(* Static *)
		(
			l_head ↦ #(fst x_head) ∗
			l_tail ↦ #(fst x_tail) ∗ ⌜isLast x_tail xs⌝ ∗
			ToknE Q_γ ∗ ToknD Q_γ ∗ TokUpdated Q_γ
		)
		∨
		(* Enqueue *)
		(
			l_head ↦ #(fst x_head) ∗
			l_tail ↦{#1/2} #(fst x_tail) ∗
				(⌜isLast x_tail xs⌝ ∗ TokBefore Q_γ ∨
				 ⌜isSndLast x_tail xs⌝ ∗ TokAfter Q_γ) ∗
			TokE Q_γ ∗ ToknD Q_γ
		)
		∨
		(* Dequeue *)
		(
			l_head ↦{#1/2} #(fst x_head) ∗
			l_tail ↦ #(fst x_tail) ∗ ⌜isLast x_tail xs⌝ ∗
			ToknE Q_γ ∗ TokD Q_γ ∗ TokUpdated Q_γ
		)
		∨
		(* Both *)
		(
			l_head ↦{#1/2} #(fst x_head) ∗
			l_tail ↦{#1/2} #(fst x_tail) ∗
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
			(l_head ↦ #(fst x_head) ∗ ToknD Q_γ) ∨ 
			(l_head ↦{#1/2} #(fst x_head) ∗ TokD Q_γ)
		) ∗
		(
			(l_tail ↦ #(fst x_tail) ∗ ⌜isLast x_tail xs⌝ ∗ ToknE Q_γ ∗ TokUpdated Q_γ) ∨
			(
				l_tail ↦{#1/2} #(fst x_tail) ∗ TokE Q_γ ∗
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
	iExists xs, xs_rest, xs_old, x_head, x_tail; iFrame.
	  + iLeft. iFrame.
	  + iRight. iLeft. iFrame. iLeft. iFrame.
	  + iRight. iLeft. iFrame. iRight. iFrame.
	  + iRight. iRight. iLeft. iFrame.
	  + iRight. iRight. iRight. iFrame. iLeft. iFrame.
	  + iRight. iRight. iRight. iFrame. iRight. iFrame.
Qed.

Definition is_queue (q : val) (Q_γ: Qgnames) : iProp Σ :=
	∃ head tail : loc, ∃ H_lock T_lock : val,
	∃ l : loc , ⌜q = #l⌝ ∗
		l ↦□ ((#head, #tail), (H_lock, T_lock)) ∗
		inv N (queue_invariant head tail Q_γ) ∗
		is_lock Q_γ.(γ_Hlock) H_lock (TokD Q_γ) ∗
		is_lock Q_γ.(γ_Tlock) T_lock (TokE Q_γ).

Lemma initialize_spec : {{{ True }}} 
							initialize #() 
						{{{ v Q_γ, RET v; is_queue v Q_γ}}}.
Proof.
	iIntros (Φ) "_ HΦ".
	wp_lam.
	wp_pures.
	wp_alloc l_2 as "Hl_2".
	wp_alloc l'_1 as "Hl'_1".
	wp_pures.
	iMod (pointsto_persist with "Hl'_1") as "#Hl'_1".
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
	iMod (inv_alloc N _ (queue_invariant l_head l_tail Queue_gnames) with "[Hl_head Hl_tail Hl'_1 Hl_2 Hγ_nE Hγ_nD Hγ_Before Hγ_After]") as "#HqueueInv".
	{
		iNext. iExists [(l'_1, NONEV, l_2)], [], [], (l'_1, NONEV, l_2), (l'_1, NONEV, l_2). cbn. iSplitR; first done. iSplitL "Hl'_1 Hl_2"; first auto.
		iLeft. iFrame. iPureIntro. exists []. reflexivity.
	}
	wp_alloc l_queue as "Hl_queue".
	iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
	iApply ("HΦ" $! #l_queue Queue_gnames).
	iModIntro.
	iExists l_head, l_tail, hlock, tlock, l_queue.
	auto.
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
	wp_alloc lₙ₂ as "Hlₙ₂".
	wp_alloc l'ₙ₁ as "Hl'ₙ₁".
	iMod (pointsto_persist with "Hl'ₙ₁") as "#Hl'ₙ₁".
	wp_let.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "H_tlock").
	iIntros "(Hlocked_γ_Tlock & HTokE)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (! #l_tail)%E.
	iInv "H_queue_inv" as "(%xs & %xs_rest & %xs_old & %x_head & %x_tail & #Hxs_eq & HisLL_xs & >Hcases)".
	(* Open in Static / Dequeue *)
	iAssert (ToknE qg ∗ (l_head ↦ #(fst x_head) ∗ ToknD qg ∨ l_head ↦{#1 / 2} #(fst x_head) ∗ TokD qg) ∗ l_tail ↦ #(fst x_tail) ∗ ⌜isLast x_tail xs⌝ ∗ TokE qg ∗ TokUpdated qg)%I with "[Hcases HTokE]" as "(HToknE & HEnqueue_Both)".
	{
		iDestruct "Hcases" as "[HStatic | [HEnqueue | [HDequeue | HBoth]]]".
		- iDestruct "HStatic" as "(Hl_head & Hl_tail & H_isLast & HToknE & HToknD & HTokUpdated)". iFrame. iLeft. iFrame.
		- admit. (* Impossible: TokE *)
		- iDestruct "HDequeue" as "(Hl_head & Hl_tail & H_isLast & HToknE & HToknD & HTokUpdated)". iFrame. iRight. iFrame.
		- admit. (* Impossible: TokE *)
	}
	iDestruct "HEnqueue_Both" as "(Hl_head_case & [Hl_tail1 Hl_tail2] & [%xs_fromtail %H_isLast] & HTokE & HTokUpdated)".
	wp_load.
	iModIntro.
	iAssert (fst x_tail ↦□ (snd x_tail, #(trd x_tail)) ∗ isLL (xs))%I with "[HisLL_xs]" as "[#Hx_tail HisLL_xs]".
	{ 
		rewrite H_isLast. iDestruct "HisLL_xs" as "[Hnull Hchain]".
		destruct xs_fromtail.
		- iPoseProof "Hchain" as "#Hchain". iFrame. auto.
		- iDestruct "Hchain" as "[#H1 H2]"; iFrame. auto.
	}
	iDestruct "HTokUpdated" as "[HTokBefore HTokAfter]".
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	iSplitL "Hl_head_case Hl_tail1 HTokE HTokBefore HisLL_xs".
	(* Close in Enqueue / Both : Before *)
	{  
		iNext. iExists xs, xs_rest, xs_old, x_head, x_tail.
		iSplitR; first done.
		iSplitL "HisLL_xs"; first done.
		iDestruct "Hl_head_case" as "[[Hl_head HToknD] | [Hl_head HTokD]]".
		1: iRight; iLeft.
		2: iRight; iRight; iRight.
		all: iFrame; iLeft; iFrame; iPureIntro; exists xs_fromtail; done.
	}
	wp_load.
	wp_pures.
	wp_bind (#(trd x_tail) <- #l'ₙ₁)%E.
	iInv "H_queue_inv" as "(%xs_2 & %xs_rest_2 & %xs_old_2 & %x_head_2 & %x_tail_2 & #Hxs_eq_2 & HisLL_xs_2 & >Hcases_2)".
	(* Open in Enqueue / Both : Before *)
	iAssert (ToknE qg ∗ TokAfter qg ∗ (l_head ↦ #(fst x_head_2) ∗ ToknD qg ∨ l_head ↦{#1 / 2} #(fst x_head_2) ∗ TokD qg) ∗ l_tail ↦{#1 / 2} #(fst x_tail_2) ∗ (⌜isLast x_tail_2 xs_2⌝ ∗ TokBefore qg) ∗ TokE qg)%I with "[Hcases_2 HToknE HTokAfter]" as "(HToknE & HTokAfter & HEnqueue_Both)".
	{
		iDestruct "Hcases_2" as "[HStatic | [HEnqueue | [HDequeue | HBoth]]]".
		- admit. (* Impossible: ToknE *)
		- iDestruct "HEnqueue" as "(Hl_head & Hl_tail1 & [([%xs_fromtail_2 %H_isLast_2] & HTokBefore) | ((%x_new_2 & %xs_fromtail_2 & %H_isSndLast) & HTokAfter2)] & HTokE & HToknD)".
			+ iFrame. iSplitL.
				* iLeft. iSplitL "Hl_head"; done. 
				* iPureIntro. exists xs_fromtail_2; done.
			+ admit. (* Impossible: TokAfter*)
		- admit. (* Impossible: ToknE *)
		- iDestruct "HBoth" as "(Hl_head & Hl_tail1 & [([%xs_fromtail_2 %H_isLast_2] & HTokBefore) | ((%x_new_2 & %xs_fromtail_2 & %H_isSndLast) & HTokAfter2)] & HTokE & HToknD)".
			+ iFrame. iSplitL.
				* iRight. done.
				* iPureIntro. exists xs_fromtail_2; done.
			+ admit. (* Impossible: TokAfter *)
	}
	iDestruct "HEnqueue_Both" as "(Hl_head_case & Hl_tail1 & ([%xs_fromtail_2 %H_isLast_2] & HTokBefore) & HTokE)".
	iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]".
	iAssert (▷(trd x_tail ↦ NONEV ∗ isLL_chain xs_2))%I with "[HisLL_xs_2]" as "[Hnull HisLL_chain_xs_2]".
	{
		iNext.
		iAssert (fst x_tail_2 ↦□ (snd x_tail_2, #(trd x_tail_2)) ∗ isLL (xs_2))%I with "[HisLL_xs_2]" as "[#Hx_tail_2 HisLL_xs_2]".
		{
			rewrite H_isLast_2. iDestruct "HisLL_xs_2" as "[Hnull Hchain]".
			destruct xs_fromtail_2.
			- iPoseProof "Hchain" as "#Hchain". iFrame. auto.
			- iDestruct "Hchain" as "[#H1 H2]"; iFrame. auto.
		}
		iAssert (⌜x_tail = x_tail_2⌝%I) as "<-".
		{ iApply fst_equal; auto. }
		by rewrite H_isLast_2.
	}
	wp_store.
	iAssert (fst x_tail_2 ↦□ (snd x_tail_2, #(trd x_tail_2)) ∗ isLL_chain xs_2)%I with "[HisLL_chain_xs_2]" as "[#Hx_tail_2 HisLL_chain_xs_2]".
	{
		rewrite H_isLast_2. destruct xs_fromtail_2.
		- iPoseProof "HisLL_chain_xs_2" as "#HisLL_chain_xs_2". iFrame. auto.
		- iDestruct "HisLL_chain_xs_2" as "[#H1 H2]"; iFrame. auto.
	}
	iAssert (⌜x_tail = x_tail_2⌝%I) as "<-".
	{ iApply fst_equal; auto. }
	iMod (pointsto_persist with "Hnull") as "#Hnull".
	iDestruct "Hl_tail" as "[Hl_tail1 Hl_tail2]".
	iModIntro.
	set x_new := (l'ₙ₁, SOMEV v, lₙ₂).
	set xs_new := x_new :: xs_2.
	iAssert (isLL xs_new) with "[Hlₙ₂ HisLL_chain_xs_2]" as "HisLL_xs_new".
	{
		unfold xs_new, isLL. iFrame. rewrite H_isLast_2. iFrame. auto.
	}
	iPoseProof (isLL_and_chain with "HisLL_xs_new") as "[HisLL_xs_new #HisLL_chain_xs_new]".
	iSplitL "Hl_head_case Hl_tail1 HTokE HTokAfter HisLL_xs_new".
	(* Close in Enqueue / Both: After *)
	{
		iNext. iExists xs_new, (x_new :: xs_rest_2), xs_old_2, x_head_2, x_tail.
		iPoseProof "Hxs_eq_2" as "%Hxs_eq_2".
		iSplitR. { iPureIntro. unfold xs_new. cbn. rewrite Hxs_eq_2. auto. }
		iFrame.
		iDestruct "Hl_head_case" as "[[Hl_head HToknD] | [Hl_head HTokD]]".
		1: iRight; iLeft.
		2: iRight; iRight; iRight.
		all: iFrame; iRight; iFrame; iPureIntro; exists x_new, xs_fromtail_2;
		unfold xs_new; by rewrite H_isLast_2.
	}
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (#l_tail <- #l'ₙ₁)%E.
	iInv "H_queue_inv" as "(%xs_3 & %xs_rest_3 & %xs_old_3 & %x_head_3 & %x_tail_3 & #Hxs_eq_3 & HisLL_xs_3 & >Hcases_3)".
	(* Open in Enqueue / Both : After *)
	iAssert (ToknE qg ∗ TokBefore qg ∗ (l_head ↦ #(fst x_head_3) ∗ ToknD qg ∨ l_head ↦{#1 / 2} #(fst x_head_3) ∗ TokD qg) ∗ l_tail ↦{#1 / 2} #(fst x_tail_3) ∗ (⌜isSndLast x_tail_3 xs_3⌝ ∗ TokAfter qg) ∗ TokE qg)%I with "[Hcases_3 HToknE HTokBefore]" as "(HToknE & HTokBefore & HEnqueue_Both)".
	{
		iDestruct "Hcases_3" as "[HStatic | [HEnqueue | [HDequeue | HBoth]]]".
		- admit. (* Impossible: ToknE *)
		- iDestruct "HEnqueue" as "(Hl_head & Hl_tail1 & [([%xs_fromtail_3 %H_isLast_3] & HTokBefore2) | ((%x_new_2 & %xs_fromtail_3 & %H_isSndLast) & HTokAfter)] & HTokE & HToknD)".
			+ admit. (* Impossible: TokBefore*)
			+ iFrame. iSplitL.
				* iLeft. iSplitL "Hl_head"; done. 
				* iPureIntro. exists x_new_2, xs_fromtail_3; done.
		- admit. (* Impossible: ToknE *)
		- iDestruct "HBoth" as "(Hl_head & Hl_tail1 & [([%xs_fromtail_3 %H_isLast_3] & HTokBefore2) | ((%x_new_2 & %xs_fromtail_3 & %H_isSndLast) & HTokAfter)] & HTokE & HTokD)".
			+ admit. (* Impossible: TokBefore*)
			+ iFrame. iSplitL.
				* iRight. done.
				* iPureIntro. exists x_new_2, xs_fromtail_3; done.
	}
	iDestruct "HEnqueue_Both" as "(Hl_head_case & Hl_tail1 & ((%x_new_2 & %xs_fromtail_3 & %H_isSndLast) & HTokAfter) & HTokE)".
	iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq2]".
	rewrite dfrac_op_own.
	rewrite Qp.half_half.
	wp_store.
	iModIntro.
	iAssert (isLL xs_3 ∗ isLL_chain xs_3)%I with "[HisLL_xs_3]" as "[HisLL_xs_3 #HisLL_chain_xs_3]".
	{ by iApply isLL_and_chain. }
	iAssert (⌜x_tail_3 = x_tail⌝)%I as "%Heq_x_tail".
	{
		iApply (isLL_chain_agree x_tail_3 x_tail [x_new_2] [] [] []).
		- by simplify_eq.
		- subst. iPoseProof (isLL_chain_split [x_new_2 ; x_tail_3] xs_fromtail_3 with "HisLL_chain_xs_3") as "[Hgoal _]". done.
		- subst. iPoseProof (isLL_chain_split [x_tail] xs_fromtail with 
		"HisLL_chain_xs") as "[Hgoal _]". done.
	}
	iAssert (⌜x_new_2 = x_new⌝)%I as "%Heq_x_new".
	{
		iApply (isLL_chain_agree_next x_tail x_new_2 x_new [] [] [] []).
		- subst. iPoseProof (isLL_chain_split [x_new_2; x_tail] xs_fromtail_3 with "HisLL_chain_xs_3") as "[Hgoal _]". done.
		- subst. iPoseProof (isLL_chain_split [x_new; x_tail] xs_fromtail_2 with "HisLL_chain_xs_new") as "[Hgoal _]". done.
	}
	iSplitR "HTokE Hlocked_γ_Tlock HΦ".
	(* Close in Static/Dequeue *)
	{
		iNext. iExists xs_3, xs_rest_3, xs_old_3, x_head_3, x_new.
		iSplitR; first done.
		iFrame.
		iDestruct "Hl_head_case" as "[[Hl_head HToknD] | [Hl_head HTokD]]".
		1: iLeft. (* Close Static *)
		2: iRight; iRight; iLeft. (* Close Dequeue *)
		all: iFrame; iPureIntro; exists (x_tail_3 :: xs_fromtail_3); subst; done.
	}
	wp_seq.
	wp_load.
	wp_pures.
	wp_apply (release_spec with "[$H_tlock $HTokE $Hlocked_γ_Tlock]").
	done.
Admitted.

Lemma dequeue_spec Q (qg : Qgnames) : {{{ is_queue Q qg}}} 
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
	iInv "H_queue_inv" as "H_queue_inv_inv".
	iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_inv") as "H_queue_inv_inv".
	iDestruct "H_queue_inv_inv" as "(%xs & %xs_rest & %xs_old & %x_head & %x_tail & >%H_eq_xs & H_isLL_xs & [ [Hl_head HToknD] | [Hl_head HTokD2] ] & H_tail)".
	2: admit. (* Impossible: TokD*)
	wp_load.
	iModIntro.
	iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
	iPoseProof (isLL_and_chain with "H_isLL_xs") as "[H_isLL_xs #H_isLL_chain_xs_1]".
	iSplitL "Hl_head2 HTokD H_tail H_isLL_xs".
	{
		iNext. iApply queue_invariant_equiv_simple.
		iExists xs, xs_rest, xs_old, x_head, x_tail. iFrame.
		iSplitR; first done. iRight. done.
	}
	wp_let.
	subst.
	iPoseProof (isLL_chain_node with "H_isLL_chain_xs_1") as "H_fst_x_head".
	wp_load.
	wp_pures.
	wp_bind (! #(trd x_head))%E.
	iInv "H_queue_inv" as "H_queue_inv_inv".
	iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_inv") as "H_queue_inv_inv".
	iDestruct "H_queue_inv_inv" as "(%xs_2 & %xs_rest_2 & %xs_old_2 & %x_head_2 & %x_tail_2 & >%H_eq_xs_2 & H_isLL_xs_2 & [ [Hl_head >HToknD2] | [>Hl_head2 HTokD] ] & H_tail)".
	1: admit. (* Impossible: ToknD*)
	iPoseProof (isLL_and_chain with "H_isLL_xs_2") as "[H_isLL_xs_2 #HisLL_chain_xs_2]".
	iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq2]".
	iAssert (▷⌜x_head_2 = x_head⌝)%I as ">%H_x_head_eq".
	{
		iNext.
		simplify_eq.
		iApply (isLL_chain_agree x_head_2 x_head xs_rest_2 xs_old_2 xs_rest xs_old); auto.
	}
	subst.
	(* Case analysis: Is queue empty? *)
	destruct xs_rest_2 as [| x_tail_2_2 xs_rest_2'].
	- (* Queue is empty. *)
	  iDestruct "H_isLL_xs_2" as "[Htrd_x_head_null _]".
	  wp_load.
	  iModIntro.
	  iSplitL "Hl_head HToknD H_tail Htrd_x_head_null".
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
	  destruct (list_first_last x_tail_2_2 xs_rest_2') as [x_head_next [xs_rest_2'' Hxs_rest_eq]].
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
	  iDestruct "H_isLL_chain_x_head_next" as "(Hfst_x_head_next & Htrd_x_head_next & Hfst_x_head)".
	  wp_load.
	  iModIntro.
	  iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
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
	  wp_bind (#l_head <- #(fst x_head_next))%E.
	  iInv "H_queue_inv" as "H_queue_inv_inv".
	  iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_inv") as "H_queue_inv_inv".
	  iDestruct "H_queue_inv_inv" as "(%xs_3 & %xs_rest_3 & %xs_old_3 & %x_head_3 & %x_tail_3 & >%H_eq_xs_3 & H_isLL_xs_3 & [ [Hl_head >HToknD2] | [>Hl_head2 HTokD] ] & H_tail)".
	  1: admit. (* Impossible ToknD *)
	  iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq3]".
	  rewrite dfrac_op_own.
	  rewrite Qp.half_half.
	  wp_store.
	  iModIntro.
	  iSplitL "Hl_head H_tail HToknD H_isLL_xs_3".
	  {
		iNext.
		iPoseProof (isLL_and_chain with "H_isLL_xs_3") as "[H_isLL_xs_3 #H_isLL_chain_xs_3]".
		subst.
		iAssert (⌜x_head = x_head_3⌝)%I as "->".
		{
			iApply (isLL_chain_agree x_head x_head_3 xs_rest xs_old xs_rest_3 xs_old_3); by simplify_eq.
		}
		(* Sync up xs_rest_2 with xs_rest_3 *)
		destruct xs_rest_3 as [|x_tail_3_2 xs_rest_3'].
		- (* Impossible case. xs_rest_3 must contain at least one element. *)
		  iDestruct "H_isLL_xs_3" as "[H_x_head_3_null _]".
		  iCombine "H_x_head_3_null Htrd_x_head_next" as "_" gives "[_ %Hcontra]".
		  simplify_eq.
		- destruct (list_first_last x_tail_3_2 xs_rest_3') as [x_head_next_3 [xs_rest_3'' Hxs_rest_eq_3]].
		  rewrite Hxs_rest_eq_3.
		  rewrite <- app_assoc. rewrite <- app_assoc.
		  iAssert (⌜x_head_next = x_head_next_3⌝)%I as "->"; first by iApply isLL_chain_agree_next.
		  iApply queue_invariant_equiv_simple.
		  iExists (xs_rest_3'' ++ [x_head_next_3] ++ [x_head_3] ++ xs_old_3), xs_rest_3'', ([x_head_3] ++ xs_old_3), x_head_next_3, x_tail_3.
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
Admitted.

End proofs.