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

(* Notation for nodes *)
Definition n_in {A B C} (x : A * B * C ) := (let '(a, b, c) := x in a).
Definition n_val {A B C} (x : A * B * C ) := (let '(a, b, c) := x in b).
Definition n_out {A B C} (x : A * B * C ) := (let '(a, b, c) := x in c).


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
(* TODO: Prove this! *)
Global Instance isLL_chain_persistent xs : Persistent (isLL_chain xs).
Proof.
	Admitted.

Definition isLL (xs : list (loc * val * loc) ) : iProp Σ :=
	match xs with
	| [] => True
	| x :: xs' => (n_out x) ↦ NONEV ∗ isLL_chain xs
	end.

Lemma isLL_and_chain : forall xs,
	isLL xs -∗
	isLL xs ∗ isLL_chain xs.
Proof.
	iIntros (xs) "HisLLxs".
	destruct xs as [| x' xs']; first done.
	unfold isLL.
	iPoseProof "HisLLxs" as "[Hn_outx' #HisLLxs]".
	iFrame.
	by iSplit.
Qed.

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

Lemma isLL_chain_node : forall xs_1 x xs_2,
	isLL_chain (xs_1 ++ x :: xs_2) -∗
	n_in(x) ↦□ (n_val x, #(n_out x)).
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
		* iDestruct "HisLL_chain_xs_ys" as "(Hx' & Hn_outy' & HIsLL_chain_ys')".
		  fold isLL_chain. iSplit; done.
	  + iAssert (isLL_chain (x'' :: xs'') ∗ isLL_chain ys)%I as "[IHxs' IHys]".
	  	{
			iApply "IH". iDestruct "HisLL_chain_xs_ys" as "(_ & _ & Hchain)"; done.
		}
		iSplit; try done.
		iDestruct "HisLL_chain_xs_ys" as "(Hn_inx' & Hn_outx'' & _)".
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
	iDestruct "HisLL_chain_yx" as "(#Hn_iny_2 & #Hn_outy_1 & Hn_iny_1)".
	iDestruct "HisLL_chain_zx" as "(#Hfsztz_2 & #Hn_outz_1 & Hn_inz_1)".
	iCombine "Hn_outy_1 Hn_outz_1" gives "[_ %Heq_n_in]".
	simplify_eq.
	iApply n_in_equal; try done. by rewrite Heq_n_in.
Qed.

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

Lemma initialize_spec : 
	{{{ True }}} 
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
	(* Open in Static / Dequeue *)
	iInv "H_queue_inv" as "H_queue_inv_inv".
	iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_inv") as "H_queue_inv_inv".
	iDestruct "H_queue_inv_inv" as "(%xs & %xs_rest & %xs_old & %x_head & %x_tail & >%H_eq_xs & HisLL_xs & H_head & [ ( [Hl_tail1 Hl_tail2] & >[%xs_fromtail %H_isLast] & HToknE & HTokUpdated ) | (_ & >HTokE2 & _) ])".
	2: admit. (* Impossible: TokE *)
	wp_load.
	iModIntro.
	iAssert (n_in x_tail ↦□ (n_val x_tail, #(n_out x_tail)) ∗ isLL (xs))%I with "[HisLL_xs]" as "[#Hx_tail HisLL_xs]".
	{ 
		rewrite H_isLast. iDestruct "HisLL_xs" as "[Hnull Hchain]".
		destruct xs_fromtail.
		- iPoseProof "Hchain" as "#Hchain". iFrame. auto.
		- iDestruct "Hchain" as "[#H1 H2]"; iFrame. auto.
	}
	iDestruct "HTokUpdated" as "[HTokBefore HTokAfter]".
	iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
	iSplitL "H_head Hl_tail1 HTokE HTokBefore HisLL_xs".
	(* Close in Enqueue / Both : Before *)
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
	wp_bind (#(n_out x_tail) <- #l'ₙ₁)%E.
	(* Open in Enqueue / Both : Before *)
	iInv "H_queue_inv" as "H_queue_inv_inv".
	iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_inv") as "H_queue_inv_inv".
	iDestruct "H_queue_inv_inv" as "(%xs_2 & %xs_rest_2 & %xs_old_2 & %x_head_2 & %x_tail_2 & >%H_eq_xs_2 & HisLL_xs_2 & H_head & [ ( _ & _ & >HToknE2 & _ ) | (>Hl_tail1 & HTokE & [[>[%xs_fromtail_2 %H_isLast_2] HTokBefore] | [_ >HTokAfter2]]) ])".
	1,3: admit. (* Impossible: ToknE & TokAfter *)
	iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]".
	iAssert (▷(n_out x_tail ↦ NONEV ∗ isLL_chain xs_2))%I with "[HisLL_xs_2]" as "[Hnull HisLL_chain_xs_2]".
	{
		iNext.
		iAssert (n_in x_tail_2 ↦□ (n_val x_tail_2, #(n_out x_tail_2)) ∗ isLL (xs_2))%I with "[HisLL_xs_2]" as "[#Hx_tail_2 HisLL_xs_2]".
		{
			rewrite H_isLast_2. iDestruct "HisLL_xs_2" as "[Hnull Hchain]".
			destruct xs_fromtail_2.
			- iPoseProof "Hchain" as "#Hchain". iFrame. auto.
			- iDestruct "Hchain" as "[#H1 H2]"; iFrame. auto.
		}
		iAssert (⌜x_tail = x_tail_2⌝%I) as "<-".
		{ iApply n_in_equal; auto. }
		by rewrite H_isLast_2.
	}
	wp_store.
	iAssert (n_in x_tail_2 ↦□ (n_val x_tail_2, #(n_out x_tail_2)) ∗ isLL_chain xs_2)%I with "[HisLL_chain_xs_2]" as "[#Hx_tail_2 HisLL_chain_xs_2]".
	{
		rewrite H_isLast_2. destruct xs_fromtail_2.
		- iPoseProof "HisLL_chain_xs_2" as "#HisLL_chain_xs_2". iFrame. auto.
		- iDestruct "HisLL_chain_xs_2" as "[#H1 H2]"; iFrame. auto.
	}
	iAssert (⌜x_tail = x_tail_2⌝%I) as "<-".
	{ iApply n_in_equal; auto. }
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
	iSplitL "H_head Hl_tail1 HTokE HTokAfter HisLL_xs_new".
	(* Close in Enqueue / Both: After *)
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
	wp_bind (#l_tail <- #l'ₙ₁)%E.
	(* Open in Enqueue / Both : After *)
	iInv "H_queue_inv" as "H_queue_inv_inv".
	iPoseProof (queue_invariant_equiv_simple with "H_queue_inv_inv") as "H_queue_inv_inv".
	iDestruct "H_queue_inv_inv" as "(%xs_3 & %xs_rest_3 & %xs_old_3 & %x_head_3 & %x_tail_3 & >%H_eq_xs_3 & HisLL_xs_3 & H_head & [ ( _ & _ & >HToknE2 & _ ) | (>Hl_tail1 & HTokE & [[_ >HTokBefore2] | [>(%x_new_2 & %xs_fromtail_3 & %H_isSndLast) HTokAfter]])])".
	1,2: admit. (* Impossible: ToknE & TokBefore *)
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
		- rewrite H_isSndLast. iPoseProof (isLL_chain_split [x_new_2 ; x_tail_3] xs_fromtail_3 with "HisLL_chain_xs_3") as "[Hgoal _]". done.
		- rewrite H_isLast. iPoseProof (isLL_chain_split [x_tail] xs_fromtail with 
		"HisLL_chain_xs") as "[Hgoal _]". done.
	}
	iAssert (⌜x_new_2 = x_new⌝)%I as "%Heq_x_new".
	{
		iApply (isLL_chain_agree_next x_tail x_new_2 x_new [] [] [] []).
		- rewrite H_isSndLast Heq_x_tail. iPoseProof (isLL_chain_split [x_new_2; x_tail] xs_fromtail_3 with "HisLL_chain_xs_3") as "[Hgoal _]". done.
		- unfold xs_new. rewrite H_isLast_2. iPoseProof (isLL_chain_split [x_new; x_tail] xs_fromtail_2 with "HisLL_chain_xs_new") as "[Hgoal _]". done.
	}
	iSplitR "HTokE Hlocked_γ_Tlock HΦ".
	(* Close in Static/Dequeue *)
	{
		iNext.
		iApply queue_invariant_equiv_simple.
		iExists xs_3, xs_rest_3, xs_old_3, x_head_3, x_new.
		iSplitR; first done.
		iFrame.
		iLeft.
		iFrame.
		iExists (x_tail_3 :: xs_fromtail_3); subst; done.
	}
	wp_seq.
	wp_load.
	wp_pures.
	wp_apply (release_spec with "[$H_tlock $HTokE $Hlocked_γ_Tlock]").
	done.
Admitted.

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
	iPoseProof (isLL_chain_node with "H_isLL_chain_xs_1") as "H_n_in_x_head".
	wp_load.
	wp_pures.
	wp_bind (! #(n_out x_head))%E.
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
	  iDestruct "H_isLL_xs_2" as "[Hn_out_x_head_null _]".
	  wp_load.
	  iModIntro.
	  iSplitL "Hl_head HToknD H_tail Hn_out_x_head_null".
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
	  iDestruct "H_isLL_chain_x_head_next" as "(Hn_in_x_head_next & Hn_out_x_head_next & Hn_in_x_head)".
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
	  wp_bind (#l_head <- #(n_in x_head_next))%E.
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
		  iCombine "H_x_head_3_null Hn_out_x_head_next" as "_" gives "[_ %Hcontra]".
		  simplify_eq.
		- destruct (exists_first (x_tail_3_2 :: xs_rest_3')) as [x_head_next_3 [xs_rest_3'' Hxs_rest_eq_3]]; first done.
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




(* SEQUENTIAL *)

Record QSeqgnames := {γ_Hlock_seq 	: gname;
					  γ_Tlock_seq 	: gname;
					 }.

Definition is_queue_seq (q : val) (xs_queue: list (loc * val * loc)) (Q_γ: QSeqgnames) : iProp Σ :=
	∃ head tail : loc, ∃ H_lock T_lock : val, ∃x_head x_tail : (loc * val * loc),
	∃ l : loc , ⌜q = #l⌝ ∗
		l ↦□ ((#head, #tail), (H_lock, T_lock)) ∗
		isLL (xs_queue ++ [x_head]) ∗
		head ↦ #(n_in x_head) ∗
		tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail (xs_queue ++ [x_head])⌝ ∗
		is_lock Q_γ.(γ_Hlock_seq) H_lock (True) ∗
		is_lock Q_γ.(γ_Tlock_seq) T_lock (True).


Lemma initialize_spec_seq : 
	{{{ True }}} 
		initialize #() 
	{{{ v Q_γ, RET v; is_queue_seq v [] Q_γ }}}.
Proof.
	iIntros (Φ _) "HΦ".
	wp_lam.
	wp_alloc l_2 as "Hl_2".
	wp_alloc l'_1 as "Hl'_1".
	wp_pures.
	iMod (pointsto_persist with "Hl'_1") as "#Hl'_1".
	wp_pures.
	wp_apply (newlock_spec True); first done.
	iIntros (hlock γ_Hlock) "Hγ_Hlock".
	wp_let.
	wp_apply (newlock_spec True); first done.
	iIntros (tlock γ_Tlock) "Hγ_Tlock".
	wp_let.
	wp_alloc l_tail as "Hl_tail".
	wp_alloc l_head as "Hl_head".
	set (Queue_gnames := {| γ_Hlock_seq := γ_Hlock;
							γ_Tlock_seq := γ_Tlock;
					|}).
	wp_alloc l_queue as "Hl_queue".
	iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
	iApply ("HΦ" $! #l_queue Queue_gnames).
	iModIntro.
	iExists l_head, l_tail, hlock, tlock. 
	do 2 iExists (l'_1, NONEV, l_2).
	iExists l_queue.
	iFrame.
	do 3 (iSplit; first done).
	by iExists [].
Qed.

Lemma enqueue_spec_seq Q (v : val) (xs : list (loc * val * loc)) (qg : QSeqgnames) :
	{{{ is_queue_seq Q xs qg }}}
		enqueue Q v 
	{{{w x, RET w; ⌜n_val x = SOMEV v⌝ ∗ is_queue_seq Q (x :: xs) qg }}}.
Proof.
	iIntros (Φ) "(%l_head & %l_tail & %H_lock & %T_lock & %x_head & %x_tail &
				  %l_queue & -> & #Hl_queue & H_isLL_xs & Hl_head & Hl_tail &
				  %HisLast_x_tail & #H_hlock & #H_tlock) HΦ".
	destruct HisLast_x_tail as [xs_rest Hxs_split].
	rewrite Hxs_split.
	iDestruct "H_isLL_xs" as "[Hn_out_x_tail #H_isLL_chain_xs]".
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
	iIntros "(Hlocked_γ_Tlock & _)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_load.
	subst.
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
	iApply ("HΦ" $! #() (l'ₙ₁, SOMEV v, lₙ₂)).
	iSplit; first done.
	iExists l_head, l_tail, H_lock, T_lock, x_head, (l'ₙ₁, SOMEV v, lₙ₂), l_queue.
	iFrame.
	do 2 (iSplit; first done).
	iSplit.
	{
		iSimpl.
		rewrite Hxs_split.
		repeat iSplit; done.
	}
	iSplit; first by iExists (xs ++ [x_head]).
	iSplit; done.
Qed.

Lemma dequeue_spec_seq Q (xs : list (loc * val * loc)) (qg : QSeqgnames) : 
	{{{ is_queue_seq Q xs qg }}}
		dequeue Q
	{{{ v, RET v; (⌜xs = []⌝ ∗ ⌜v = NONEV⌝ ∗ is_queue_seq Q xs qg) ∨
				  (∃x xs', ⌜xs = xs' ++ [x]⌝ ∗ ⌜v = n_val x⌝ ∗
													is_queue_seq Q xs' qg) }}}.
Proof.
	iIntros (Φ) "(%l_head & %l_tail & %H_lock & %T_lock & %x_head & %x_tail &
				  %l_queue & -> & #Hl_queue & H_isLL_xs & Hl_head & Hl_tail &
				  %HisLast_x_tail & #H_hlock & #H_tlock) HΦ".
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
	iPoseProof (isLL_chain_node xs x_head [] with "[H_isLL_chain_xs]") as "Hn_in_x_head"; first done.
	wp_load.
	wp_pures.
	(* Is the queue empty? *)
	destruct xs as [| x' xs_queue' ].
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
	  do 2 (iSplit; first done).
	  iExists l_head, l_tail, H_lock, T_lock, x_head, x_tail, l_queue.
	  iFrame.
	  repeat iSplit; done.
	- (* Queue is not empty *)
	  destruct (exists_first (x' :: xs_queue')) as [x_head_next [xs_queue'' Hxs_queue_eq]]; first done.
	  rewrite Hxs_queue_eq.
	  iPoseProof (isLL_chain_split xs_queue'' [x_head_next; x_head] with "[H_isLL_chain_xs]") as "[_ H_isLL_chain_x_head_next]"; first by rewrite <- app_assoc.
	  iDestruct "H_isLL_chain_x_head_next" as "(Hn_in_x_head_next & H_n_out_x_head & _)".
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
	  iExists x_head_next, xs_queue''.
	  do 2 (iSplit; first done).
	  iExists l_head, l_tail, H_lock, T_lock, x_head_next, x_tail, l_queue.
	  iFrame.
	  do 2 (iSplit; first done).
	  iSplitL "H_isLL_xs".
	  {
		rewrite <- Hxs_queue_eq.
		iDestruct "H_isLL_xs" as "[H_n_out_x_tail _]".
		iFrame.
		iPoseProof (isLL_chain_split (x' :: xs_queue') [x_head] with "H_isLL_chain_xs") as "[HisLL_chain_no_head _]".
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