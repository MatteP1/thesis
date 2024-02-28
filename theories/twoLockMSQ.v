From iris.algebra Require Import excl.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Export invariants.
From iris.unstable.heap_lang Require Import interpreter.

Local Existing Instance spin_lock.

(* Definition get_some : val :=
	rec: "get_some" "x" :=
		match: "x" with
			  NONE => #() #() (* Crash if not some *)
			| SOME "y" => "y"
		end. *)

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

Record Qgnames := {γ_Hlock : gname;
				  γ_Tlock : gname;
				  γ_E : gname;
				  γ_nE : gname;
				  γ_D : gname;
				  γ_nD : gname;
				  γ_Before : gname;
				  γ_After : gname;
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
Notation fst x := (let '(a, b, c) := x in a).
Notation snd x := (let '(a, b, c) := x in b).
Notation trd x := (let '(a, b, c) := x in c).


Fixpoint isLL_chain (xs : list (loc * val * loc) ) : iProp Σ :=
	match xs with
	| [] => True
	| [(l'₁, v₁, l₂)] => l'₁ ↦□ (v₁, #l₂)
	| (l'ᵢ₁, vᵢ₁, lᵢ₂) :: (((l'ᵢ, vᵢ, lᵢ₁) :: xs'') as xs') =>
		l'ᵢ₁ ↦□ (vᵢ₁, #lᵢ₂) ∗
		lᵢ₁ ↦□ #l'ᵢ₁ ∗ isLL_chain xs'
	end.

Definition isLL (xs : list (loc * val * loc) ) : iProp Σ :=
	match xs with
	| [] => True
	| (l'ₙ, vₙ, lₙ₁) :: xs' => lₙ₁ ↦ NONEV ∗ isLL_chain xs
	end.

Lemma isLL_extend : forall xs (x y : (loc * val * loc)),
	{{{ isLL (x :: xs) ∗
		fst y ↦□ (snd y, #(trd y)) ∗
		trd y ↦ NONEV }}}
			#(trd x) <- #(fst y)
	{{{ w, RET w; isLL (y :: x :: xs) }}}.
Proof.
	iIntros (xs ((l'ₙ, vₙ), lₙ₁) ((l'ₙ₁, vₙ₁), lₙ₂) Φ) "([Hlₙ₁ HisLL_chain_xs] & Hfsty & Htrdy) HΦ".
	wp_store.
	iMod (pointsto_persist with "Hlₙ₁") as "Hlₙ₁".
	iApply "HΦ".
	iModIntro. iFrame.
Qed.

(* TODO: Remove *)
Definition points_to_last (q : Qp) (l : loc) (xs : list (loc * val * loc)) : iProp Σ :=
	∃ x_last xs' , ⌜xs = x_last :: xs'⌝ ∗ l ↦{# q} #(fst x_last).

(* TODO: Remove *)
Definition points_to_snd_last (q : Qp) (l : loc) (xs : list (loc * val * loc)) : iProp Σ :=
	∃ x_snd_last x_last xs' , ⌜xs = x_last :: x_snd_last :: xs'⌝ ∗ l ↦{# q} #(fst x_snd_last).

Definition isLast {A} (x : A) xs := ∃ xs_rest, xs = x :: xs_rest.
Definition is2Last {A} (x : A) xs := ∃ x_first xs_rest, xs = x_first :: x :: xs_rest.

(* TODO: Add tokens *)
Definition queue_invariant (head tail : loc) : iProp Σ :=
	∃ xs xs_rest x_head xs_old,
	⌜xs = xs_rest ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	(
		(* Static *)
		(
			head ↦ #(fst x_head) ∗
			∃x_last, ⌜isLast x_last xs⌝ ∗ tail ↦ #(fst x_last)
		)
		∨
		(* Enqueue *)
		(
			head ↦ #(fst x_head) ∗
			(points_to_last (1/2)%Qp tail xs ∨ points_to_snd_last ((1/2)%Qp) tail xs)
			(* TODO: change to using isLast/is2last *)
		)
		∨
		(* Dequeue *)
		(
			head ↦{# 1/2} #(fst x_head) ∗
			points_to_last (1)%Qp tail xs
			(* TODO: change to using isLast/is2last *)
		)
		∨
		(* Both *)
		(
			head ↦{# 1/2} #(fst x_head) ∗
			(points_to_last (1/2)%Qp tail xs ∨ points_to_snd_last (1/2)%Qp tail xs)
			(* TODO: change to using isLast/is2last *)
		)
	).

Definition is_queue (q : val) (Q_γ: Qgnames) : iProp Σ :=
	∃ head tail : loc, ∃ H_lock T_lock : val, 
	∃ l : loc , ⌜q = #l⌝ ∗
		l ↦□ ((#head, #tail), (H_lock, T_lock)) ∗
		inv N (queue_invariant head tail) ∗
		is_lock Q_γ.(γ_Hlock) H_lock (TokD Q_γ) ∗
		is_lock Q_γ.(γ_Tlock) T_lock (TokE Q_γ).


Lemma initialize_spec : {{{ True }}} 
							initialize #() 
						{{{ v Q_γ, RET v; is_queue v Q_γ}}}.
Proof.
	iIntros (Φ) "_ HΦ".
	wp_lam. 
	wp_pures.
	iMod (own_alloc (Excl ()) ) as (γ_E) "Hγ_E"; first done.
	wp_alloc null' as "Hnull'".
	iMod (pointsto_persist with "Hnull'") as "#Hnull'".
	wp_alloc null as "Hnull".
	wp_pures.
	wp_alloc node' as "Hnode'".
	iMod (pointsto_persist with "Hnode'") as "#Hnode'".
	wp_pures.
	wp_alloc head as "Hhead".
	wp_let.
	iMod (inv_alloc N _ (∃x xs, node_inv node' (x :: xs)) with "[Hnull]") as "#HnodeInv".
	{
		iNext. iExists NONEV, []. cbn. iExists null. auto.
	}
	iAssert (head_prop head)%I with "[Hhead]" as "Hhead_prop".
	{
		iExists node'. auto.
	}
	wp_alloc tail as "Htail".
	wp_let.
	iAssert (head_prop tail)%I with "[Htail]" as "Htail_prop".
	{
		iExists node'. auto.
	}
	wp_apply (newlock_spec with "Hhead_prop").
	iIntros (hlock γh) "Hγh".
	wp_let.
	wp_apply (newlock_spec with "Htail_prop").
	iIntros (tlock γt) "Hγt".
	wp_let.
	wp_alloc queue as "Hqueue".
	iApply "HΦ".
	iExists head, tail, hlock, tlock, γh, γt, queue.
	iSplitR.
	{ done. }
	iFrame.
	done.
Qed.

Lemma enqueue_spec Q (v : val) : {{{ is_queue Q }}}
							 enqueue Q v 
						 {{{w, RET w; True}}}.
Proof.
	iIntros (Φ) "(%head & %tail & %H_lock & %T_lock & %γh & %γt & 
				  %l & -> & Hq & #H_hlock & #H_tlock) HΦ".
	wp_lam.
	wp_let.
	wp_pures.
	wp_alloc null' as "Hnull'".
	iMod (pointsto_persist with "Hnull'") as "#Hnull'".
	wp_alloc null as "Hnull".
	wp_alloc node' as "Hnode'".
	iMod (pointsto_persist with "Hnode'") as "#Hnode'".
	wp_let.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "H_tlock").
	iIntros "(Hlocked_γt & %tail' & Htail & Htail_inv)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (! #tail)%E.
	iInv "Htail_inv" as "(%x & %xs & H)". simpl in *.
	iDestruct "H" as "(%tail_next & #Htail' & %tail_next' & Htail_next & Htail_next_inv)".
	wp_load.
	iSplitL "Htail_next Htail_next_inv".
	{  
		iExists x, xs, tail_next. iModIntro. iNext. iSplitR; first done.
		iExists tail_next'. iSplitL "Htail_next"; done.
	}
	iModIntro.
	wp_load.
	wp_lam.
	wp_match.
	wp_pures.
	wp_bind (#tail_next <- #node')%E.
	(* STUCK: Don't know that tail_next points to something. *)
	iInv "Htail_next_inv" as "(%l' & Htail_next & #Hl')".
	wp_store.
	iModIntro.
	iSplitL "Htail_next".
	{ iNext. iExists node. iFrame. }
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (#tail <- #node)%E.
	iInv "Hinv" as "(%tl2 & Htail & Htl2node)".
	wp_store.
	iSplitL "Htail Hnode Hnext Hnull".
	{
		iMod (inv_alloc N _ (points_to_node next) with "[Hnext Hnull]") as "#Hnext".
		{
			iNext. iExists null. eauto.
		}
		iModIntro. iNext. iExists node. iFrame. iExists next, (SOMEV v).
		iSplitR. done. done.
	}
	iModIntro.
	wp_seq.
	wp_load.
	wp_pures.
	wp_apply (release_spec with "[$H_tlock $Hlocked_γt $Hinv]").
	iApply "HΦ".
Qed.

Lemma dequeue_spec Q : {{{ is_queue Q }}} 
							 dequeue Q 
						 {{{v, RET v; True}}}.
Proof.
	iIntros (Φ) "(%head & %tail & %H_lock & %T_lock & %γh & %γt & 
				  %l & -> & Hq & #H_hlock & #H_tlock) HΦ".
	wp_lam.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "H_hlock").
	iIntros "(Hlocked_γh & #Hinv)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (! #head)%E.
	iInv "Hinv" as "(%hl & Hhead & %hl_next & %x & #Hhl & #Hinvn)".
	wp_load.
	iSplitL "Hhead".
	{ 
		iExists hl. iModIntro. iNext. iFrame. iExists hl_next, x.
		iFrame. auto.
	}
	iModIntro.
	wp_let.
	wp_load.
	wp_lam.
	wp_match.
	wp_pures.
	wp_bind (! #hl_next)%E.
	iInv "Hinvn" as ">(%r & %next & Hhl_next & #Hr & %Hor)".
	wp_load.
	iModIntro.
	iSplitL "Hhl_next".
	{
		iNext. iExists r, next. auto.
	}
	wp_let.
	destruct Hor as [Heq | [xnext [y Heq]]]; subst.
	- wp_load.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_apply (release_spec with "[$H_hlock $Hinv $Hlocked_γh]").
	  iIntros "_".
	  wp_seq.
	  iApply "HΦ".
	  done.
	- wp_load.
	  wp_pures.
	  wp_load.
	  wp_lam.
	  wp_match.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  wp_bind (#head <- #r)%E.
	  iInv "Hinv" as "(%hl2 & Hhead & %hl2_next & %z & #Hhl2 & #Hinvn2)".
	  wp_store.
Admitted.

End proofs.