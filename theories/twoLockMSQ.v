From iris.algebra Require Import excl.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Export invariants.
From iris.unstable.heap_lang Require Import interpreter.

Local Existing Instance spin_lock.

Definition get_some : val :=
	rec: "get_some" "x" :=
		match: "x" with
			  NONE => #() #() (* Crash if not some *)
			| SOME "y" => "y"
		end.

Definition initialize : val := 
	rec: "initialize" <> := 
		let: "node" := ref (SOME (NONE, ref (ref(NONE)))) in
		let: "head" := ref "node" in
		let: "tail" := ref "node" in
		let: "H_lock" := newlock #() in
		let: "T_lock" := newlock #() in
		ref (("head", "tail"), ("H_lock", "T_lock")).

Definition enqueue : val := 
	rec: "enqueue" "Q" "value" :=
		let: "node" := ref (SOME (SOME "value", ref(ref(NONE)))) in
		acquire (Snd ( Snd (!"Q")));; (* Acqurie T_lock *)
		Snd (get_some !(!(Snd (Fst(!"Q"))))) <- "node" ;;
		Snd (Fst (!"Q")) <- "node" ;;
		release (Snd (Snd (!"Q"))).

Definition dequeue : val := 
	rec: "dequeue" "Q" := 
		acquire (Fst (Snd (!"Q")));; (* Acquire H_lock *)
		let: "node" := !(Fst (Fst (!"Q"))) in (* Get Head node *)
		let: "new_head" := !(Snd(get_some (!"node"))) in (* Find Head.Next *)
		if: !"new_head" = NONE then (* Check if Queue is empty *)
			(* No Next node. Queue is empty. *)
			release (Fst (Snd(!"Q"))) ;;
			NONEV
		else
			(* Queue not empty. Pop first element in Queue *)
			let: "value" := Fst (get_some (!"new_head")) in (* Get its value *)
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

Let N := nroot .@ "twoLockMSQ".

(* Fixpoint is_node_list (l : loc) xs : iProp Σ := 
	∃ l' : loc, l ↦ #l' ∗
	match xs with
	| [] => l' ↦□ NONEV
	| x :: xs' => 
		∃ (l_next : loc),
		l ↦□ (SOMEV (x, #l_next)) ∗
		is_node_list l_next xs'
	end. *)

Definition points_to_node (l : loc) : iProp Σ :=
	∃ (r : loc) (next : val), l ↦ #r ∗ r ↦□ next
					∗ ((⌜next = NONEV⌝) ∨ (∃ (next_next : loc) y, ⌜next = (SOMEV (y, #next_next))⌝)).

Definition is_node (l : loc) : iProp Σ :=
	∃ (l_next : loc) x,
		l ↦□ (SOMEV (x, #l_next)) ∗
		inv N (points_to_node (l_next)).

Definition queue_inv (t : loc) : iProp Σ :=
	∃ l : loc, t ↦ #l ∗ is_node l.

Definition is_queue (v : val) : iProp Σ :=
	∃ head tail : loc, ∃ H_lock T_lock : val, ∃ γH γT : gname, 
	∃ l : loc , ⌜v = #l⌝ ∗ 
		l ↦ ((#head, #tail), (H_lock, T_lock)) ∗
		is_lock γH H_lock (inv N (queue_inv head)) ∗
		is_lock γT T_lock (inv N (queue_inv tail)).

(* Definition is_queue (v : val) : iProp Σ :=
	∃ head tail : loc, ∃ H_lock T_lock : val, ∃ γH γT : gname, 
	∃ l : loc , ⌜v = #l⌝ ∗ 
				l ↦ ((#head, #tail), (H_lock, T_lock)) ∗
				is_lock γH H_lock (∃ head' next : loc, 
					∃ x,
						head ↦ #head' ∗ 
						head' ↦ (SOMEV (x, #next))
					)
				∗
				is_lock γT T_lock (
					∃ tail' next next' : loc, 
					∃ x,
						tail ↦ #tail' ∗ 
						tail' ↦ (SOMEV (x, #next)) ∗
						next ↦ #next' ∗
						next' ↦ NONEV
				  ). *)

Lemma initialize_spec : {{{ True }}} 
							initialize #() 
						{{{ v, RET v; is_queue v }}}.
Proof.
	iIntros (Φ) "_ HΦ".
	wp_lam. 
	wp_pures.
	wp_alloc n' as "Hn'".
	wp_alloc n as "Hn".
	wp_pures.
	wp_alloc s' as "Hs'".
	wp_pures.
	wp_alloc h as "Hh".
	wp_let.
	iMod (pointsto_persist with "Hs'") as "#Hs'".
	iMod (pointsto_persist with "Hn'") as "#Hn'".
	iMod (inv_alloc N _ (points_to_node n) with "[Hn Hn']") as "#Hn".
	{ iNext. iExists n', (InjLV #()). iFrame. iSplitR. done. iLeft. done. }
	iAssert (is_node s') as "#Hs'node".
	{
		iExists n, NONEV. iSplitR. done. done.
	}
	iMod (inv_alloc N _ (queue_inv h) with "[Hh]") as "#HhInv".
	{
		iNext. iExists s'. iFrame. done.
	}
	wp_alloc t as "Ht".
	wp_let.
	iMod (inv_alloc N _ (queue_inv t) with "[Ht]") as "#HtInv".
	{
		iNext. iExists s'. iFrame. done.
	}
	wp_apply (newlock_spec with "HhInv").
	iIntros (hlock γh) "Hγh".
	wp_let.
	wp_apply (newlock_spec with "HtInv").
	iIntros (tlock γt) "Hγt".
	wp_let.
	wp_alloc q as "Hq".
	iApply "HΦ".
	iExists h, t, hlock, tlock, γh, γt, q.
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
	wp_alloc null as "Hnull".
	iMod (pointsto_persist with "Hnull") as "#Hnull".
	wp_alloc next as "Hnext".
	wp_alloc node as "Hnode".
	iMod (pointsto_persist with "Hnode") as "#Hnode".
	wp_let.
	wp_load.
	wp_pures.
	wp_apply (acquire_spec with "H_tlock").
	iIntros "(Hlocked_γt & #Hinv)".
	wp_seq.
	wp_load.
	wp_pures.
	wp_bind (! #tail)%E.
	iInv "Hinv" as "(%tl & Htail & %tl_next & %x & #Htl & #Hinvn)".
	wp_load.
	iSplitL "Htail".
	{ 
		iExists tl. iModIntro. iNext. iFrame. iExists tl_next, x.
		iFrame. auto.
	}
	iModIntro.
	wp_load.
	wp_lam.
	wp_match.
	wp_pures.
	wp_bind (#tl_next <- #node)%E.
	iInv "Hinvn" as "(%r & %r_next & Htl_next & Hr)".
	wp_store.
	iModIntro.
	iSplitL "Htl_next".
	{ iNext. iExists node, (InjRV (InjRV v, #next)). iFrame.
		iSplitR. done. iRight. eauto. }
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