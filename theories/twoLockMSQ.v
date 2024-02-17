From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
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

(* Fixpoint is_queue_list (l tail : loc) xs : iProp Σ := 
	match xs with
	| [] => ∃ l' tail' : loc, l ↦ #l' ∗ 
							  tail ↦ #tail' ∗ 
							  ⌜l' = tail'⌝
	| x :: xs' => 
	(
		∃ l' next: loc , l ↦ #l' ∗ 
							l' ↦ (SOMEV (SOMEV #x, #next))
							∗ (is_queue_list next tail xs')
	)
	end. *)

Definition is_queue (v : val) : iProp Σ :=
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
				  ).

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
	wp_alloc t as "Ht".
	wp_let.
	wp_apply (newlock_spec with "Hh").
	iIntros (lk1 γ1) "Hγ1".
	wp_let.
	wp_apply (newlock_spec with "Ht").
	iIntros (lk2 γ2) "Hγ2".
	wp_let.
	wp_alloc q as "Hq".
	iApply "HΦ".
	iExists h, t, lk1, lk2, γ1, γ2, q.
	iSplitR.
	{ done. }
	iFrame.
	Admitted.

Lemma enqueue_spec Q v : {{{ is_queue v }}} 
							 enqueue Q v 
						 {{{v, RET v; True}}}.
Proof.
	Admitted.

Lemma dequeue_spec Q v : {{{ is_queue v }}} 
							 dequeue Q 
						 {{{v, RET v; True}}}.
Proof.
	Admitted.

End proofs.