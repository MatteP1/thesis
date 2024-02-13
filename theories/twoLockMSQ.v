From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.

Definition initialize `{!lock} : val := 
	rec: "initialize" <> := 
		let: "node" := ref (SOME (NONE, ref(NONE))) in
		let: "H_lock" := newlock #() in
		let: "T_lock" := newlock #() in
		ref (("node", "node"), ("H_lock", "T_lock")).

Definition enqueue `{!lock} : val := 
	rec: "enqueue" "Q" "value" :=
		let: "node" := ref (SOME (SOME "value", ref(NONE))) in
		acquire (Snd ( Snd (!"Q")));; (* Acqurie T_lock*)
		let: "old_tail" := 
			SOME (Fst ("get_some" (!(Snd (Fst(!"Q"))))), "node") in
		(Snd (Fst!"Q")) <- "old_tail" ;;
		"Q" <- ((Fst (Fst (!"Q")), "node"), Snd(!"Q")) ;;
		release (Snd (Snd (!"Q"))).

Definition dequeue `{!lock}: val := 
	rec: "dequeue" "Q" := 
		acquire (Fst (Snd (!"Q")));; (* Acquire H_lock*)
		let: "node" := (Fst (Fst (!"Q"))) in
		let: "new_head" := Snd("get_some" (!"node")) in
		if: "new_head" = NONEV then
			release (Fst (Snd(!"Q"))) ;;
			NONEV
		else
			let: "value" := (Fst (!"new_head")) in
			"Q" <- (("new_head", (Snd(Fst(!"Q")))), Snd (! "Q"));;
			release (Fst (Snd (!"Q")));;
			"value".


Section proofs.

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Let N := nroot .@ "twoLockMSQ".

(* Definition queue_invariant (head tail : loc) : iProp Σ := 
	∃ xs, isList xs . *)

Definition is_queue (v : val) : iProp Σ := 
	∃ head tail : loc, ∃ H_lock T_lock : val, ∃ γH γT : gname, 
	∃ l : loc , ⌜v = #l⌝ ∗ l ↦ ((#head, #tail), (H_lock, T_lock))
	∗ True (* H_lock is a lock*)
	∗ True. (* T_lock is a lock*)

Lemma initialize_spec : {{{ True }}} initialize #() {{{v, RET v; True}}}.
Proof.
	Admitted.

Lemma enqueue_spec Q v : {{{ True }}} enqueue Q #v {{{v, RET v; True}}}.
Proof.
	Admitted.

Lemma dequeue_spec Q : {{{ True }}} dequeue Q {{{v, RET v; True}}}.
Proof.
	Admitted.

End proofs.