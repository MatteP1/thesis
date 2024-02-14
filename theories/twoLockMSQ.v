From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.

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
		let: "H_lock" := newlock #() in
		let: "T_lock" := newlock #() in
		ref ((ref "node", ref "node"), ("H_lock", "T_lock")).

Definition enqueue : val := 
	rec: "enqueue" "Q" "value" :=
		let: "node" := ref (SOME (SOME "value", ref(ref(NONE)))) in
		acquire (Snd ( Snd (!"Q")));; (* Acqurie T_lock *)
		Snd ("get_some" (!(Snd (Fst(!"Q"))))) <- "node" ;;
		Snd (Fst (!"Q")) <- "node" ;;
		release (Snd (Snd (!"Q"))).

Definition dequeue : val := 
	rec: "dequeue" "Q" := 
		acquire (Fst (Snd (!"Q")));; (* Acquire H_lock *)
		let: "node" := !(Fst (Fst (!"Q"))) in (* Get Head node *)
		let: "new_head" := !(Snd("get_some" (!"node"))) in (* Find Head.Next *)
		if: !"new_head" = NONE then (* Check if Queue is empty *)
			(* No Next node. Queue is empty. *)
			release (Fst (Snd(!"Q"))) ;;
			NONEV
		else
			(* Queue not empty. Pop first element in Queue *)
			let: "value" := Fst (!"new_head") in (* Get its value *)
			Fst (Fst (!"Q")) <- "new_head" (* Swing Head to next node *)
			release (Fst (Snd (!"Q")));; (* Release H_lock *)
			"value". (* Return value *)

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