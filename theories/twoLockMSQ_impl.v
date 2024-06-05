From stdpp Require Import countable.
From iris.algebra Require Import excl.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants.
(* From iris.unstable.heap_lang Require Import interpreter. *)

Local Existing Instance spin_lock.

Definition initialize : val :=
  rec: "initialize" <> :=
    let: "node" := ref (NONE, ref (NONE)) in (* Create initial Head node *)
    let: "H_lock" := newlock #() in (* Create Head lock *)
    let: "T_lock" := newlock #() in (* Create Tail lock *)
    ref ((ref "node", ref "node"), ("H_lock", "T_lock")). (* Create queue *)

Definition enqueue : val :=
  rec: "enqueue" "Q" "value" :=
    let: "node" := ref (SOME "value", ref(NONE)) in (* Create new node *)
    acquire (Snd (Snd (!"Q"))) ;; (* Acqurie Tail lock *)
    Snd (!(!(Snd (Fst(!"Q"))))) <- "node" ;; (* Add new node to linked list *)
    Snd (Fst (!"Q")) <- "node" ;; (* Swing Tail to new node *)
    release (Snd (Snd (!"Q"))). (* Release Tail lock *)

Definition dequeue : val :=
  rec: "dequeue" "Q" :=
    acquire (Fst (Snd (!"Q")));; (* Acquire Head lock *)
    let: "node" := !(Fst (Fst (!"Q"))) in (* Get Head node *)
    let: "new_head" := !(Snd(!"node")) in (* Find Head node's successor *)
    if: "new_head" = NONE then (* Check if Queue is empty *)
      (* No successor node. Queue is empty. *)
      release (Fst (Snd(!"Q"))) ;;
      NONEV
    else
      (* Queue not empty. Pop first element in Queue *)
      let: "value" := Fst (!"new_head") in (* Get its value *)
      Fst (Fst (!"Q")) <- "new_head" ;; (* Swing Head to successor node *)
      release (Fst (Snd (!"Q"))) ;; (* Release Head lock *)
      "value". (* Return dequeued value *)

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

(* To run the tests, import the HeapLang interpreter. Requires Iris-Unstable. *)
(* Compute (exec 200 test_dequeue_empty2). *)

End tests.
