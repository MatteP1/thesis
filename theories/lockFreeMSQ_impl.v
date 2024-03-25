From stdpp Require Import countable.
From iris.algebra Require Import excl.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.base_logic.lib Require Import invariants.
From iris.unstable.heap_lang Require Import interpreter.

Definition initialize : val :=
	rec: "initialize" <> :=
		let: "node" := ref (NONE, ref (NONE)) in
		ref (ref "node", ref "node").

Definition enqueue : val :=
	rec: "enqueue" "Q" "value" :=
		let: "node" := ref (SOME "value", ref(NONE)) in
		(rec: "loop" "_" := 
			let: "tail" := !(Snd !"Q") in
			let: "next" := !(Snd !"tail") in
			if: "tail" = !(Snd !"Q") then
				if: "next" = NONE then
					if: CAS (Snd !"tail") "next" "node" then
						CAS (Snd !"Q") "tail" "node"
					else "loop" #()
				else CAS (Snd !"Q") "tail" "next";; "loop" #()
			else "loop" #()
		) #().

Definition dequeue : val :=
	rec: "dequeue" "Q" :=
		(rec: "loop" "_" :=
			let: "head" := !(Fst !"Q") in
			let: "tail" := !(Snd !"Q") in
			let: "next" := !(Snd !"head") in
			if: "head" = !(Fst !"Q") then
				if: "head" = "tail" then
					if: "next" = NONE then
						NONEV
					else
						CAS (Snd !"Q") "tail" "next";; "loop" #()
				else
					let: "value" := Fst (!"next") in
					if: CAS (Fst !"Q") "head" "next" then
						"value"
					else "loop" #()
			else "loop" #()
		) #().

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
