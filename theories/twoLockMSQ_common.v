From iris.heap_lang Require Import notation.

(* ===== Linked Lists ===== *)

(* Notation for nodes *)
Definition n_in {A B C} (x : A * B * C ) := (let '(a, b, c) := x in a).
Definition n_val {A B C} (x : A * B * C ) := (let '(a, b, c) := x in b).
Definition n_out {A B C} (x : A * B * C ) := (let '(a, b, c) := x in c).


(* Fist and Last of lists *)
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

Lemma list_last_eq {A} : forall (xs_1 xs_2 : list A) x_1 x_2,
	xs_1 ++ [x_1] = xs_2 ++ [x_2] ->
	xs_1 = xs_2 /\ x_1 = x_2.
Proof.
	induction xs_1 as [| x'_1 xs'_1 IH]; intros xs_2 x_1 x_2 Heq.
	- destruct xs_2 as [| x'_2 xs'_2].
	  + simpl in Heq. by inversion Heq.
	  + inversion Heq. destruct xs'_2; discriminate.
	- destruct xs_2 as [| x'_2 xs'_2].
	  + inversion Heq. destruct xs'_1; discriminate.
	  + simplify_eq. split.
	  	* f_equal. by eapply IH.
		* by eapply IH.
Qed.


Fixpoint proj_val (xs: list (loc * val * loc)) :=
match xs with
| [] => []
| x :: xs' => n_val x :: proj_val xs'
end.

Lemma proj_val_split: forall xs_1 xs_2,
	proj_val (xs_1 ++ xs_2) = proj_val xs_1 ++ proj_val xs_2.
Proof.
	induction xs_1 as [| x xs'_1 IH]; intros xs_2.
	- done.
	- simpl. f_equal. apply IH.
Qed.

Fixpoint wrap_some (xs: list val) :=
match xs with
| [] => []
| x :: xs' => (SOMEV x) :: wrap_some xs'
end.

Lemma wrap_some_split: forall xs_1 xs_2,
	wrap_some (xs_1 ++ xs_2) = wrap_some xs_1 ++ wrap_some xs_2.
Proof.
	induction xs_1 as [| x xs'_1 IH]; intros xs_2.
	- done.
	- simpl. f_equal. apply IH.
Qed.