From iris.heap_lang Require Import lang proofmode notation.

(* ===== Common defintions and Lemmas ===== *)

(* ----- Linked Lists ----- *)

(* A node consists of an 'in'-location, a value, and an 'out'-location *)
Definition node : Type := loc * val * loc.

(* Notation for nodes *)
Definition n_in {A B C} (x : A * B * C ) := (let '(a, b, c) := x in a).
Definition n_val {A B C} (x : A * B * C ) := (let '(a, b, c) := x in b).
Definition n_out {A B C} (x : A * B * C ) := (let '(a, b, c) := x in c).

(* Fist and Last of lists *)
Definition isFirst {A} (x : A) xs := ∃ xs_rest, xs = xs_rest ++ [x].
Definition isLast {A} (x : A) xs := ∃ xs_rest, xs = x :: xs_rest.
Definition isSndLast {A} (x : A) xs := ∃ x_first xs_rest, xs = x_first :: x :: xs_rest.

Lemma isLast_remove {A} : forall (x y : A) (xs ys : list A),
	isLast x (xs ++ [y] ++ ys) <->
	isLast x (xs ++ [y]).
Proof.
	intros x y xs ys.
	split.
	- intros [xs' HisLast]. 
	  destruct xs as [|x' xs''].
	  + exists []. simpl. by inversion HisLast.
	  + inversion HisLast; subst. by exists (xs'' ++ [y]).
	- intros [xs' HisLast].
	  exists (xs' ++ ys).
	  rewrite app_assoc.
	  by rewrite HisLast.
Qed.

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

(* ------ Projecting out the value (second element of triple) ------ *)
Fixpoint proj_val {A B C} (xs: list (A * B * C)) :=
match xs with
| [] => []
| x :: xs' => n_val x :: proj_val xs'
end.

Lemma proj_val_split {A B C}: forall (xs_1 xs_2 : list (A * B * C)),
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

(* ------ Miscelanious ------ *)

(* Used for Prophecies *)
Definition val_of_list (vs : list (val * val)) : val :=
  match vs with
  | []          => #()
  | (v, _) :: _ => v
  end.


(* ------ Defining the 'All' Preidcate ------ *)
Section All.

Context `{!heapGS Σ}.

Fixpoint All {A} (xs : list A) (f : A -> iProp Σ) : iProp Σ :=
	match xs with
	| [] => True
	| x :: xs' => f x ∗ All xs' f
	end.

Lemma All_split {A} : forall (xs_1 xs_2 : list A) f,
	All (xs_1 ++ xs_2) f ∗-∗ All xs_1 f ∗ All xs_2 f.
Proof.
	iIntros (xs_1).
	iInduction (xs_1) as [| x xs'_1] "IH"; iIntros (xs_2 f).
	- simpl. iSplit; first auto. iIntros "[_ H]". done.
	- simpl. iSplit.
	  + iIntros "[Hfx HAll]". iFrame. by iApply "IH".
	  + iIntros "[[Hfx HAll1] HAll2]". iFrame. iApply "IH". iFrame.
Qed.

End All.


(* ------ Defining the 'is Linked List' predicate ------ *)
Section isLL.

Context `{!heapGS Σ}.

(*
	isLL is short for: 'is Linked List'.
	isLL_chain states that every node x in xs satisfies
		n_in x ↦□ (n_val x, #(n_out x)).
   	Further, all adjacent pairs, [x ; x'], are connected by x' pointing to x.
	Example:
	The list
	[(l_3_in, v_3, l_3_out);
	 (l_2_in, v_2, l_2_out);
	 (l_1_in, v_1, l_1_out)]
	generates:
	(v_3, l_3_out) <- l_3_in 	∗	l_3_in <- l_2_out	∗
	(v_2, l_2_out) <- l_2_in 	∗	l_2_in <- l_1_out	∗
	(x_1, l_1_out) <- l_1_in
*)

Fixpoint isLL_chain (xs : list node ) : iProp Σ :=
	match xs with
	| [] => True
	| [x] => n_in x ↦□ (n_val x, #(n_out x))
	| x :: ((x' :: xs'') as xs') =>
				n_in x ↦□ (n_val x, #(n_out x)) ∗
				n_out x' ↦□ #(n_in x) ∗
				isLL_chain xs'
	end.

(* isLL_chain is persistent for all xs *)
Global Instance isLL_chain_persistent xs : Persistent (isLL_chain xs).
Proof.
	induction xs as [|x [|x' xs']]; apply _.
Qed.

(* xs defines a linked list, when the tail (the first element of the list) points to NONEV, and all the nodes form a linked list chain. *)
Definition isLL (xs : list node) : iProp Σ :=
	match xs with
	| [] => True
	| x :: xs' => (n_out x) ↦ NONEV ∗ isLL_chain xs
	end.

(* Since isLL_chain is persistent, we can always extract it from isLL. *)
Lemma isLL_and_chain : forall xs,
	isLL xs -∗
	isLL xs ∗ isLL_chain xs.
Proof.
	iIntros (xs) "HisLLxs".
	destruct xs as [| x xs']; first done.
	unfold isLL.
	iPoseProof "HisLLxs" as "[Hx_to_none #HisLLxs]".
	iFrame.
	by iSplit.
Qed.

(* if two nodes have the same 'in' location, then it is the same node. *)
Lemma n_in_equal (x y : node) :
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

(* If x is an element in an isLL_chain, then it is a node. *)
Lemma isLL_chain_node : forall xs_1 x xs_2,
	isLL_chain (xs_1 ++ x :: xs_2) -∗
	n_in x ↦□ (n_val x, #(n_out x)).
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
	iInduction xs as [|x xs'] "IH".
	- by iSplit.
	- destruct xs' as [| x' xs''].
	  + destruct ys as [| y ys'].
		* by iSplit.
		* iSimpl in "HisLL_chain_xs_ys".
		  iDestruct "HisLL_chain_xs_ys" as "(Hx_node & Hy_to_x & HIsLL_chain_ys')".
		  iFrame "#".
	  + iAssert (isLL_chain (x' :: xs'') ∗ isLL_chain ys)%I as "[HisLL_chain_xs' HisLL_chain_ys]".
	  	{
			iApply "IH".
			by iDestruct "HisLL_chain_xs_ys" as "(_ & _ & Hchain)".
		}
		iDestruct "HisLL_chain_xs_ys" as "(Hx_node & Hx'_to_x & _)".
		iFrame "#".
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
	iDestruct "HisLL_chain_yx" as "(#Hy_node & #Hx_to_y & Hx_node)".
	iDestruct "HisLL_chain_zx" as "(#Hz_node & #Hx_to_z & _)".
	iCombine "Hx_to_y Hx_to_z" gives "[_ %Hy_z_in_eq]".
	simplify_eq.
	iApply n_in_equal; try done. by rewrite Hy_z_in_eq.
Qed.

Lemma isLL_chain_agree_further : forall x y z ys ys' zs zs' xs,
	isLL_chain (ys ++ [y] ++ xs ++ [x] ++ ys') -∗
	isLL_chain (zs ++ [z] ++ xs ++ [x] ++ zs') -∗
	⌜y = z⌝.
Proof.
	iIntros (x y z ys ys' zs zs' xs) "#HisLL_chain_ys #HisLL_chain_zs".
	destruct xs as [| x' xs'].
	- iApply (isLL_chain_agree_next x y z ys ys' zs zs'); done.
	- iApply (isLL_chain_agree_next x' y z ys (xs' ++ [x] ++ ys') zs ((xs' ++ [x] ++ zs'))); done.
Qed.

Lemma isLL_split : forall xs ys,
	isLL (xs ++ ys) -∗
	isLL xs ∗ isLL_chain ys.
Proof.
	iIntros (xs ys) "HisLL_xs_ys".
	iPoseProof (isLL_and_chain with "HisLL_xs_ys") as "[HisLL_xs_ys #HisLL_chain_xs_ys]".
	iPoseProof (isLL_chain_split with "HisLL_chain_xs_ys") as "[HisLL_chain_xs HisLL_chain_ys]".
	iFrame "HisLL_chain_ys".
	destruct xs as [| x xs']; first done.
	iDestruct "HisLL_xs_ys" as "[Hx_to_none _]".
	by iFrame.
Qed.

End isLL.
