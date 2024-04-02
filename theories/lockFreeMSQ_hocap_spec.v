From stdpp Require Import countable.
From iris.algebra Require Import excl list agree gmap lib.frac_auth.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.base_logic.lib Require Import invariants.
From MSQueue Require Import lockFreeMSQ_impl.
From MSQueue Require Import twoLockMSQ_common.
(* TODO: consider changing twolockMSQ_common to common. *)

Section proofs.

Definition linkedListUR : ucmra :=
	gmapUR nat (agreeR (prodO (prodO locO valO) locO)).

Fixpoint to_ll_go (i : nat) (xs : list (loc * val * loc)) : linkedListUR :=
  match xs with
  | [] => ∅
  | x :: xs' => <[i:=to_agree x]>(to_ll_go (S i) xs')
  end.
Definition to_ll : list (loc * val * loc) → linkedListUR := to_ll_go 0.

Context `{!heapGS Σ}.
Context `{!inG Σ (authR linkedListUR)}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Variable N : namespace.
Notation Ni := (N .@ "internal").

(* ===== Concurrent Specification for Two-lock M&S Queue ===== *)

(* Ghost variable names *)
Record Qgnames := {γ_Abst 	: gname;
				   γ_Snap 	: gname;
				  }.

Notation "Q_γ ⤇● xs_v" := (own Q_γ.(γ_Abst) (●F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇● xs_v") : bi_scope.
Notation "Q_γ ⤇◯ xs_v" := (own Q_γ.(γ_Abst) (◯F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇◯ xs_v") : bi_scope.
Notation "Q_γ ⤇[ q ] xs_v" := (own Q_γ.(γ_Abst) (◯F{ q } (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇[ q ] xs_v") : bi_scope.

Lemma queue_contents_frag_agree Q_γ xs_v xs_v' p q :
	Q_γ ⤇[p] xs_v -∗ Q_γ ⤇[q] xs_v' -∗ ⌜xs_v = xs_v'⌝.
Proof.
	iIntros "Hp Hq".
	iCombine "Hp Hq" as "Hpq" gives "%HValid".
	iPureIntro.
	rewrite <- frac_auth_frag_op in HValid.
	rewrite frac_auth_frag_valid in HValid.
	destruct HValid as [_ HAgree].
	by apply to_agree_op_inv_L.
Qed.

Lemma queue_contents_auth_frag_agree Q_γ xs_v xs_v' p :
	Q_γ ⤇● xs_v' -∗ Q_γ ⤇[p] xs_v -∗ ⌜xs_v = xs_v'⌝.
Proof.
	iIntros "Hp Hq".
	iCombine "Hp Hq" as "Hpq" gives "%HValid".
	iPureIntro.
	apply frac_auth_included_total in HValid.
	by apply to_agree_included_L.
Qed.

Lemma queue_contents_op Q_γ xs_v p q :
	Q_γ ⤇[p] xs_v ∗ Q_γ ⤇[q] xs_v ∗-∗ Q_γ ⤇[p + q] xs_v.
Proof.
	iSplit.
	- iIntros "[Hp Hq]".
	  by iCombine "Hp Hq" as "Hpq".
	- iIntros "Hpq".
	  iApply own_op.
	  rewrite <- frac_auth_frag_op.
	  by rewrite agree_idemp.
Qed.

Lemma queue_contents_update Q_γ xs_v xs_v' xs_v'' :
	Q_γ ⤇● xs_v' -∗ Q_γ ⤇◯ xs_v ==∗ Q_γ ⤇● xs_v'' ∗ Q_γ ⤇◯ xs_v''.
Proof.
	iIntros "Hauth Hfrag".
	iCombine "Hauth Hfrag" as "Hcombined".
	rewrite <- own_op.
	iApply (own_update with "Hcombined").
	by apply frac_auth_update_1.
Qed.

Notation current Q_γ xs := (own Q_γ.(γ_Snap) (● (to_ll (reverse xs)))).
Notation snapshot Q_γ xs := (own Q_γ.(γ_Snap) (◯ (to_ll (reverse xs)))).

Lemma get_snapshot : ∀ Q_γ xs,
	current Q_γ xs -∗
	current Q_γ xs ∗ snapshot Q_γ xs.
Proof.
	Admitted.

Lemma current_and_snapshot : ∀ Q_γ xs xs',
	current Q_γ xs -∗
	snapshot Q_γ xs' -∗
	∃xs'', ⌜xs = xs'' ++ xs'⌝.
Proof.
	Admitted.

Lemma current_update : ∀ Q_γ xs x,
	current Q_γ xs ==∗ current Q_γ (x :: xs).
Proof.
	Admitted.

Definition queue_invariant (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, Q_γ ⤇● xs_v ∗ (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: (loc * val * loc)), (* Concrete state *)
	current Q_γ xs ∗
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	(* Relation between concrete and abstract state *)
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	l_head ↦ #(n_in x_head) ∗
	l_tail ↦ #(n_in x_tail) ∗
	⌜In x_tail xs⌝.

Definition is_queue (v_q : val) (Q_γ: Qgnames) : iProp Σ :=
	∃ l_queue l_head l_tail : loc,
	⌜v_q = #l_queue⌝ ∗
	l_queue ↦□ (#l_head, #l_tail) ∗
	inv Ni (queue_invariant l_head l_tail Q_γ).

(* is_queue is persistent *)
Global Instance is_queue_persistent v_q Q_γ : Persistent (is_queue v_q Q_γ).
Proof. apply _. Qed.

Lemma initialize_spec:
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γ, RET v_q; is_queue v_q Q_γ ∗
						  Q_γ ⤇◯ [] }}}.
Proof.
	iIntros (Φ) "_ HΦ".
	wp_lam.
	wp_pures.
	wp_alloc l_1_out as "Hl_1_out".
	wp_alloc l_1_in as "Hl_1_in".
	wp_pures.
	iMod (pointsto_persist with "Hl_1_in") as "#Hl_1_in".
	wp_alloc l_tail as "Hl_tail".
	wp_alloc l_head as "Hl_head".
	iMod (own_alloc (●F (to_agree []) ⋅ ◯F (to_agree []))) as (γ_Abst) "[Hγ_Abst_auth Hγ_Abst_frac]"; first by apply frac_auth_valid.
	iMod (own_alloc (● (to_ll [(l_1_in, NONEV, l_1_out)]))) as (γ_Snap) "Hγ_Snap_curr".
	{
		apply auth_auth_valid.
		apply singleton_valid.
		rewrite <- agree_idemp.
		by apply to_agree_op_valid_L.
	}
	set (Queue_gnames := {| γ_Abst := γ_Abst;
							γ_Snap := γ_Snap
					|}).
	iMod (inv_alloc Ni _ (queue_invariant l_head l_tail Queue_gnames) with "[Hγ_Abst_auth Hγ_Snap_curr Hl_head Hl_tail Hl_1_in Hl_1_out]") as "#HqueueInv".
	{
		iNext. iExists []; iFrame.
		iExists [(l_1_in, NONEV, l_1_out)], [], [], (l_1_in, NONEV, l_1_out), (l_1_in, NONEV, l_1_out); iFrame.
		do 3 (iSplit; first done).
		iLeft.
		done.
	}
	wp_alloc l_queue as "Hl_queue".
	iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
	iApply ("HΦ" $! #l_queue Queue_gnames).
	iModIntro.
	iFrame.
	iExists l_queue, l_head, l_tail.
	by repeat iSplit.
Qed.

Lemma enqueue_spec v_q (v : val) (Q_γ : Qgnames) (P Q : iProp Σ) :
	□(∀xs_v, (Q_γ ⤇● xs_v ∗ P ={⊤ ∖ ↑Ni}=∗ ▷ (Q_γ ⤇● (v :: xs_v) ∗ Q))) -∗
	{{{ is_queue v_q Q_γ ∗ P}}}
		enqueue v_q v
	{{{ w, RET w; Q }}}.
Proof.
	iIntros "#Hvs".
	iIntros (Φ) "!> [(%l_queue & %l_head & %l_tail & -> &
				 #Hl_queue & #Hqueue_inv) HP] HΦ".
	wp_lam.
	wp_let.
	wp_pures.
	wp_alloc l_new_out as "Hl_new_out".
	wp_alloc l_new_in as "Hl_new_in".
	iMod (pointsto_persist with "Hl_new_in") as "#Hl_new_in".
	set x_new := (l_new_in, SOMEV v, l_new_out).
	change l_new_in with (n_in x_new).
	change l_new_out with (n_out x_new).
	change (SOMEV v) with (n_val x_new).
	wp_let.
	wp_pures.
	set loop := (rec: "loop" "_" := let: "tail" := ! (Snd ! #l_queue) in let: "next" := ! (Snd ! "tail") in if: "tail" = ! (Snd ! #l_queue) then if: "next" = InjL #() then if: Snd (CmpXchg (Snd ! "tail") "next" #l_new_in) then Snd (CmpXchg (Snd ! #l_queue) "tail" #l_new_in) else "loop" #() else Snd (CmpXchg (Snd ! #l_queue) "tail" "next");; "loop" #() else "loop" #())%V.
	iLöb as "IH".
	wp_load.
	wp_pures.
	wp_bind (! #l_tail)%E.
	(* First Invariant Opening *)
	iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs1 & %xs1_queue & %xs1_old & %x_head & %x_tail & >Hcurr & >%Heq_xs1 & HisLL_xs1 & >%Hconc_abst_eq & Hhead & Htail & >%HisLastOrSndLast1)".
	wp_load.
	iPoseProof (isLL_and_chain with "HisLL_xs1") as "[HisLL_xs1 #HisLL_chain_xs1]".
	iAssert ((n_in x_tail ↦□ (n_val x_tail, #(n_out x_tail)))%I) as "#Hx_tail".
	{
		destruct HisLastOrSndLast1 as [[xs_fromtail HisLast] | [x_first [xs_fromtail HisSndLast]]].
		- iPoseProof (isLL_chain_node [] x_tail xs_fromtail with "[HisLL_chain_xs1]") as "#Hx_tail"; by rewrite HisLast.
		- iPoseProof (isLL_chain_node [x_first] x_tail xs_fromtail with "[HisLL_chain_xs1]") as "#Hx_tail"; by rewrite HisSndLast.
	}
	iPoseProof (get_snapshot with "Hcurr") as "[Hcurr Hsnap1]".
	iModIntro.
	(* Close invariant*)
	iSplitL "Hhead Htail HisLL_xs1 HAbst Hcurr".
	{
		iNext.
		iExists xs_v; iFrame.
		iExists xs1, xs1_queue, xs1_old, x_head, x_tail; iFrame.
		done.
	}
	(* TODO: possibly add more *)
	iClear (Hconc_abst_eq xs_v Heq_xs1 x_head) "".
	wp_let.
	wp_load.
	wp_pures.
	wp_bind (! #(n_out x_tail))%E.
	(* Second Invariant Opening *)
	iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs2 & %xs2_queue & %xs2_old & %x_head & %x_tail' & >Hcurr & >%Heq_xs2 & HisLL_xs2 & >%Hconc_abst_eq & Hhead & Htail & >%HisLastOrSndLast2)".
	iAssert (∃xs_diff, ⌜xs2 = xs_diff ++ xs1⌝)%I with "[Hcurr Hsnap1]" as "(%xs_diff & %Hxs2xs1_eq)"; first by (iApply (current_and_snapshot Q_γ xs2 xs1 with "Hcurr Hsnap1")).
	(* CASE ANALYSIS: Is x_tail last? *)
	assert (Hxs2tail: isLast x_tail xs2 \/ ∃xs x_next xs', xs2 = xs ++ x_next :: x_tail :: xs').
	{
		destruct xs_diff as [ | x_last xs_diff'].
		- simpl in Hxs2xs1_eq.
		  rewrite Hxs2xs1_eq in HisLastOrSndLast1 *.
		  destruct HisLastOrSndLast1 as [Hlast | Hsndlast].
		  + by left.
		  + right.
		  	exists []. apply Hsndlast.
		- right. 
		  destruct HisLastOrSndLast1 as [[xs_fromtail ->] | [x_first [xs_fromtail HisSndLast]]].
		  + destruct (exists_first (x_last :: xs_diff')) as [x_first [x_diff'' Hx_first]]; first done. 
		  exists x_diff'', x_first, xs_fromtail.
		  rewrite Hxs2xs1_eq. rewrite Hx_first.
		  by rewrite <- app_assoc.
		  +  exists (x_last :: xs_diff'), x_first, xs_fromtail.
		  rewrite Hxs2xs1_eq. 
		  by rewrite HisSndLast.
	}
	destruct Hxs2tail as [HisLast_xs2 |Hxs2eq].
	- destruct HisLast_xs2 as [xs_fromtail Hxs2eq].
	  rewrite Hxs2eq.
	  iDestruct "HisLL_xs2" as "[Htailout #HisLL_chain_xs2]".
	  wp_load.
	  iModIntro.
	  iSplitL "Hhead Htail Htailout Hcurr HAbst".
	  {
		iNext.
		iExists xs_v; iFrame.
		rewrite <- Hxs2eq.
		iExists xs2, xs2_queue, xs2_old, x_head, x_tail'; iFrame.
		iSplit; first done.
		rewrite Hxs2eq.
		iFrame.
		iSplit; first done.
		iSplit; first done.
		rewrite <- Hxs2eq.
		done.
	  }
	  (* TODO: possibly add more *)
	  iClear (Hconc_abst_eq xs_v Heq_xs2 x_head) "".
	  wp_let.
	  (* consistency check *)
	  wp_load.
	  wp_pures.
	  (* Third Invariant Opening *)
	  wp_bind (! #l_tail)%E.
	  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs3 & %xs3_queue & %xs3_old & %x_head & %x_tail'' & >Hcurr & >%Heq_xs3 & HisLL_xs3 & >%Hconc_abst_eq & Hhead & Htail & >%HisLastOrSndLast3)".
	  wp_load.
	  iModIntro.
	  iSplitL "Hhead Htail HisLL_xs3 Hcurr HAbst".
	  {
		iNext.
		iExists xs_v; iFrame.
		iExists xs3, xs3_queue, xs3_old, x_head, x_tail''; iFrame.
		iSplit; first done.
		iSplit; first done.
		done.
	  }
	  (* TODO: possibly add more *)
	  iClear (Hconc_abst_eq xs_v Heq_xs3 x_head) "".
	  wp_pures.
	  case_bool_decide; wp_if.
	  + (* Consistent*)
		wp_pures.
		wp_load.
		wp_pures.
		wp_bind (CmpXchg _ _ _).
		iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs4 & %xs4_queue & %xs4_old & %x_head & %x_tail''' & >Hcurr & >%Heq_xs4 & HisLL_xs4 & >%Hconc_abst_eq & Hhead & Htail & >%HisLastOrSndLast4)".
		iAssert (∃xs_diff', ⌜xs4 = xs_diff' ++ xs1⌝)%I with "[Hcurr Hsnap1]" as "(%xs_diff' & %Hxs4xs1_eq)"; first by (iApply (current_and_snapshot Q_γ xs4 xs1 with "Hcurr Hsnap1")).
		assert (Hxs4tail: isLast x_tail xs4 \/ ∃xs x_next xs', xs4 = xs ++ x_next :: x_tail :: xs').
		{
			destruct xs_diff' as [ | x_last xs_diff''].
			- simpl in Hxs4xs1_eq.
			rewrite Hxs4xs1_eq in HisLastOrSndLast1 *.
			destruct HisLastOrSndLast1 as [Hlast | Hsndlast].
			+ by left.
			+ right.
				exists []. apply Hsndlast.
			- right. 
			destruct HisLastOrSndLast1 as [[xs_fromtail' ->] | [x_first [xs_fromtail' HisSndLast]]].
			+ destruct (exists_first (x_last :: xs_diff'')) as [x_first [x_diff'' Hx_first]]; first done. 
			exists x_diff'', x_first, xs_fromtail'.
			rewrite Hxs4xs1_eq. rewrite Hx_first.
			by rewrite <- app_assoc.
			+  exists (x_last :: xs_diff''), x_first, xs_fromtail'.
			rewrite Hxs4xs1_eq. 
			by rewrite HisSndLast.
		}
		destruct Hxs4tail as [HisLast_xs4 |Hxs4eq].
		* 
		wp_cmpxchg as H1 | H2.
		* iModIntro.
		  iAssert (⌜x_tail''' = x_tail⌝)%I as "->".
			{
				iPoseProof (isLL_and_chain with "HisLL_xs4") as "[HisLL_xs4 #HisLL_chain_xs4]".
				iApply n_in_equal; auto.
				destruct HisLastOrSndLast4 as [[xs_fromtail HisLast] | [x_first [xs_fromtail HisSndLast]]].
				- iPoseProof (isLL_chain_node [] x_tail''' xs_fromtail with "[HisLL_chain_xs4]") as "#Hx_tail'''"; by rewrite HisLast.
				- iPoseProof (isLL_chain_node [x_first] x_tail''' xs_fromtail with "[HisLL_chain_xs4]") as "#Hx_tail'''"; by rewrite HisSndLast.
			}
		  iAssert (⌜xs4 = x_next :: x_tail :: xs'⌝)%I as "%Hxs4eq".
		  {
			iDestruct (current_and_snapshot Q_γ xs4 xs2 with "Hcurr Hsnap2") as "(%xs'' & %Hxs4xs2eq)".
			rewrite Heq in Hxs4xs2eq.
			destruct xs'', xs; first done.
			all: simpl in *; rewrite Hxs4xs2eq in HisLastOrSndLast4;
			destruct HisLastOrSndLast4; admit.
		  }
		  iSplitL "Hhead Htail HisLL_xs4 Hcurr HAbst".
		  	{
				iNext.
				iExists xs_v; iFrame.
				iExists xs4, xs4_queue, xs4_old, x_head, x_next; iFrame.
				iSplit; first done.
				iSplit; first done.
				iLeft.
				rewrite Hxs4eq.
				by iExists (x_tail :: xs').
			}
		  wp_pures.
		  wp_lam.
		  iApply ("IH" with "HP HΦ Hl_new_out"). 
		* iModIntro.
		  iSplitL "Hhead Htail HisLL_xs4 Hcurr HAbst".
			{
				iNext.
				iExists xs_v; iFrame.
				iExists xs4, xs4_queue, xs4_old, x_head, x_tail'''; iFrame.
				iSplit; first done.
				iSplit; first done.
				done.
			}
		  wp_pures.
		  wp_lam.
		  iApply ("IH" with "HP HΦ Hl_new_out"). 
	+ (* Inconsistent*)
		wp_lam.
		iApply ("IH" with "HP HΦ Hl_new_out").
	- destruct Hxs2eq as [xs [x_next [xs' Heq]]].
	  iPoseProof (isLL_and_chain with "HisLL_xs2") as "[HisLL_xs2 #HisLL_chain_xs2]".
	  iAssert (▷(isLL_chain [x_next; x_tail]))%I as "Hchain".
	  {
		iNext. rewrite Heq.
		iDestruct (isLL_chain_split xs (x_next :: x_tail :: xs') with "HisLL_chain_xs2") as "[_ Hchain]".
		iDestruct (isLL_chain_split [x_next; x_tail] xs' with "Hchain") as "[Hchain' _]".
		done. 
	  }
	  iDestruct "Hchain" as "(Hx_next & Hx_tail_x_next & _)".
	  wp_load.
	  iPoseProof (get_snapshot with "Hcurr") as "[Hcurr Hsnap2]".
	  iModIntro.
	  iSplitL "Hhead Htail HisLL_xs2 Hcurr HAbst".
	{
		iNext.
		iExists xs_v; iFrame.
		iExists (xs2_queue ++ [x_head] ++ xs2_old), xs2_queue, xs2_old, x_head, x_tail'; iFrame.
		rewrite Heq_xs2.
		iFrame.
		iSplit; first done.
		iSplit; first done.
		rewrite Heq_xs2 in HisLastOrSndLast2.
		done.
	}
	(* TODO: possibly add more *)
	iClear (Hconc_abst_eq xs_v Heq_xs2 x_head) "".
	wp_let.
	(* consistency check *)
	wp_load.
	wp_pures.
	(* Third Invariant Opening *)
	wp_bind (! #l_tail)%E.
	iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs3 & %xs3_queue & %xs3_old & %x_head & %x_tail'' & >Hcurr & >%Heq_xs3 & HisLL_xs3 & >%Hconc_abst_eq & Hhead & Htail & >%HisLastOrSndLast3)".
	wp_load.
	iModIntro.
	iSplitL "Hhead Htail HisLL_xs3 Hcurr HAbst".
	{
		iNext.
		iExists xs_v; iFrame.
		iExists xs3, xs3_queue, xs3_old, x_head, x_tail''; iFrame.
		iSplit; first done.
		iSplit; first done.
		done.
	}
	(* TODO: possibly add more *)
	iClear (Hconc_abst_eq xs_v Heq_xs3 x_head) "".
	wp_pures.
	case_bool_decide; wp_if.
	+ (* Consistent*)
		wp_pures.
		wp_load.
		wp_pures.
		wp_bind (CmpXchg _ _ _).
		iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs4 & %xs4_queue & %xs4_old & %x_head & %x_tail''' & >Hcurr & >%Heq_xs4 & HisLL_xs4 & >%Hconc_abst_eq & Hhead & Htail & >%HisLastOrSndLast4)".
		wp_cmpxchg as H1 | H2.
		* iModIntro.
		  iAssert (⌜x_tail''' = x_tail⌝)%I as "->".
			{
				iPoseProof (isLL_and_chain with "HisLL_xs4") as "[HisLL_xs4 #HisLL_chain_xs4]".
				iApply n_in_equal; auto.
				destruct HisLastOrSndLast4 as [[xs_fromtail HisLast] | [x_first [xs_fromtail HisSndLast]]].
				- iPoseProof (isLL_chain_node [] x_tail''' xs_fromtail with "[HisLL_chain_xs4]") as "#Hx_tail'''"; by rewrite HisLast.
				- iPoseProof (isLL_chain_node [x_first] x_tail''' xs_fromtail with "[HisLL_chain_xs4]") as "#Hx_tail'''"; by rewrite HisSndLast.
			}
		  iAssert (⌜xs4 = x_next :: x_tail :: xs'⌝)%I as "%Hxs4eq".
		  {
			iDestruct (current_and_snapshot Q_γ xs4 xs2 with "Hcurr Hsnap2") as "(%xs'' & %Hxs4xs2eq)".
			rewrite Heq in Hxs4xs2eq.
			destruct xs'', xs; first done.
			all: simpl in *; rewrite Hxs4xs2eq in HisLastOrSndLast4;
			destruct HisLastOrSndLast4; admit.
		  }
		  iSplitL "Hhead Htail HisLL_xs4 Hcurr HAbst".
		  	{
				iNext.
				iExists xs_v; iFrame.
				iExists xs4, xs4_queue, xs4_old, x_head, x_next; iFrame.
				iSplit; first done.
				iSplit; first done.
				iLeft.
				rewrite Hxs4eq.
				by iExists (x_tail :: xs').
			}
		  wp_pures.
		  wp_lam.
		  iApply ("IH" with "HP HΦ Hl_new_out"). 
		* iModIntro.
		  iSplitL "Hhead Htail HisLL_xs4 Hcurr HAbst".
			{
				iNext.
				iExists xs_v; iFrame.
				iExists xs4, xs4_queue, xs4_old, x_head, x_tail'''; iFrame.
				iSplit; first done.
				iSplit; first done.
				done.
			}
		  wp_pures.
		  wp_lam.
		  iApply ("IH" with "HP HΦ Hl_new_out"). 
	+ (* Inconsistent*)
		wp_lam.
		iApply ("IH" with "HP HΦ Hl_new_out").
Admitted.

Lemma dequeue_spec v_q (Q_γ : Qgnames) (P : iProp Σ) (Q : val -> iProp Σ):
	□(∀xs_v, (Q_γ ⤇● xs_v ∗ P
				={⊤ ∖ ↑Ni}=∗
				▷ (( ⌜xs_v = []⌝ ∗ Q_γ ⤇● xs_v ∗ Q NONEV) ∨
				(∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗ Q_γ ⤇● xs_v' ∗ Q (SOMEV x_v)))
			)
	 )
	-∗
	{{{ is_queue v_q Q_γ ∗ P }}}
		dequeue v_q
	{{{ v, RET v; Q v }}}.
Proof.
	Admitted.

End proofs.

Notation "Q_γ ⤇● xs_v" := (own Q_γ.(γ_Abst) (●F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇● xs_v") : bi_scope.
Notation "Q_γ ⤇◯ xs_v" := (own Q_γ.(γ_Abst) (◯F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇◯ xs_v") : bi_scope.
Notation "Q_γ ⤇[ q ] xs_v" := (own Q_γ.(γ_Abst) (◯F{ q } (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇[ q ] xs_v") : bi_scope.
