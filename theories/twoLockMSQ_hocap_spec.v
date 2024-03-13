From stdpp Require Import countable.
From iris.algebra Require Import excl list agree lib.frac_auth.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants token.
From MSQueue Require Import twoLockMSQ_impl.
From MSQueue Require Import twoLockMSQ_common.

Local Existing Instance spin_lock.

Section proofs.

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!tokenG Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Let N := nroot .@ "twoLockMSQ".

(* ===== Concurrent Specification for Two-lock M&S Queue ===== *)

(* Ghost variable names *)
Record Qgnames := {γ_Abst 	: gname;
				   γ_Hlock 	: gname;
				   γ_Tlock 	: gname;
				   γ_E 		: gname;
				   γ_nE 	: gname;
				   γ_D 		: gname;
				   γ_nD 	: gname;
				   γ_Before : gname;
				   γ_After 	: gname;
				  }.

(* Tokens *)
Definition TokHlock (g : Qgnames) := token g.(γ_Hlock).
Definition TokTlock (g : Qgnames) := token g.(γ_Tlock).
Definition TokE (g : Qgnames) := token g.(γ_E).
Definition ToknE (g : Qgnames) := token g.(γ_nE).
Definition TokD (g : Qgnames) := token g.(γ_D).
Definition ToknD (g : Qgnames) := token g.(γ_nD).
Definition TokBefore (g : Qgnames) := token g.(γ_Before).
Definition TokAfter (g : Qgnames) := token g.(γ_After).
Definition TokUpdated (g : Qgnames) := ((TokBefore g) ∗ (TokAfter g))%I.

Definition queue_invariant (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, own Q_γ.(γ_Abst) (●F (to_agree xs_v)) ∗ (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: (loc * val * loc)), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	(
		(* Static *)
		(
			l_head ↦ #(n_in x_head) ∗
			l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail xs⌝ ∗
			ToknE Q_γ ∗ ToknD Q_γ ∗ TokUpdated Q_γ
		)
		∨
		(* Enqueue *)
		(
			l_head ↦ #(n_in x_head) ∗
			l_tail ↦{#1/2} #(n_in x_tail) ∗
				(⌜isLast x_tail xs⌝ ∗ TokBefore Q_γ ∨
				 ⌜isSndLast x_tail xs⌝ ∗ TokAfter Q_γ) ∗
			TokE Q_γ ∗ ToknD Q_γ
		)
		∨
		(* Dequeue *)
		(
			l_head ↦{#1/2} #(n_in x_head) ∗
			l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail xs⌝ ∗
			ToknE Q_γ ∗ TokD Q_γ ∗ TokUpdated Q_γ
		)
		∨
		(* Both *)
		(
			l_head ↦{#1/2} #(n_in x_head) ∗
			l_tail ↦{#1/2} #(n_in x_tail) ∗
				(⌜isLast x_tail xs⌝ ∗ TokBefore Q_γ ∨
				 ⌜isSndLast x_tail xs⌝ ∗ TokAfter Q_γ) ∗
			TokE Q_γ ∗ TokD Q_γ
		)
	).

Definition queue_invariant_simple (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, own Q_γ.(γ_Abst) (●F (to_agree xs_v)) ∗ (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: (loc * val * loc)), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	(
		(
			(l_head ↦ #(n_in x_head) ∗ ToknD Q_γ) ∨ 
			(l_head ↦{#1/2} #(n_in x_head) ∗ TokD Q_γ)
		) ∗
		(
			(l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail xs⌝ ∗ ToknE Q_γ ∗ TokUpdated Q_γ) ∨
			(
				l_tail ↦{#1/2} #(n_in x_tail) ∗ TokE Q_γ ∗
				(
					(⌜isLast x_tail xs⌝ ∗ TokBefore Q_γ) ∨
				 	(⌜isSndLast x_tail xs⌝ ∗ TokAfter Q_γ)
				)
			)
		)
	).

Lemma queue_invariant_equiv_simple : forall l_head l_tail Q_γ,
	(queue_invariant l_head l_tail Q_γ) ∗-∗
	(queue_invariant_simple l_head l_tail Q_γ).
Proof.
	iIntros (l_head l_tail Q_γ).
	iSplit.
	- iIntros "(%xs_v & HAbst_auth & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_split & HisLL_xs & %Hconc_abst_eq & [H_Static | [H_Enqueue | [H_Dequeue | H_Both]]])"; 
	iExists xs_v; iFrame; iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
	  + iDestruct "H_Static" as "(Hl_head & Hl_tail & HisLast & HTokne & HToknD & HTokUpdated)".
	  	iSplit; first done.
		iSplitL "Hl_head HToknD"; first (iLeft; iFrame).
		iLeft. iFrame.
	  + iDestruct "H_Enqueue" as "(Hl_head & Hl_tail & [[HisLast HTokAfter] | [HisSndLast HAfter]] & HToke & HToknD)".
	    * iSplit; first done.
		  iSplitL "Hl_head HToknD"; first (iLeft; iFrame). 
		  iRight. iFrame. iLeft. iFrame.
		* iSplit; first done.
		  iSplitL "Hl_head HToknD"; first (iLeft; iFrame). 
		  iRight. iFrame. iRight. iFrame.
	  + iDestruct "H_Dequeue" as "(Hl_head & Hl_tail & HisLast & HTokne & HTokD & HTokUpdated)".
	    iSplit; first done.
		iSplitL "Hl_head HTokD"; first (iRight; iFrame).
		iLeft. iFrame.
	  + iDestruct "H_Both" as "(Hl_head & Hl_tail & [[HisLast HTokAfter] | [HisSndLast HAfter]] & HToke & HTokD)".
	    * iSplit; first done.
		  iSplitL "Hl_head HTokD"; first (iRight; iFrame). 
		  iRight. iFrame. iLeft. iFrame.
		* iSplit; first done.
		  iSplitL "Hl_head HTokD"; first (iRight; iFrame). 
		  iRight. iFrame. iRight. iFrame.
	- iIntros "(%xs_v & HAbst_auth & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_split & HisLL_xs & %Hconc_abst_eq & [[Hl_head HToknD] | [Hl_head HTokD]] & [(Hl_tail & HisLast & HToknE & HTokUpdated) | (Hl_tail & HTokE & [[HisLast HTokBefore] | [HisSndLast HTokAfter]])])";
	iExists xs_v; iFrame; iExists xs, xs_queue, xs_old, x_head, x_tail; eauto 10 with iFrame.
Qed.

Definition is_queue (v_q : val) (Q_γ: Qgnames) : iProp Σ :=
	∃ l_queue l_head l_tail : loc, ∃ H_lock T_lock : val,
	⌜v_q = #l_queue⌝ ∗
	l_queue ↦□ ((#l_head, #l_tail), (H_lock, T_lock)) ∗
	inv N (queue_invariant l_head l_tail Q_γ) ∗
	is_lock Q_γ.(γ_Hlock) H_lock (TokD Q_γ) ∗
	is_lock Q_γ.(γ_Tlock) T_lock (TokE Q_γ).

(* is_queue is persistent *)
Global Instance is_queue_persistent v_q Q_γ : Persistent (is_queue v_q Q_γ).
Proof. apply _. Qed.

Lemma initialize_spec:
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γ, RET v_q; is_queue v_q Q_γ ∗
						  own Q_γ.(γ_Abst) (◯F (to_agree [])) }}}.
Proof.
	iIntros (Φ) "_ HΦ".
	wp_lam.
	wp_pures.
	wp_alloc l_1_out as "Hl_1_out".
	wp_alloc l_1_in as "Hl_1_in".
	wp_pures.
	iMod (pointsto_persist with "Hl_1_in") as "#Hl_1_in".
	wp_pures.
	iMod token_alloc as (γ_D) "Hγ_D".
	wp_apply (newlock_spec with "Hγ_D").
	iIntros (hlock γ_Hlock) "Hγ_Hlock".
	wp_let.
	iMod token_alloc as (γ_E) "Hγ_E".
	wp_apply (newlock_spec with "Hγ_E").
	iIntros (tlock γ_Tlock) "Hγ_Tlock".
	wp_let.
	wp_alloc l_tail as "Hl_tail".
	wp_alloc l_head as "Hl_head".
	iMod token_alloc as (γ_nE) "Hγ_nE".
	iMod token_alloc as (γ_nD) "Hγ_nD".
	iMod token_alloc as (γ_Before) "Hγ_Before".
	iMod token_alloc as (γ_After) "Hγ_After".
	iMod (own_alloc (●F (to_agree []) ⋅ ◯F (to_agree []))) as (γ_Abst) "[Hγ_Abst_auth Hγ_Abst_frac]"; first by apply frac_auth_valid.
	set (Queue_gnames := {| γ_Abst := γ_Abst;
							γ_Hlock := γ_Hlock;
							γ_Tlock := γ_Tlock;
							γ_E := γ_E;
							γ_nE := γ_nE;
							γ_D := γ_D;
							γ_nD := γ_nD;
							γ_Before := γ_Before;
							γ_After := γ_After
					|}).
	iMod (inv_alloc N _ (queue_invariant l_head l_tail Queue_gnames) with "[Hγ_Abst_auth Hl_head Hl_tail Hl_1_in Hl_1_out Hγ_nE Hγ_nD Hγ_Before Hγ_After]") as "#HqueueInv".
	{
		iNext. iExists []. iFrame. iExists [(l_1_in, NONEV, l_1_out)], [], [], (l_1_in, NONEV, l_1_out), (l_1_in, NONEV, l_1_out). cbn. iSplit; first done. iSplitL "Hl_1_in Hl_1_out"; first auto. iSplit; first done.
		iLeft. iFrame. iPureIntro. by exists [].
	}
	wp_alloc l_queue as "Hl_queue".
	iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
	iApply ("HΦ" $! #l_queue Queue_gnames).
	iModIntro.
	iFrame.
	iExists l_queue, l_head, l_tail, hlock, tlock.
	by repeat iSplit.
Qed.

Lemma enqueue_spec v_q (v : val) (Q_γ : Qgnames) (P Q : iProp Σ) :
	□(∀xs_v, (own Q_γ.(γ_Abst) (●F (to_agree xs_v)) ∗ P
				={⊤ ∖ ↑N}=∗ own Q_γ.(γ_Abst) (●F (to_agree (v :: xs_v))) ∗ Q))
	-∗
	{{{ is_queue v_q Q_γ ∗ P}}}
		enqueue v_q v
	{{{ w, RET w; Q }}}.
Proof.
	Admitted.

Lemma dequeue_spec v_q (Q_γ : Qgnames) (P : iProp Σ) (Q : val -> iProp Σ):
	□(∀xs_v, (own Q_γ.(γ_Abst) (●F (to_agree xs_v)) ∗ P
				={⊤ ∖ ↑N}=∗
		      	(( ⌜xs_v = []⌝ ∗ own Q_γ.(γ_Abst) (●F (to_agree (xs_v))) ∗ Q NONEV) ∨
				(∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗ own Q_γ.(γ_Abst) (●F (to_agree (xs_v'))) ∗ Q (SOMEV x_v)))
			)
	 )
	-∗
	{{{ is_queue v_q Q_γ ∗ P}}}
		dequeue v_q
	{{{ v, RET v; Q v }}}.
Proof.
	Admitted.

End proofs.
