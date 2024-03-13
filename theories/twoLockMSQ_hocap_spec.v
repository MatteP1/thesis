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

(* TODO: write in correct invariant *)
Definition queue_invariant (Ψ : val -> iProp Σ) (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: (loc * val * loc)), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	All xs_v Ψ ∗
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

Definition queue_invariant_simple (Ψ : val -> iProp Σ) (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: (loc * val * loc)), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	All xs_v Ψ ∗
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

Lemma queue_invariant_equiv_simple : forall Ψ l_head l_tail Q_γ,
	(queue_invariant Ψ l_head l_tail Q_γ) ∗-∗
	(queue_invariant_simple Ψ l_head l_tail Q_γ).
Proof.
	iIntros (Ψ l_head l_tail Q_γ).
	iSplit.
	- iIntros "(%xs_v & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_split & HisLL_xs & %Hconc_abst_eq & HAll & [H_Static | [H_Enqueue | [H_Dequeue | H_Both]]])"; 
	iExists xs_v, xs, xs_queue, xs_old, x_head, x_tail; iFrame.
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
	- iIntros "(%xs_v & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_split & HisLL_xs & %Hconc_abst_eq & HAll & [[Hl_head HToknD] | [Hl_head HTokD]] & [(Hl_tail & HisLast & HToknE & HTokUpdated) | (Hl_tail & HTokE & [[HisLast HTokBefore] | [HisSndLast HTokAfter]])])";
	iExists xs_v, xs, xs_queue, xs_old, x_head, x_tail; eauto 10 with iFrame.
Qed.

Definition is_queue (Ψ : val -> iProp Σ) (v_q : val) (Q_γ: Qgnames) : iProp Σ :=
	∃ l_queue l_head l_tail : loc, ∃ H_lock T_lock : val,
	⌜v_q = #l_queue⌝ ∗
	l_queue ↦□ ((#l_head, #l_tail), (H_lock, T_lock)) ∗
	inv N (queue_invariant Ψ l_head l_tail Q_γ) ∗
	is_lock Q_γ.(γ_Hlock) H_lock (TokD Q_γ) ∗
	is_lock Q_γ.(γ_Tlock) T_lock (TokE Q_γ).

(* is_queue is persistent *)
Global Instance is_queue_persistent Ψ v_q Q_γ : Persistent (is_queue Ψ v_q Q_γ).
Proof. apply _. Qed.

(* Todo Write in spec *)

Lemma initialize_spec (Ψ : val -> iProp Σ):
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γ, RET v_q; is_queue Ψ v_q Q_γ }}}.
Proof.
	iIntros (Φ) "_ HΦ". Admitted.

Lemma enqueue_spec v_q Ψ (v : val) (qg : Qgnames) :
	{{{ is_queue Ψ v_q qg ∗ Ψ v }}}
		enqueue v_q v
	{{{ w, RET w; True }}}.
Proof.
	Admitted.

Lemma dequeue_spec P Q v_q Ψ (qg : Qgnames) :
	{{{ (P ={⊤ ∖ ↑N}=∗ Q) ∗ own qg.(γ_Abst) (●F (to_agree [])) ∗ is_queue Ψ v_q qg }}}
		dequeue v_q
	{{{ v, RET v; ⌜v = NONEV⌝ ∨ (∃ x_v, ⌜v = SOMEV x_v⌝ ∗ Ψ x_v) }}}.
Proof.
	iIntros (Φ) "H HΦ".
	Admitted.

End proofs.
