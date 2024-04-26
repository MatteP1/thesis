From stdpp Require Import sets countable.
From iris.algebra Require Import list agree gset lib.frac_auth.
From iris.bi Require Import fixpoint big_op.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation primitive_laws.
From iris.base_logic.lib Require Import invariants.
From MSQueue Require Import lockFreeMSQ_impl.
From MSQueue Require Import MSQ_common.
From MSQueue Require Import lockFreeMSQ_hocap_spec.

(* NOTE: This file is very similar to twoLockMSQ_derived. They differ in the following ways:
	- This file imports the lock-free implementations
	- The resource algebras used are different
	- This file uses the Qgnames of the lock-free hocap spec directly. *)

Section sequential_proofs.

Context `{!heapGS Σ}.
Context `{!inG Σ (authR (gsetUR nodeO))}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Variable N : namespace.

(* ===== Sequential Specification for Lock-Free M&S Queue ===== *)

Definition is_queue_seq (v_q : val) (xs_v: list val) (Q_γH: Qgnames) : iProp Σ :=
	is_queue N v_q Q_γH ∗
	Q_γH ⤇◯ xs_v.

Lemma initialize_spec_seq :
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γH, RET v_q; is_queue_seq v_q [] Q_γH }}}.
Proof.
	iIntros (Φ _) "HΦ".
	wp_apply (initialize_spec N); first done.
	iIntros (v_q Q_γH) "[His_queue Habst_frag]".
	iApply ("HΦ" $! v_q Q_γH).
	by iFrame.
Qed.

Lemma enqueue_spec_seq v_q (v : val) (xs_v : list val) (Q_γH : Qgnames) :
	{{{ is_queue_seq v_q xs_v Q_γH }}}
		enqueue v_q v
	{{{w, RET w; is_queue_seq v_q (v :: xs_v) Q_γH }}}.
Proof.
	iIntros (Φ) "(#His_queue & Hfrag) HΦ".
	set (P := (Q_γH ⤇◯ xs_v)%I).
	set (Q := (Q_γH ⤇◯ (v :: xs_v))%I).
	wp_apply (enqueue_spec N v_q v Q_γH P Q with "[] [Hfrag]").
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		unfold P, Q.
		iIntros "[Hauth Hfrag]".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by iApply (queue_contents_auth_frag_agree _ xs_v xs_v' 1 with "Hauth Hfrag").
		by iMod (queue_contents_update _ xs_v xs_v (v :: xs_v) with "Hauth Hfrag").
	}
	(* Proving pre-condition of hocap enqueue spec *)
	{ by iFrame. }
	iIntros (w) "HQ".
	iApply ("HΦ" $! w).
	by repeat iSplit.
Qed.

Lemma dequeue_spec_seq v_q (xs_v : list val) (Q_γH : Qgnames) :
	{{{ is_queue_seq v_q xs_v Q_γH }}}
		dequeue v_q
	{{{ v, RET v; (⌜xs_v = []⌝ ∗ ⌜v = NONEV⌝ ∗ is_queue_seq v_q xs_v Q_γH) ∨
								(∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗
										⌜v = SOMEV x_v⌝ ∗ is_queue_seq v_q xs_v' Q_γH) }}}.
Proof.
	iIntros (Φ) "(#His_queue & Hfrag) HΦ".
	set (P := (Q_γH ⤇◯ xs_v)%I).
	set (Q := λ v, ((⌜xs_v = []⌝ ∗ ⌜v = NONEV⌝ ∗ Q_γH ⤇◯ xs_v) ∨
									(∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗
										⌜v = SOMEV x_v⌝ ∗ Q_γH ⤇◯ xs_v'))%I).
	wp_apply (dequeue_spec N v_q Q_γH P Q with "[] [Hfrag]" ).
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		iIntros "[Hauth Hfrag]".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by iApply (queue_contents_auth_frag_agree _ xs_v xs_v' 1 with "Hauth Hfrag").
		destruct (ll_case_first xs_v) as [->|[x_v [xs_v' ->]]].
		- iLeft.
		  iModIntro.
		  iSplit; first done.
		  iFrame.
		  unfold P, Q.
		  iLeft.
		  by repeat iSplit.
		- iMod (queue_contents_update _ _ _ (xs_v') with "Hauth Hfrag") as "[Hauth Hfrag]".
		  iRight.
		  iExists x_v, xs_v'.
		  iModIntro.
		  iSplit; first done.
		  iFrame.
		  iRight.
		  iExists x_v, xs_v'.
		  by repeat iSplit.
	}
	(* Proving pre-condition of hocap enqueue spec *)
	{ by iFrame. }
	iIntros (w) "HQ".
	iApply ("HΦ" $! w).
	unfold Q.
	iDestruct "HQ" as "[(-> & %Hres & Hfrag) | (%x_v & %xs_v' & %Hxs_v_eq & %Hres & Hfrag)]".
	- iLeft.
	  by repeat iSplit.
	- iRight.
	  iExists x_v, xs_v'.
	  by repeat iSplit.
Qed.

End sequential_proofs.


Section concurrent_proofs.

Context `{!heapGS Σ}.
Context `{!inG Σ (authR (gsetUR nodeO))}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Variable N : namespace.
Notation NC := (N .@ "concurrent").

(* ===== Concurrent Specification for Lock-Free M&S Queue ===== *)

Definition is_queue_conc (Ψ : val -> iProp Σ) (v_q : val) (Q_γH: Qgnames) : iProp Σ :=
	is_queue N v_q Q_γH ∗
	inv NC (∃xs_v, Q_γH ⤇◯ xs_v ∗ All xs_v Ψ).

(* is_queue_conc is persistent *)
Global Instance is_queue_conc_persistent Ψ v_q Q_γH : Persistent (is_queue_conc Ψ v_q Q_γH).
Proof. apply _. Qed.

Lemma initialize_spec_conc (Ψ : val -> iProp Σ):
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γH, RET v_q; is_queue_conc Ψ v_q Q_γH }}}.
Proof.
	iIntros (Φ _) "HΦ".
	iApply wp_fupd.
	wp_apply (initialize_spec N); first done.
	iIntros (v_q Q_γH) "[His_queue Habst_frag]".
	iApply ("HΦ" $! v_q Q_γH).
	iMod (inv_alloc NC _ (∃xs_v, Q_γH ⤇◯ xs_v ∗ All xs_v Ψ) with "[Habst_frag]") as "HInv"; first (iExists []; auto).
	by iFrame.
Qed.

Lemma enqueue_spec_conc v_q Ψ (v : val) (Q_γH : Qgnames) :
	{{{ is_queue_conc Ψ v_q Q_γH ∗ Ψ v }}}
		enqueue v_q v
	{{{ w, RET w; True }}}.
Proof.
	iIntros (Φ) "[(#His_queue & #HInv) HΨ] HΦ".
	set (P := Ψ v).
	set (Q := True%I).
	wp_apply (enqueue_spec N v_q v Q_γH P Q with "[] [HΨ]").
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		unfold P, Q.
		iIntros "[Hauth HΨ]".
		iInv "HInv" as "(%xs_v & >Hfrag & HAll)".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by iApply (queue_contents_auth_frag_agree _ xs_v xs_v' 1 with "Hauth Hfrag").
		iMod (queue_contents_update _ xs_v xs_v (v :: xs_v) with "Hauth Hfrag") as "[Hauth Hfrag]".
		iModIntro.
		iSplitL "Hfrag HAll HΨ".
		- iNext.
		  iExists (v :: xs_v).
		  iFrame.
		- by iFrame.
	}
	(* Proving pre-condition of hocap enqueue spec *)
	{ by iFrame. }
	iIntros (w) "HQ".
	by iApply ("HΦ" $! w).
Qed.

Lemma dequeue_spec_conc v_q Ψ (Q_γH : Qgnames) :
	{{{ is_queue_conc Ψ v_q Q_γH }}}
		dequeue v_q
	{{{ v, RET v; ⌜v = NONEV⌝ ∨ (∃ x_v, ⌜v = SOMEV x_v⌝ ∗ Ψ x_v) }}}.
Proof.
	iIntros (Φ) "(#His_queue & #HInv) HΦ".
	set (P := True%I : iProp Σ).
	set (Q := λ v, (⌜v = NONEV⌝ ∨ (∃x_v, ⌜v = SOMEV x_v⌝ ∗ Ψ x_v))%I).
	wp_apply (dequeue_spec N v_q Q_γH P Q).
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		iIntros "[Hauth _]".
		iInv "HInv" as "(%xs_v & >Hfrag & HAll)".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by iApply (queue_contents_auth_frag_agree _ xs_v xs_v' 1 with "Hauth Hfrag").
		destruct (ll_case_first xs_v) as [->|[x_v [xs_v' ->]]].
		- iModIntro.
		  (* Close Invariant NC *)
		  iSplitL "Hfrag HAll"; first (iExists []; auto).
		  iModIntro.
		  iLeft.
		  iFrame.
		  iSplit; first done.
		  unfold Q.
		  by iLeft.
		- iMod (queue_contents_update _ _ _ (xs_v') with "Hauth Hfrag") as "[Hauth Hfrag]".
		  iPoseProof (All_split with "HAll") as "[HAll_xs_v' [HΨ _]]".
		  iModIntro.
		  (* Close Invariant NC *)
		  iSplitL "Hfrag HAll_xs_v'"; first (iExists xs_v'; iFrame).
		  iModIntro.
		  iRight.
		  iExists x_v, xs_v'.
		  iSplit; first done.
		  iFrame.
		  unfold Q.
		  iRight.
		  iExists x_v.
		  iSplit; done.
	}
	(* Proving pre-condition of hocap enqueue spec *)
	{ iFrame "#". }
	iIntros (w) "HQ".
	iApply ("HΦ" $! w).
	unfold Q.
	done.
Qed.

End concurrent_proofs.