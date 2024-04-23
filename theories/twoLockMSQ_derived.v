From stdpp Require Import countable.
From iris.algebra Require Import excl list agree lib.frac_auth.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants token.
From MSQueue Require Import twoLockMSQ_impl.
From MSQueue Require Import MSQ_common.
From MSQueue Require Import twoLockMSQ_hocap_spec.

Local Existing Instance spin_lock.

Section sequential_proofs.

Variable N : namespace.

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!tokenG Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

(* ===== Sequential Specification for Two-lock M&S Queue ===== *)

Record SeqQgnames := {γ_Hlock_seq 	: gname;
					  γ_Tlock_seq 	: gname;
					 }.

Definition proj_Qgnames_seq (Q_γH : Qgnames) : SeqQgnames :=
	{| γ_Hlock_seq := Q_γH.(γ_Hlock);
	   γ_Tlock_seq := Q_γH.(γ_Tlock);
	|}.

Definition is_queue_seq (v_q : val) (xs_v: list val) (Q_γS: SeqQgnames) : iProp Σ :=
	∃ Q_γH : Qgnames,
	⌜proj_Qgnames_seq Q_γH = Q_γS⌝ ∗
	is_queue N v_q Q_γH ∗
	Q_γH ⤇◯ xs_v.

Lemma initialize_spec_seq :
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γS, RET v_q; is_queue_seq v_q [] Q_γS }}}.
Proof.
	iIntros (Φ _) "HΦ".
	wp_apply (initialize_spec N); first done.
	iIntros (v_q Q_γH) "[His_queue Habst_frag]".
	set (Q_γS := proj_Qgnames_seq Q_γH).
	iApply ("HΦ" $! v_q Q_γS).
	iExists Q_γH.
	by iFrame.
Qed.

Lemma enqueue_spec_seq v_q (v : val) (xs_v : list val) (Q_γS : SeqQgnames) :
	{{{ is_queue_seq v_q xs_v Q_γS }}}
		enqueue v_q v
	{{{w, RET w; is_queue_seq v_q (v :: xs_v) Q_γS }}}.
Proof.
	iIntros (Φ) "(%Q_γH & %Heq & #His_queue & Hfrag) HΦ".
	set (P := (Q_γH ⤇◯ xs_v)%I).
	set (Q := (Q_γH ⤇◯ (v :: xs_v))%I).
	wp_apply (enqueue_spec N v_q v Q_γH P Q with "[] [Hfrag]").
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		rewrite /P /Q.
		iIntros "[Hauth Hfrag]".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by
			iApply (queue_contents_auth_frag_agree Q_γH xs_v xs_v' 1 with "Hauth Hfrag").
		by iMod (queue_contents_update Q_γH xs_v xs_v (v :: xs_v) with "Hauth Hfrag").
	}
	(* Proving pre-condition of hocap enqueue spec *)
	{ by iFrame. }
	iIntros (w) "HQ".
	iApply ("HΦ" $! w).
	iExists Q_γH.
	by repeat iSplit.
Qed.

Lemma dequeue_spec_seq v_q (xs_v : list val) (Q_γS : SeqQgnames) :
	{{{ is_queue_seq v_q xs_v Q_γS }}}
		dequeue v_q
	{{{ v, RET v; (⌜xs_v = []⌝ ∗ ⌜v = NONEV⌝ ∗ is_queue_seq v_q xs_v Q_γS) ∨
				  (∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗
				  		⌜v = SOMEV x_v⌝ ∗ is_queue_seq v_q xs_v' Q_γS) }}}.
Proof.
	iIntros (Φ) "(%Q_γH & %Heq & #His_queue & Hfrag) HΦ".
	set (P := (Q_γH ⤇◯ xs_v)%I).
	set (Q := λ v, ((⌜xs_v = []⌝ ∗ ⌜v = NONEV⌝ ∗ Q_γH ⤇◯ xs_v) ∨
					(∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗
						⌜v = SOMEV x_v⌝ ∗ Q_γH ⤇◯ xs_v'))%I).
	wp_apply (dequeue_spec N v_q Q_γH P Q with "[] [Hfrag]" ).
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		iIntros "[Hauth Hfrag]".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by
			iApply (queue_contents_auth_frag_agree Q_γH xs_v xs_v' 1 with "Hauth Hfrag").
		destruct xs_v as [| x xs ].
		- iLeft.
		  iModIntro.
		  iSplit; first done.
		  iFrame.
		  rewrite /P /Q.
		  iLeft.
		  by repeat iSplit.
		- destruct (exists_first (x :: xs)) as [x_v [xs_v' Hxs_v_eq]]; first done.
		  iMod (queue_contents_update Q_γH _ _ (xs_v') with "Hauth Hfrag") as "[Hauth Hfrag]".
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
	  repeat iSplit; try done.
	  iExists Q_γH.
	  by repeat iSplit.
	- iRight.
	  iExists x_v, xs_v'.
	  repeat iSplit; try done.
	  iExists Q_γH.
	by repeat iSplit.
Qed.

End sequential_proofs.


Section concurrent_proofs.

Variable N : namespace.
Notation NC := (N .@ "concurrent").

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!tokenG Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

(* ===== Concurrent Specification for Two-lock M&S Queue ===== *)

(* Ghost variable names *)
Record ConcQgnames := {γ_Hlock_conc 	: gname;
					   γ_Tlock_conc 	: gname;
					   γ_E_conc 		: gname;
					   γ_nE_conc 		: gname;
					   γ_D_conc 		: gname;
					   γ_nD_conc 		: gname;
					   γ_Before_conc 	: gname;
					   γ_After_conc 	: gname;
					}.

Definition proj_Qgnames_conc (Q_γH : Qgnames) : ConcQgnames :=
	{| γ_Hlock_conc := Q_γH.(γ_Hlock);
	   γ_Tlock_conc := Q_γH.(γ_Tlock);
	   γ_E_conc := Q_γH.(γ_E);
	   γ_nE_conc := Q_γH.(γ_nE);
	   γ_D_conc := Q_γH.(γ_D);
	   γ_nD_conc := Q_γH.(γ_nD);
	   γ_Before_conc := Q_γH.(γ_Before);
	   γ_After_conc := Q_γH.(γ_After)
	|}.

Definition is_queue_conc (Ψ : val -> iProp Σ) (v_q : val) (Q_γC: ConcQgnames) : iProp Σ :=
	∃ Q_γH : Qgnames,
	⌜proj_Qgnames_conc Q_γH = Q_γC⌝ ∗
	is_queue N v_q Q_γH ∗
	inv NC (∃xs_v, Q_γH ⤇◯ xs_v ∗ All xs_v Ψ).

(* is_queue_conc is persistent *)
Global Instance is_queue_conc_persistent Ψ v_q Q_γC : Persistent (is_queue_conc Ψ v_q Q_γC).
Proof. apply _. Qed.

Lemma initialize_spec_conc (Ψ : val -> iProp Σ):
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γC, RET v_q; is_queue_conc Ψ v_q Q_γC }}}.
Proof.
	iIntros (Φ _) "HΦ".
	iApply wp_fupd.
	wp_apply (initialize_spec N); first done.
	iIntros (v_q Q_γH) "[His_queue Habst_frag]".
	set (Q_γC := proj_Qgnames_conc Q_γH).
	iApply ("HΦ" $! v_q Q_γC).
	iExists Q_γH.
	iMod (inv_alloc NC _ (∃xs_v, Q_γH ⤇◯ xs_v ∗ All xs_v Ψ) with "[Habst_frag]") as "HInv"; first (iExists []; auto).
	by iFrame.
Qed.

Lemma enqueue_spec_conc v_q Ψ (v : val) (Q_γC : ConcQgnames) :
	{{{ is_queue_conc Ψ v_q Q_γC ∗ Ψ v }}}
		enqueue v_q v
	{{{ w, RET w; True }}}.
Proof.
	iIntros (Φ) "[(%Q_γH & %Heq & #His_queue & #HInv) HΨ] HΦ".
	set (P := Ψ v).
	set (Q := True%I).
	wp_apply (enqueue_spec N v_q v Q_γH P Q with "[] [HΨ]").
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		rewrite /P /Q.
		iIntros "[Hauth HΨ]".
		iInv "HInv" as "(%xs_v & >Hfrag & HAll)".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by
			iApply (queue_contents_auth_frag_agree Q_γH xs_v xs_v' 1 with "Hauth Hfrag").
		iMod (queue_contents_update Q_γH xs_v xs_v (v :: xs_v) with "Hauth Hfrag") as "[Hauth Hfrag]".
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

Lemma dequeue_spec_conc v_q Ψ (Q_γC : ConcQgnames) :
	{{{ is_queue_conc Ψ v_q Q_γC }}}
		dequeue v_q
	{{{ v, RET v; ⌜v = NONEV⌝ ∨ (∃ x_v, ⌜v = SOMEV x_v⌝ ∗ Ψ x_v) }}}.
Proof.
	iIntros (Φ) "(%Q_γH & %Heq & #His_queue & #HInv) HΦ".
	set (P := True%I : iProp Σ).
	set (Q := λ v, (⌜v = NONEV⌝ ∨ (∃x_v, ⌜v = SOMEV x_v⌝ ∗ Ψ x_v))%I).
	wp_apply (dequeue_spec N v_q Q_γH P Q).
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		iIntros "[Hauth _]".
		iInv "HInv" as "(%xs_v & >Hfrag & HAll)".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by
			iApply (queue_contents_auth_frag_agree Q_γH xs_v xs_v' 1 with "Hauth Hfrag").
		destruct xs_v as [| x xs ].
		- iModIntro.
		  (* Close Invariant NC *)
		  iSplitL "Hfrag HAll"; first (iExists []; auto).
		  iModIntro.
		  iLeft.
		  iFrame.
		  iSplit; first done.
		  rewrite /Q.
		  by iLeft.
		- destruct (exists_first (x :: xs)) as [x_v [xs_v' ->]]; first done.
		  iMod (queue_contents_update Q_γH _ _ (xs_v') with "Hauth Hfrag") as "[Hauth Hfrag]".
		  iPoseProof (All_split with "HAll") as "[HAll_xs_v' [HΨ _]]".
		  iModIntro.
		  (* Close Invariant NC *)
		  iSplitL "Hfrag HAll_xs_v'"; first (iExists xs_v'; iFrame).
		  iModIntro.
		  iRight.
		  iExists x_v, xs_v'.
		  iSplit; first done.
		  iFrame.
		  rewrite /Q.
		  iRight.
		  iExists x_v.
		  iSplit; done.
	}
	(* Proving pre-condition of hocap enqueue spec *)
	{ auto. }
	iIntros (w) "HQ".
	iApply ("HΦ" $! w).
	unfold Q.
	done.
Qed.

End concurrent_proofs.