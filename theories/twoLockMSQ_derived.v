From stdpp Require Import countable.
From iris.algebra Require Import excl list agree lib.frac_auth.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants token.
From MSQueue Require Import twoLockMSQ_impl.
From MSQueue Require Import twoLockMSQ_common.
From MSQueue Require Import twoLockMSQ_hocap_spec.

Local Existing Instance spin_lock.

Section proofs.

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!tokenG Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Notation "Q_γ ⤇● xs_v" := (own Q_γ.(γ_Abst) (●F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇● xs_v") : bi_scope.
Notation "Q_γ ⤇◯ xs_v" := (own Q_γ.(γ_Abst) (◯F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇◯ xs_v") : bi_scope.
Notation "Q_γ ⤇[ q ] xs_v" := (own Q_γ.(γ_Abst) (◯F{ q } (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇[ q ] xs_v") : bi_scope.

(* ===== Sequential Specification for Two-lock M&S Queue ===== *)

(* TODO: For some reason, the fields cannot be the same as other record fields *)
Record SeqQgnames := {γ_Hlock_seq 	: gname;
					  γ_Tlock_seq 	: gname;
					 }.

Definition is_queue_seq (v_q : val) (xs_v: list val) (Q_γS: SeqQgnames) : iProp Σ :=
	∃ Q_γH : Qgnames, 
	is_queue v_q Q_γH ∗
	Q_γH ⤇◯ xs_v.

Lemma initialize_spec_seq :
	{{{ True }}} 
		initialize #() 
	{{{ v_q Q_γS, RET v_q; is_queue_seq v_q [] Q_γS }}}.
Proof.
	iIntros (Φ _) "HΦ".
	wp_apply initialize_spec; first done.
	iIntros (v_q Q_γH) "[His_queue Habst_frag]".
	set (Q_γS := {| γ_Hlock_seq := Q_γH.(γ_Hlock);
					γ_Tlock_seq := Q_γH.(γ_Tlock);
				 |}).
	iApply ("HΦ" $! v_q Q_γS).
	iExists Q_γH.
	by iFrame.
Qed.

Lemma enqueue_spec_seq v_q (v : val) (xs_v : list val) (Q_γ : SeqQgnames) :
	{{{ is_queue_seq v_q xs_v Q_γ }}}
		enqueue v_q v 
	{{{w, RET w; is_queue_seq v_q (v :: xs_v) Q_γ }}}.
Proof.
	iIntros (Φ) "(%Q_γH & #His_queue & Hfrag) HΦ".
	set (P := (Q_γH ⤇◯ xs_v)%I).
	set (Q := (Q_γH ⤇◯ (v :: xs_v))%I).
	wp_apply (enqueue_spec v_q v Q_γH P Q with "[] [Hfrag]" ).
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		rewrite /P /Q.
		iIntros "[Hauth Hfrag]".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by
			iApply (abstLL_auth_frag_agree Q_γH xs_v xs_v' 1 with "Hauth Hfrag").
		by iMod (abstLL_update Q_γH xs_v xs_v (v :: xs_v) with "Hauth Hfrag").
	}
	(* Proving pre-condition of hocap enqueue spec *)
	{ by iFrame. }
	iIntros (w) "HQ".
	iApply ("HΦ" $! w).
	iExists Q_γH.
	by repeat iSplit.
Qed.

Lemma dequeue_spec_seq v_q (xs_v : list val) (Q_γ : SeqQgnames) : 
	{{{ is_queue_seq v_q xs_v Q_γ }}}
		dequeue v_q
	{{{ v, RET v; (⌜xs_v = []⌝ ∗ ⌜v = NONEV⌝ ∗ is_queue_seq v_q xs_v Q_γ) ∨
				  (∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗ 
				  		⌜v = SOMEV x_v⌝ ∗ is_queue_seq v_q xs_v' Q_γ) }}}.
Proof.
	iIntros (Φ) "(%Q_γH & #His_queue & Hfrag) HΦ".
	set (P := (Q_γH ⤇◯ xs_v)%I).
	set (Q := λ v, ((⌜xs_v = []⌝ ∗ ⌜v = NONEV⌝ ∗ Q_γH ⤇◯ xs_v) ∨ 
					(∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗ 
						⌜v = SOMEV x_v⌝ ∗ Q_γH ⤇◯ xs_v'))%I).
	wp_apply (dequeue_spec v_q Q_γH P Q with "[] [Hfrag]" ).
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		iIntros "[Hauth Hfrag]".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by
			iApply (abstLL_auth_frag_agree Q_γH xs_v xs_v' 1 with "Hauth Hfrag").
		destruct xs_v as [| x xs ].
		- iLeft.
		  iModIntro.
		  iSplit; first done.
		  iFrame.
		  rewrite /P /Q.
		  iLeft.
		  by repeat iSplit.
		- destruct (exists_first (x :: xs)) as [x_v [xs_v' Hxs_v_eq]]; first done.
		  iMod (abstLL_update Q_γH _ _ (xs_v') with "Hauth Hfrag") as "[Hauth Hfrag]".
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
	iDestruct "HQ" as "[(-> & %Hres & Hfrag) | (%x_v & %xs_v' & %Heq & %Hres & Hfrag)]".
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

End proofs.

Section proofs.

Let NC := nroot .@ "twoLockMSQ_C".

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!tokenG Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Notation "Q_γ ⤇● xs_v" := (own Q_γ.(γ_Abst) (●F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇● xs_v") : bi_scope.
Notation "Q_γ ⤇◯ xs_v" := (own Q_γ.(γ_Abst) (◯F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇◯ xs_v") : bi_scope.
Notation "Q_γ ⤇[ q ] xs_v" := (own Q_γ.(γ_Abst) (◯F{ q } (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇[ q ] xs_v") : bi_scope.

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

(* Tokens *)
Definition TokHlock (g : ConcQgnames) := token g.(γ_Hlock_conc).
Definition TokTlock (g : ConcQgnames) := token g.(γ_Tlock_conc).
Definition TokE (g : ConcQgnames) := token g.(γ_E_conc).
Definition ToknE (g : ConcQgnames) := token g.(γ_nE_conc).
Definition TokD (g : ConcQgnames) := token g.(γ_D_conc).
Definition ToknD (g : ConcQgnames) := token g.(γ_nD_conc).
Definition TokBefore (g : ConcQgnames) := token g.(γ_Before_conc).
Definition TokAfter (g : ConcQgnames) := token g.(γ_After_conc).
Definition TokUpdated (g : ConcQgnames) := ((TokBefore g) ∗ (TokAfter g))%I.


Definition is_queue_conc (Ψ : val -> iProp Σ) (v_q : val) (Q_γC: ConcQgnames) : iProp Σ :=
	∃ Q_γH : Qgnames, 
	is_queue v_q Q_γH ∗
	inv NC (∃xs_v, Q_γH ⤇◯ xs_v ∗ All xs_v Ψ).

(* is_queue is persistent *)
Global Instance is_queue_conc_persistent Ψ v_q Q_γ : Persistent (is_queue_conc Ψ v_q Q_γ).
Proof. apply _. Qed.

Lemma initialize_spec (Ψ : val -> iProp Σ):
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γ, RET v_q; is_queue_conc Ψ v_q Q_γ }}}.
Proof.
	iIntros (Φ _) "HΦ".
	iApply wp_fupd.
	wp_apply initialize_spec; first done.
	iIntros (v_q Q_γH) "[His_queue Habst_frag]".
	set (Q_γC := {| γ_Hlock_conc := Q_γH.(γ_Hlock);
					γ_Tlock_conc := Q_γH.(γ_Tlock);
					γ_E_conc := Q_γH.(γ_E);
					γ_nE_conc := Q_γH.(γ_nE);
					γ_D_conc := Q_γH.(γ_D);
					γ_nD_conc := Q_γH.(γ_nD);
					γ_Before_conc := Q_γH.(γ_Before);
					γ_After_conc := Q_γH.(γ_After)
				 |}).
	iApply ("HΦ" $! v_q Q_γC).
	iExists Q_γH.
	iMod (inv_alloc NC _ (∃xs_v, Q_γH ⤇◯ xs_v ∗ All xs_v Ψ) with "[Habst_frag]") as "HInv"; first (iExists []; auto).
	by iFrame.
Qed.

Lemma enqueue_spec v_q Ψ (v : val) (Q_γ : ConcQgnames) :
	{{{ is_queue_conc Ψ v_q Q_γ ∗ Ψ v }}}
		enqueue v_q v
	{{{ w, RET w; True }}}.
Proof.
	iIntros (Φ) "[(%Q_γH & #His_queue & #HInv) HΨ] HΦ".
	set (P := Ψ v).
	set (Q := True%I).
	wp_apply (enqueue_spec v_q v Q_γH P Q with "[] [HΨ]" ).
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		rewrite /P /Q.
		iIntros "[Hauth HΨ]".
		iInv "HInv" as "(%xs_v & >Hfrag & HAll)".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by
			iApply (abstLL_auth_frag_agree Q_γH xs_v xs_v' 1 with "Hauth Hfrag").
		iMod (abstLL_update Q_γH xs_v xs_v (v :: xs_v) with "Hauth Hfrag") as "[Hauth Hfrag]".
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

Lemma dequeue_spec v_q Ψ (Q_γ : ConcQgnames) :
	{{{ is_queue_conc Ψ v_q Q_γ }}}
		dequeue v_q
	{{{ v, RET v; ⌜v = NONEV⌝ ∨ (∃ x_v, ⌜v = SOMEV x_v⌝ ∗ Ψ x_v) }}}.
Proof.
	iIntros (Φ) "(%Q_γH & #His_queue & #HInv) HΦ".
	(* TODO: There must exist some True in the context for it to work... *)
	(* set (P := (True)%I). *)
	set (Q := λ v, (⌜v = NONEV⌝ ∨ (∃x_v, ⌜v = SOMEV x_v⌝ ∗ Ψ x_v))%I).
	wp_apply (dequeue_spec v_q Q_γH True%I Q).
	(* Proving viewshift *)
	{
		iIntros (xs_v') "!>".
		iIntros "[Hauth _]".
		iInv "HInv" as "(%xs_v & >Hfrag & HAll)".
		iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by
			iApply (abstLL_auth_frag_agree Q_γH xs_v xs_v' 1 with "Hauth Hfrag").
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
		  iMod (abstLL_update Q_γH _ _ (xs_v') with "Hauth Hfrag") as "[Hauth Hfrag]".
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
	{ eauto. }
	iIntros (w) "HQ".
	iApply ("HΦ" $! w).
	unfold Q.
	done.
Qed.

End proofs.