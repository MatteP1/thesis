From stdpp Require Import countable.
From iris.algebra Require Import excl list agree lib.frac_auth.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants token.
From MSQueue Require Import MSQ_common.
From MSQueue Require Import queue_specs.
From MSQueue Require Import twoLockMSQ_impl.
From MSQueue Require Import twoLockMSQ_hocap_spec.

Local Existing Instance spin_lock.

Section sequential_proofs.

Context `{!heapGS Σ}.
Context `{!queueG Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Variable N : namespace.

(* ===== Sequential Specification for Two-lock M&S Queue ===== *)

Record SeqQgnames := { γ_Hlock_seq : gname;
                       γ_Tlock_seq : gname;
                     }.

Definition projQgnames_S (G_H : Qgnames) : SeqQgnames :=
  {| γ_Hlock_seq := G_H.(γ_Hlock);
     γ_Tlock_seq := G_H.(γ_Tlock);
  |}.

Definition isQueue_S (v_q : val) (xs_v: list val) (G_S: SeqQgnames) : iProp Σ :=
  ∃ G_H : Qgnames,
  ⌜projQgnames_S G_H = G_S⌝ ∗
  isQueue N v_q G_H ∗
  G_H.(γ_Abst) ⤇◯ xs_v.

Lemma initialize_spec_seq :
  {{{ True }}}
    initialize #()
  {{{ v_q G_S, RET v_q; isQueue_S v_q [] G_S }}}.
Proof.
  iIntros (Φ _) "HΦ".
  wp_apply (initialize_spec N); first done.
  iIntros (v_q G_H) "[HisQueue Habst_frag]".
  set (G_S := projQgnames_S G_H).
  iApply ("HΦ" $! v_q G_S).
  iExists G_H.
  by iFrame.
Qed.

Lemma enqueue_spec_seq v_q (v : val) (xs_v : list val) (G_S : SeqQgnames) :
  {{{ isQueue_S v_q xs_v G_S }}}
    enqueue v_q v
  {{{w, RET w; isQueue_S v_q (v :: xs_v) G_S }}}.
Proof.
  iIntros (Φ) "(%G_H & %Heq & #HisQueue & Hfrag) HΦ".
  set (P := (G_H.(γ_Abst) ⤇◯ xs_v)%I).
  set (Q := (G_H.(γ_Abst) ⤇◯ (v :: xs_v))%I).
  wp_apply (enqueue_spec N v_q v G_H P Q with "[] [Hfrag]").
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
  iExists G_H.
  by repeat iSplit.
Qed.

Lemma dequeue_spec_seq v_q (xs_v : list val) (G_S : SeqQgnames) :
  {{{ isQueue_S v_q xs_v G_S }}}
    dequeue v_q
  {{{ w, RET w; (⌜xs_v = []⌝ ∗ ⌜w = NONEV⌝ ∗ isQueue_S v_q xs_v G_S) ∨
                (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗
                    ⌜w = SOMEV v⌝ ∗ isQueue_S v_q xs_v' G_S) }}}.
Proof.
  iIntros (Φ) "(%G_H & %Heq & #HisQueue & Hfrag) HΦ".
  set (P := (G_H.(γ_Abst) ⤇◯ xs_v)%I).
  set (Q := λ w, ((⌜xs_v = []⌝ ∗ ⌜w = NONEV⌝ ∗ G_H.(γ_Abst) ⤇◯ xs_v) ∨
                  (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗
                    ⌜w = SOMEV v⌝ ∗ G_H.(γ_Abst) ⤇◯ xs_v'))%I).
  wp_apply (dequeue_spec N v_q G_H P Q with "[] [Hfrag]" ).
  (* Proving viewshift *)
  {
    iIntros (xs_v') "!>".
    iIntros "[Hauth Hfrag]".
    iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by iApply (queue_contents_auth_frag_agree _ xs_v xs_v' 1 with "Hauth Hfrag").
    destruct (ll_case_first xs_v) as [->|[v [xs_v' ->]]].
    - iLeft.
      iModIntro.
      iSplit; first done.
      iFrame.
      unfold P, Q.
      iLeft.
      by repeat iSplit.
    - iMod (queue_contents_update _ _ _ (xs_v') with "Hauth Hfrag") as "[Hauth Hfrag]".
      iRight.
      iExists v, xs_v'.
      iModIntro.
      iSplit; first done.
      iFrame.
      iRight.
      iExists v, xs_v'.
      by repeat iSplit.
  }
  (* Proving pre-condition of hocap enqueue spec *)
  { by iFrame. }
  iIntros (w) "HQ".
  iApply ("HΦ" $! w).
  unfold Q.
  iDestruct "HQ" as "[(-> & %Hres & Hfrag) | (%v & %xs_v' & %Hxs_v_eq & %Hres & Hfrag)]".
  - iLeft.
    repeat iSplit; try done.
    iExists G_H.
    by repeat iSplit.
  - iRight.
    iExists v, xs_v'.
    repeat iSplit; try done.
    iExists G_H.
    by repeat iSplit.
Qed.

End sequential_proofs.


Section concurrent_proofs.

Context `{!heapGS Σ}.
Context `{!queueG Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Variable N : namespace.
Notation NC := (N .@ "concurrent").

(* ===== Concurrent Specification for Two-lock M&S Queue ===== *)

(* Ghost variable names *)
Record ConcQgnames := { γ_Hlock_conc  : gname;
                        γ_Tlock_conc  : gname;
                        γ_E_conc      : gname;
                        γ_nE_conc     : gname;
                        γ_D_conc      : gname;
                        γ_nD_conc     : gname;
                        γ_Before_conc : gname;
                        γ_After_conc  : gname;
                      }.

Definition projQgnames_C (G_H : Qgnames) : ConcQgnames :=
  {| γ_Hlock_conc := G_H.(γ_Hlock);
     γ_Tlock_conc := G_H.(γ_Tlock);
     γ_E_conc := G_H.(γ_E);
     γ_nE_conc := G_H.(γ_nE);
     γ_D_conc := G_H.(γ_D);
     γ_nD_conc := G_H.(γ_nD);
     γ_Before_conc := G_H.(γ_Before);
     γ_After_conc := G_H.(γ_After)
  |}.

Definition isQueue_C (Ψ : val -> iProp Σ) (v_q : val) (G_C: ConcQgnames) : iProp Σ :=
  ∃ G_H : Qgnames,
  ⌜projQgnames_C G_H = G_C⌝ ∗
  isQueue N v_q G_H ∗
  inv NC (∃xs_v, G_H.(γ_Abst) ⤇◯ xs_v ∗ All xs_v Ψ).

(* isQueue_C is persistent *)
Global Instance isQueue_C_persistent Ψ v_q G_C : Persistent (isQueue_C Ψ v_q G_C).
Proof. apply _. Qed.

Lemma initialize_spec_conc (Ψ : val -> iProp Σ):
  {{{ True }}}
    initialize #()
  {{{ v_q G_C, RET v_q; isQueue_C Ψ v_q G_C }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iApply wp_fupd.
  wp_apply (initialize_spec N); first done.
  iIntros (v_q G_H) "[HisQueue Habst_frag]".
  set (G_C := projQgnames_C G_H).
  iApply ("HΦ" $! v_q G_C).
  iExists G_H.
  iMod (inv_alloc NC _ (∃xs_v, G_H.(γ_Abst) ⤇◯ xs_v ∗ All xs_v Ψ) with "[Habst_frag]") as "HInv"; first (iExists []; auto).
  by iFrame.
Qed.

Lemma enqueue_spec_conc v_q Ψ (v : val) (G_C : ConcQgnames) :
  {{{ isQueue_C Ψ v_q G_C ∗ Ψ v }}}
    enqueue v_q v
  {{{ w, RET w; True }}}.
Proof.
  iIntros (Φ) "[(%G_H & %Heq & #HisQueue & #HInv) HΨ] HΦ".
  set (P := Ψ v).
  set (Q := True%I).
  wp_apply (enqueue_spec N v_q v G_H P Q with "[] [HΨ]").
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

Lemma dequeue_spec_conc v_q Ψ (G_C : ConcQgnames) :
  {{{ isQueue_C Ψ v_q G_C }}}
    dequeue v_q
  {{{ w, RET w; ⌜w = NONEV⌝ ∨ (∃ v, ⌜w = SOMEV v⌝ ∗ Ψ v) }}}.
Proof.
  iIntros (Φ) "(%G_H & %Heq & #HisQueue & #HInv) HΦ".
  set (P := True%I : iProp Σ).
  set (Q := λ w, (⌜w = NONEV⌝ ∨ (∃v, ⌜w = SOMEV v⌝ ∗ Ψ v))%I).
  wp_apply (dequeue_spec N v_q G_H P Q).
  (* Proving viewshift *)
  {
    iIntros (xs_v') "!>".
    iIntros "[Hauth _]".
    iInv "HInv" as "(%xs_v & >Hfrag & HAll)".
    iAssert (⌜xs_v = xs_v'⌝)%I with "[Hauth Hfrag]" as "<-"; first by iApply (queue_contents_auth_frag_agree _ xs_v xs_v' 1 with "Hauth Hfrag").
    destruct (ll_case_first xs_v) as [->|[v [xs_v' ->]]].
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
      iExists v, xs_v'.
      iSplit; first done.
      iFrame.
      unfold Q.
      iRight.
      iExists v.
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
