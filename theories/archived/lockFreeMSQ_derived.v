From stdpp Require Import sets countable.
From iris.algebra Require Import list agree gset lib.frac_auth.
From iris.bi Require Import fixpoint big_op.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation primitive_laws.
From iris.base_logic.lib Require Import invariants.
From MSQueue Require Import MSQ_common.
From MSQueue Require Import queue_specs.
From MSQueue Require Import lockFreeMSQ_impl.
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

Definition isQueue_S (v_q : val) (xs_v: list val) (G: Qgnames) : iProp Σ :=
  isQueue N v_q G ∗
  G.(γ_Abst) ⤇◯ xs_v.

Lemma initialize_spec_seq :
  {{{ True }}}
    initialize #()
  {{{ v_q G, RET v_q; isQueue_S v_q [] G }}}.
Proof.
  iIntros (Φ _) "HΦ".
  wp_apply (initialize_spec N); first done.
  iIntros (v_q G) "[HisQueue Habst_frag]".
  iApply ("HΦ" $! v_q G).
  by iFrame.
Qed.

Lemma enqueue_spec_seq v_q (v : val) (xs_v : list val) (G : Qgnames) :
  {{{ isQueue_S v_q xs_v G }}}
    enqueue v_q v
  {{{w, RET w; isQueue_S v_q (v :: xs_v) G }}}.
Proof.
  iIntros (Φ) "(#HisQueue & Hfrag) HΦ".
  set (P := (G.(γ_Abst) ⤇◯ xs_v)%I).
  set (Q := (G.(γ_Abst) ⤇◯ (v :: xs_v))%I).
  wp_apply (enqueue_spec N v_q v G P Q with "[] [Hfrag]").
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

Lemma dequeue_spec_seq v_q (xs_v : list val) (G : Qgnames) :
  {{{ isQueue_S v_q xs_v G }}}
    dequeue v_q
  {{{ w, RET w; (⌜xs_v = []⌝ ∗ ⌜w = NONEV⌝ ∗ isQueue_S v_q xs_v G) ∨
                (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗
                    ⌜w = SOMEV v⌝ ∗ isQueue_S v_q xs_v' G) }}}.
Proof.
  iIntros (Φ) "(#HisQueue & Hfrag) HΦ".
  set (P := (G.(γ_Abst) ⤇◯ xs_v)%I).
  set (Q := λ w, ((⌜xs_v = []⌝ ∗ ⌜w = NONEV⌝ ∗ G.(γ_Abst) ⤇◯ xs_v) ∨
                  (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗
                    ⌜w = SOMEV v⌝ ∗ G.(γ_Abst) ⤇◯ xs_v'))%I).
  wp_apply (dequeue_spec N v_q G P Q with "[] [Hfrag]" ).
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
    by repeat iSplit.
  - iRight.
    iExists v, xs_v'.
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

Definition isQueue_C (Ψ : val -> iProp Σ) (v_q : val) (G: Qgnames) : iProp Σ :=
  isQueue N v_q G ∗
  inv NC (∃xs_v, G.(γ_Abst) ⤇◯ xs_v ∗ All xs_v Ψ).

(* isQueue_C is persistent *)
Global Instance isQueue_C_persistent Ψ v_q G : Persistent (isQueue_C Ψ v_q G).
Proof. apply _. Qed.

Lemma initialize_spec_conc (Ψ : val -> iProp Σ):
  {{{ True }}}
    initialize #()
  {{{ v_q G, RET v_q; isQueue_C Ψ v_q G }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iApply wp_fupd.
  wp_apply (initialize_spec N); first done.
  iIntros (v_q G) "[HisQueue Habst_frag]".
  iApply ("HΦ" $! v_q G).
  iMod (inv_alloc NC _ (∃xs_v, G.(γ_Abst) ⤇◯ xs_v ∗ All xs_v Ψ) with "[Habst_frag]") as "HInv"; first (iExists []; auto).
  by iFrame.
Qed.

Lemma enqueue_spec_conc v_q Ψ (v : val) (G : Qgnames) :
  {{{ isQueue_C Ψ v_q G ∗ Ψ v }}}
    enqueue v_q v
  {{{ w, RET w; True }}}.
Proof.
  iIntros (Φ) "[(#HisQueue & #HInv) HΨ] HΦ".
  set (P := Ψ v).
  set (Q := True%I).
  wp_apply (enqueue_spec N v_q v G P Q with "[] [HΨ]").
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

Lemma dequeue_spec_conc v_q Ψ (G : Qgnames) :
  {{{ isQueue_C Ψ v_q G }}}
    dequeue v_q
  {{{ w, RET w; ⌜w = NONEV⌝ ∨ (∃ v, ⌜w = SOMEV v⌝ ∗ Ψ v) }}}.
Proof.
  iIntros (Φ) "(#HisQueue & #HInv) HΦ".
  set (P := True%I : iProp Σ).
  set (Q := λ w, (⌜w = NONEV⌝ ∨ (∃v, ⌜w = SOMEV v⌝ ∗ Ψ v))%I).
  wp_apply (dequeue_spec N v_q G P Q).
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
