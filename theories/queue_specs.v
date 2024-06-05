From iris.algebra Require Import list agree lib.frac_auth.
From iris.heap_lang Require Import lang proofmode notation.
From MSQueue Require Import MSQ_common.
From iris.base_logic.lib Require Import invariants.


(* ===== Defining the RA for the Abstract State of the Queue ===== *)
Section queue_contents.

Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

(* ------ Abstract State of Queue ------ *)
Notation "γ ⤇● xs_v" := (own γ (●F (to_agree xs_v)))
  (at level 20, format "γ  ⤇●  xs_v") : bi_scope.
Notation "γ ⤇◯ xs_v" := (own γ (◯F (to_agree xs_v)))
  (at level 20, format "γ  ⤇◯  xs_v") : bi_scope.
Notation "γ ⤇[ q ] xs_v" := (own γ (◯F{ q } (to_agree xs_v)))
  (at level 20, format "γ  ⤇[ q ]  xs_v") : bi_scope.

Lemma queue_contents_alloc xs_v:
  ⊢ |==> ∃ γ, (γ ⤇● xs_v ∗ γ ⤇◯ xs_v).
Proof.
  iStartProof.
  iMod (own_alloc (●F (to_agree xs_v) ⋅ ◯F (to_agree xs_v))) as (γ) "[Hγ_auth Hγ_frac]"; first by apply frac_auth_valid.
  iModIntro.
  iExists γ.
  iFrame.
Qed.

Lemma queue_contents_frag_agree γ xs_v xs_v' p q :
  γ ⤇[p] xs_v -∗ γ ⤇[q] xs_v' -∗ ⌜xs_v = xs_v'⌝.
Proof.
  iIntros "Hp Hq".
  iCombine "Hp Hq" as "Hpq" gives "%HValid".
  iPureIntro.
  rewrite <- frac_auth_frag_op in HValid.
  rewrite frac_auth_frag_valid in HValid.
  destruct HValid as [_ HAgree].
  by apply to_agree_op_inv_L.
Qed.

Lemma queue_contents_auth_frag_agree γ xs_v xs_v' p :
  γ ⤇● xs_v' -∗ γ ⤇[p] xs_v -∗ ⌜xs_v = xs_v'⌝.
Proof.
  iIntros "Hp Hq".
  iCombine "Hp Hq" as "Hpq" gives "%HValid".
  iPureIntro.
  apply frac_auth_included_total in HValid.
  by apply to_agree_included_L.
Qed.

Lemma queue_contents_op γ xs_v p q :
  γ ⤇[p] xs_v ∗ γ ⤇[q] xs_v ∗-∗ γ ⤇[p + q] xs_v.
Proof.
  iSplit.
  - iIntros "[Hp Hq]".
    by iCombine "Hp Hq" as "Hpq".
  - iIntros "Hpq".
    iApply own_op.
    rewrite <- frac_auth_frag_op.
    by rewrite agree_idemp.
Qed.

Lemma queue_contents_update γ xs_v xs_v' xs_v'' :
  γ ⤇● xs_v' -∗ γ ⤇◯ xs_v ==∗ γ ⤇● xs_v'' ∗ γ ⤇◯ xs_v''.
Proof.
  iIntros "Hauth Hfrag".
  iCombine "Hauth Hfrag" as "Hcombined".
  rewrite <- own_op.
  iApply (own_update with "Hcombined").
  by apply frac_auth_update_1.
Qed.

End queue_contents.

Notation "γ ⤇● xs_v" := (own γ (●F (to_agree xs_v)))
  (at level 20, format "γ  ⤇●  xs_v") : bi_scope.
Notation "γ ⤇◯ xs_v" := (own γ (◯F (to_agree xs_v)))
  (at level 20, format "γ  ⤇◯  xs_v") : bi_scope.
Notation "γ ⤇[ q ] xs_v" := (own γ (◯F{ q } (to_agree xs_v)))
  (at level 20, format "γ  ⤇[ q ]  xs_v") : bi_scope.


(* ===== HOCAP-Style Queue Specification ===== *)
Class queue := Queue {
  initialize : val;
  enqueue : val;
  dequeue : val;

  (* The Resource Algebras used by the queue *)
  queueG : gFunctors → Type;

  (* The ghost names used by the queue *)
  Qgnames : Type;
  (* It must contain a ghost name for the abstract state *)
  γ_Abst : Qgnames → gname;

  N : namespace;
  Ni := (N .@ "internal");

  (* The isQueue predicate *)
  isQueue `{!heapGS Σ} {L : queueG Σ} `{!inG Σ (frac_authR (agreeR (listO val)))} (v_q : val) (G: Qgnames) : iProp Σ;

  (* isQueue must be persistent *)
  #[global] isQueue_persistent `{!heapGS Σ} {L : queueG Σ} `{!inG Σ (frac_authR (agreeR (listO val)))} v_q G :: Persistent (isQueue (L:=L) v_q G);

  (* HOCAP-Style Initialise Specifictaion *)
  initialize_spec `{!heapGS Σ} {L : queueG Σ} `{!inG Σ (frac_authR (agreeR (listO val)))} :
  {{{ True }}}
    initialize #()
  {{{ v_q G, RET v_q; isQueue (L:=L) v_q G ∗ G.(γ_Abst) ⤇◯ [] }}};

  (* HOCAP-Style Enqueue Specifictaion *)
  enqueue_spec `{!heapGS Σ} {L : queueG Σ} `{!inG Σ (frac_authR (agreeR (listO val)))} (v_q v : val) (G : Qgnames) (P Q : iProp Σ) :
  □(∀xs_v, (G.(γ_Abst) ⤇● xs_v ∗ P ={⊤ ∖ ↑Ni}=∗ ▷ (G.(γ_Abst) ⤇● (v :: xs_v) ∗ Q))) -∗
  {{{ isQueue (L:=L) v_q G ∗ P}}}
    enqueue v_q v
  {{{ w, RET w; Q }}};

  (* HOCAP-Style Dequeue Specifictaion *)
  dequeue_spec `{!heapGS Σ} {L : queueG Σ} `{!inG Σ (frac_authR (agreeR (listO val)))} (v_q : val) (G : Qgnames) (P : iProp Σ) (Q : val -> iProp Σ):
  □(∀xs_v, (G.(γ_Abst) ⤇● xs_v ∗ P
              ={⊤ ∖ ↑Ni}=∗
              ▷ (( ⌜xs_v = []⌝ ∗ G.(γ_Abst) ⤇● xs_v ∗ Q NONEV) ∨
              (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗ G.(γ_Abst) ⤇● xs_v' ∗ Q (SOMEV v)))
            )
   )
  -∗
  {{{ isQueue (L:=L) v_q G ∗ P }}}
    dequeue v_q
  {{{ w, RET w; Q w }}}
}.

Existing Class queueG.

(* ===== Sequential Specification for Queue ===== *)
Section sequential_proofs.

Context `{!queue}.
Context `{!queueG Σ}.
Context `{!heapGS Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Definition isQueue_seq (v_q : val) (xs_v: list val) (G: Qgnames) : iProp Σ :=
  isQueue v_q G ∗
  γ_Abst G ⤇◯ xs_v.

Lemma initialize_spec_seq :
  {{{ True }}}
    initialize #()
  {{{ v_q G, RET v_q; isQueue_seq v_q [] G }}}.
Proof.
  iIntros (Φ _) "HΦ".
  wp_apply (initialize_spec); first done.
  done.
Qed.

Lemma enqueue_spec_seq v_q (v : val) (xs_v : list val) (G : Qgnames) :
  {{{ isQueue_seq v_q xs_v G }}}
    enqueue v_q v
  {{{w, RET w; isQueue_seq v_q (v :: xs_v) G }}}.
Proof.
  iIntros (Φ) "(#HisQueue & Hfrag) HΦ".
  set (P := ((γ_Abst G) ⤇◯ xs_v)%I).
  set (Q := ((γ_Abst G) ⤇◯ (v :: xs_v))%I).
  wp_apply (enqueue_spec v_q v G P Q with "[] [Hfrag]").
  (* Proving view-shift *)
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
  {{{ isQueue_seq v_q xs_v G }}}
    dequeue v_q
  {{{ w, RET w; (⌜xs_v = []⌝ ∗ ⌜w = NONEV⌝ ∗ isQueue_seq v_q xs_v G) ∨
                (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗
                    ⌜w = SOMEV v⌝ ∗ isQueue_seq v_q xs_v' G) }}}.
Proof.
  iIntros (Φ) "(#HisQueue & Hfrag) HΦ".
  set (P := ((γ_Abst G) ⤇◯ xs_v)%I).
  set (Q := λ w, ((⌜xs_v = []⌝ ∗ ⌜w = NONEV⌝ ∗ (γ_Abst G) ⤇◯ xs_v) ∨
                  (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗
                    ⌜w = SOMEV v⌝ ∗ (γ_Abst G) ⤇◯ xs_v'))%I).
  wp_apply (dequeue_spec v_q G P Q with "[] [Hfrag]" ).
  (* Proving view-shift *)
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



(* ===== Concurrent Specification for Queue ===== *)
Section concurrent_proofs.

Notation NC := (N .@ "concurrent").

Context `{!queue}.
Context `{!queueG Σ}.
Context `{!heapGS Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Definition isQueue_C (Ψ : val -> iProp Σ) (v_q : val) (G: Qgnames) : iProp Σ :=
  isQueue v_q G ∗
  inv NC (∃xs_v, (γ_Abst G) ⤇◯ xs_v ∗ All xs_v Ψ).

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
  wp_apply (initialize_spec); first done.
  iIntros (v_q G) "[HisQueue Habst_frag]".
  iApply ("HΦ" $! v_q G).
  iMod (inv_alloc NC _ (∃xs_v, (γ_Abst G) ⤇◯ xs_v ∗ All xs_v Ψ) with "[Habst_frag]") as "HInv"; first (iExists []; auto).
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
  wp_apply (enqueue_spec v_q v G P Q with "[] [HΨ]").
  (* Proving view-shift *)
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
  wp_apply (dequeue_spec v_q G P Q).
  (* Proving view-shift *)
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
