From iris.algebra Require Import list agree lib.frac_auth.
From iris.heap_lang Require Import lang proofmode notation.


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


(* ===== Hocap-Style Queue Specification ===== *)
Class queue := Queue {
  initialize : val;
  enqueue : val;
  dequeue : val;

  (* The Resource Algebra used by the queue *)
  queueG : gFunctors → Type;

  (* The ghost names used by the queue *)
  Qgnames : Type;
  (* It must contain a ghost name for the abstract state *)
  γ_Abst : Qgnames → gname;

  N : namespace;
  Ni := (N .@ "internal");

  (* The is_queue predicate *)
  is_queue `{!heapGS Σ} {L : queueG Σ} `{!inG Σ (frac_authR (agreeR (listO val)))} (v_q : val) (Q_γ: Qgnames) : iProp Σ;

  (* is_queue must be persistent *)
  #[global] is_queue_persistent `{!heapGS Σ} {L : queueG Σ} `{!inG Σ (frac_authR (agreeR (listO val)))} v_q Q_γ :: Persistent (is_queue (L:=L) v_q Q_γ);

  (* Hocap-Style Initialise Specifictaion *)
  initialize_spec `{!heapGS Σ} {L : queueG Σ} `{!inG Σ (frac_authR (agreeR (listO val)))} :
  {{{ True }}}
    initialize #()
  {{{ v_q Q_γ, RET v_q; is_queue (L:=L) v_q Q_γ ∗ Q_γ.(γ_Abst) ⤇◯ [] }}};

  (* Hocap-Style Enqueue Specifictaion *)
  enqueue_spec `{!heapGS Σ} {L : queueG Σ} `{!inG Σ (frac_authR (agreeR (listO val)))} v_q (v : val) (Q_γ : Qgnames) (P Q : iProp Σ) :
  □(∀xs_v, (Q_γ.(γ_Abst) ⤇● xs_v ∗ P ={⊤ ∖ ↑Ni}=∗ ▷ (Q_γ.(γ_Abst) ⤇● (v :: xs_v) ∗ Q))) -∗
  {{{ is_queue (L:=L) v_q Q_γ ∗ P}}}
    enqueue v_q v
  {{{ w, RET w; Q }}};

  (* Hocap-Style Dequeue Specifictaion *)
  dequeue_spec `{!heapGS Σ} {L : queueG Σ} `{!inG Σ (frac_authR (agreeR (listO val)))} v_q (Q_γ : Qgnames) (P : iProp Σ) (Q : val -> iProp Σ):
  □(∀xs_v, (Q_γ.(γ_Abst) ⤇● xs_v ∗ P
              ={⊤ ∖ ↑Ni}=∗
              ▷ (( ⌜xs_v = []⌝ ∗ Q_γ.(γ_Abst) ⤇● xs_v ∗ Q NONEV) ∨
              (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗ Q_γ.(γ_Abst) ⤇● xs_v' ∗ Q (SOMEV v)))
            )
   )
  -∗
  {{{ is_queue (L:=L) v_q Q_γ ∗ P }}}
    dequeue v_q
  {{{ w, RET w; Q w }}}
}.


(* ===== Sequential Specification for Queue ===== *)
Section sequential_proofs.

(* Variable N : namespace.

Definition is_queue_seq (v_q : val) (xs_v: list val) (Q_γH: Qgnames) : iProp Σ :=
  is_queue N v_q Q_γH ∗
  Q_γH.(γ_Abst) ⤇◯ xs_v.

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
  set (P := (Q_γH.(γ_Abst) ⤇◯ xs_v)%I).
  set (Q := (Q_γH.(γ_Abst) ⤇◯ (v :: xs_v))%I).
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
  {{{ w, RET w; (⌜xs_v = []⌝ ∗ ⌜w = NONEV⌝ ∗ is_queue_seq v_q xs_v Q_γH) ∨
                (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗
                    ⌜w = SOMEV v⌝ ∗ is_queue_seq v_q xs_v' Q_γH) }}}.
Proof.
  iIntros (Φ) "(#His_queue & Hfrag) HΦ".
  set (P := (Q_γH.(γ_Abst) ⤇◯ xs_v)%I).
  set (Q := λ w, ((⌜xs_v = []⌝ ∗ ⌜w = NONEV⌝ ∗ Q_γH.(γ_Abst) ⤇◯ xs_v) ∨
                  (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗
                    ⌜w = SOMEV v⌝ ∗ Q_γH.(γ_Abst) ⤇◯ xs_v'))%I).
  wp_apply (dequeue_spec N v_q Q_γH P Q with "[] [Hfrag]" ).
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
Qed. *)

End sequential_proofs.



(* ===== Concurrent Specification for Queue ===== *)
Section concurrent_proofs.

(* Notation NC := (N .@ "concurrent").

Definition is_queue_conc (Ψ : val -> iProp Σ) (v_q : val) (Q_γH: Qgnames) : iProp Σ :=
  is_queue N v_q Q_γH ∗
  inv NC (∃xs_v, Q_γH.(γ_Abst) ⤇◯ xs_v ∗ All xs_v Ψ).

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
  iMod (inv_alloc NC _ (∃xs_v, Q_γH.(γ_Abst) ⤇◯ xs_v ∗ All xs_v Ψ) with "[Habst_frag]") as "HInv"; first (iExists []; auto).
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
  {{{ w, RET w; ⌜w = NONEV⌝ ∨ (∃ v, ⌜w = SOMEV v⌝ ∗ Ψ v) }}}.
Proof.
  iIntros (Φ) "(#His_queue & #HInv) HΦ".
  set (P := True%I : iProp Σ).
  set (Q := λ w, (⌜w = NONEV⌝ ∨ (∃v, ⌜w = SOMEV v⌝ ∗ Ψ v))%I).
  wp_apply (dequeue_spec N v_q Q_γH P Q).
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
Qed. *)

End concurrent_proofs.
