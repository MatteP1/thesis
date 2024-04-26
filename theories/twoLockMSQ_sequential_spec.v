From stdpp Require Import countable.
From iris.algebra Require Import excl.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants.
From MSQueue Require Import twoLockMSQ_impl.
From MSQueue Require Import MSQ_common.

Local Existing Instance spin_lock.

Section proofs.

Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!inG Σ (exclR unitO)}.

Notation N := (nroot .@ "twoLockMSQ_seq").

(* ===== Sequential Specification for Two-lock M&S Queue ===== *)

(* ----- Ghost variable names ----- *)
Record SeqQgnames := { γ_Hlock 	: gname;
                       γ_Tlock	: gname;
                     }.

(* ----- The 'is_queue' Predicate for Sequential Spec ------ *)
Definition is_queue_seq (v_q : val) (xs_v: list val) (Q_γ: SeqQgnames) : iProp Σ :=
  ∃ l_queue l_head l_tail : loc, ∃ h_lock t_lock : val,
  ⌜v_q = #l_queue⌝ ∗
  l_queue ↦□ ((#l_head, #l_tail), (h_lock, t_lock)) ∗
  ∃ (xs_queue : list node), ∃x_head x_tail : node,
  ⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
  isLL (xs_queue ++ [x_head]) ∗
  l_head ↦ #(n_in x_head) ∗
  l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail (xs_queue ++ [x_head])⌝ ∗
  is_lock Q_γ.(γ_Hlock) h_lock (True) ∗
  is_lock Q_γ.(γ_Tlock) t_lock (True).


(* ----- Specification for Initialise ----- *)
Lemma initialize_spec_seq :
  {{{ True }}}
    initialize #()
  {{{ v_q Q_γ, RET v_q; is_queue_seq v_q [] Q_γ }}}.
Proof.
  iIntros (Φ _) "HΦ".
  wp_lam.
  wp_alloc l_1_out as "Hx1_to_none".
  wp_alloc l_1_in as "Hx1_node".
  wp_pures.
  set x_1 := (l_1_in, NONEV, l_1_out).
  change l_1_in with (n_in x_1).
  change l_1_out with (n_out x_1).
  pose proof (eq_refl : NONEV = n_val x_1) as Hx1_val.
  rewrite {2}Hx1_val.
  clearbody x_1.
  iMod (pointsto_persist with "Hx1_node") as "#Hx1_node".
  wp_apply (newlock_spec True); first done.
  iIntros (h_lock γ_Hlock) "Hγ_Hlock".
  wp_let.
  wp_apply (newlock_spec True); first done.
  iIntros (t_lock γ_Tlock) "Hγ_Tlock".
  set (Queue_gnames := {| γ_Hlock := γ_Hlock;
                          γ_Tlock := γ_Tlock;
                       |}).
  wp_let.
  wp_alloc l_tail as "Hl_tail".
  wp_alloc l_head as "Hl_head".
  wp_alloc l_queue as "Hl_queue".
  iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
  iApply ("HΦ" $! #l_queue Queue_gnames).
  iModIntro.
  iExists l_queue, l_head, l_tail, h_lock, t_lock.
  repeat iSplit; try done.
  iExists [], x_1, x_1.
  iFrame.
  repeat iSplit; try done.
  by iExists [].
Qed.

(* ----- Specification for Enqueue ----- *)
Lemma enqueue_spec_seq v_q (v : val) (xs_v : list val) (Q_γ : SeqQgnames) :
  {{{ is_queue_seq v_q xs_v Q_γ }}}
    enqueue v_q v
  {{{w, RET w; is_queue_seq v_q (v :: xs_v) Q_γ }}}.
Proof.
  iIntros (Φ) "(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> & #Hl_queue & %xs_queue & %x_head & %x_tail & %Hconc_abst_eq & HisLL_xs & Hl_head & Hl_tail & %HisLast_xtail & #Hh_lock & #Ht_lock) HΦ".
  destruct HisLast_xtail as [xs_rest Hxs_eq].
  rewrite Hxs_eq.
  iDestruct "HisLL_xs" as "[Hxtail_to_none #HisLL_chain_xs]".
  wp_lam.
  wp_let.
  wp_pures.
  wp_alloc l_new_out as "Hxnew_to_none".
  wp_alloc l_new_in as "Hxnew_node".
  set x_new := (l_new_in, SOMEV v, l_new_out).
  change l_new_in with (n_in x_new).
  change l_new_out with (n_out x_new).
  change (SOMEV v) with (n_val x_new).
  pose proof (eq_refl : SOMEV v = n_val x_new) as Hxnew_val.
  clearbody x_new.
  iMod (pointsto_persist with "Hxnew_node") as "#Hxnew_node".
  wp_let.
  wp_load.
  wp_pures.
  wp_apply (acquire_spec with "Ht_lock").
  iIntros "(Hlocked_γ_Tlock & _)".
  wp_seq.
  wp_load.
  wp_pures.
  wp_load.
  iPoseProof (isLL_chain_node [] x_tail xs_rest with "[HisLL_chain_xs]") as "Hxtail_node"; first done.
  wp_load.
  wp_pures.
  wp_store.
  iMod (pointsto_persist with "Hxtail_to_none") as "#Hxtail_to_xnew".
  wp_load.
  wp_pures.
  wp_store.
  wp_load.
  wp_pures.
  wp_apply (release_spec with "[$Ht_lock $Hlocked_γ_Tlock]").
  iIntros (_).
  iApply ("HΦ" $! #()).
  iExists l_queue, l_head, l_tail, h_lock, t_lock.
  do 2 (iSplit; first done).
  iExists (x_new :: xs_queue), x_head, x_new.
  iFrame.
  repeat iSplit; try done.
  - iPureIntro. simpl. f_equal; done.
  - iSimpl; rewrite Hxs_eq. by repeat iSplit.
  - by iExists (xs_queue ++ [x_head]).
Qed.

(* ----- Specification for Dequeue ----- *)
Lemma dequeue_spec_seq v_q (xs_v : list val) (Q_γ : SeqQgnames) :
  {{{ is_queue_seq v_q xs_v Q_γ }}}
    dequeue v_q
  {{{ v, RET v; (⌜xs_v = []⌝ ∗ ⌜v = NONEV⌝ ∗ is_queue_seq v_q xs_v Q_γ) ∨
                (∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗
                    ⌜v = SOMEV x_v⌝ ∗ is_queue_seq v_q xs_v' Q_γ) }}}.
Proof.
  iIntros (Φ) "(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> & #Hl_queue & %xs_queue & %x_head & %x_tail & %Hconc_abst_eq & HisLL_xs & Hl_head & Hl_tail & %HisLast_xtail & #Hh_lock & #Ht_lock) HΦ".
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  wp_lam.
  wp_load.
  wp_pures.
  wp_apply (acquire_spec with "Hh_lock").
  iIntros "(Hlocked_γ_Hlock & _)".
  wp_seq.
  wp_load.
  wp_pures.
  wp_load.
  wp_let.
  iPoseProof (isLL_chain_node xs_queue x_head [] with "[HisLL_chain_xs]") as "Hxhead_node"; first done.
  wp_load.
  wp_pures.
  (* CASE ANALYSIS: Is queue empty? *)
  destruct (ll_case_first xs_queue) as [->|[x_head_next [xs_queue' ->]]].
  - (* Queue is empty *)
    iDestruct "HisLL_xs" as "[Hxhead_to_none _]".
    wp_load.
    wp_let.
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply (release_spec with "[$Hh_lock $Hlocked_γ_Hlock]").
    iIntros (_).
    wp_seq.
    iModIntro.
    iApply ("HΦ" $! NONEV).
    iLeft.
    destruct xs_v; last inversion Hconc_abst_eq.
    do 2 (iSplit; first done).
    iExists l_queue, l_head, l_tail, h_lock, t_lock.
    do 2 (iSplit; first done).
    iExists [], x_head, x_tail.
    iFrame.
    repeat iSplit; done.
  - (* Queue is not empty *)
    iPoseProof (isLL_chain_split xs_queue' [x_head_next; x_head] with "[HisLL_chain_xs]") as "[_ HisLL_chain_xheadnext]"; first by rewrite <- app_assoc.
    iDestruct "HisLL_chain_xheadnext" as "(Hxheadnext_node & Hxhead_to_xheadnext & _)".
    wp_load.
    wp_let.
    wp_pures.
    wp_load.
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    wp_load.
    wp_pures.
    wp_apply (release_spec with "[$Hh_lock $Hlocked_γ_Hlock]").
    iIntros (_).
    wp_seq.
    iModIntro.
    iApply ("HΦ" $! (n_val x_head_next)).
    iRight.
    destruct (ll_case_first xs_v) as [->|[x_head_next_val [xs_val_rest ->]]].
    {
      rewrite proj_val_split in Hconc_abst_eq.
      exfalso.
      by apply (app_cons_not_nil (proj_val xs_queue') [] (n_val x_head_next)).
    }
    iExists x_head_next_val, xs_val_rest.
    rewrite proj_val_split wrap_some_split /= in Hconc_abst_eq.
    apply list_last_eq in Hconc_abst_eq as [Hconc_abst_eq Hxheadnext_val_eq].
    repeat (iSplit; try done).
    iExists l_queue, l_head, l_tail, h_lock, t_lock.
    do 2 (iSplit; first done).
    iExists xs_queue', x_head_next, x_tail.
    iDestruct (isLL_split with "HisLL_xs") as "[HisLL_new _]".
    iFrame.
    rewrite <- app_assoc in HisLast_xtail.
    apply isLast_remove in HisLast_xtail.
    repeat (iSplit; try done).
Qed.

End proofs.