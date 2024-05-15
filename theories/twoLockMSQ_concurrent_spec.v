From stdpp Require Import countable.
From iris.algebra Require Import excl.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants token.
From MSQueue Require Import MSQ_common.
From MSQueue Require Import twoLockMSQ_impl.

Local Existing Instance spin_lock.

Class queueG Σ := {
  queueGlock :: lockG Σ;
  queueGtoken :: tokenG Σ
}.

Section proofs.

Context `{!heapGS Σ}.
Context `{!queueG Σ}.
Context `{!tokenG Σ}.

Notation N := (nroot .@ "twoLockMSQ_conc").

(* ===== Concurrent Specification for Two-lock M&S Queue ===== *)

(* ----- Ghost variable names ----- *)
Record ConcQgnames := { γ_Hlock   : gname;
                        γ_Tlock   : gname;
                        γ_E       : gname;
                        γ_nE      : gname;
                        γ_D       : gname;
                        γ_nD      : gname;
                        γ_Before  : gname;
                        γ_After   : gname;
                      }.

(* ----- Tokens ----- *)
Definition TokHlock (g : ConcQgnames) := token g.(γ_Hlock).
Definition TokTlock (g : ConcQgnames) := token g.(γ_Tlock).
Definition TokE (g : ConcQgnames) := token g.(γ_E).
Definition TokNE (g : ConcQgnames) := token g.(γ_nE).
Definition TokD (g : ConcQgnames) := token g.(γ_D).
Definition TokND (g : ConcQgnames) := token g.(γ_nD).
Definition TokBefore (g : ConcQgnames) := token g.(γ_Before).
Definition TokAfter (g : ConcQgnames) := token g.(γ_After).
Definition TokUpdated (g : ConcQgnames) := ((TokBefore g) ∗ (TokAfter g))%I.

(* ----- Queue Invariants ------ *)
Definition queue_invariant (Ψ : val -> iProp Σ) (l_head l_tail : loc) (G : ConcQgnames) : iProp Σ :=
  ∃ xs_v, All xs_v Ψ ∗ (* Abstract state *)
  ∃ xs xs_queue xs_old (x_head x_tail: node), (* Concrete state *)
  ⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
  isLL xs ∗
  (* Relation between concrete and abstract state *)
  ⌜projVal xs_queue = wrapSome xs_v⌝ ∗
  (
    (* Static *)
    (
      l_head ↦ #(n_in x_head) ∗
      l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail xs⌝ ∗
      TokNE G ∗ TokND G ∗ TokUpdated G
    )
    ∨
    (* Enqueue *)
    (
      l_head ↦ #(n_in x_head) ∗
      l_tail ↦{#1/2} #(n_in x_tail) ∗
        (⌜isLast x_tail xs⌝ ∗ TokBefore G ∨
         ⌜isSndLast x_tail xs⌝ ∗ TokAfter G) ∗
      TokE G ∗ TokND G
    )
    ∨
    (* Dequeue *)
    (
      l_head ↦{#1/2} #(n_in x_head) ∗
      l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail xs⌝ ∗
      TokNE G ∗ TokD G ∗ TokUpdated G
    )
    ∨
    (* Both *)
    (
      l_head ↦{#1/2} #(n_in x_head) ∗
      l_tail ↦{#1/2} #(n_in x_tail) ∗
        (⌜isLast x_tail xs⌝ ∗ TokBefore G ∨
         ⌜isSndLast x_tail xs⌝ ∗ TokAfter G) ∗
      TokE G ∗ TokD G
    )
  ).

Definition queue_invariant_simple (Ψ : val -> iProp Σ) (l_head l_tail : loc) (G : ConcQgnames) : iProp Σ :=
  ∃ xs_v, All xs_v Ψ ∗ (* Abstract state *)
  ∃ xs xs_queue xs_old (x_head x_tail: node), (* Concrete state *)
  ⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
  isLL xs ∗
  (* Relation between concrete and abstract state *)
  ⌜projVal xs_queue = wrapSome xs_v⌝ ∗
  (
    (l_head ↦ #(n_in x_head) ∗ TokND G) ∨
    (l_head ↦{#1/2} #(n_in x_head) ∗ TokD G)
  ) ∗
  (
    (l_tail ↦ #(n_in x_tail) ∗ ⌜isLast x_tail xs⌝ ∗ TokNE G ∗ TokUpdated G) ∨
    (
      l_tail ↦{#1/2} #(n_in x_tail) ∗ TokE G ∗
      (
        (⌜isLast x_tail xs⌝ ∗ TokBefore G) ∨
        (⌜isSndLast x_tail xs⌝ ∗ TokAfter G)
      )
    )
  ).

Lemma queue_invariant_equiv_simple : ∀ Ψ l_head l_tail G,
  (queue_invariant Ψ l_head l_tail G) ∗-∗
  (queue_invariant_simple Ψ l_head l_tail G).
Proof.
  iIntros (Ψ l_head l_tail G).
  iSplit.
  - iIntros "(%xs_v & HAll & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_eq & HisLL_xs & %Hconc_abst_eq & [HStatic | [HEnqueue | [HDequeue | HBoth]]])";
    iExists xs_v; iFrame "HAll"; iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
    + iDestruct "HStatic" as "(Hl_head & Hl_tail & HisLast & HTokNE & HTokND & HTokUpdated)".
      iSplit; first done.
      iSplitL "Hl_head HTokND"; first (iLeft; iFrame).
      iLeft. iFrame.
    + iDestruct "HEnqueue" as "(Hl_head & Hl_tail & [[HisLast HTokAfter] | [HisSndLast HAfter]] & HToke & HTokND)".
      * iSplit; first done.
        iSplitL "Hl_head HTokND"; first (iLeft; iFrame).
        iRight. iFrame. iLeft. iFrame.
      * iSplit; first done.
        iSplitL "Hl_head HTokND"; first (iLeft; iFrame).
        iRight. iFrame. iRight. iFrame.
    + iDestruct "HDequeue" as "(Hl_head & Hl_tail & HisLast & HTokNE & HTokD & HTokUpdated)".
      iSplit; first done.
      iSplitL "Hl_head HTokD"; first (iRight; iFrame).
      iLeft. iFrame.
    + iDestruct "HBoth" as "(Hl_head & Hl_tail & [[HisLast HTokAfter] | [HisSndLast HAfter]] & HToke & HTokD)".
      * iSplit; first done.
        iSplitL "Hl_head HTokD"; first (iRight; iFrame).
        iRight. iFrame. iLeft. iFrame.
      * iSplit; first done.
        iSplitL "Hl_head HTokD"; first (iRight; iFrame).
        iRight. iFrame. iRight. iFrame.
  - iIntros "(%xs_v & HAll & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_eq & HisLL_xs & %Hconc_abst_eq & [[Hl_head HTokND] | [Hl_head HTokD]] & [(Hl_tail & HisLast & HTokNE & HTokUpdated) | (Hl_tail & HTokE & [[HisLast HTokBefore] | [HisSndLast HTokAfter]])])";
  iExists xs_v; iFrame "HAll"; iExists xs, xs_queue, xs_old, x_head, x_tail; eauto 10 with iFrame.
Qed.

(* ----- The 'isQueue' Predicate for Concurrent Spec ------ *)
Definition isQueue_C (Ψ : val -> iProp Σ) (v_q : val) (G: ConcQgnames) : iProp Σ :=
  ∃ l_queue l_head l_tail : loc, ∃ h_lock t_lock : val,
  ⌜v_q = #l_queue⌝ ∗
  l_queue ↦□ ((#l_head, #l_tail), (h_lock, t_lock)) ∗
  inv N (queue_invariant Ψ l_head l_tail G) ∗
  is_lock G.(γ_Hlock) h_lock (TokD G) ∗
  is_lock G.(γ_Tlock) t_lock (TokE G).

(* isQueue_C is persistent *)
Global Instance isQueue_C_persistent Ψ v_q G : Persistent (isQueue_C Ψ v_q G).
Proof. apply _. Qed.


(* ----- Specification for Initialise ----- *)
Lemma initialize_spec_conc (Ψ : val -> iProp Σ):
  {{{ True }}}
    initialize #()
  {{{ v_q G, RET v_q; isQueue_C Ψ v_q G }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
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
  wp_pures.
  iMod token_alloc as (γ_D) "Hγ_D".
  wp_apply (newlock_spec with "Hγ_D").
  iIntros (h_lock γ_Hlock) "Hγ_Hlock".
  wp_let.
  iMod token_alloc as (γ_E) "Hγ_E".
  wp_apply (newlock_spec with "Hγ_E").
  iIntros (t_lock γ_Tlock) "Hγ_Tlock".
  wp_let.
  wp_alloc l_tail as "Hl_tail".
  wp_alloc l_head as "Hl_head".
  iMod token_alloc as (γ_nE) "Hγ_nE".
  iMod token_alloc as (γ_nD) "Hγ_nD".
  iMod token_alloc as (γ_Before) "Hγ_Before".
  iMod token_alloc as (γ_After) "Hγ_After".
  set (Queue_gnames := {| γ_Hlock := γ_Hlock;
                          γ_Tlock := γ_Tlock;
                          γ_E := γ_E;
                          γ_nE := γ_nE;
                          γ_D := γ_D;
                          γ_nD := γ_nD;
                          γ_Before := γ_Before;
                          γ_After := γ_After
                       |}).
  iMod (inv_alloc N _ (queue_invariant Ψ l_head l_tail Queue_gnames) with "[Hl_head Hl_tail Hx1_to_none Hγ_nE Hγ_nD Hγ_Before Hγ_After]") as "#HqueueInv".
  {
    iNext.
    iExists []. iSplit; first done.
    iExists [x_1], [], [], x_1, x_1; iFrame.
    do 3 (iSplit; first done).
    iLeft.
    iFrame.
    by iExists [].
  }
  wp_alloc l_queue as "Hl_queue".
  iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
  iApply ("HΦ" $! #l_queue Queue_gnames).
  iModIntro.
  iExists l_queue, l_head, l_tail, h_lock, t_lock.
  by repeat iSplit.
Qed.

(* ----- Specification for Enqueue ----- *)
Lemma enqueue_spec_conc v_q Ψ (v : val) (G : ConcQgnames) :
  {{{ isQueue_C Ψ v_q G ∗ Ψ v }}}
    enqueue v_q v
  {{{ w, RET w; True }}}.
Proof.
  iIntros (Φ) "[(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> &
               #Hl_queue & #Hqueue_inv & #Hh_lock & #Ht_lock) HΨ_v] HΦ".
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
  iIntros "(Hlocked_γ_Tlock & HTokE)".
  wp_seq.
  wp_load.
  wp_pures.
  wp_bind (! #l_tail)%E.
  (* Open in Static / Dequeue *)
  iInv "Hqueue_inv" as "Hqueue_inv_open".
  iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
  iDestruct "Hqueue_inv_open" as "(%xs_v & HAll_xs & %xs & %xs_queue & %xs_old & %x_head & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( [Hl_tail1 Hl_tail2] & >[%xs_fromtail %HisLast] & HTokNE & HTokUpdated ) | (_ & >HTokE' & _) ])"; last by iCombine "HTokE HTokE'" gives "%H". (* Impossible: TokE *)
  wp_load.
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  iPoseProof (isLL_chain_node [] x_tail xs_fromtail with "[HisLL_chain_xs]") as "#Hxtail_node"; first by rewrite HisLast.
  iDestruct "HTokUpdated" as "[HTokBefore HTokAfter]".
  iModIntro.
  (* Close in Enqueue / Both : Before *)
  iSplitL "Hhead Hl_tail1 HTokE HTokBefore HisLL_xs HAll_xs".
  {
    iNext.
    iApply queue_invariant_equiv_simple.
    iExists xs_v; iFrame "HAll_xs".
    iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
    do 2 (iSplit; first done).
    iRight.
    iFrame.
    iLeft.
    iFrame.
    by iExists xs_fromtail.
  }
  iClear (HisLast xs_fromtail Hconc_abst_eq xs_v Hxs_eq xs xs_queue x_head xs_old) "HisLL_chain_xs".
  wp_load.
  wp_pures.
  wp_bind (#(n_out x_tail) <- #(n_in x_new))%E.
  (* Open in Enqueue / Both : Before *)
  iInv "Hqueue_inv" as "Hqueue_inv_open".
  iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
  iDestruct "Hqueue_inv_open" as "(%xs_v & HAll_xs & %xs & %xs_queue & %xs_old & %x_head & %x_tail' & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( _ & _ & >HTokNE' & _ ) | (>Hl_tail1 & HTokE & [[>[%xs_fromtail %HisLast] HTokBefore] | [_ >HTokAfter']]) ])";
  [ by iCombine "HTokNE HTokNE'" gives "%H" | | (* Impossible: TokNE *)
    by iCombine "HTokAfter HTokAfter'" gives "%H" ]. (* Impossible: TokAfter *)
  iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]".
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  rewrite HisLast.
  iAssert (▷⌜x_tail' = x_tail⌝)%I as ">->".
  {
    iNext.
    iPoseProof (isLL_chain_node [] x_tail' xs_fromtail with "[HisLL_chain_xs]") as "#Hxtail'_node"; first done.
    by iApply n_in_equal.
  }
  iDestruct "HisLL_xs" as "[Hxtail_to_none _]".
  wp_store. (* Linearisation Point *)
  iMod (pointsto_persist with "Hxtail_to_none") as "#Hxtail_to_xnew".
  iDestruct "Hl_tail" as "[Hl_tail1 Hl_tail2]".
  set xs_new := x_new :: xs.
  iAssert (isLL xs_new) with "[Hxnew_to_none HisLL_chain_xs]" as "HisLL_xs_new".
  {
    rewrite /xs_new /isLL HisLast.
    iFrame.
    unfold isLL_chain; auto.
  }
  iPoseProof (isLL_and_chain with "HisLL_xs_new") as "[HisLL_xs_new #HisLL_chain_xs_new]".
  iModIntro.
  (* Close in Enqueue / Both: After *)
  iSplitL "Hhead Hl_tail1 HTokE HTokAfter HisLL_xs_new HAll_xs HΨ_v".
  {
    iNext.
    iApply queue_invariant_equiv_simple.
    iExists (v :: xs_v); iFrame "HAll_xs HΨ_v".
    iExists xs_new, (x_new :: xs_queue), xs_old, x_head, x_tail.
    iSplit. { by rewrite /xs_new Hxs_eq. }
    iFrame.
    iSplit. { iPureIntro. simpl. f_equal; done. }
    iRight.
    iFrame.
    iRight.
    iFrame.
    iExists x_new, xs_fromtail.
    by rewrite /xs_new HisLast.
  }
  iClear (HisLast xs_fromtail Hconc_abst_eq xs_v Hxs_eq xs_new xs xs_queue x_head xs_old Htail_eq) "HisLL_chain_xs HisLL_chain_xs_new".
  wp_seq.
  wp_load.
  wp_pures.
  wp_bind (#l_tail <- #(n_in x_new))%E.
  (* Open in Enqueue / Both : After *)
  iInv "Hqueue_inv" as "Hqueue_inv_open".
  iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
  iDestruct "Hqueue_inv_open" as "(%xs_v & HAll_xs & %xs & %xs_queue & %xs_old & %x_head & %x_tail'' & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( _ & _ & >HTokNE' & _ ) | (>Hl_tail1 & HTokE & [[_ >HTokBefore'] | [>(%x_new' & %xs_fromtail & %HisSndLast) HTokAfter]])])";
  [ by iCombine "HTokNE HTokNE'" gives "%H" | (* Impossible: TokNE *)
    by iCombine "HTokBefore HTokBefore'" gives "%H" | ]. (* Impossible: TokBefore *)
  iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]".
  rewrite dfrac_op_own Qp.half_half.
  wp_store.
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  iAssert (⌜x_tail'' = x_tail⌝)%I as "->".
  {
    iPoseProof (isLL_chain_node [x_new'] x_tail'' xs_fromtail with "[HisLL_chain_xs]") as "#Hxtail''_node"; first by rewrite HisSndLast.
    by iApply n_in_equal.
  }
  iAssert (⌜x_new' = x_new⌝)%I as "->".
  {
    rewrite HisSndLast.
    iPoseProof (isLL_chain_node [] x_new' (x_tail :: xs_fromtail) with "[HisLL_chain_xs]") as "#Hxnew'_node"; first done.
    iDestruct "HisLL_chain_xs" as "(_ & Hxtail_to_xnew' & _)".
    iCombine "Hxtail_to_xnew Hxtail_to_xnew'" gives "[_ %H]".
    by iApply n_in_equal.
  }
  iModIntro.
  (* Close in Static / Dequeue *)
  iSplitR "HTokE Hlocked_γ_Tlock HΦ".
  {
    iNext.
    iApply queue_invariant_equiv_simple.
    iExists xs_v; iFrame "HAll_xs".
    iExists xs, xs_queue, xs_old, x_head, x_new; iFrame.
    do 2 (iSplit; first done).
    iLeft.
    iFrame.
    by iExists (x_tail :: xs_fromtail).
  }
  wp_seq.
  wp_load.
  wp_pures.
  wp_apply (release_spec with "[$Ht_lock $HTokE $Hlocked_γ_Tlock]").
  done.
Qed.

(* ----- Specification for Dequeue ----- *)
Lemma dequeue_spec_conc v_q Ψ (G : ConcQgnames) :
  {{{ isQueue_C Ψ v_q G }}}
    dequeue v_q
  {{{ w, RET w; ⌜w = NONEV⌝ ∨ (∃ v, ⌜w = SOMEV v⌝ ∗ Ψ v) }}}.
Proof.
  iIntros (Φ) "(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> &
               #Hl_queue & #Hqueue_inv & #Hh_lock & #Ht_lock) HΦ".
  wp_lam.
  wp_load.
  wp_pures.
  wp_apply (acquire_spec with "Hh_lock").
  iIntros "(Hlocked_γ_Hlock & HTokD)".
  wp_seq.
  wp_load.
  wp_pures.
  wp_bind (! #l_head)%E.
  (* Open in Static / Enqueue *)
  iInv "Hqueue_inv" as "Hqueue_inv_open".
  iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
  iDestruct "Hqueue_inv_open" as "(%xs_v & HAll_xs & %xs & %xs_queue & %xs_old & %x_head & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & [ [Hl_head HTokND] | [Hl_head >HTokD'] ] & Htail)";
  last by iCombine "HTokD HTokD'" gives "%H". (* Impossible: TokD*)
  wp_load.
  iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  iModIntro.
  (* Close in Dequeue / Both *)
  iSplitL "Hl_head1 HTokD Htail HisLL_xs HAll_xs".
  {
    iNext.
    iApply queue_invariant_equiv_simple.
    iExists xs_v; iFrame "HAll_xs".
    iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
    do 2 (iSplit; first done).
    by iRight.
  }
  subst.
  iPoseProof (isLL_chain_node with "HisLL_chain_xs") as "Hxhead_node".
  iClear (Hconc_abst_eq xs_v xs_queue xs_old x_tail) "HisLL_chain_xs".
  wp_let.
  wp_load.
  wp_pures.
  wp_bind (! #(n_out x_head))%E.
  (* Open in Dequeue / Both *)
  iInv "Hqueue_inv" as "Hqueue_inv_open".
  iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
  iDestruct "Hqueue_inv_open" as "(%xs_v & HAll_xs & %xs & %xs_queue & %xs_old & %x_head' & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & [ [Hl_head >HTokND'] | [>Hl_head1 HTokD] ] & Htail)";
  first by iCombine "HTokND HTokND'" gives "%H". (* Impossible: TokND*)
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq]".
  subst.
  iAssert (▷⌜x_head' = x_head⌝)%I as ">->".
  {
    iNext.
    iPoseProof (isLL_chain_node xs_queue x_head' xs_old with "[HisLL_chain_xs]") as "#Hxhead'_node"; first done.
    by iApply n_in_equal.
  }
  (* CASE ANALYSIS: Is queue empty? *)
  destruct (ll_case_first xs_queue) as [->|[x_head_next [xs_queue' ->]]].
  - (* Queue is empty. *)
    iDestruct "HisLL_xs" as "[Hxhead_to_none _]".
    wp_load. (* Linearisation Point *)
    iModIntro.
    (* Close in Static / Enqueue *)
    iSplitL "Hl_head HTokND Htail Hxhead_to_none".
    {
      iNext.
      iApply queue_invariant_equiv_simple.
      iExists []; iSplit; first done.
      iExists ([] ++ [x_head] ++ xs_old), [], xs_old, x_head, x_tail; iFrame. do 3 (iSplit; first done). iLeft. iFrame.
      by rewrite dfrac_op_own Qp.half_half.
    }
    wp_let.
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply (release_spec with "[$Hh_lock $HTokD $Hlocked_γ_Hlock]").
    iIntros (_).
    wp_seq.
    iModIntro.
    iApply "HΦ".
    by iLeft.
  - (* Queue is non-empty*)
    iAssert (▷(isLL_chain [x_head_next; x_head]))%I as "HisLL_chain_xheadnext".
    {
      iNext.
      rewrite <- app_assoc.
      iDestruct (isLL_chain_split with "HisLL_chain_xs") as "[_ H]".
      iClear "HisLL_chain_xs".
      rewrite -> app_assoc.
      iDestruct (isLL_chain_split with "H") as "[H' _]".
      done.
    }
    iDestruct "HisLL_chain_xheadnext" as "(Hxheadnext_node & Hxhead_to_xheadnext & _)".
    wp_load.
    iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
    iModIntro.
    (* Close in Dequeue / Both *)
    iSplitL "Hl_head1 HisLL_xs Htail HTokD HAll_xs".
    {
      iNext.
      iApply queue_invariant_equiv_simple.
      iExists xs_v; iFrame "HAll_xs".
      iExists ((xs_queue' ++ [x_head_next]) ++ [x_head] ++ xs_old), (xs_queue' ++ [x_head_next]), xs_old, x_head, x_tail; iFrame.
      do 2 (iSplit; first done).
      by iRight.
    }
    iClear (Hconc_abst_eq xs_v xs_queue' xs_old x_tail Hhead_eq) "HisLL_chain_xs".
    wp_let.
    wp_pures.
    wp_load.
    wp_pures.
    wp_load.
    wp_pures.
    wp_bind (#l_head <- #(n_in x_head_next))%E.
    (* Open in Dequeue / Both *)
    iInv "Hqueue_inv" as "Hqueue_inv_open".
    iPoseProof (queue_invariant_equiv_simple Ψ l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
    iDestruct "Hqueue_inv_open" as "(%xs_v & HAll_xs & %xs & %xs_queue & %xs_old & %x_head'' & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & [ [Hl_head >HTokND'] | [>Hl_head1 HTokD] ] & Htail)";
    first by iCombine "HTokND HTokND'" gives "%H". (* Impossible TokND *)
    iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq]".
    rewrite dfrac_op_own Qp.half_half.
    subst.
    iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
    iAssert (▷⌜x_head'' = x_head⌝)%I as ">->".
    {
      iNext.
      iPoseProof (isLL_chain_node xs_queue x_head'' xs_old with "[HisLL_chain_xs]") as "#Hxhead''_node"; first done.
      by iApply n_in_equal.
    }
    wp_store. (* Linearisation Point *)
    (* Sync up xs_queue *)
    destruct (ll_case_first xs_queue) as [->|[x_head_next' [xs_queue' ->]]].
    { (* Impossible case. xs_queue must contain at least one element. *)
      iDestruct "HisLL_xs" as "[Hxhead_to_none _]".
      iCombine "Hxhead_to_none Hxhead_to_xheadnext" gives "[_ %Hcontra]".
      simplify_eq.
    }
    rewrite <- app_assoc.
    iAssert (⌜x_head_next' = x_head_next⌝)%I as "->".
    {
      iPoseProof (isLL_chain_split xs_queue' _ with "HisLL_chain_xs") as "(_ & Hxheadnext'_node & Hxhead_to_xheadnext' & _)".
      iCombine "Hxhead_to_xheadnext Hxhead_to_xheadnext'" gives "[_ %Heq]".
      by iApply n_in_equal.
    }
    (* Sync up abstract state *)
    destruct (ll_case_first xs_v) as [->|[v [xs_v' ->]]].
    {
      rewrite projVal_split in Hconc_abst_eq.
      exfalso.
      by apply (app_cons_not_nil (projVal xs_queue') [] (n_val x_head_next)).
    }
    rewrite projVal_split wrapSome_split /= in Hconc_abst_eq.
    apply list_last_eq in Hconc_abst_eq as [Hxs_rest_val_eq Hxheadnext_v_eq].
    iPoseProof (All_split with "HAll_xs") as "[HAll_xs_val_rest [Hxheadnext_val_Ψ _]]".
    iModIntro.
    (* Close in Static / Enqueue *)
    iSplitL "Hl_head Htail HTokND HisLL_xs HAll_xs_val_rest".
    {
      iNext.
      iApply queue_invariant_equiv_simple.
      iExists xs_v'; iFrame "HAll_xs_val_rest".
      iExists (xs_queue' ++ [x_head_next] ++ (x_head :: xs_old)), xs_queue', (x_head :: xs_old), x_head_next, x_tail; iFrame.
      do 2 (iSplit; first done).
      iLeft.
      iFrame.
    }
    wp_seq.
    wp_load.
    wp_pures.
    wp_apply (release_spec with "[$Hh_lock $HTokD $Hlocked_γ_Hlock]").
    iIntros (_).
    wp_seq.
    iModIntro.
    iApply "HΦ".
    iRight.
    iExists v.
    by iSplit.
Qed.

End proofs.