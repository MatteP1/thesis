From stdpp Require Import countable.
From iris.algebra Require Import list agree lib.frac_auth.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import invariants token.
From MSQueue Require Import MSQ_common.
From MSQueue Require Import queue_specs.
From MSQueue Require Import twoLockMSQ_impl.

(* NOTE: This file is very similar to twoLockMSQ_concurrent_spec. The main difference is that, instead of the 'All' predicate in the invariant, we have the abstract contents of the queue. The meaningful differences in the proofs have been highlighted with 'CHANGE' comments. *)

Local Existing Instance spin_lock.

Class queueG Σ := {
  queueGlock :: lockG Σ;
  queueGtoken :: tokenG Σ
}.

Section proofs.

Context `{!heapGS Σ}.
Context `{!queueG Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Variable N : namespace.
Notation Ni := (N .@ "internal").

(* ===== HOCAP Specification for Two-lock M&S Queue ===== *)

(* ----- Ghost variable names ----- *)
Record Qgnames := { γ_Abst    : gname;
                    γ_Hlock   : gname;
                    γ_Tlock   : gname;
                    γ_E       : gname;
                    γ_nE      : gname;
                    γ_D       : gname;
                    γ_nD      : gname;
                    γ_Before  : gname;
                    γ_After   : gname;
                  }.

(* ----- Tokens ----- *)
Definition TokHlock (g : Qgnames) := token g.(γ_Hlock).
Definition TokTlock (g : Qgnames) := token g.(γ_Tlock).
Definition TokE (g : Qgnames) := token g.(γ_E).
Definition TokNE (g : Qgnames) := token g.(γ_nE).
Definition TokD (g : Qgnames) := token g.(γ_D).
Definition TokND (g : Qgnames) := token g.(γ_nD).
Definition TokBefore (g : Qgnames) := token g.(γ_Before).
Definition TokAfter (g : Qgnames) := token g.(γ_After).
Definition TokUpdated (g : Qgnames) := ((TokBefore g) ∗ (TokAfter g))%I.

(* ----- Queue Invariants ------ *)
Definition queue_invariant (l_head l_tail : loc) (G : Qgnames) : iProp Σ :=
  ∃ xs_v, G.(γ_Abst) ⤇● xs_v ∗ (* Abstract state *)
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

Definition queue_invariant_simple (l_head l_tail : loc) (G : Qgnames) : iProp Σ :=
  ∃ xs_v, G.(γ_Abst) ⤇● xs_v ∗ (* Abstract state *)
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

Lemma queue_invariant_equiv_simple : ∀ l_head l_tail G,
  (queue_invariant l_head l_tail G) ∗-∗
  (queue_invariant_simple l_head l_tail G).
Proof.
  iIntros (l_head l_tail G).
  iSplit.
  - iIntros "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_eq & HisLL_xs & %Hconc_abst_eq & [HStatic | [HEnqueue | [HDequeue | HBoth]]])";
    iExists xs_v; iFrame "HAbst"; iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
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
  - iIntros "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail & Hxs_eq & HisLL_xs & %Hconc_abst_eq & [[Hl_head HTokND] | [Hl_head HTokD]] & [(Hl_tail & HisLast & HTokNE & HTokUpdated) | (Hl_tail & HTokE & [[HisLast HTokBefore] | [HisSndLast HTokAfter]])])";
  iExists xs_v; iFrame "HAbst"; iExists xs, xs_queue, xs_old, x_head, x_tail; eauto 10 with iFrame.
Qed.

(* ----- The 'isQueue' Predicate ------ *)
Definition isQueue (v_q : val) (G: Qgnames) : iProp Σ :=
  ∃ l_queue l_head l_tail : loc, ∃ h_lock T_lock : val,
  ⌜v_q = #l_queue⌝ ∗
  l_queue ↦□ ((#l_head, #l_tail), (h_lock, T_lock)) ∗
  inv Ni (queue_invariant l_head l_tail G) ∗
  is_lock G.(γ_Hlock) h_lock (TokD G) ∗
  is_lock G.(γ_Tlock) T_lock (TokE G).

(* isQueue is persistent *)
Global Instance isQueue_persistent v_q G : Persistent (isQueue v_q G).
Proof. apply _. Qed.


(* ----- Specification for Initialise ----- *)
Lemma initialize_spec:
  {{{ True }}}
    initialize #()
  {{{ v_q G, RET v_q; isQueue v_q G ∗ G.(γ_Abst) ⤇◯ [] }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  (* --- Step into initialize function --- *)
  wp_lam.
  (* --- Create head node: x_1 --- *)
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
  (* --- Create head and tail locks --- *)
  iMod token_alloc as (γ_D) "Hγ_D".
  wp_apply (newlock_spec with "Hγ_D").
  iIntros (h_lock γ_Hlock) "Hγ_Hlock".
  wp_let.
  iMod token_alloc as (γ_E) "Hγ_E".
  wp_apply (newlock_spec with "Hγ_E").
  iIntros (t_lock γ_Tlock) "Hγ_Tlock".
  wp_let.
  (* --- Create queue structure --- *)
  wp_alloc l_tail as "Hl_tail".
  wp_alloc l_head as "Hl_head".
  wp_alloc l_queue as "Hl_queue".
  iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
  (* --- Allocate tokens for invariant --- *)
  iMod token_alloc as (γ_nE) "Hγ_nE".
  iMod token_alloc as (γ_nD) "Hγ_nD".
  iMod token_alloc as (γ_Before) "Hγ_Before".
  iMod token_alloc as (γ_After) "Hγ_After".
  (* CHANGE: allocate the abstract state of the queue as empty *)
  (* --- Allocate auth. and frag. views of empty abstract state --- *)
  iMod (queue_contents_alloc []) as (γ_Abst) "[Hγ_Abst_auth Hγ_Abst_frac]".
  (* --- Collect ghost names in record --- *)
  set (G := {| γ_Abst := γ_Abst;
               γ_Hlock := γ_Hlock;
               γ_Tlock := γ_Tlock;
               γ_E := γ_E;
               γ_nE := γ_nE;
               γ_D := γ_D;
               γ_nD := γ_nD;
               γ_Before := γ_Before;
               γ_After := γ_After
            |}).
  (* --- Allocate queue invariant --- *)
  iMod (inv_alloc Ni _ (queue_invariant l_head l_tail G) with "[Hγ_Abst_auth Hl_head Hl_tail Hx1_to_none Hγ_nE Hγ_nD Hγ_Before Hγ_After]") as "#HqueueInv".
  {
    iNext.
    iExists []; iFrame "Hγ_Abst_auth".
    iExists [x_1], [], [], x_1, x_1; iFrame.
    do 3 (iSplit; first done).
    iLeft.
    iFrame.
    by iExists [].
  }
  (* --- Prove post-condition --- *)
  iApply ("HΦ" $! #l_queue G).
  iModIntro.
  iFrame "Hγ_Abst_frac".
  iExists l_queue, l_head, l_tail, h_lock, t_lock.
  by repeat iSplit.
Qed.

(* ----- Specification for Enqueue ----- *)
Lemma enqueue_spec v_q (v : val) (G : Qgnames) (P Q : iProp Σ) :
  □(∀xs_v, (G.(γ_Abst) ⤇● xs_v ∗ P ={⊤ ∖ ↑Ni}=∗ ▷ (G.(γ_Abst) ⤇● (v :: xs_v) ∗ Q))) -∗
  {{{ isQueue v_q G ∗ P}}}
    enqueue v_q v
  {{{ w, RET w; Q }}}.
Proof.
  (* CHANGE: assume the view-shift *)
  (* --- Assume view-shift and pre-condition --- *)
  iIntros "#Hvs".
  iIntros (Φ) "!> [(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> &
               #Hl_queue & #Hqueue_inv & #Hh_lock & #Ht_lock) HP] HΦ".
  (* --- Step into enqueue function --- *)
  wp_lam.
  wp_let.
  (* --- Create new node: x_new --- *)
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
  (* --- Acquire tail lock --- *)
  wp_load.
  wp_pures.
  wp_apply (acquire_spec with "Ht_lock").
  iIntros "(Hlocked_γ_Tlock & HTokE)".
  wp_seq.
  (* --- Read current tail node: x_tail --- *)
  wp_load.
  wp_pures.
  (* To perform load, we must know what l_tail points to *)
  (* --- Open Invariant in Static / Dequeue --- *)
  wp_bind (! #l_tail)%E.
  iInv "Hqueue_inv" as "Hqueue_inv_open".
  iPoseProof (queue_invariant_equiv_simple l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
  iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( Hl_tail & >[%xs_fromtail %HisLast] & HTokNE & HTokUpdated ) | (_ & >HTokE' & _) ])"; last by iCombine "HTokE HTokE'" gives "%H". (* Impossible: TokE *)
  (* --- Perform load: l_tail points to x_tail --- *)
  wp_load.
  (* --- Keep half of tail pointer --- *)
  iDestruct "Hl_tail" as "[Hl_tail1 Hl_tail2]".
  (* --- Resource management --- *)
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  iPoseProof (isLL_chain_node [] x_tail xs_fromtail with "[HisLL_chain_xs]") as "#Hxtail_node"; first by rewrite HisLast.
  iDestruct "HTokUpdated" as "[HTokBefore HTokAfter]".
  iModIntro.
  (* --- Close Invariant in Enqueue / Both : Before --- *)
  iSplitL "Hhead Hl_tail1 HTokE HTokBefore HisLL_xs HAbst".
  {
    iNext.
    iApply queue_invariant_equiv_simple.
    iExists xs_v; iFrame "HAbst".
    iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
    do 2 (iSplit; first done).
    iRight.
    iFrame.
    iLeft.
    iFrame.
    by iExists xs_fromtail.
  }
  iClear (HisLast xs_fromtail Hconc_abst_eq xs_v Hxs_eq xs xs_queue x_head xs_old) "HisLL_chain_xs".
  (* --- Add x_new to linked list --- *)
  wp_load.
  wp_pures.
  (* To perform store, we must have a points-to predicate for [n_out x_tail] *)
  (* --- Open Invariant in Enqueue / Both : Before --- *)
  wp_bind (#(n_out x_tail) <- #(n_in x_new))%E.
  iInv "Hqueue_inv" as "Hqueue_inv_open".
  iPoseProof (queue_invariant_equiv_simple l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
  iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail' & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( _ & _ & >HTokNE' & _ ) | (>Hl_tail1 & HTokE & [[>[%xs_fromtail %HisLast] HTokBefore] | [_ >HTokAfter']]) ])";
  [ by iCombine "HTokNE HTokNE'" gives "%H" | | (* Impossible: TokNE *)
    by iCombine "HTokAfter HTokAfter'" gives "%H" ]. (* Impossible: TokAfter *)
  (* --- Deduce that l_tail still points to x_tail --- *)
  iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]";
  rewrite dfrac_op_own Qp.half_half.
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  rewrite HisLast.
  iAssert (▷⌜x_tail' = x_tail⌝)%I as ">->".
  {
    iNext.
    iPoseProof (isLL_chain_node [] x_tail' xs_fromtail with "[HisLL_chain_xs]") as "#Hxtail'_node"; first done.
    by iApply n_in_equal.
  }
  (* --- x_tail is last, so must point to None --- *)
  iDestruct "HisLL_xs" as "[Hxtail_to_none _]".
  (* --- Perform store: this adds x_new to the linked list --- *)
  wp_store. (* Linearisation Point *)
  iMod (pointsto_persist with "Hxtail_to_none") as "#Hxtail_to_xnew".
  (* --- Keep half of tail pointer --- *)
  iDestruct "Hl_tail" as "[Hl_tail1 Hl_tail2]".
  (* --- Resource management --- *)
  set xs_new := x_new :: xs.
  iAssert (isLL xs_new) with "[Hxnew_to_none HisLL_chain_xs]" as "HisLL_xs_new".
  {
    rewrite /xs_new /isLL HisLast.
    iFrame.
    unfold isLL_chain; auto.
  }
  iPoseProof (isLL_and_chain with "HisLL_xs_new") as "[HisLL_xs_new #HisLL_chain_xs_new]".
  (* CHANGE: The store was a linearisation point. Update the abstract state using the view-shift *)
  (* --- Apply view-shift --- *)
  iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[HAbst_new HQ]"; first by iFrame.
  iModIntro.
  (* --- Close Invariant in Enqueue / Both: After --- *)
  iSplitL "Hhead Hl_tail1 HTokE HTokAfter HisLL_xs_new HAbst_new".
  {
    iNext.
    iApply queue_invariant_equiv_simple.
    iExists (v :: xs_v); iFrame "HAbst_new".
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
  (* --- Swing tail pointer to x_new --- *)
  wp_load.
  wp_pures.
  (* To perform store, we must have a points-to predicate for l_tail *)
  (* --- Open Invariant in Enqueue / Both : After --- *)
  wp_bind (#l_tail <- #(n_in x_new))%E.
  iInv "Hqueue_inv" as "Hqueue_inv_open".
  iPoseProof (queue_invariant_equiv_simple l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
  iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail'' & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & Hhead & [ ( _ & _ & >HTokNE' & _ ) | (>Hl_tail1 & HTokE & [[_ >HTokBefore'] | [>(%x_new' & %xs_fromtail & %HisSndLast) HTokAfter]])])";
  [ by iCombine "HTokNE HTokNE'" gives "%H" | (* Impossible: TokNE *)
    by iCombine "HTokBefore HTokBefore'" gives "%H" | ]. (* Impossible: TokBefore *)
  (* We get that l_tail points to some node x_tail'', which is only the second last node. Hence, there is some node x_new', which is the last node. *)
  (* --- Deduce that x_tail'' is x_tail --- *)
  iCombine "Hl_tail1 Hl_tail2" as "Hl_tail" gives "[_ %Htail_eq]";
  rewrite dfrac_op_own Qp.half_half.
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  iAssert (▷⌜x_tail'' = x_tail⌝)%I as ">->".
  {
    iNext.
    iPoseProof (isLL_chain_node [x_new'] x_tail'' xs_fromtail with "[HisLL_chain_xs]") as "#Hxtail''_node"; first by rewrite HisSndLast.
    by iApply n_in_equal.
  }
  (* --- Deduce that x_new' is our enqueued node: x_new --- *)
  iAssert (▷⌜x_new' = x_new⌝)%I as ">->".
  {
    iNext.
    rewrite HisSndLast.
    iPoseProof (isLL_chain_node [] x_new' (x_tail :: xs_fromtail) with "[HisLL_chain_xs]") as "#Hxnew'_node"; first done.
    iDestruct "HisLL_chain_xs" as "(_ & Hxtail_to_xnew' & _)".
    iCombine "Hxtail_to_xnew Hxtail_to_xnew'" gives "[_ %H]".
    by iApply n_in_equal.
  }
  (* --- Perform store: this swings l_tail to x_new --- *)
  wp_store.
  iModIntro.
  (* --- Close Invariant in Static / Dequeue --- *)
  iSplitR "HTokE Hlocked_γ_Tlock HΦ HQ".
  {
    iNext.
    iApply queue_invariant_equiv_simple.
    iExists xs_v; iFrame "HAbst".
    iExists xs, xs_queue, xs_old, x_head, x_new; iFrame.
    do 2 (iSplit; first done).
    iLeft.
    iFrame.
    by iExists (x_tail :: xs_fromtail).
  }
  wp_seq.
  (* --- Release tail lock --- *)
  wp_load.
  wp_pures.
  wp_apply (release_spec with "[$Ht_lock $HTokE $Hlocked_γ_Tlock]").
  (* CHANGE: prove Q *)
  iIntros (_).
  (* --- Prove post-condition --- *)
  by iApply "HΦ".
Qed.

(* ----- Specification for Dequeue ----- *)
Lemma dequeue_spec v_q (G : Qgnames) (P : iProp Σ) (Q : val -> iProp Σ):
  □(∀xs_v, (G.(γ_Abst) ⤇● xs_v ∗ P
              ={⊤ ∖ ↑Ni}=∗
              ▷ (( ⌜xs_v = []⌝ ∗ G.(γ_Abst) ⤇● xs_v ∗ Q NONEV) ∨
              (∃v xs_v', ⌜xs_v = xs_v' ++ [v]⌝ ∗ G.(γ_Abst) ⤇● xs_v' ∗ Q (SOMEV v)))
            )
   )
  -∗
  {{{ isQueue v_q G ∗ P }}}
    dequeue v_q
  {{{ w, RET w; Q w }}}.
Proof.
  (* CHANGE: assume the view-shift *)
  (* --- Assume view-shift and pre-condition --- *)
  iIntros "#Hvs".
  iIntros (Φ) "!> [(%l_queue & %l_head & %l_tail & %h_lock & %t_lock & -> &
               #Hl_queue & #Hqueue_inv & #Hh_lock & #Ht_lock) HP] HΦ".
  (* --- Step into dequeue function --- *)
  wp_lam.
  (* --- Acquire head lock --- *)
  wp_load.
  wp_pures.
  wp_apply (acquire_spec with "Hh_lock").
  iIntros "(Hlocked_γ_Hlock & HTokD)".
  wp_seq.
  (* --- Read current head node: x_head --- *)
  wp_load.
  wp_pures.
  (* To perform load, we must know what l_head points to *)
  (* --- Open Invariant in Static / Enqueue --- *)
  wp_bind (! #l_head)%E.
  iInv "Hqueue_inv" as "Hqueue_inv_open".
  iPoseProof (queue_invariant_equiv_simple l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
  iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & [ [Hl_head HTokND] | [Hl_head >HTokD'] ] & Htail)";
  last by iCombine "HTokD HTokD'" gives "%H". (* Impossible: TokD *)
  (* --- Perform load: l_head points to x_head --- *)
  wp_load.
  (* --- Keep half of head pointer --- *)
  iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
  (* --- Resource management --- *)
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  iModIntro.
  (* --- Close Invariant in Dequeue / Both --- *)
  iSplitL "Hl_head1 HTokD Htail HisLL_xs HAbst".
  {
    iNext.
    iApply queue_invariant_equiv_simple.
    iExists xs_v; iFrame "HAbst".
    iExists xs, xs_queue, xs_old, x_head, x_tail; iFrame.
    do 2 (iSplit; first done).
    by iRight.
  }
  subst.
  iPoseProof (isLL_chain_node with "HisLL_chain_xs") as "Hxhead_node".
  iClear (Hconc_abst_eq xs_v xs_queue xs_old x_tail) "HisLL_chain_xs".
  (* --- l_head pointed to x_head --- *)
  wp_let.
  (* --- Read x_head's next --- *)
  wp_load.
  wp_pures.
  (* To read next of x_head, we must know what it points to *)
  (* --- Open Invariant in Dequeue / Both --- *)
  wp_bind (! #(n_out x_head))%E.
  iInv "Hqueue_inv" as "Hqueue_inv_open".
  iPoseProof (queue_invariant_equiv_simple l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
  iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head' & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & [ [Hl_head >HTokND'] | [>Hl_head1 HTokD] ] & Htail)";
  first by iCombine "HTokND HTokND'" gives "%H". (* Impossible: TokND *)
  (* --- Deduce that l_head still points to x_head --- *)
  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
  iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq]";
  rewrite dfrac_op_own Qp.half_half.
  subst.
  iAssert (▷⌜x_head' = x_head⌝)%I as ">->".
  {
    iNext.
    iPoseProof (isLL_chain_node xs_queue x_head' xs_old with "[HisLL_chain_xs]") as "#Hxhead'_node"; first done.
    by iApply n_in_equal.
  }
  (* --- CASE ANALYSIS: Is queue empty? --- *)
  destruct (ll_case_first xs_queue) as [->|[x_head_next [xs_queue' ->]]].
  - (* CASE: Queue is empty. *)
    (* --- Deduce that x_head must point to None --- *)
    iDestruct "HisLL_xs" as "[Hxhead_to_none _]".
    (* --- Perform load: x_head points to None --- *)
    wp_load. (* Linearisation Point *)
    (* CHANGE: The load was a linearisation point. Update resources using the view-shift. *)
    (* --- Apply view-shift --- *)
    iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[(>-> & HAbst & HQ) | (%v & %xs_v' & >-> & HAbst_new & HQ) ]";
    [ by iFrame | |
      (* The abstract state must be empty. Hence, the second disjunct is impossible. *)
      rewrite wrapSome_split in Hconc_abst_eq;
      exfalso;
      by apply (app_cons_not_nil (wrapSome xs_v') [] (SOMEV v))
    ].
    iModIntro.
    (* --- Close Invariant in Static / Enqueue --- *)
    iSplitL "Hl_head HTokND Htail Hxhead_to_none HAbst".
    {
      iNext.
      iApply queue_invariant_equiv_simple.
      iExists []; iFrame "HAbst".
      iExists ([] ++ [x_head] ++ xs_old), [], xs_old, x_head, x_tail; iFrame. do 3 (iSplit; first done). iLeft. iFrame.
    }
    (* --- x_head pointed to None --- *)
    wp_let.
    (* --- Queue was empty, so take branch that returns None --- *)
    wp_pures.
    (* --- Release head lock --- *)
    wp_load.
    wp_pures.
    wp_apply (release_spec with "[$Hh_lock $HTokD $Hlocked_γ_Hlock]").
    iIntros (_).
    wp_seq.
    iModIntro.
    (* --- Prove post-condition --- *)
    (* CHANGE: prove Q *)
    by iApply "HΦ".
  - (* CASE: Queue is non-empty *)
    (* --- Deduce that x_head is followed by some node x_head_next --- *)
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
    (* --- Perform load: x_head points to some node x_head_next --- *)
    wp_load.
    (* --- Keep half of head pointer --- *)
    iDestruct "Hl_head" as "[Hl_head1 Hl_head2]".
    iModIntro.
    (* --- Close Invariant in Dequeue / Both --- *)
    iSplitL "Hl_head1 HisLL_xs Htail HTokD HAbst".
    {
      iNext.
      iApply queue_invariant_equiv_simple.
      iExists xs_v; iFrame "HAbst".
      iExists ((xs_queue' ++ [x_head_next]) ++ [x_head] ++ xs_old), (xs_queue' ++ [x_head_next]), xs_old, x_head, x_tail; iFrame.
      do 2 (iSplit; first done).
      by iRight.
    }
    iClear (Hconc_abst_eq xs_v xs_queue' xs_old x_tail Hhead_eq) "HisLL_chain_xs".
    (* --- x_head pointed to x_head_next --- *)
    wp_let.
    (* --- Queue is not empty, so take branch that dequeues --- *)
    wp_pures.
    (* --- Read value to dequeue (value of x_head_next) --- *)
    wp_load.
    wp_pures.
    (* --- Swing head pointer to x_head_next --- *)
    wp_load.
    wp_pures.
    (* To perform store, we must have a points-to predicate for l_head *)
    (* --- Open Invariant in Dequeue / Both --- *)
    wp_bind (#l_head <- #(n_in x_head_next))%E.
    iInv "Hqueue_inv" as "Hqueue_inv_open".
    iPoseProof (queue_invariant_equiv_simple l_head l_tail G with "Hqueue_inv_open") as "Hqueue_inv_open".
    iDestruct "Hqueue_inv_open" as "(%xs_v & HAbst & %xs & %xs_queue & %xs_old & %x_head'' & %x_tail & >%Hxs_eq & HisLL_xs & >%Hconc_abst_eq & [ [Hl_head >HTokND'] | [>Hl_head1 HTokD] ] & Htail)";
    first by iCombine "HTokND HTokND'" gives "%H". (* Impossible TokND *)
    (* --- Deduce that l_head still points to x_head --- *)
    iCombine "Hl_head1 Hl_head2" as "Hl_head" gives "[_ %Hhead_eq]";
    rewrite dfrac_op_own Qp.half_half.
    subst.
    iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLL_chain_xs]".
    iAssert (▷⌜x_head'' = x_head⌝)%I as ">->".
    {
      iNext.
      iPoseProof (isLL_chain_node xs_queue x_head'' xs_old with "[HisLL_chain_xs]") as "#Hxhead''_node"; first done.
      by iApply n_in_equal.
    }
    (* --- Perform store: this swings l_head to x_head_next --- *)
    wp_store. (* Linearisation Point *)
    (* --- Sync up xs_queue --- *)
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
    (* CHANGE: The store was a linearisation point. Update the abstract state using the view-shift. *)
    (* --- Apply view-shift --- *)
    iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[(>-> & HAbst & HQ) | (%v & %xs_v' & >-> & HAbst_new & HQ) ]";
    [ by iFrame |
      (* The abstract state cannot be empty. Hence, the first disjunct is impossible. *)
      rewrite projVal_split in Hconc_abst_eq;
      exfalso;
      by apply (app_cons_not_nil (projVal xs_queue') [] (n_val x_head_next)) |
    ].
    (* --- Reason about relationship between conc. and abst. states --- *)
    rewrite projVal_split wrapSome_split /= in Hconc_abst_eq.
    apply list_last_eq in Hconc_abst_eq as [Hxs_rest_val_eq Hxheadnext_v_eq].
    iModIntro.
    (* --- Close Invariant in Static / Enqueue --- *)
    iSplitL "Hl_head Htail HTokND HisLL_xs HAbst_new".
    {
      iNext.
      iApply queue_invariant_equiv_simple.
      iExists xs_v'; iFrame "HAbst_new".
      iExists (xs_queue' ++ [x_head_next] ++ (x_head :: xs_old)), xs_queue', (x_head :: xs_old), x_head_next, x_tail; iFrame.
      do 2 (iSplit; first done).
      iLeft.
      iFrame.
    }
    wp_seq.
    (* --- Release head lock --- *)
    wp_load.
    wp_pures.
    wp_apply (release_spec with "[$Hh_lock $HTokD $Hlocked_γ_Hlock]").
    iIntros (_).
    wp_seq.
    iModIntro.
    (* --- Prove post-condition --- *)
    iApply "HΦ".
    (* CHANGE: prove Q *)
    by rewrite Hxheadnext_v_eq.
Qed.

End proofs.

Definition twoLockMSQ : queue :=
{|
  queue_specs.isQueue Σ _ (_ : queueG Σ) _ :=
    isQueue (nroot.@"two-lock-MSQ");
  queue_specs.initialize_spec _ _ _ _ := initialize_spec (nroot.@"two-lock-MSQ");
  queue_specs.enqueue_spec _ _ _ _ := enqueue_spec (nroot.@"two-lock-MSQ");
  queue_specs.dequeue_spec _ _ _ _ := dequeue_spec (nroot.@"two-lock-MSQ");
|}.
