From stdpp Require Import sets countable.
From iris.algebra Require Import list agree gset lib.frac_auth.
From iris.bi Require Import fixpoint big_op.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation primitive_laws.
From iris.base_logic.lib Require Import invariants.
From MSQueue Require Import MSQ_common.
From MSQueue Require Import queue_specs.
From MSQueue Require Import lockAndCCFreeMSQ_impl.

Section proofs.

Definition nodeO : Type := prodO (prodO locO valO) locO.

Context `{!heapGS Σ}.
Context `{!inG Σ (authR (gsetUR nodeO))}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Variable N : namespace.
Notation Ni := (N .@ "internal").

(* ===== Hocap Specification for Lock-Free M&S Queue ===== *)

(* ----- Ghost variable names ----- *)
Record Qgnames := { γ_Abst : gname;
                    γ_Head : gname;
                    γ_Tail : gname;
                    γ_Last : gname;
                  }.

(* ------ Concrete Reachability ------ *)
Definition Reach (Φ : node -> node -> iProp Σ) (x_n x_m : node) : iProp Σ:=
  n_in x_n ↦□ (n_val x_n, #(n_out x_n)) ∗
  (⌜x_n = x_m⌝ ∨ ∃x_p : node, n_out x_n ↦□ #(n_in x_p) ∗ Φ x_p x_m).

Lemma Reach_mono : ∀ Φ Ψ,
  □ (∀ x_n x_m, Φ x_n x_m -∗ Ψ x_n x_m) -∗ ∀ x_n x_m, Reach Φ x_n x_m -∗ Reach Ψ x_n x_m.
Proof.
  iIntros (Φ Ψ) "HΦΨ".
  iIntros (x_n x_m) "HReach".
  iDestruct "HReach" as "[Hxn_node [-> | (%x_p & Hxn_to_xp & HΦ)]]".
  - iFrame. by iLeft.
  - iFrame. iRight. iExists x_p. iFrame. by iApply "HΦΨ".
Qed.

Definition Reach' : ((node * node) -> iProp Σ) -> (node * node) -> iProp Σ :=
  uncurry ∘ Reach ∘ curry.

Definition reach x_n x_m := bi_least_fixpoint Reach' (x_n, x_m).

Notation "x_n ⤳ x_m" := (reach x_n x_m)
  (at level 20, format "x_n  ⤳  x_m") : bi_scope.

Instance bimonopred_reach : BiMonoPred Reach'.
Proof.
  split; simpl.
  - iIntros (Φ Ψ HNEΦ HNEΨ) "#HΦΨ".
    iIntros ([x_n x_m]) "HReach'".
    iApply Reach_mono; last done.
    iModIntro.
    iIntros (x_n' x_m') "HΦ".
    by iApply "HΦΨ".
  - solve_proper.
Qed.

(* ---- Results about reach ---- *)

(* reach is persistent *)
Definition Phi_pers (p : prodO nodeO nodeO) : iProp Σ :=
  <pers> bi_least_fixpoint Reach' p.

Local Instance Phi_pers_ne : NonExpansive Phi_pers.
Proof. solve_proper. Qed.

Global Instance reach_persistent x y : Persistent (x ⤳ y).
Proof.
  rewrite /Persistent.
  iIntros "Hx_reach_y".
  iPoseProof (least_fixpoint_iter _ Phi_pers with "[] Hx_reach_y") as "H"; last by iApply "H".
  clear x y.
  iModIntro.
  iIntros ([x y]) "HpersIH".
  rewrite /Reach' /Reach /Phi_pers (least_fixpoint_unfold Reach' (x, y))
          {2}/Reach' /Reach /curry /=.
  iDestruct "HpersIH" as "[#Hx_node [-> | (%x_p & #Hx_to_xp & #HpersIH)]]".
  - iModIntro. iFrame "Hx_node". by iLeft.
  - iModIntro. iFrame "Hx_node". iRight. iExists x_p. iFrame "#".
Qed.

(* Reflexivity of reach *)
Lemma reach_refl : ∀ x_n,
  x_n ⤳ x_n ∗-∗ n_in x_n ↦□ (n_val x_n, #(n_out x_n)).
Proof.
  iIntros (x_n).
  iSplit.
  - iIntros "#Hxn_reach_xn". rewrite /reach least_fixpoint_unfold.
    by iDestruct "Hxn_reach_xn" as "[Hxn_node _]".
  - iIntros "#Hxn_node". rewrite /reach least_fixpoint_unfold.
    iFrame "#". by iLeft.
Qed.

(* Transitivity of reach *)
Definition Phi_trans (p : prodO nodeO nodeO) : iProp Σ := ∀ x_o,
  bi_least_fixpoint Reach' (p.2, x_o) -∗ bi_least_fixpoint Reach' (p.1, x_o).

Local Instance Phi_trans_ne : NonExpansive Phi_trans.
Proof. solve_proper. Qed.

Lemma reach_trans : ∀ x_n x_m x_o,
  x_n ⤳ x_m -∗
  x_m ⤳ x_o -∗
  x_n ⤳ x_o.
Proof.
  iIntros (x_n x_m x_o) "#Hxn_reach_xm".
  unfold reach.
  iPoseProof (least_fixpoint_iter _ Phi_trans with "[] Hxn_reach_xm") as "H"; last by iApply "H".
  iClear (x_o x_n x_m) "Hxn_reach_xm".
  iModIntro.
  iIntros ([x_n x_m]) "HtransIH".
  rewrite /Reach' /reach /Phi_trans /curry /Reach /=.
  iDestruct "HtransIH" as "[#Hxn_node [-> | (%x_p & #Hxn_to_xp & HtransIH)]]".
  - (* Base case: x_n = x_m *)
    iIntros (x_o) "Hxm_reach_xo". done.
  - (* Inductive case: x_n ↦□ x_p, and x_p satisfies transitivity (with x_m) *)
    iIntros (x_o) "Hxm_reach_xo".
    (* We know x_n steps to x_p, so it suffices to show that x_p ⤳ x_o: *)
    rewrite (least_fixpoint_unfold Reach' (x_n, x_o)) {4}/Reach'
            /Reach /curry /=.
    iFrame "Hxn_node".
    iRight.
    iExists x_p.
    iFrame "#".
    (* x_p ⤳ x_o follows by the induction hypothesis *)
    by iApply "HtransIH".
Qed.

(* Both the from and to nodes are indeed nodes *)
Lemma reach_from_is_node : ∀ x_n x_m,
  x_n ⤳ x_m -∗ n_in x_n ↦□ (n_val x_n, #(n_out x_n)).
Proof.
  iIntros (x_n x_m) "Hxn_reach_xm".
  rewrite /reach (least_fixpoint_unfold Reach').
  by iDestruct "Hxn_reach_xm" as "[Hxn_node _]".
Qed.


Definition Phi_to_node (p : prodO nodeO nodeO) : iProp Σ :=
  n_in p.2 ↦□ (n_val p.2, #(n_out p.2)).

Local Instance Phi_to_node_ne : NonExpansive Phi_to_node.
Proof. solve_proper. Qed.

Lemma reach_to_is_node : ∀ x_n x_m,
  x_n ⤳ x_m -∗ n_in x_m ↦□ (n_val x_m, #(n_out x_m)).
Proof.
  iIntros (x_n x_m) "Hxn_reach_xm".
  unfold reach.
  iPoseProof (least_fixpoint_iter _ Phi_to_node with "[] Hxn_reach_xm") as "H"; last by iApply "H".
  clear x_n x_m.
  iModIntro.
  iIntros ([x_n x_m]) "HnodeIH".
  rewrite /Reach' /Reach /Phi_to_node /curry /=.
  by iDestruct "HnodeIH" as "[#Hxn_node [-> | (%x_p & #Hxn_to_xp & #HnodeIH)]]".
Qed.

(* Case distinction for concrete reachability *)
Lemma reach_case : ∀ x_n x_m,
  x_n ⤳ x_m -∗
  (⌜x_n = x_m⌝ ∨ ∃x_p : node, n_out x_n ↦□ #(n_in x_p) ∗ x_p ⤳ x_m).
Proof.
  iIntros (x_n x_m) "Hxn_reach_xm".
  rewrite {1}/reach {1}least_fixpoint_unfold {1}/Reach' /Reach /curry /=.
  iDestruct "Hxn_reach_xm" as "[_ [-> | (%x_p & #Hxn_to_xp & #Hxp_reach_xm)]]".
  - by iLeft.
  - iRight. iExists x_p. iFrame "#".
Qed.

(* If x_n points to none, then it only reaches itself *)
Lemma reach_last : ∀ x_n x_m,
  x_n ⤳ x_m -∗
  n_out x_n ↦ NONEV -∗
  ⌜x_n = x_m⌝ ∗ n_out x_n ↦ NONEV.
Proof.
  iIntros (x_n x_m) "Hxn_reach_xm Hxn_to_none".
  iDestruct (reach_case with "Hxn_reach_xm") as "[Heq | (%x_p & #Hxn_to_xp & _)]"; first by iFrame.
  iCombine "Hxn_to_none Hxn_to_xp" gives "[_ %Hcontra]".
  simplify_eq.
Qed.

(* if both x_n and x_m are nodes and x_n points to x_m, then x_n ⤳ x_m *)
Lemma reach_one_step : ∀ (x_n x_m : nodeO),
  n_in x_n ↦□ (n_val x_n, #(n_out x_n)) -∗
  n_in x_m ↦□ (n_val x_m, #(n_out x_m)) -∗
  n_out x_n ↦□ #(n_in x_m) -∗
  x_n ⤳ x_m.
Proof.
  iIntros (x_n x_m) "#Hxn_node #Hxm_node #Hxn_to_xm".
  rewrite /reach least_fixpoint_unfold {1}/Reach' /Reach /curry /=.
  iFrame "Hxn_node". iRight. iExists x_m. iFrame "#". by iApply reach_refl.
Qed.

(* ----- Abstract Reachability ------ *)
Notation "x ⤏ γ" := (own γ (◯ {[x]}))
  (at level 20, format "x  ⤏  γ") : bi_scope.

Notation "γ ↣ x" := (∃s, own γ (● s) ∗ [∗ set] x_m ∈ s, reach x_m x)%I
  (at level 20, format "γ  ↣  x") : bi_scope.

Lemma Abs_Reach_Alloc: ∀ x,
  x ⤳ x ==∗ ∃ γ, γ ↣ x ∗ x ⤏ γ.
Proof.
  iIntros (x) "#Hx_reach_x".
  iMod (own_alloc (● ({[x]}) ⋅ ◯ ({[x]}))) as (γ) "[Hγ_auth Hγ_ar_x]"; first by apply auth_both_valid_discrete.
  iModIntro.
  iExists γ.
  iFrame "Hγ_ar_x".
  iExists {[x]}.
  iFrame.
  by rewrite big_opS_singleton.
Qed.

Lemma Abs_Reach_Concr: ∀ x_n x_m γ_m,
  x_n ⤏ γ_m -∗
  γ_m ↣ x_m -∗
  x_n ⤳ x_m ∗ γ_m ↣ x_m.
Proof.
  iIntros (x_n x_m γ_m) "#Hxn_ar_γm Hγm_ap_xm".
  iDestruct "Hγm_ap_xm" as "(%s & Hγm_auth & #H_reach_xm)".
  iCombine "Hγm_auth" "Hxn_ar_γm" gives "%Hincluded".
  iSplitR "Hγm_auth"; last by iExists s; iFrame.
  rewrite auth_both_valid_discrete in Hincluded.
  destruct Hincluded as [Hincluded _].
  rewrite gset_included singleton_subseteq_l in Hincluded.
  rewrite (big_opS_delete _ s x_n); last done.
  by iDestruct "H_reach_xm" as "[Hxn_reach_xm _]".
Qed.

Lemma Abs_Reach_Abs: ∀ x_n x_m γ_m,
  x_n ⤳ x_m -∗
  γ_m ↣ x_m ==∗
  x_n ⤏ γ_m ∗ γ_m ↣ x_m.
Proof.
  iIntros (x_n x_m γ_m) "#xn_reach_xm Hγm_ap_xm".
  iDestruct "Hγm_ap_xm" as "(%s & Hγm_auth & #H_reach_xm)".
  (* Is x_n in s? *)
  destruct (decide (x_n ∈ s)) as [ Hxn_in_s | Hxn_notin_s ].
  (* Case: x_n ∈ s. It then follows by auth_update_dfrac_alloc *)
  - iMod (own_update _ _ (● s ⋅ ◯ {[x_n]}) with "Hγm_auth") as "[Hγm_auth #Hxn_ar_γm]".
    + apply (auth_update_dfrac_alloc _ s {[x_n]}).
      rewrite gset_included.
      by apply singleton_subseteq_l.
    + iFrame "Hxn_ar_γm". iExists s. by iFrame.
  (* Case: x_n ∉ s. We update ● s to ● ({[x_n]} ∪ s) ⋅ ◯ ({[x_n]} ∪ s) *)
  - iMod (own_update _ _ (● ({[x_n]} ∪ s) ⋅ ◯ ({[x_n]} ∪ s)) with "Hγm_auth") as "(Hγm_auth & #Hγm_frag)".
    + apply auth_update_alloc.
      apply gset_local_update.
      set_solver.
    + rewrite auth_frag_op.
      iDestruct "Hγm_frag" as "[Hxn_ar_γm _]".
      iFrame "Hxn_ar_γm".
      iExists ({[x_n]} ∪ s).
      iFrame "Hγm_auth".
      iApply big_opS_insert; first done.
      by iFrame "#".
Qed.

Lemma Abs_Reach_Advance: ∀ x_m γ_m x_o,
  γ_m ↣ x_m -∗
  x_m ⤳ x_o ==∗
  γ_m ↣ x_o ∗ x_o ⤏ γ_m.
Proof.
  iIntros (x_m γ_m x_o) "Hγm_ap_xm #Hxm_reach_xo".
  iDestruct "Hγm_ap_xm" as "(%s & Hγm_auth & #H_reach_xm)".
  iMod (own_update _ _ (● ({[x_o]} ∪ s) ⋅ ◯ ({[x_o]} ∪ s)) with "Hγm_auth") as "(Hγm_auth & Hγm_frag)".
  - apply auth_update_alloc.
    apply gset_local_update.
    set_solver.
  - iModIntro.
    rewrite auth_frag_op.
    iDestruct "Hγm_frag" as "[Hxo_ar_γm _]".
    iFrame "Hxo_ar_γm".
    iExists ({[x_o]} ∪ s).
    iFrame "Hγm_auth".
    iAssert ([∗ set] x' ∈ s, x' ⤳ x_o)%I as "H_reach_xo".
    {
      iApply (big_sepS_impl with "H_reach_xm").
      iModIntro.
      iIntros (x) "%Hx_in_s #Hx_reach_xm".
      by iApply reach_trans.
    }
    destruct (decide (x_o ∈ s)) as [ Hxo_in_s | Hxo_notin_s ].
    + assert (Heq: {[x_o]} ∪ s = s); first set_solver.
      by rewrite Heq.
    + iApply (big_opS_union _ {[x_o]} s); first set_solver.
      iSplit; last done.
      rewrite big_opS_singleton.
      iApply reach_refl.
      by iApply reach_to_is_node.
Qed.

(* ----- Queue Invariant ------ *)
Definition queue_invariant (l_head l_tail : loc) (G : Qgnames) : iProp Σ :=
  ∃ xs_v, G.(γ_Abst) ⤇● xs_v ∗ (* Abstract state *)
  ∃ xs xs_queue (x_head x_tail x_last: node), (* Concrete state *)
  ⌜xs = xs_queue ++ [x_head]⌝ ∗
  isLL xs ∗
  ⌜isLast x_last xs⌝ ∗
  (* Relation between concrete and abstract state *)
  ⌜projVal xs_queue = wrapSome xs_v⌝ ∗
  l_head ↦ #(n_in x_head) ∗
  l_tail ↦ #(n_in x_tail) ∗
  G.(γ_Head) ↣ x_head ∗ x_head ⤏ G.(γ_Tail) ∗
  G.(γ_Tail) ↣ x_tail ∗ x_tail ⤏ G.(γ_Last) ∗
  G.(γ_Last) ↣ x_last.

(* ----- The 'isQueue' Predicate ------ *)
Definition isQueue (v_q : val) (G: Qgnames) : iProp Σ :=
  ∃ l_queue l_head l_tail : loc,
  ⌜v_q = #l_queue⌝ ∗
  l_queue ↦□ (#l_head, #l_tail) ∗
  inv Ni (queue_invariant l_head l_tail G).

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
  wp_alloc l_tail as "Hl_tail".
  wp_alloc l_head as "Hl_head".
  iMod (queue_contents_alloc []) as (γ_Abst) "[Hγ_Abst_auth Hγ_Abst_frac]".
  iAssert (x_1 ⤳ x_1)%I as "Hx1_reach_x1"; first by iApply reach_refl.
  iMod (Abs_Reach_Alloc x_1 with "Hx1_reach_x1") as (γ_Head) "[HγHead_ap_x1 _]".
  iMod (Abs_Reach_Alloc x_1 with "Hx1_reach_x1") as (γ_Tail) "[HγTail_ap_x1 #Hx1_ar_γTail]".
  iMod (Abs_Reach_Alloc x_1 with "Hx1_reach_x1") as (γ_Last) "[HγLast_ap_x1 #Hx1_ar_γLast]".
  set (Queue_gnames := {| γ_Abst := γ_Abst;
                          γ_Head := γ_Head;
                          γ_Tail := γ_Tail;
                          γ_Last := γ_Last;
                       |}).
  iMod (inv_alloc Ni _ (queue_invariant l_head l_tail Queue_gnames) with "[Hγ_Abst_auth Hl_head Hl_tail Hx1_to_none HγHead_ap_x1 HγTail_ap_x1 HγLast_ap_x1]") as "#HqueueInv".
  {
    iNext.
    iExists []; iFrame "Hγ_Abst_auth"; simpl.
    iExists [x_1], [], x_1, x_1, x_1; iFrame.
    repeat iSplit; try done.
    by iExists [].
  }
  wp_alloc l_queue as "Hl_queue".
  iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
  iApply ("HΦ" $! #l_queue Queue_gnames).
  iModIntro.
  iFrame.
  iExists l_queue, l_head, l_tail.
  by repeat iSplit.
Qed.

(* ----- Lemma about swining tail (used in both Enqueue and Dequeue) ----- *)
Lemma swing_tail (l_head l_tail : loc) (x_tail x_newtail : node) (G : Qgnames) :
  {{{ inv Ni (queue_invariant l_head l_tail G) ∗ x_tail ⤳ x_newtail ∗ x_newtail ⤏ G.(γ_Last) }}}
    CAS #l_tail #(n_in x_tail) #(n_in x_newtail)
  {{{w, RET w; ⌜w = #true⌝ ∨ ⌜w = #false⌝ }}}.
Proof.
  iIntros (Φ) "(#Hqueue_inv & #Hxtail_reach_xnewtail & #Hxnewtail_ar_γLast) HΦ".
  wp_bind (CmpXchg _ _ _).
  (* Open Invariant *)
  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_ap_xhead & >#Hxhead_ar_γTail & HγTail_ap_xtail' & >#Hxtail'_ar_γLast & HγLast_ap_xlast)".
  wp_cmpxchg as Hxtail_eq | Hxtail_neq.
  - (* CAS succeeded *)
    iAssert (⌜x_tail' = x_tail⌝)%I as "->".
    {
      iPoseProof (reach_from_is_node with "Hxtail_reach_xnewtail") as "Hxtail_node".
      iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_ap_xtail'") as "[#Hxhead_reach_xtail' _]".
      iPoseProof (reach_to_is_node with "Hxhead_reach_xtail'") as "Hxtail'_node".
      iApply n_in_equal; try done.
    }
    iMod (Abs_Reach_Advance with "HγTail_ap_xtail' Hxtail_reach_xnewtail") as "[HγTail_ap_xnew #Hxnew_ar_γTail]".
    iModIntro.
    (* Close Invariant *)
    iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_ap_xhead HγTail_ap_xnew HγLast_ap_xlast".
    {
      iNext.
      iExists xs_v; iFrame "HAbst".
      iExists xs, xs_queue, x_head, x_newtail, x_last; iFrame.
      iFrame "%#".
    }
    wp_pures.
    iApply "HΦ".
    by iLeft.
  - (* CAS failed *)
    iModIntro.
    (* Close Invariant *)
    iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_ap_xhead HγTail_ap_xtail' HγLast_ap_xlast".
    {
      iNext.
      iExists xs_v; iFrame "HAbst".
      iExists xs, xs_queue, x_head, x_tail', x_last; iFrame.
      iFrame "%#".
    }
    wp_pures.
    iApply "HΦ".
    by iRight.
Qed.

(* ----- Specification for Enqueue ----- *)
Lemma enqueue_spec v_q (v : val) (G : Qgnames) (P Q : iProp Σ) :
  □(∀xs_v, (G.(γ_Abst) ⤇● xs_v ∗ P ={⊤ ∖ ↑Ni}=∗ ▷ (G.(γ_Abst) ⤇● (v :: xs_v) ∗ Q))) -∗
  {{{ isQueue v_q G ∗ P}}}
    enqueue v_q v
  {{{ w, RET w; Q }}}.
Proof.
  iIntros "#Hvs".
  iIntros (Φ) "!> [(%l_queue & %l_head & %l_tail & -> &
               #Hl_queue & #Hqueue_inv) HP] HΦ".
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
  wp_closure.
  remember (rec: "loop" "_" := let: "tail" := ! (Snd ! #l_queue) in let: "next" := ! (Snd ! "tail") in if: "next" = InjL #() then if: Snd (CmpXchg (Snd ! "tail") "next" #(n_in x_new)) then Snd (CmpXchg (Snd ! #l_queue) "tail" #(n_in x_new)) else "loop" #() else Snd (CmpXchg (Snd ! #l_queue) "tail" "next");; "loop" #())%V as loop.
  iLöb as "IH".
  rewrite Heqloop.
  wp_pures.
  rewrite <- Heqloop.
  wp_load.
  wp_pures.
  wp_bind (! #l_tail)%E.
  (* Invariant Opening: 1 *)
  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_ap_xhead & >#Hxhead_ar_γTail & HγTail_ap_xtail & >#Hxtail_ar_γLast & HγLast_ap_xlast)".
  wp_load.
  iAssert ((n_in x_tail ↦□ (n_val x_tail, #(n_out x_tail)))%I) as "#Hxtail_node".
  {
    iApply (reach_to_is_node x_head).
    by iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_ap_xtail") as "[Hxhead_reach_xtail _]".
  }
  iModIntro.
  (* Close Invariant: 1 *)
  iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_ap_xhead HγTail_ap_xtail HγLast_ap_xlast".
  {
    iNext.
    iExists xs_v; iFrame "HAbst".
    iExists xs, xs_queue, x_head, x_tail, x_last; iFrame.
    iFrame "%#".
  }
  iClear (Hconc_abst_eq xs_v Hxs_eq x_head HisLast_xlast x_last xs xs_queue) "Hxhead_ar_γTail".
  wp_let.
  wp_load.
  wp_pures.
  wp_bind (! #(n_out x_tail))%E.
  (* Invariant Opening: 2 *)
  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_ap_xhead & >#Hxhead_ar_γTail & HγTail_ap_xtail' & >#Hxtail'_ar_γLast & HγLast_ap_xlast)".
  iPoseProof (Abs_Reach_Concr x_tail x_last (G.(γ_Last)) with "Hxtail_ar_γLast HγLast_ap_xlast") as "[#Hxtail_reach_xlast HγLast_ap_xlast]".
  (* CASE ANALYSIS: Is x_tail last? *)
  iDestruct (reach_case with "Hxtail_reach_xlast") as "[><- | (%x_tail_next & Hxtail_to_xtailnext & Hxtailnext_reach_xlast)]".
  - (* x_tail is last. i.e. x_tail = x_last *)
    iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLLchain_xs]".
    iAssert (▷n_out x_tail ↦ NONEV)%I with "[HisLL_xs]" as "Hxtail_to_none".
    {
      iNext.
      destruct HisLast_xlast as [xs_rest ->].
      by iDestruct "HisLL_xs" as "[Hxtail_to_none _]".
    }
    wp_load.
    iModIntro.
    (* Close Invariant: 2 *)
    iSplitL "Hl_head Hl_tail Hxtail_to_none HAbst HγHead_ap_xhead HγTail_ap_xtail' HγLast_ap_xlast".
    {
      iNext.
      iExists xs_v; iFrame "HAbst".
      iExists xs, xs_queue, x_head, x_tail', x_tail; iFrame.
      iFrame "%#".
      destruct HisLast_xlast as [xs_rest ->].
      by iFrame "#".
    }
    iClear (Hconc_abst_eq xs_v Hxs_eq x_head HisLast_xlast xs xs_queue x_tail') "Hxhead_ar_γTail Hxtail_reach_xlast HisLLchain_xs Hxtail'_ar_γLast".
    wp_let.
    wp_pures.
    wp_load.
    wp_pures.
    (* Attempt to add x_new to linked list *)
    wp_bind (CmpXchg _ _ _).
    (* Invariant Opening: 3 *)
    iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_ap_xhead & >#Hxhead_ar_γTail & HγTail_ap_xtail' & >#Hxtail'_ar_γLast & HγLast_ap_xlast)".
    iPoseProof (Abs_Reach_Concr x_tail x_last (G.(γ_Last)) with "Hxtail_ar_γLast HγLast_ap_xlast") as "[#Hxtail_reach_xlast HγLast_ap_xlast]".
    (* CASE ANALYSIS: Is tail still last? *)
    iDestruct (reach_case with "Hxtail_reach_xlast") as "[><- | (%x_tail_next & Hxtail_to_xtailnext & Hxtailnext_reach_xlast)]"; last first.
    + (* x_tail is no longer last, hence the CAS fails *)
      (* Note: Have to apply wp_cmpxchg_fail manually due to bug. *)
      wp_apply wp_cmpxchg_fail; [ | | iFrame "#" | ]; first done; first solve_vals_compare_safe; iIntros "_".
      iModIntro.
      (* Close Invariant: 3 *)
      iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_ap_xhead HγTail_ap_xtail' HγLast_ap_xlast".
      {
        iNext.
        iExists xs_v; iFrame "HAbst".
        iExists xs, xs_queue, x_head, x_tail', x_last; iFrame.
        iFrame "%#".
      }
      wp_pures.
      iApply ("IH" with "HP HΦ Hxnew_to_none").
    + (* x_tail is still last, hence the CAS succeeds and x_new is added to the linked list. This is a linearisation point *)
      iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLLchain_xs]".
      iAssert (▷n_out x_tail ↦ NONEV)%I with "[HisLL_xs]" as "Hxtail_to_none".
      {
        iNext.
        destruct HisLast_xlast as [xs_rest ->].
        by iDestruct "HisLL_xs" as "[Hxtail_to_none _]".
      }
      wp_cmpxchg_suc. (* Linearisation Point *)
      iMod (pointsto_persist with "Hxtail_to_none") as "#Hxtail_to_xnew".
      iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[HAbst_new HQ]"; first by iFrame.
      iPoseProof (reach_one_step x_tail x_new with "[] [] []") as "Hxtail_reach_xnew"; try done.
      iMod (Abs_Reach_Advance with "HγLast_ap_xlast Hxtail_reach_xnew") as "[HγLast_ap_xnew #Hxnew_ar_γLast]".
      iModIntro.
      (* Close Invariant: 3 *)
      iSplitL "Hl_head Hl_tail Hxnew_to_none HAbst_new HγHead_ap_xhead HγTail_ap_xtail' HγLast_ap_xnew".
      {
        iNext.
        iExists (v :: xs_v); iFrame "HAbst_new".
        iExists (x_new :: xs), (x_new :: xs_queue), x_head, x_tail', x_new; iFrame.
        iFrame "%#".
        repeat iSplit.
        - by rewrite Hxs_eq.
        - destruct HisLast_xlast as [xs_rest ->]. iFrame "#".
        - by iExists xs.
        - iPureIntro. simpl. by f_equal.
      }
      iClear (Hconc_abst_eq xs_v Hxs_eq x_head HisLast_xlast x_tail' xs xs_queue) "HisLLchain_xs Hxhead_ar_γTail Hxtail'_ar_γLast".
      wp_pures.
      wp_load.
      wp_pures.
      (* Attempt to swing tail pointer *)
      wp_apply (swing_tail with "[Hqueue_inv Hxtail_reach_xnew Hxnew_ar_γLast]"); first iFrame "#".
      iIntros (w) "_".
      by iApply "HΦ".
  - (* x_tail is not last *)
    wp_load.
    iPoseProof (reach_from_is_node with "Hxtailnext_reach_xlast") as "Hxtailnext_node".
    iMod (Abs_Reach_Abs with "Hxtailnext_reach_xlast HγLast_ap_xlast") as "[#Hxtailnext_ar_γLast HγLast_ap_xlast]".
    iModIntro.
    (* Close Invariant: 2 *)
    iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_ap_xhead HγTail_ap_xtail' HγLast_ap_xlast".
    {
      iNext.
      iExists xs_v; iFrame "HAbst".
      iExists xs, xs_queue, x_head, x_tail', x_last; iFrame.
      iFrame "%#".
    }
    iClear (Hconc_abst_eq xs_v Hxs_eq x_head HisLast_xlast x_last xs xs_queue x_tail') "Hxhead_ar_γTail Hxtail_reach_xlast Hxtailnext_reach_xlast Hxtail'_ar_γLast".
    wp_let.
    wp_pures.
    wp_load.
    wp_pures.
    iPoseProof (reach_one_step x_tail x_tail_next with "[] [] []") as "Hxtail_reach_xtailnext"; try done.
    (* Attempt to swing tail pointer *)
    wp_apply (swing_tail with "[Hqueue_inv Hxtail_reach_xtailnext Hxtailnext_ar_γLast]"); first iFrame "#".
    iIntros (w) "_".
    wp_pures.
    iApply ("IH" with "HP HΦ Hxnew_to_none").
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
  iIntros "#Hvs".
  iIntros (Φ) "!> [(%l_queue & %l_head & %l_tail & -> &
               #Hl_queue & #Hqueue_inv) HP] HΦ".
  wp_lam.
  wp_closure.
  remember (rec: "loop" "_" := let: "head" := ! (Fst ! #l_queue) in let: "tail" := ! (Snd ! #l_queue) in let: "next" := ! (Snd ! "head") in if: "head" = "tail" then if: "next" = InjL #() then InjLV #() else Snd (CmpXchg (Snd ! #l_queue) "tail" "next");; "loop" #() else let: "value" := Fst ! "next" in if: Snd (CmpXchg (Fst ! #l_queue) "head" "next") then "value" else "loop" #())%V as loop.
  iLöb as "IH".
  rewrite Heqloop.
  wp_pures.
  rewrite <- Heqloop.
  wp_load.
  wp_pures.
  wp_bind (! #l_head)%E.
  (* Invariant Opening: 1 *)
  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_ap_xhead & >#Hxhead_ar_γTail & HγTail_ap_xtail & >#Hxtail_ar_γLast & HγLast_ap_xlast)".
  wp_load.
  iAssert ((n_in x_head ↦□ (n_val x_head, #(n_out x_head)))%I) as "#Hxhead_node".
  {
    iApply (reach_from_is_node x_head x_tail).
    by iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_ap_xtail") as "[Hxhead_reach_xtail _]".
  }
  iPoseProof (reach_refl with "Hxhead_node") as "Hxhead_reach_xhead".
  iMod (Abs_Reach_Abs with "Hxhead_reach_xhead HγHead_ap_xhead") as "[#Hxhead_ar_γHead HγHead_ap_xhead]".
  iPoseProof (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_ap_xtail") as "[#Hxhead_reach_xtail HγTail_ap_xtail]".
  iPoseProof (Abs_Reach_Concr with "Hxtail_ar_γLast HγLast_ap_xlast") as "[#Hxtail_reach_xlast HγLast_ap_xlast]".
  iPoseProof (reach_trans with "Hxhead_reach_xtail Hxtail_reach_xlast") as "Hxhead_reach_xlast".
  iMod (Abs_Reach_Abs with "Hxhead_reach_xlast HγLast_ap_xlast") as "[#Hxhead_ar_γLast HγLast_ap_xlast]".
  iClear "Hxhead_reach_xhead Hxhead_reach_xtail Hxtail_reach_xlast Hxhead_reach_xlast".
  iModIntro.
  (* Close Invariant: 1 *)
  iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_ap_xhead HγTail_ap_xtail HγLast_ap_xlast".
  {
    iNext.
    iExists xs_v; iFrame "HAbst".
    iExists xs, xs_queue, x_head, x_tail, x_last; iFrame.
    iFrame "%#".
  }
  iClear (Hconc_abst_eq xs_v Hxs_eq x_tail HisLast_xlast x_last xs xs_queue) "Hxtail_ar_γLast".
  wp_pures.
  wp_load.
  wp_pures.
  wp_bind (! #l_tail)%E.
  (* Invariant Opening: 2 *)
  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_ap_xhead & >#Hxhead'_ar_γTail & HγTail_ap_xtail & >#Hxtail_ar_γLast & HγLast_ap_xlast)".
  wp_load.
  iAssert ((n_in x_tail ↦□ (n_val x_tail, #(n_out x_tail)))%I) as "#Hxtail_node".
  {
    iApply (reach_to_is_node x_head x_tail).
    by iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_ap_xtail") as "[Hxhead_reach_xtail _]".
  }
  iPoseProof (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_ap_xtail") as "[#Hxhead_reach_xtail HγTail_ap_xtail]".
  iMod (Abs_Reach_Abs with "[] HγTail_ap_xtail") as "[#Hxtail_ar_γTail HγTail_ap_xtail]".
  { by iApply reach_refl. }
  iModIntro.
  (* Close Invariant: 2 *)
  iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_ap_xhead HγTail_ap_xtail HγLast_ap_xlast".
  {
    iNext.
    iExists xs_v; iFrame "HAbst".
    iExists xs, xs_queue, x_head', x_tail, x_last; iFrame.
    iFrame "%#".
  }
  iClear (Hconc_abst_eq xs_v Hxs_eq x_head' HisLast_xlast x_last xs xs_queue) "Hxhead'_ar_γTail".
  wp_let.
  wp_load.
  wp_pures.
  wp_bind (! #(n_out x_head))%E.
  (* Invariant Opening: 3 *)
  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_ap_xhead & >#Hxhead'_ar_γTail & HγTail_ap_xtail & >#Hxtail'_ar_γLast & HγLast_ap_xlast)".
  iPoseProof (Abs_Reach_Concr with "Hxhead_ar_γLast HγLast_ap_xlast") as "[#Hxhead_reach_xlast HγLast_ap_xlast]".
  (* CASE ANALYSIS: Is x_head the last element in the linked list? *)
  iDestruct (reach_case with "Hxhead_reach_xlast") as "[><- | (%x_head_next & Hxhead_to_xheadnext & Hxheadnext_reach_xlast)]".
  - (* x_head is the last element: x_head = x_last. This means that the queue is empty, hence dequeue will return 'None'. This is a linearisation point. *)
    destruct HisLast_xlast as [xs_rest ->].
    iDestruct "HisLL_xs" as "[Hxhead_to_none HisLL_chain_xs]".
    (* x_head ⤳ x_head' *)
    iPoseProof (Abs_Reach_Concr with "Hxhead_ar_γHead HγHead_ap_xhead") as "[Hxhead_reach_xhead' HγHead_ap_xhead]".
    (* x_head ⤳ x_tail' *)
    iPoseProof (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_ap_xtail") as "[Hxhead_reach_xtail' HγTail_ap_xtail]".
    (* x_head = x_head' *)
    iPoseProof (reach_last with "Hxhead_reach_xhead' Hxhead_to_none") as "[><- Hxhead_to_none]".
    (* x_head = x_tail' *)
    iPoseProof (reach_last with "Hxhead_reach_xtail' Hxhead_to_none") as "[><- Hxhead_to_none]".
    (* x_head = x_tail *)
    iPoseProof (reach_last with "Hxhead_reach_xtail Hxhead_to_none") as "[><- Hxhead_to_none]".
    wp_load. (* Linearisation Point *)
    iAssert (⌜xs_queue = []⌝)%I as "->".
    {
      rewrite Hxs_eq.
      destruct (ll_case_first xs_queue) as [->|[x_head_next [xs_queue_rest' ->]]]; first done.
      rewrite <- app_assoc.
      iPoseProof (isLL_chain_split with "HisLL_chain_xs") as "(_ & _ & Hxhead_to_xheadnext & _)".
      iCombine "Hxhead_to_none Hxhead_to_xheadnext" gives "[_ %Hcontra]".
      simplify_eq.
    }
    iAssert (⌜xs_v = []⌝)%I as "->".
    { by destruct xs_v. }
    iMod ("Hvs" $! [] with "[HAbst HP]") as "[(_ & HAbst & HQ) | (%v & %xs_v' & >%Hcontra & HAbst_new & HQ) ]";
    [ by iFrame | |
      (* The abstract state must be empty. Hence the second disjunct is impossible. *)
      exfalso;
      by apply (app_cons_not_nil xs_v' [] v)
    ].
    iModIntro.
    (* Close Invariant: 3 *)
    iSplitL "Hl_head Hl_tail Hxhead_to_none HAbst HγHead_ap_xhead HγTail_ap_xtail HγLast_ap_xlast".
    {
      iNext.
      iExists []; iFrame "HAbst".
      iExists [x_head], [], x_head, x_head, x_head; iFrame.
      iFrame "%#".
      iSplit; first done.
      by iExists [].
    }
    iClear (Hconc_abst_eq xs_rest Hxs_eq) "Hxhead'_ar_γTail Hxtail'_ar_γLast Hxhead_reach_xlast HisLL_chain_xs".
    wp_let.
    wp_pures.
    case_bool_decide; last contradiction.
    wp_if_true.
    wp_pures.
    iModIntro.
    by iApply "HΦ".
  - (* x_head is not the last element *)
    wp_load.
    iPoseProof (reach_from_is_node with "Hxheadnext_reach_xlast") as "Hxheadnext_node".
    iMod (Abs_Reach_Abs with "Hxheadnext_reach_xlast HγLast_ap_xlast") as "[#Hxheadnext_ar_γLast HγLast_ap_xlast]".
    iModIntro.
    (* Close Invariant: 3 *)
    iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_ap_xhead HγTail_ap_xtail HγLast_ap_xlast".
    {
      iNext.
      iExists xs_v; iFrame "HAbst".
      iExists xs, xs_queue, x_head', x_tail', x_last; iFrame.
      iFrame "%#".
    }
    iClear (Hconc_abst_eq xs_v Hxs_eq HisLast_xlast x_head' x_tail' xs_queue xs x_last) "Hxhead'_ar_γTail Hxtail'_ar_γLast Hxhead_reach_xlast Hxheadnext_reach_xlast".
    wp_let.
    wp_pures.
    (* CASE ANALYSIS: is tail lagging behind? *)
    case_bool_decide as His_xhead_xtail_eq.
    + (* n_in x_head = n_in x_tail. I.e. x_tail is lagging behind. Swing it to next *)
      iAssert (⌜x_head = x_tail⌝)%I as "->"; first (iApply n_in_equal; done).
      wp_if_true.
      wp_pures.
      wp_load.
      wp_pures.
      iPoseProof (reach_one_step x_tail x_head_next with "[] [] []") as "Hxtail_reach_xheadnext"; try done.
      (* Swing Tail pointer *)
      wp_apply (swing_tail with "[Hqueue_inv Hxtail_reach_xheadnext Hxheadnext_ar_γLast]"); first iFrame "#".
      iIntros (w) "_".
      wp_pures.
      iApply ("IH" with "HP HΦ").
    + (* x_tail is not lagging behind. Attempt to swing head pointer *)
      wp_if_false.
      wp_load.
      wp_pures.
      wp_load.
      wp_pures.
      wp_bind (CmpXchg _ _ _).
      (* Invariant Opening: 4 *)
      iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_ap_xhead' & >#Hxhead'_ar_γTail & HγTail_ap_xtail' & >#Hxtail'_ar_γLast & HγLast_ap_xlast)".
      wp_cmpxchg as Hxhead_eq | Hxhead_neq.
      * (* CAS succeeded. Head pointer swung to x_head_next. Linearisation point. *)
        iAssert (⌜x_head' = x_head⌝)%I as "->".
        {
          iPoseProof (Abs_Reach_Concr with "Hxhead'_ar_γTail HγTail_ap_xtail'") as "[#Hconcr HγTail_ap_xtail']".
          iApply n_in_equal; try done.
          by iApply reach_from_is_node.
        }
        iAssert (⌜∃xs_queue', xs_queue = xs_queue' ++ [x_head_next]⌝)%I as "[%xs_queue_new ->]".
        {
          destruct (ll_case_first xs_queue) as [->|[x_head_next' [xs_queue' ->]]].
          - (* Queue cannot empty, as x_head doesn't point to none *)
            rewrite Hxs_eq.
            iDestruct "HisLL_xs" as "[Hxhead_to_none _]".
            iCombine "Hxhead_to_xheadnext Hxhead_to_none" gives "[_ %Hcontra]".
            simplify_eq.
          - iExists xs_queue'.
            rewrite Hxs_eq.
            rewrite <- app_assoc.
            iPoseProof (isLL_and_chain with "HisLL_xs") as "[_ HisLL_chain_xs]".
            iDestruct (isLL_chain_split with "HisLL_chain_xs") as "[_ ( #Hxheadnext'_node & #Hxhead_to_xheadnext' & _)]".
            iCombine "Hxhead_to_xheadnext Hxhead_to_xheadnext'" gives "[_ %Hxheadnext_in_eq]".
            iDestruct (n_in_equal with "[] [Hxheadnext_node] [Hxheadnext'_node]") as "%Hxheadnext_eq"; try done.
            by rewrite Hxheadnext_eq.
        }
        iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[(>-> & HAbst & HQ) | (%v & %xs_v' & >%Hxs_v_eq & HAbst_new & HQ) ]";
        [ by iFrame |
          (* The abstract state cannot be empty. Hence the first disjunct is impossible *)
          rewrite projVal_split in Hconc_abst_eq;
          exfalso;
          by apply (app_cons_not_nil (projVal xs_queue_new) [] (n_val x_head_next)) |
        ].
        rewrite Hxs_v_eq projVal_split wrapSome_split in Hconc_abst_eq.
        apply list_last_eq in Hconc_abst_eq as [Hconc_abst_eq Hxheadnext_v_eq].
        rewrite Hxs_eq.
        iDestruct (isLL_split with "HisLL_xs") as "[HisLL_new _]".
        iPoseProof (reach_one_step x_head x_head_next with "[] [] []") as "Hxhead_reach_xheadnext"; try done.
        iMod (Abs_Reach_Advance with "HγHead_ap_xhead' Hxhead_reach_xheadnext") as "[HγHead_ap_xheadnext #Hxheadnext_ar_γHead]".
        iDestruct (reach_case with "Hxhead_reach_xtail") as "[-> | (%x_head_next' & Hxhead_to_xheadnext' & Hxheadnext_reach_xtail) ]"; first contradiction.
        iAssert (⌜x_head_next' = x_head_next⌝)%I as "->".
        {
          iCombine "Hxhead_to_xheadnext Hxhead_to_xheadnext'" gives "[_ %Hxheadnext_in_eq]".
          iApply n_in_equal; try done.
          by iApply reach_from_is_node.
        }
        iAssert (x_head_next ⤳ x_tail')%I as "#Hxheadnext_reach_xtail'".
        {
          iApply (reach_trans with "Hxheadnext_reach_xtail").
          by iDestruct (Abs_Reach_Concr with "Hxtail_ar_γTail HγTail_ap_xtail'") as "[Hxtail_reach_xtail' _]".
        }
        iMod (Abs_Reach_Abs with "Hxheadnext_reach_xtail' HγTail_ap_xtail'") as "[#Hxheadnext_ar_γTail HγTail_ap_xtail']".
        iModIntro.
        (* Close Invariant: 4 *)
        iSplitL "Hl_head Hl_tail HisLL_new HAbst_new HγHead_ap_xheadnext HγTail_ap_xtail' HγLast_ap_xlast".
        {
          iNext.
          iExists xs_v'; iFrame "HAbst_new".
          iExists (xs_queue_new ++ [x_head_next]), xs_queue_new, x_head_next, x_tail', x_last; iFrame.
          iFrame "%#".
          rewrite Hxs_eq in HisLast_xlast.
          rewrite <- app_assoc in HisLast_xlast.
          apply isLast_remove in HisLast_xlast.
          by iSplit.
        }
        wp_pures.
        iApply "HΦ".
        by rewrite Hxheadnext_v_eq.
      * (* CAS failed *)
        iModIntro.
        (* Close Invariant: 4 *)
        iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_ap_xhead' HγTail_ap_xtail' HγLast_ap_xlast".
        {
          iNext.
          iExists xs_v; iFrame "HAbst".
          iExists xs, xs_queue, x_head', x_tail', x_last; iFrame.
          iFrame "%#".
        }
        wp_pures.
        iApply ("IH" with "HP HΦ").
Qed.

End proofs.


Definition lockAndCCFreeMSQ : queue :=
{|
  queue_specs.isQueue Σ _ (_ : inG Σ (authR (gsetUR nodeO))) _ :=
    isQueue (nroot.@"lock-cc-free-MSQ");
  queue_specs.initialize_spec _ _ _ _ := initialize_spec (nroot.@"lock-cc-free-MSQ");
  queue_specs.enqueue_spec _ _ _ _ := enqueue_spec (nroot.@"lock-cc-free-MSQ");
  queue_specs.dequeue_spec _ _ _ _ := dequeue_spec (nroot.@"lock-cc-free-MSQ");
|}.
