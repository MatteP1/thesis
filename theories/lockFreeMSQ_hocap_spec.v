From stdpp Require Import sets countable.
From iris.algebra Require Import excl list agree gset lib.frac_auth.
From iris.bi Require Import fixpoint big_op.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation primitive_laws.
From iris.base_logic.lib Require Import invariants.
From MSQueue Require Import lockFreeMSQ_impl.
From MSQueue Require Import twoLockMSQ_common.
(* TODO: consider changing twolockMSQ_common to common. *)

Section proofs.

Definition node : Type := loc * val * loc.
Definition nodeO : Type := prodO (prodO locO valO) locO.

Context `{!heapGS Σ}.
Context `{!inG Σ (authR (gsetUR nodeO))}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Variable N : namespace.
Notation Ni := (N .@ "internal").

(* Todo: maybe renaming. *)
Definition Reach (Φ : node -> node -> iProp Σ) (x_n x_m : node) : iProp Σ:= 
	n_in x_n ↦□ (n_val x_n, #(n_out x_n)) ∗
	(⌜x_n = x_m⌝ ∨ ∃x_p : node, n_out x_n ↦□ #(n_in x_p) ∗ Φ x_p x_m).

Lemma Reach_mono : forall Φ Ψ,
	□ (∀ x_n x_m, Φ x_n x_m -∗ Ψ x_n x_m) -∗ ∀ x_n x_m, Reach Φ x_n x_m -∗ Reach Ψ x_n x_m.
Proof.
	iIntros (Φ Ψ) "HΦΨ".
	iIntros (x_n x_m) "HReach".
	iDestruct "HReach" as "[Hx_n [-> | (%x_p & Hx_n_out & HΦ)]]".
	- iFrame. by iLeft.
	- iFrame. iRight. iExists x_p. iFrame. by iApply "HΦΨ".
Qed.

Definition Reach' : ((node * node) -> iProp Σ) -> (node * node) -> iProp Σ :=
	uncurry ∘ Reach ∘ curry.

Definition reach x_n x_m := bi_least_fixpoint Reach' (x_n, x_m).

Notation "x_n ⤳ x_m" := (reach x_n x_m)
	(at level 20, format "x_n ⤳ x_m") : bi_scope.

Instance bimonopred_reach : BiMonoPred Reach'.
Proof.
	split; simpl.
	- iIntros (Φ Ψ HNEΦ HNEΨ) "#HΦΨ".
	  iIntros ([x_n x_m]) "HReach". iApply Reach_mono; last done.
	  iModIntro.
	  iIntros (x_n' x_m') "HΦ". by iApply "HΦΨ".
	- solve_proper.
Qed.

Definition Phi_pers (p : prodO nodeO nodeO) : iProp Σ :=
	<pers> bi_least_fixpoint Reach' p.

Local Instance Phi_pers_ne : NonExpansive Phi_pers.
Proof. solve_proper. Qed.


(* TODO: cleanup *)
(* reach is persistent *)
Global Instance reach_persistent x y : Persistent (x ⤳ y).
Proof.
	unfold Persistent.
	iIntros "H".
	iPoseProof (least_fixpoint_iter _ Phi_pers with "[] H") as "H"; last by iApply "H".
	iModIntro.
	iIntros ([y1 y2]) "HReach'".
	rewrite /Reach' /Reach /Phi_pers /=.
	iDestruct "HReach'" as "[#Hpt [-> | (%x_p & #Hpt_out & #Htransx_p)]]".
	- rewrite least_fixpoint_unfold.
	  iModIntro. rewrite /Reach' /Reach /=. iFrame "#". by iLeft.
	- rewrite (least_fixpoint_unfold Reach' (y1, y2)).
	  iModIntro. rewrite {3}/Reach' /Reach /=. iFrame "#".
	  iRight. iExists x_p. iFrame "#".
Qed.

Lemma reach_refl : ∀ x_n,
	x_n ⤳ x_n ∗-∗ n_in x_n ↦□ (n_val x_n, #(n_out x_n)).
Proof.
	iIntros (x_n).
	iSplit.
	- iIntros "Hreach". unfold reach. rewrite least_fixpoint_unfold.
	  by iDestruct "Hreach" as "[H _]".
	- iIntros "Hx_n". unfold reach. rewrite least_fixpoint_unfold.
	  iFrame. by iLeft.
Qed.

Definition Phi_trans (p : prodO nodeO nodeO) : iProp Σ := ∀ x_o,
	bi_least_fixpoint Reach' (p.2, x_o) -∗ bi_least_fixpoint Reach' (p.1, x_o).

Local Instance Phi_trans_ne : NonExpansive Phi_trans.
Proof. solve_proper. Qed.

(* todo: rewrite with ssreflect: rewrite /Reach /=.*)
(* TODO: cleanup *)
Lemma reach_trans : ∀ x_n x_m x_o,
	x_n ⤳ x_m -∗
	x_m ⤳ x_o -∗
	x_n ⤳ x_o.
Proof.
	iIntros (x_n x_m x_o) "Hreachnm".
	unfold reach.
	iPoseProof (least_fixpoint_iter _ Phi_trans with "[] Hreachnm") as "H"; last by iApply "H".
	iModIntro.
	iIntros ([y1 y2]) "Htransy".
	unfold Reach'.
	unfold Reach.
	simpl.
	iDestruct "Htransy" as "[#Hpt [-> | (%x_p & #Hpt_out & Htransx_p)]]".
	- unfold Phi_trans.
	  iIntros (x_o') "H". simpl. done.
	- unfold Phi_trans. simpl.
	  iIntros (x_o') "H". unfold curry. simpl.
	  rewrite (least_fixpoint_unfold Reach' (y1, x_o')).
	  simpl.
	  rewrite /Reach.
	  iFrame "#".
	  iRight.
	  iExists x_p.
	  iFrame "#".
	  by iApply "Htransx_p".
Qed.

Definition Phi_node (p : prodO nodeO nodeO) : iProp Σ :=
	n_in p.2 ↦□ (n_val p.2, #(n_out p.2)).

Local Instance Phi_node_ne : NonExpansive Phi_node.
Proof. solve_proper. Qed.

(* TODO: cleanup *)
Lemma reach_node : ∀ x_n x_m,
	x_n ⤳ x_m -∗ n_in x_m ↦□ (n_val x_m, #(n_out x_m)).
Proof.
	iIntros (x_n x_m) "Hreachnm".
	unfold reach.
	iPoseProof (least_fixpoint_iter _ Phi_node with "[] Hreachnm") as "H"; last by iApply "H".
	iModIntro.
	iIntros ([y1 y2]) "HReach'".
	rewrite /Reach' /Reach /Phi_node /=.
	iDestruct "HReach'" as "[#Hpt [-> | (%x_p & #Hpt_out & #Hnodex_p)]]".
	- done.
	- rewrite /curry /=. done.
Qed.

Lemma reach_case : ∀ x_n x_m,
	x_n ⤳ x_m -∗
	(⌜x_n = x_m⌝ ∨ ∃x_p : node, n_out x_n ↦□ #(n_in x_p) ∗ x_p ⤳ x_m).
Proof.
	iIntros (x_n x_m) "Hreach".
	unfold reach.
	rewrite {1}least_fixpoint_unfold.
	rewrite {1}/Reach' /Reach /=.
	iDestruct "Hreach" as "[#Hpt [-> | (%x_p & #Hpt_out & #Hnodex_p)]]".
	- by iLeft.
	- iRight. iExists x_p. iFrame "#".
Qed.

(* ===== Concurrent Specification for Two-lock M&S Queue ===== *)

(* Ghost variable names *)
Record Qgnames := {γ_Abst 	: gname;
				   γ_Head 	: gname;
				   γ_Tail 	: gname;
				   γ_Last 	: gname;
				  }.

Notation "Q_γ ⤇● xs_v" := (own Q_γ.(γ_Abst) (●F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇● xs_v") : bi_scope.
Notation "Q_γ ⤇◯ xs_v" := (own Q_γ.(γ_Abst) (◯F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇◯ xs_v") : bi_scope.
Notation "Q_γ ⤇[ q ] xs_v" := (own Q_γ.(γ_Abst) (◯F{ q } (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇[ q ] xs_v") : bi_scope.

Lemma queue_contents_frag_agree Q_γ xs_v xs_v' p q :
	Q_γ ⤇[p] xs_v -∗ Q_γ ⤇[q] xs_v' -∗ ⌜xs_v = xs_v'⌝.
Proof.
	iIntros "Hp Hq".
	iCombine "Hp Hq" as "Hpq" gives "%HValid".
	iPureIntro.
	rewrite <- frac_auth_frag_op in HValid.
	rewrite frac_auth_frag_valid in HValid.
	destruct HValid as [_ HAgree].
	by apply to_agree_op_inv_L.
Qed.

Lemma queue_contents_auth_frag_agree Q_γ xs_v xs_v' p :
	Q_γ ⤇● xs_v' -∗ Q_γ ⤇[p] xs_v -∗ ⌜xs_v = xs_v'⌝.
Proof.
	iIntros "Hp Hq".
	iCombine "Hp Hq" as "Hpq" gives "%HValid".
	iPureIntro.
	apply frac_auth_included_total in HValid.
	by apply to_agree_included_L.
Qed.

Lemma queue_contents_op Q_γ xs_v p q :
	Q_γ ⤇[p] xs_v ∗ Q_γ ⤇[q] xs_v ∗-∗ Q_γ ⤇[p + q] xs_v.
Proof.
	iSplit.
	- iIntros "[Hp Hq]".
	  by iCombine "Hp Hq" as "Hpq".
	- iIntros "Hpq".
	  iApply own_op.
	  rewrite <- frac_auth_frag_op.
	  by rewrite agree_idemp.
Qed.

Lemma queue_contents_update Q_γ xs_v xs_v' xs_v'' :
	Q_γ ⤇● xs_v' -∗ Q_γ ⤇◯ xs_v ==∗ Q_γ ⤇● xs_v'' ∗ Q_γ ⤇◯ xs_v''.
Proof.
	iIntros "Hauth Hfrag".
	iCombine "Hauth Hfrag" as "Hcombined".
	rewrite <- own_op.
	iApply (own_update with "Hcombined").
	by apply frac_auth_update_1.
Qed.

Notation "x ⤏ γ" := (own γ (◯ {[x]}))
	(at level 20, format "x ⤏ γ") : bi_scope.

Notation "γ ↣ x" := (∃s, own γ (● s) ∗ [∗ set] x_m ∈ s, reach x_m x)%I
	(at level 20, format "γ ↣ x") : bi_scope.

(* TODO: cleanup *)
Lemma Abs_Reach_Alloc: forall x,
	x ⤳ x ==∗ ∃ γ, γ ↣ x ∗ x ⤏ γ.
Proof.
	iIntros (x) "#HxRx".
	iMod (own_alloc (● ({[x]}) ⋅ ◯ ({[x]}))) as (γ_reach) "[Hγ_Reach_auth Hγ_Reach_frac]"; first by apply auth_both_valid_discrete.
	iModIntro.
	iExists γ_reach.
	iFrame "Hγ_Reach_frac".
	iExists {[x]}.
	iFrame.
	by rewrite big_opS_singleton.
Qed.

(* TODO: cleanup *)
Lemma Abs_Reach_Concr: forall x_n x_m γ_m,
	x_n ⤏ γ_m -∗
	γ_m ↣ x_m -∗
	x_n ⤳ x_m ∗ γ_m ↣ x_m.
Proof.
	iIntros (x_n x_m γ_m) "#Har Hap".
	iDestruct "Hap" as "(%s & Hauth & #HB_reach)".
	iCombine "Hauth" "Har" gives "%Hincluded".
	rewrite auth_both_valid_discrete in Hincluded.
	destruct Hincluded as [Hincluded _].
	iAssert (x_n ⤳ x_m)%I as "Hxn_reach_xm".
	{
		rewrite (big_opS_delete _ s x_n).
		- by iDestruct "HB_reach" as "[Hreach _]".
		- rewrite gset_included in Hincluded.
		  by apply singleton_subseteq_l.
	}
	iFrame "Hxn_reach_xm".
	iExists s.
	by iFrame.
Qed.

(* TODO: cleanup *)
Lemma Abs_Reach_Abs: forall x_n x_m γ_m,
	x_n ⤳ x_m -∗
	γ_m ↣ x_m ==∗
	x_n ⤏ γ_m ∗ γ_m ↣ x_m.
Proof.
	iIntros (x_n x_m γ_m) "#Hconcr Hap".
	iDestruct "Hap" as "(%s & Hauth & #HB_reach)".
	(* Is x_n in s? *)
	destruct (decide (x_n ∈ s)) as [ Hin | Hnotin ].
	(* Case: x_n ∈ s. It then follows by auth_update_dfrac_alloc *)
	- iMod (own_update _ _ (● s ⋅ ◯ {[x_n]}) with "Hauth") as "[Hauth Hfrag]".
	  + apply (auth_update_dfrac_alloc _ s {[x_n]}).
		rewrite gset_included.
	  	by apply singleton_subseteq_l.
	  + iFrame "Hfrag". iExists s. by iFrame "#".
	(* Case: x_n ∉ s. We update ● s to ● ({[x_n]} ∪ s) ⋅ ◯ ({[x_n]} ∪ s) *)
	- iMod (own_update _ _ (● ({[x_n]} ∪ s) ⋅ ◯ ({[x_n]} ∪ s)) with "Hauth") as "(Hauth & Hfrag)".
	  + apply auth_update_alloc.
	    apply gset_local_update.
		set_solver.
	  + rewrite auth_frag_op.
	  	iDestruct "Hfrag" as "[Hfrag _]".
		iFrame "Hfrag".
		iExists ({[x_n]} ∪ s).
		iFrame "Hauth".
		iApply big_opS_insert; first done.
		by iFrame "#".
Qed.

(* TODO: cleanup *)
Lemma Abs_Reach_Advance: forall x_m γ_m x_o,
	γ_m ↣ x_m -∗
	x_m ⤳ x_o ==∗
	γ_m ↣ x_o ∗ x_o ⤏ γ_m.
Proof.
	iIntros (x_m γ_m x_o) "Hap #Hxm_to_xo".
	iDestruct "Hap" as "(%s & Hauth & #HB_reach)".
	iMod (own_update _ _ (● ({[x_o]} ∪ s) ⋅ ◯ ({[x_o]} ∪ s)) with "Hauth") as "(Hauth & Hfrag)".
	- apply auth_update_alloc.
	  apply gset_local_update.
	  set_solver.
	- rewrite auth_frag_op.
	  iDestruct "Hfrag" as "[Hfrag _]".
	  iFrame "Hfrag".
	  iExists ({[x_o]} ∪ s).
	  iFrame "Hauth".
	  destruct (decide (x_o ∈ s)) as [ Hin | Hnotin ].
	  + assert (Heq: {[x_o]} ∪ s = s); first set_solver.
	    rewrite Heq.
		iApply (big_sepS_impl with "HB_reach").
		do 2 iModIntro.
		iIntros (x) "%Hxin #Hx_to_xm".
		by iApply reach_trans.
	  + iApply (big_opS_union _ {[x_o]} s); first set_solver.
	  	iModIntro.
		iSplit.
		* rewrite big_opS_singleton.
		  iApply reach_refl.
		  by iApply reach_node.
		* iApply (big_sepS_impl with "HB_reach").
		  iModIntro.
		  iIntros (x) "%Hxin #Hx_to_xm".
		  by iApply reach_trans.
Qed.

Definition queue_invariant (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, Q_γ ⤇● xs_v ∗ (* Abstract state *)
	∃ xs xs_queue (x_head x_tail x_last: (loc * val * loc)), (* Concrete state *)
	⌜xs = xs_queue ++ [x_head]⌝ ∗
	isLL xs ∗
	⌜isLast x_last xs⌝ ∗
	(* Relation between concrete and abstract state *)
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	l_head ↦ #(n_in x_head) ∗
	l_tail ↦ #(n_in x_tail) ∗
	Q_γ.(γ_Head) ↣ x_head ∗ x_head ⤏ Q_γ.(γ_Tail) ∗
	Q_γ.(γ_Tail) ↣ x_tail ∗ x_tail ⤏ Q_γ.(γ_Last) ∗
	Q_γ.(γ_Last) ↣ x_last.

Definition is_queue (v_q : val) (Q_γ: Qgnames) : iProp Σ :=
	∃ l_queue l_head l_tail : loc,
	⌜v_q = #l_queue⌝ ∗
	l_queue ↦□ (#l_head, #l_tail) ∗
	inv Ni (queue_invariant l_head l_tail Q_γ).

(* is_queue is persistent *)
Global Instance is_queue_persistent v_q Q_γ : Persistent (is_queue v_q Q_γ).
Proof. apply _. Qed.

Lemma initialize_spec:
	{{{ True }}}
		initialize #()
	{{{ v_q Q_γ, RET v_q; is_queue v_q Q_γ ∗
						  Q_γ ⤇◯ [] }}}.
Proof.
	iIntros (Φ) "_ HΦ".
	wp_lam.
	wp_pures.
	wp_alloc l_1_out as "Hl_1_out".
	wp_alloc l_1_in as "Hl_1_in".
	wp_pures.
	iMod (pointsto_persist with "Hl_1_in") as "#Hl_1_in".
	wp_alloc l_tail as "Hl_tail".
	wp_alloc l_head as "Hl_head".
	iMod (own_alloc (●F (to_agree []) ⋅ ◯F (to_agree []))) as (γ_Abst) "[Hγ_Abst_auth Hγ_Abst_frac]"; first by apply frac_auth_valid.
	iAssert ((l_1_in, NONEV, l_1_out) ⤳ (l_1_in, NONEV, l_1_out))%I as "Hreach"; first by iApply reach_refl.
	iMod (Abs_Reach_Alloc (l_1_in, InjLV #(), l_1_out) with "Hreach") as (γ_Head) "[Hγ_Head _]".
	iMod (Abs_Reach_Alloc (l_1_in, InjLV #(), l_1_out) with "Hreach") as (γ_Tail) "[Hγ_Tail #HAbstReach_γ_Tail]".
	iMod (Abs_Reach_Alloc (l_1_in, InjLV #(), l_1_out) with "Hreach") as (γ_Last) "[Hγ_Last #HAbstReachγ_Last]".
	set (Queue_gnames := {| γ_Abst := γ_Abst;
							γ_Head := γ_Head;
							γ_Tail := γ_Tail;
							γ_Last := γ_Last;
					|}).
	iMod (inv_alloc Ni _ (queue_invariant l_head l_tail Queue_gnames) with "[Hγ_Abst_auth Hl_head Hl_tail Hl_1_in Hl_1_out Hγ_Head Hγ_Tail Hγ_Last]") as "#HqueueInv".
	{
		iNext. iExists []; iFrame; simpl.
		iExists [(l_1_in, NONEV, l_1_out)], [], (l_1_in, NONEV, l_1_out), (l_1_in, NONEV, l_1_out), (l_1_in, NONEV, l_1_out); iFrame.
		do 2 (iSplit; first done).
		iSplit; first by iExists [].
		iSplit; first done.
		iFrame "HAbstReach_γ_Tail HAbstReachγ_Last".
	}
	wp_alloc l_queue as "Hl_queue".
	iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
	iApply ("HΦ" $! #l_queue Queue_gnames).
	iModIntro.
	iFrame.
	iExists l_queue, l_head, l_tail.
	by repeat iSplit.
Qed.

Lemma enqueue_spec v_q (v : val) (Q_γ : Qgnames) (P Q : iProp Σ) :
	□(∀xs_v, (Q_γ ⤇● xs_v ∗ P ={⊤ ∖ ↑Ni}=∗ ▷ (Q_γ ⤇● (v :: xs_v) ∗ Q))) -∗
	{{{ is_queue v_q Q_γ ∗ P}}}
		enqueue v_q v
	{{{ w, RET w; Q }}}.
Proof.
	iIntros "#Hvs".
	iIntros (Φ) "!> [(%l_queue & %l_head & %l_tail & -> &
				 #Hl_queue & #Hqueue_inv) HP] HΦ".
	wp_lam.
	wp_let.
	wp_pures.
	wp_alloc l_new_out as "Hl_new_out".
	wp_alloc l_new_in as "Hl_new_in".
	iMod (pointsto_persist with "Hl_new_in") as "#Hl_new_in".
	set x_new := (l_new_in, SOMEV v, l_new_out).
	change l_new_in with (n_in x_new).
	change l_new_out with (n_out x_new).
	change (SOMEV v) with (n_val x_new).
	wp_let.
	wp_pures.
	set loop := (rec: "loop" "_" := let: "tail" := ! (Snd ! #l_queue) in let: "next" := ! (Snd ! "tail") in if: "tail" = ! (Snd ! #l_queue) then if: "next" = InjL #() then if: Snd (CmpXchg (Snd ! "tail") "next" #l_new_in) then Snd (CmpXchg (Snd ! #l_queue) "tail" #l_new_in) else "loop" #() else Snd (CmpXchg (Snd ! #l_queue) "tail" "next");; "loop" #() else "loop" #())%V.
	iLöb as "IH".
	wp_load.
	wp_pures.
	wp_bind (! #l_tail)%E.
	(* First Invariant Opening *)
	iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead_ar_γTail & HγTail_pt_xtail & >#Hxtail_ar_γLast & HγLast_pt_xlast)".
	wp_load.
	(* iPoseProof (isLL_and_chain with "HisLL_xs1") as "[HisLL_xs1 #HisLL_chain_xs1]". *)
	iAssert ((n_in x_tail ↦□ (n_val x_tail, #(n_out x_tail)))%I) as "#Hxtail_node".
	{
		iApply (reach_node x_head).
		by iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_pt_xtail") as "[Hxhead_reach_xtail _]".
	}
	iModIntro.
	(* Close invariant*)
	iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
	{
		iNext.
		iExists xs_v; iFrame "HAbst".
		iExists xs, xs_queue, x_head, x_tail, x_last; iFrame.
		iFrame "%#".
	}
	(* TODO: possibly add more *)
	iClear (Hconc_abst_eq xs_v Hxs_eq x_head HisLast_xlast x_last xs xs_queue) "Hxhead_ar_γTail".
	wp_let.
	wp_load.
	wp_pures.
	wp_bind (! #(n_out x_tail))%E.
	(* Second Invariant Opening *)
	iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead_ar_γTail & HγTail_pt_xtail & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
	iPoseProof (Abs_Reach_Concr x_tail x_last (Q_γ.(γ_Last)) with "Hxtail_ar_γLast HγLast_pt_xlast") as "[#Hxtail_reach_xlast HγLast_pt_xlast]".
	(* CASE ANALYSIS: Is x_tail last? *)
	iDestruct (reach_case with "Hxtail_reach_xlast") as "[>%Htail_last_eq | (%x_m & Hxtail_out & Hxm_reach_xlast)]".
	- (* x_tail is last. i.e. x_tail = x_last *)
	  admit.
	- (* x_tail is not last *)
	  admit.
	(* BELOW IS OLD *)
	destruct Hxs2tail as [HisLast_xs2 |Hxs2eq].
	- destruct HisLast_xs2 as [xs_fromtail Hxs2eq].
	  rewrite Hxs2eq.
	  iDestruct "HisLL_xs2" as "[Hl_tailout #HisLL_chain_xs2]".
	  wp_load.
	  iModIntro.
	  iSplitL "Hl_head Hl_tail Hl_tailout Hcurr HAbst".
	  {
		iNext.
		iExists xs_v; iFrame "HAbst".
		rewrite <- Hxs2eq.
		iExists xs2, xs2_queue, xs2_old, x_head, x_tail'; iFrame.
		iSplit; first done.
		rewrite Hxs2eq.
		iFrame.
		iSplit; first done.
		iSplit; first done.
		rewrite <- Hxs2eq.
		done.
	  }
	  (* TODO: possibly add more *)
	  iClear (Hconc_abst_eq xs_v Heq_xs2 x_head) "".
	  wp_let.
	  (* consistency check *)
	  wp_load.
	  wp_pures.
	  (* Third Invariant Opening *)
	  wp_bind (! #l_tail)%E.
	  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs3 & %xs3_queue & %xs3_old & %x_head & %x_tail'' & >Hcurr & >%Heq_xs3 & HisLL_xs3 & >%Hconc_abst_eq & Hl_head & Hl_tail & >%Hx_tail''_in_xs3)".
	  wp_load.
	  iModIntro.
	  iSplitL "Hl_head Hl_tail HisLL_xs3 Hcurr HAbst".
	  {
		iNext.
		iExists xs_v; iFrame "HAbst".
		iExists xs3, xs3_queue, xs3_old, x_head, x_tail''; iFrame.
		iSplit; first done.
		iSplit; first done.
		done.
	  }
	  (* TODO: possibly add more *)
	  iClear (Hconc_abst_eq xs_v Heq_xs3 x_head) "".
	  wp_pures.
	  case_bool_decide; wp_if.
	  + (* Consistent*)
		wp_pures.
		wp_load.
		wp_pures.
		wp_bind (CmpXchg _ _ _).
		iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs4 & %xs4_queue & %xs4_old & %x_head & %x_tail''' & >Hcurr & >%Heq_xs4 & HisLL_xs4 & >%Hconc_abst_eq & Hl_head & Hl_tail & >%Hx_tail'''_in_xs4)".
		iAssert (∃xs_diff', ⌜xs4 = xs_diff' ++ xs1⌝)%I with "[Hcurr Hsnap1]" as "(%xs_diff' & %Hxs4xs1_eq)"; first by (iApply (current_and_snapshot Q_γ xs4 xs1 with "Hcurr Hsnap1")).
		assert (Hxs4tail: isLast x_tail xs4 \/ ∃xs x_next xs', xs4 = xs ++ x_next :: x_tail :: xs').
		{
			destruct xs_diff' as [ | x_last xs_diff''].
			- simpl in Hxs4xs1_eq.
			rewrite Hxs4xs1_eq in Hx_tail_in_xs1 *.
			destruct (In_split x_tail xs1 Hx_tail_in_xs1) as [xs1' [xs1'' Heq]].
			destruct xs1' as [| x' xs1'2].
			+ left. rewrite Heq. by exists xs1''.
			+ right.
				destruct (exists_first (x' :: xs1'2)) as [x_first [xs1'2_rest Hx_first]]; first done. 
				exists xs1'2_rest, x_first, xs1''. rewrite Hx_first in Heq.
				rewrite Heq. by rewrite <- app_assoc.
			- right. 
			destruct (In_split x_tail xs1 Hx_tail_in_xs1) as [xs1' [xs1'' Heq]].
			destruct xs1' as [| x' xs1'2].
			+ destruct (exists_first (x_last :: xs_diff'')) as [x_first [xs_diff''' Hx_first]]; first done. 
			exists xs_diff''', x_first, xs1''.
			rewrite Hxs4xs1_eq. rewrite Hx_first.
			rewrite <- app_assoc.
			by rewrite Heq.
			+ destruct (exists_first (x' :: xs1'2)) as [x_first [xs1'2_rest Hx_first]]; first done. 
			exists (x_last :: xs_diff'' ++ xs1'2_rest), x_first, xs1''.
			rewrite Hxs4xs1_eq. 
			rewrite Heq.
			rewrite Hx_first.
			rewrite <- (app_assoc (x_last :: xs_diff'') xs1'2_rest _) .
			f_equal.
			rewrite <- app_assoc. auto.
		}
		destruct Hxs4tail as [HisLast_xs4 | Hxs4eq].
		* destruct HisLast_xs4 as [xs_fromtail' Hx_tail_last].
		  rewrite Hx_tail_last.
		  iDestruct "HisLL_xs4" as "[Hx_tail_out #HisLL_chain_xs4]".
		  wp_cmpxchg_suc.
		  iMod (pointsto_persist with "Hx_tail_out") as "#Hx_tail_out".
		  set xs_new := x_new :: xs4.
		  iAssert (isLL xs_new) with "[Hl_new_out HisLL_chain_xs4]" as "HisLL_xs_new".
		  {
			unfold xs_new, isLL. iFrame. rewrite Hx_tail_last. unfold isLL_chain; auto.
		  }
		  iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[HAbst_new HQ]"; first by iFrame.
		  iMod (current_update Q_γ xs4 x_new with "[Hcurr]") as "Hcurr_upd"; first by rewrite Hx_tail_last.
		  fold xs_new.
		  iPoseProof (get_snapshot with "Hcurr_upd") as "[Hcurr_upd Hsnapnew]".
		  iModIntro.
		  iSplitL "Hl_head Hl_tail HisLL_xs_new HAbst_new Hcurr_upd".
		  {
			iNext.
			iExists (v :: xs_v); iFrame "HAbst_new".
			iExists xs_new, (x_new :: xs4_queue), xs4_old, x_head, x_tail'''.
			iFrame "Hcurr_upd".
			iSplit. { iPureIntro. unfold xs_new. cbn. rewrite Heq_xs4. auto. }
			iFrame.
			iSplit. { iPureIntro. simpl. f_equal. done. }
			unfold xs_new.
			simpl.
			by iRight.
		  }
		  (* TODO: possibly add more *)
	  	  iClear (Hconc_abst_eq xs_v Heq_xs4 x_head) "".
		  wp_pures.
		  wp_load.
		  wp_pures.
		  wp_bind (CmpXchg _ _ _).
		  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs5 & %xs5_queue & %xs5_old & %x_head & %x_tail'''' & >Hcurr & >%Heq_xs5 & HisLL_xs5 & >%Hconc_abst_eq & Hl_head & Hl_tail & >%Hx_tail''''_in_xs5)".
		  wp_cmpxchg as H1 | H2.
		  ** iModIntro.
		  	 iDestruct (current_and_snapshot Q_γ xs5 xs_new with "Hcurr Hsnapnew") as "(%xs5_diff & %Hxs5xsnew_eq)".
			 iSplitL "Hl_head Hl_tail HisLL_xs5 HAbst Hcurr".
			{
				iNext.
				iExists xs_v; iFrame "HAbst".
				iExists xs5, xs5_queue, xs5_old, x_head, x_new; iFrame.
				iSplit; first done.
				iSplit; first done.
				rewrite Hxs5xsnew_eq.
				iPureIntro.
				apply in_or_app.
				right.
				unfold xs_new.
				by left.
			}
			wp_pures.
			by iApply "HΦ".
		  ** iModIntro.
		  	 iDestruct (current_and_snapshot Q_γ xs5 xs_new with "Hcurr Hsnapnew") as "(%xs5_diff & %Hxs5xsnew_eq)".
			 iSplitL "Hl_head Hl_tail HisLL_xs5 HAbst Hcurr".
			{
				iNext.
				iExists xs_v; iFrame "HAbst".
				iExists xs5, xs5_queue, xs5_old, x_head, x_tail''''; iFrame.
				iSplit; first done.
				iSplit; first done.
				done.
			}
			wp_pures.
			by iApply "HΦ".
		  (* TODO: prove. Note: Very confident this branch is provable. *)
		* destruct Hxs4eq as (xs4' & x_next & xs4'' & Heq).
		  iPoseProof (isLL_and_chain with "HisLL_xs4") as "[HisLL_xs4 #HisLL_chain_xs4]".
		  iAssert (▷(isLL_chain [x_next; x_tail]))%I as "HisLLchain_x_next_x_tail".
		  {
			iNext. rewrite Heq.
			iDestruct (isLL_chain_split with "HisLL_chain_xs4") as "[_ Hchain]".
			iDestruct (isLL_chain_split [x_next; x_tail] xs4'' with "Hchain") as "[Hchain' _]". done.
		  }
		  iDestruct "HisLLchain_x_next_x_tail" as "(_ & Hx_tail_out & _)".
		  (* NOTE: Have to do this to make wp_cmpxchg_fail find the pointsto predicate due to a bug *)
		  wp_apply wp_cmpxchg_fail; [ | | iFrame "#" | ].
		  done.
		  solve_vals_compare_safe.
		  iIntros "_".
		  iModIntro.
		  iSplitL "Hl_head Hl_tail HisLL_xs4 Hcurr HAbst".
		  {
			iNext.
			iExists xs_v; iFrame "HAbst".
			iExists xs4, xs4_queue, xs4_old, x_head, x_tail'''; iFrame.
			iSplit; first done.
			iSplit; first done.
			done.
		  }
		  wp_pures.
		  wp_lam.
		  iApply ("IH" with "HP HΦ Hl_new_out").
	  + (* Inconsistent*)
		wp_lam.
		iApply ("IH" with "HP HΦ Hl_new_out").
	- destruct Hxs2eq as [xs [x_next [xs' Heq]]].
	  iPoseProof (isLL_and_chain with "HisLL_xs2") as "[HisLL_xs2 #HisLL_chain_xs2]".
	  iAssert (▷(isLL_chain [x_next; x_tail]))%I as "Hchain".
	  {
		iNext. rewrite Heq.
		iDestruct (isLL_chain_split xs (x_next :: x_tail :: xs') with "HisLL_chain_xs2") as "[_ Hchain]".
		iDestruct (isLL_chain_split [x_next; x_tail] xs' with "Hchain") as "[Hchain' _]".
		done. 
	  }
	  iDestruct "Hchain" as "(Hx_next & Hx_tail_x_next & _)".
	  wp_load.
	  iPoseProof (get_snapshot with "Hcurr") as "[Hcurr Hsnap2]".
	  iModIntro.
	  iSplitL "Hl_head Hl_tail HisLL_xs2 Hcurr HAbst".
	{
		iNext.
		iExists xs_v; iFrame "HAbst".
		iExists (xs2_queue ++ [x_head] ++ xs2_old), xs2_queue, xs2_old, x_head, x_tail'; iFrame.
		rewrite Heq_xs2.
		iFrame.
		iSplit; first done.
		iSplit; first done.
		rewrite Heq_xs2 in Hx_tail'_in_xs2.
		done.
	}
	(* TODO: possibly add more *)
	iClear (Hconc_abst_eq xs_v Heq_xs2 x_head) "".
	wp_let.
	(* consistency check *)
	wp_load.
	wp_pures.
	(* Third Invariant Opening *)
	wp_bind (! #l_tail)%E.
	iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs3 & %xs3_queue & %xs3_old & %x_head & %x_tail'' & >Hcurr & >%Heq_xs3 & HisLL_xs3 & >%Hconc_abst_eq & Hl_head & Hl_tail & >%Hx_tail''_in_xs3)".
	wp_load.
	iModIntro.
	iSplitL "Hl_head Hl_tail HisLL_xs3 Hcurr HAbst".
	{
		iNext.
		iExists xs_v; iFrame "HAbst".
		iExists xs3, xs3_queue, xs3_old, x_head, x_tail''; iFrame.
		iSplit; first done.
		iSplit; first done.
		done.
	}
	(* TODO: possibly add more *)
	iClear (Hconc_abst_eq xs_v Heq_xs3 x_head) "".
	wp_pures.
	case_bool_decide; wp_if.
	+ (* Consistent*)
		wp_pures.
		wp_load.
		wp_pures.
		wp_bind (CmpXchg _ _ _).
		iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs4 & %xs4_queue & %xs4_old & %x_head & %x_tail''' & >Hcurr & >%Heq_xs4 & HisLL_xs4 & >%Hconc_abst_eq & Hl_head & Hl_tail & >%Hx_tail'''_in_xs4)".
		wp_cmpxchg as H1 | H2.
		* iModIntro.
		  iAssert (⌜x_tail''' = x_tail⌝)%I as "->".
		  {
			iPoseProof (isLL_and_chain with "HisLL_xs4") as "[HisLL_xs4 #HisLL_chain_xs4]".
			iApply n_in_equal; auto.
			destruct (In_split x_tail''' xs4 Hx_tail'''_in_xs4) as [xs4' [xs4'' Heq4]].
			rewrite Heq4.
			by iApply (isLL_chain_node xs4' x_tail''' xs4'' with "[HisLL_chain_xs4]").
		  }
		  iDestruct (current_and_snapshot Q_γ xs4 xs2 with "Hcurr Hsnap2") as "(%xs4_diff & %Hxs4xs2_eq)".
		  iSplitL "Hl_head Hl_tail HisLL_xs4 Hcurr HAbst".
		  {
			iNext.
			iExists xs_v; iFrame "HAbst".
			iExists xs4, xs4_queue, xs4_old, x_head, x_next; iFrame.
			iSplit; first done.
			iSplit; first done.
			rewrite Hxs4xs2_eq.
			rewrite Heq.
			iPureIntro.
			apply in_or_app.
			right.
			apply in_or_app.
			right.
			apply in_eq.
		  }
		  wp_pures.
		  wp_lam.
		  iApply ("IH" with "HP HΦ Hl_new_out"). 
		* iModIntro.
		  iSplitL "Hl_head Hl_tail HisLL_xs4 Hcurr HAbst".
			{
				iNext.
				iExists xs_v; iFrame "HAbst".
				iExists xs4, xs4_queue, xs4_old, x_head, x_tail'''; iFrame.
				iSplit; first done.
				iSplit; first done.
				done.
			}
		  wp_pures.
		  wp_lam.
		  iApply ("IH" with "HP HΦ Hl_new_out"). 
	+ (* Inconsistent*)
		wp_lam.
		iApply ("IH" with "HP HΦ Hl_new_out").
Qed.


Lemma dequeue_spec v_q (Q_γ : Qgnames) (P : iProp Σ) (Q : val -> iProp Σ):
	□(∀xs_v, (Q_γ ⤇● xs_v ∗ P
				={⊤ ∖ ↑Ni}=∗
				▷ (( ⌜xs_v = []⌝ ∗ Q_γ ⤇● xs_v ∗ Q NONEV) ∨
				(∃x_v xs_v', ⌜xs_v = xs_v' ++ [x_v]⌝ ∗ Q_γ ⤇● xs_v' ∗ Q (SOMEV x_v)))
			)
	 )
	-∗
	{{{ is_queue v_q Q_γ ∗ P }}}
		dequeue v_q
	{{{ v, RET v; Q v }}}.
Proof.
	Admitted.

End proofs.

Notation "Q_γ ⤇● xs_v" := (own Q_γ.(γ_Abst) (●F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇● xs_v") : bi_scope.
Notation "Q_γ ⤇◯ xs_v" := (own Q_γ.(γ_Abst) (◯F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇◯ xs_v") : bi_scope.
Notation "Q_γ ⤇[ q ] xs_v" := (own Q_γ.(γ_Abst) (◯F{ q } (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇[ q ] xs_v") : bi_scope.
