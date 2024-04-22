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

Lemma reach_from_is_node : ∀ x_n x_m,
	x_n ⤳ x_m -∗ n_in x_n ↦□ (n_val x_n, #(n_out x_n)).
Proof.
	iIntros (x_n x_m) "Hreach".
	unfold reach.
	rewrite (least_fixpoint_unfold Reach').
	by iDestruct "Hreach" as "[Hnode _]".
Qed.

Definition Phi_node (p : prodO nodeO nodeO) : iProp Σ :=
	n_in p.2 ↦□ (n_val p.2, #(n_out p.2)).

Local Instance Phi_node_ne : NonExpansive Phi_node.
Proof. solve_proper. Qed.

(* TODO: cleanup *)
Lemma reach_to_is_node : ∀ x_n x_m,
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

Lemma reach_end_eq : ∀ x_n x_m,
	x_n ⤳ x_m -∗
	n_out x_n ↦ NONEV -∗
	⌜x_n = x_m⌝ ∗ n_out x_n ↦ NONEV.
Proof.
	iIntros (x_n x_m) "Hreach Hxn_out".
	iDestruct (reach_case with "Hreach") as "[Heq | (%x_o & Hxn_out' & Hxo_reach_xm)]"; first by iFrame. 
	iCombine "Hxn_out Hxn_out'" gives "[_ %Hcontra]".
	simplify_eq.
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
		  by iApply reach_to_is_node.
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
	(* Invariant Opening: 1 *)
	iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead_ar_γTail & HγTail_pt_xtail & >#Hxtail_ar_γLast & HγLast_pt_xlast)".
	wp_load.
	iAssert ((n_in x_tail ↦□ (n_val x_tail, #(n_out x_tail)))%I) as "#Hxtail_node".
	{
		iApply (reach_to_is_node x_head).
		by iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_pt_xtail") as "[Hxhead_reach_xtail _]".
	}
	iModIntro.
	(* Close Invariant: 1 *)
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
	(* Invariant Opening: 2 *)
	iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead_ar_γTail & HγTail_pt_xtail' & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
	iPoseProof (Abs_Reach_Concr x_tail x_last (Q_γ.(γ_Last)) with "Hxtail_ar_γLast HγLast_pt_xlast") as "[#Hxtail_reach_xlast HγLast_pt_xlast]".
	(* CASE ANALYSIS: Is x_tail last? *)
	iDestruct (reach_case with "Hxtail_reach_xlast") as "[><- | (%x_m & Hxtail_out & Hxm_reach_xlast)]".
	- (* x_tail is last. i.e. x_tail = x_last *)
	  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLLchain_xs]".
	  iAssert (▷n_out x_tail ↦ NONEV)%I with "[HisLL_xs]" as "Hxtail_out".
	  {
		iNext.
		destruct HisLast_xlast as [xs_rest ->].
		by iDestruct "HisLL_xs" as "[Hx_tail_out _]".
	  }
	  wp_load.
	  iModIntro.
	  (* Close Invariant: 2 *)
	  iSplitL "Hl_head Hl_tail Hxtail_out HAbst HγHead_pt_xhead HγTail_pt_xtail' HγLast_pt_xlast".
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
	  (* Consistency check *)
	  wp_load.
	  wp_pures.
	  wp_bind (! #l_tail)%E.
	  (* Invariant Opening: 3 *)
	  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead_ar_γTail & HγTail_pt_xtail' & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
	  wp_load.
	  iModIntro.
	  (* Close Invariant: 3 *)
	  iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail' HγLast_pt_xlast".
	  {
		iNext.
		iExists xs_v; iFrame "HAbst".
		iExists xs, xs_queue, x_head, x_tail', x_last; iFrame.
		iFrame "%#".
	  }
	  iClear (Hconc_abst_eq xs_v Hxs_eq x_head HisLast_xlast x_last xs xs_queue) "Hxhead_ar_γTail Hxtail'_ar_γLast".
	  wp_pures.
	  case_bool_decide; wp_if; last first.
	  (* TODO: Consider using + indentation *)
	  { (* Inconsistent*)
		wp_lam.
		iApply ("IH" with "HP HΦ Hl_new_out").
	  }
	  (* Consistent*)
	  clear x_tail' H.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  (* Attempt to add x_new to linked list *)
	  wp_bind (CmpXchg _ _ _).
	  (* Invariant Opening: 4 *)
	  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead_ar_γTail & HγTail_pt_xtail' & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
	  iPoseProof (Abs_Reach_Concr x_tail x_last (Q_γ.(γ_Last)) with "Hxtail_ar_γLast HγLast_pt_xlast") as "[#Hxtail_reach_xlast HγLast_pt_xlast]".
	  (* CASE ANALYSIS: Is tail still last? *)
	  iDestruct (reach_case with "Hxtail_reach_xlast") as "[><- | (%x_m & Hxtail_out & Hxm_reach_xlast)]"; last first.
	  (* TODO: Consider using + indentation *)
	  { (* x_tail is no longer last. CAS fails *)
	  	(* Note: Have to apply wp_cmpxchg_fail manually due to bug. *)
		wp_apply wp_cmpxchg_fail; [ | | iFrame "#" | ]; first done; first solve_vals_compare_safe; iIntros "_".
		iModIntro.
		(* Close Invariant: 4 *)
		iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail' HγLast_pt_xlast".
		{
		  iNext.
		  iExists xs_v; iFrame "HAbst".
		  iExists xs, xs_queue, x_head, x_tail', x_last; iFrame.
		  iFrame "%#".
		}
		wp_pures.
		wp_lam.
		iApply ("IH" with "HP HΦ Hl_new_out").
	  }
	  (* x_tail is still last. CAS succeeds *)
	  iPoseProof (isLL_and_chain with "HisLL_xs") as "[HisLL_xs #HisLLchain_xs]".
	  iAssert (▷n_out x_tail ↦ NONEV)%I with "[HisLL_xs]" as "Hxtail_out".
	  {
		iNext.
		destruct HisLast_xlast as [xs_rest ->].
		by iDestruct "HisLL_xs" as "[Hx_tail_out _]".
	  }
	  wp_cmpxchg_suc.
	  iMod (pointsto_persist with "Hxtail_out") as "#Hxtail_out".
	  iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[HAbst_new HQ]"; first by iFrame.
	  (* TODO: maybe make into lemma? *)
	  iAssert (x_tail ⤳ x_new)%I as "Hxtail_reach_xnew".
	  {
		rewrite {2}/reach least_fixpoint_unfold {1}/Reach' /Reach /=.
		iFrame "#". iRight. iExists x_new. iFrame "#".
		rewrite /curry.
		by iApply reach_refl.
	  }
	  iMod (Abs_Reach_Advance with "HγLast_pt_xlast Hxtail_reach_xnew") as "[HγLast_pt_xnew #Hxnew_ar_γLast]".
	  iModIntro.
	  (* Close Invariant: 4 *)
	  iSplitL "Hl_head Hl_tail Hl_new_out HAbst_new HγHead_pt_xhead HγTail_pt_xtail' HγLast_pt_xnew".
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
	  (* Swing Tail pointer *)
	  (* TODO: consider making into lemma *)
	  wp_bind (CmpXchg _ _ _).
	  (* Invariant Opening: 5 *)
	  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead_ar_γTail & HγTail_pt_xtail' & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
	  wp_cmpxchg as Hxtail_eq | Hxtail_neq.
	  + (* CAS succeeded *)
	  	iAssert (⌜x_tail' = x_tail⌝)%I as "->".
		{
			iApply (n_in_equal with "[] [HγTail_pt_xtail']"); try done.
			iApply (reach_to_is_node x_head).
			by iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_pt_xtail'") as "[Hxhead_reach_xtail' _]".
		}
		iMod (Abs_Reach_Advance with "HγTail_pt_xtail' Hxtail_reach_xnew") as "[HγTail_pt_xnew #Hxnew_ar_γTail]".
		iModIntro.
		(* Close Invariant: 5 *)
		iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xnew HγLast_pt_xlast".
		{
		  iNext.
		  iExists xs_v; iFrame "HAbst".
		  iExists xs, xs_queue, x_head, x_new, x_last; iFrame.
		  iFrame "%#".
		}
		wp_pures.
		by iApply "HΦ".
	  + (* CAS failed *)
	  	iModIntro.
		(* Close Invariant: 5 *)
	  	iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail' HγLast_pt_xlast".
		{
		  iNext.
		  iExists xs_v; iFrame "HAbst".
		  iExists xs, xs_queue, x_head, x_tail', x_last; iFrame.
		  iFrame "%#".
		}
		wp_pures.
		by iApply "HΦ".
	- (* x_tail is not last *)
	  wp_load.
	  iPoseProof (reach_from_is_node with "Hxm_reach_xlast") as "Hxm_node".
	  iMod (Abs_Reach_Abs with "Hxm_reach_xlast HγLast_pt_xlast") as "[#Hxm_ar_γLast HγLast_pt_xlast]".
	  iModIntro.
	  (* Close Invariant: 2 *)
	  iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail' HγLast_pt_xlast".
	  {
		iNext.
		iExists xs_v; iFrame "HAbst".
		iExists xs, xs_queue, x_head, x_tail', x_last; iFrame.
		iFrame "%#".
	  }
	  iClear (Hconc_abst_eq xs_v Hxs_eq x_head HisLast_xlast x_last xs xs_queue x_tail') "Hxhead_ar_γTail Hxtail_reach_xlast Hxm_reach_xlast Hxtail'_ar_γLast".
	  wp_let.
	  (* Consistency check *)
	  wp_load.
	  wp_pures.
	  wp_bind (! #l_tail)%E.
	  (* Invariant Opening: 3 *)
	  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead_ar_γTail & HγTail_pt_xtail' & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
	  wp_load.
	  iModIntro.
	  (* Close Invariant: 3 *)
	  iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail' HγLast_pt_xlast".
	  {
		iNext.
		iExists xs_v; iFrame "HAbst".
		iExists xs, xs_queue, x_head, x_tail', x_last; iFrame.
		iFrame "%#".
	  }
	  iClear (Hconc_abst_eq xs_v Hxs_eq x_head HisLast_xlast x_last xs xs_queue) "Hxhead_ar_γTail Hxtail'_ar_γLast".
	  wp_pures.
	  case_bool_decide; wp_if; last first.
	  (* TODO: Consider using + indentation *)
	  { (* Inconsistent*)
		wp_lam.
		iApply ("IH" with "HP HΦ Hl_new_out").
	  }
	  (* Consistent*)
	  clear x_tail' H.
	  wp_pures.
	  wp_load.
	  wp_pures.
	  (* Swing Tail pointer *)
	  (* TODO: consider making into lemma *)
	  wp_bind (CmpXchg _ _ _).
	  (* Invariant Opening: 4 *)
	  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead_ar_γTail & HγTail_pt_xtail' & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
	  wp_cmpxchg as Hxtail_eq | Hxtail_neq.
	  + (* CAS succeeded *)
	  	iAssert (⌜x_tail' = x_tail⌝)%I as "->".
		{
			iApply (n_in_equal with "[] [HγTail_pt_xtail']"); try done.
			iApply (reach_to_is_node x_head).
			by iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_pt_xtail'") as "[Hxhead_reach_xtail' _]".
		}
		(* TODO: maybe make into lemma? *)
		iAssert (x_tail ⤳ x_m)%I as "Hxtail_reach_xm".
		{
			rewrite /reach least_fixpoint_unfold {1}/Reach' /Reach /=.
			iFrame "#". iRight. iExists x_m. iFrame "#".
			rewrite /curry.
			by iApply reach_refl.
		}
		iMod (Abs_Reach_Advance with "HγTail_pt_xtail' Hxtail_reach_xm") as "[HγTail_pt_xm #Hxm_ar_γTail]".
		iModIntro.
		(* Close Invariant: 4 *)
		iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xm HγLast_pt_xlast".
		{
		  iNext.
		  iExists xs_v; iFrame "HAbst".
		  iExists xs, xs_queue, x_head, x_m, x_last; iFrame.
		  iFrame "%#".
		}
		wp_pures.
		wp_lam.
		iApply ("IH" with "HP HΦ Hl_new_out").
	  + (* CAS failed *)
	  	iModIntro.
		(* Close Invariant: 4 *)
	  	iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail' HγLast_pt_xlast".
		{
		  iNext.
		  iExists xs_v; iFrame "HAbst".
		  iExists xs, xs_queue, x_head, x_tail', x_last; iFrame.
		  iFrame "%#".
		}
		wp_pures.
		wp_lam.
		iApply ("IH" with "HP HΦ Hl_new_out").
Qed.

(* TODO: maybe move and possibly rewrite *)
Definition val_of_list (vs : list (val * val)) : val :=
  match vs with
  | []          => #()
  | (v, _) :: _ => v
  end.

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
	iIntros "#Hvs".
	iIntros (Φ) "!> [(%l_queue & %l_head & %l_tail & -> &
				 #Hl_queue & #Hqueue_inv) HP] HΦ".
	wp_lam.
	wp_pures.
	set loop := (rec: "loop" "_" := let: "head" := ! (Fst ! #l_queue) in let: "tail" := ! (Snd ! #l_queue) in let: "p" := NewProph in let: "next" := ! (Snd ! "head") in if: "head" = Resolve ! (Fst ! #l_queue) "p" #() then if: "head" = "tail" then if: "next" = InjL #() then InjLV #() else Snd (CmpXchg (Snd ! #l_queue) "tail" "next");; "loop" #() else let: "value" := Fst ! "next" in if: Snd (CmpXchg (Fst ! #l_queue) "head" "next") then "value" else "loop" #() else "loop" #())%V.
	iLöb as "IH".
	wp_load.
	wp_pures.
	wp_bind (! #l_head)%E.
	(* Invariant Opening: 1 *)
	iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head & %x_tail & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead_ar_γTail & HγTail_pt_xtail & >#Hxtail_ar_γLast & HγLast_pt_xlast)".
	wp_load.
	iAssert ((n_in x_head ↦□ (n_val x_head, #(n_out x_head)))%I) as "#Hxhead_node".
	{
		iApply (reach_from_is_node x_head x_tail).
		by iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_pt_xtail") as "[Hxhead_reach_xtail _]".
	}
	iPoseProof (reach_refl with "Hxhead_node") as "Hxhead_reach_xhead".
	iMod (Abs_Reach_Abs with "Hxhead_reach_xhead HγHead_pt_xhead") as "[#Hxhead_ar_γHead HγHead_pt_xhead]".
	iPoseProof (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_pt_xtail") as "[#Hxhead_reach_xtail HγTail_pt_xtail]".
	iPoseProof (Abs_Reach_Concr with "Hxtail_ar_γLast HγLast_pt_xlast") as "[#Hxtail_reach_xlast HγLast_pt_xlast]".
	iPoseProof (reach_trans with "Hxhead_reach_xtail Hxtail_reach_xlast") as "Hxhead_reach_xlast".
	iMod (Abs_Reach_Abs with "Hxhead_reach_xlast HγLast_pt_xlast") as "[#Hxhead_ar_γLast HγLast_pt_xlast]".
	iClear "Hxhead_reach_xhead Hxhead_reach_xtail Hxtail_reach_xlast Hxhead_reach_xlast".
	iModIntro.
	(* Close Invariant: 1 *)
	iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
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
	iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead'_ar_γTail & HγTail_pt_xtail & >#Hxtail_ar_γLast & HγLast_pt_xlast)".
	wp_load.
	iAssert ((n_in x_tail ↦□ (n_val x_tail, #(n_out x_tail)))%I) as "#Hxtail_node".
	{
		iApply (reach_to_is_node x_head x_tail).
		by iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_pt_xtail") as "[Hxhead_reach_xtail _]".
	}
	iPoseProof (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_pt_xtail") as "[#Hxhead_reach_xtail HγTail_pt_xtail]".
	iMod (Abs_Reach_Abs with "[] HγTail_pt_xtail") as "[#Hxtail_ar_γTail HγTail_pt_xtail]".
	{ by iApply reach_refl.	}
	iModIntro.
	(* Close Invariant: 2 *)
	iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
	{
		iNext.
		iExists xs_v; iFrame "HAbst".
		iExists xs, xs_queue, x_head', x_tail, x_last; iFrame.
		iFrame "%#".
	}
	iClear (Hconc_abst_eq xs_v Hxs_eq x_head' HisLast_xlast x_last xs xs_queue) "Hxhead'_ar_γTail".
	wp_let.
	wp_apply wp_new_proph; first done.
	iIntros (pvs p) "Hproph_p".
	wp_let.
	wp_load.
	wp_pures.
	(* Reason about the result of the consistency check of head *)
	destruct (decide (#(n_in x_head) = val_of_list pvs)).
	- (* Consistent *)
	  wp_bind (! #(n_out x_head))%E.
	  (* Invariant Opening: 3 *)
	  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead'_ar_γTail & HγTail_pt_xtail & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
	  iPoseProof (Abs_Reach_Concr with  "Hxhead_ar_γLast HγLast_pt_xlast") as "[#Hxhead_reach_xlast HγLast_pt_xlast]".
	  (* TODO: possibly find out more information here *)
	  (* CASE ANALYSIS: Is x_head the last element in the linked list? *)
	  iDestruct (reach_case with "Hxhead_reach_xlast") as "[><- | (%x_n & Hxhead_out & Hxn_reach_xlast)]".
	  + (* x_head is the last element: x_head = x_last *)
	  	destruct HisLast_xlast as [xs_rest ->].
		iDestruct "HisLL_xs" as "[Hxhead_out HisLL_chain_xs]".
		wp_load.
		(* x_head ⤳ x_head' *)
		iPoseProof (Abs_Reach_Concr with "Hxhead_ar_γHead HγHead_pt_xhead") as "[Hxhead_reach_xhead' HγHead_pt_xhead]".
		(* x_head ⤳ x_tail' *)
		iPoseProof (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_pt_xtail") as "[Hxhead_reach_xtail' HγTail_pt_xtail]".
		(* x_head = x_head' *)
		iPoseProof (reach_end_eq with "Hxhead_reach_xhead' Hxhead_out") as "[<- Hxhead_out]".
		(* x_head = x_tail' *)
		iPoseProof (reach_end_eq with "Hxhead_reach_xtail' Hxhead_out") as "[<- Hxhead_out]".
		(* x_head = x_tail *)
		iPoseProof (reach_end_eq with "Hxhead_reach_xtail Hxhead_out") as "[<- Hxhead_out]".
		iAssert (⌜xs_queue = []⌝)%I as "->".
		{
			rewrite Hxs_eq. 
			destruct xs_queue as [|x xs_queue_rest]; first done.
			destruct (exists_first (x :: xs_queue_rest)) as [x_head_next [xs_queue_rest' ->]]; first done.
			rewrite <- app_assoc.
			iPoseProof (isLL_chain_split with "HisLL_chain_xs") as "(_ & _ & Hxhead_out' & _)".
			iCombine "Hxhead_out Hxhead_out'" gives "[_ %Hcontra]".
			simplify_eq.
		}
		iAssert (⌜xs_v = []⌝)%I as "->".
		{ by destruct xs_v. }
		iMod ("Hvs" $! [] with "[HAbst HP]") as "[(_ & HAbst & HQ) | (%x_v & %xs_v' & >%Hcontra & HAbst_new & HQ) ]";
	  	[ by iFrame | |
		  (* The abstract state must be empty. Hence the second disjunct is impossible. *)
		  exfalso;
		  by apply (app_cons_not_nil xs_v' [] x_v)
		].
		iModIntro.
		(* Close Invariant: 3 *)
		iSplitL "Hl_head Hl_tail Hxhead_out HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
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
		wp_bind ((Fst ! #l_queue))%E.
		wp_load.
		wp_pures.
		wp_bind (Resolve ! #l_head #p #()).
		wp_apply (wp_resolve with "Hproph_p"); first done.
		(* Invariant Opening: 4 *)
		iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead'_ar_γTail & HγTail_pt_xtail & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
		wp_load.
		iModIntro.
		(* Close Invariant: 4 *)
		iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
		{
			iNext.
			iExists xs_v; iFrame "HAbst".
			iExists xs, xs_queue, x_head', x_tail', x_last; iFrame.
			iFrame "%#".
		}
		iIntros (pvs') "-> _".
		simpl in e.
		wp_pures.
		case_bool_decide; last contradiction.
		wp_if_true.
		wp_pures.
		case_bool_decide; last contradiction.
		wp_if_true.
		wp_pures.
		iModIntro.
		by iApply "HΦ".
	  + (* x_head is not the last element *)
	  	wp_load.
		iPoseProof (reach_from_is_node with "Hxn_reach_xlast") as "Hxn_node".
		iMod (Abs_Reach_Abs with "Hxn_reach_xlast HγLast_pt_xlast") as "[#Hxn_ar_γLast HγLast_pt_xlast]".
		iModIntro.
		(* Close Invariant: 3 *)
		iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
		{
			iNext.
			iExists xs_v; iFrame "HAbst".
			iExists xs, xs_queue, x_head', x_tail', x_last; iFrame.
			iFrame "%#".
		}
		iClear (Hconc_abst_eq xs_v Hxs_eq HisLast_xlast x_head' x_tail' xs_queue xs x_last) "Hxhead'_ar_γTail Hxtail'_ar_γLast Hxhead_reach_xlast Hxn_reach_xlast".
		wp_let.
		wp_load.
		wp_pures.
		wp_bind (Resolve ! #l_head #p #()).
		wp_apply (wp_resolve with "Hproph_p"); first done.
		(* Invariant Opening: 4 *)
		iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead'_ar_γTail & HγTail_pt_xtail & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
		wp_load.
		iModIntro.
		(* Close Invariant: 4 *)
		iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
		{
			iNext.
			iExists xs_v; iFrame "HAbst".
			iExists xs, xs_queue, x_head', x_tail', x_last; iFrame.
			iFrame "%#".
		}
		iClear (Hconc_abst_eq xs_v Hxs_eq HisLast_xlast x_tail' xs_queue xs x_last) "Hxhead'_ar_γTail Hxtail'_ar_γLast".
		iIntros (pvs') "-> _".
		simpl in e.
		wp_pures.
		case_bool_decide; last contradiction.
		clear e H x_head'.
		wp_if_true.
		wp_pures.
		case_bool_decide as His_xhead_xtail_eq.
		* (* n_in x_head = n_in x_tail. I.e. x_tail is lagging behind. Swing it to next *)
		  iAssert (⌜x_head = x_tail⌝)%I as "->"; first (iApply n_in_equal; done).
		  wp_if_true.
		  wp_pures.
		  wp_load.
		  wp_pures.
		  (* Swing Tail pointer *)
		  (* TODO: consider making into lemma *)
		  wp_bind (CmpXchg _ _ _).
		  (* Invariant Opening: 5 *)
		  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead'_ar_γTail & HγTail_pt_xtail' & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
		  wp_cmpxchg as Hxtail_eq | Hxtail_neq.
		  ** (* CAS succeeded *)
			iAssert (⌜x_tail' = x_tail⌝)%I as "->".
			{
				iApply (n_in_equal with "[] [HγTail_pt_xtail']"); try done.
				iApply (reach_to_is_node x_tail).
				by iDestruct (Abs_Reach_Concr with "Hxhead_ar_γTail HγTail_pt_xtail'") as "[Hxhead_reach_xtail' _]".
			}
			(* TODO: maybe make into lemma? *)
			iAssert (x_tail ⤳ x_n)%I as "Hxtail_reach_xn".
			{
				rewrite {2}/reach least_fixpoint_unfold {1}/Reach' /Reach /=.
				iFrame "#". iRight. iExists x_n. iFrame "#".
				rewrite /curry.
				by iApply reach_refl.
			}
			iMod (Abs_Reach_Advance with "HγTail_pt_xtail' Hxtail_reach_xn") as "[HγTail_pt_xn #Hxn_ar_γTail]".
			iModIntro.
			(* Close Invariant: 5 *)
			iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xn HγLast_pt_xlast".
			{
			  iNext.
			  iExists xs_v; iFrame "HAbst".
			  iExists xs, xs_queue, x_head', x_n, x_last; iFrame.
			  iFrame "%#".
			}
			wp_pures.
			wp_lam.
			iApply ("IH" with "HP HΦ").
		  ** (* CAS failed *)
			iModIntro.
			(* Close Invariant: 5 *)
			iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail' HγLast_pt_xlast".
			{
			  iNext.
			  iExists xs_v; iFrame "HAbst".
			  iExists xs, xs_queue, x_head', x_tail', x_last; iFrame.
			  iFrame "%#".
			}
			wp_pures.
			wp_lam.
			iApply ("IH" with "HP HΦ").
		* (* x_tail is not lagging behind. Attempt to swing head pointer *)
		  wp_if_false.
		  wp_load.
		  wp_pures.
		  wp_load.
		  wp_pures.
		  wp_bind (CmpXchg _ _ _).
		  (* Invariant Opening: 5 *)
		  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead' & >#Hxhead'_ar_γTail & HγTail_pt_xtail' & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
		  wp_cmpxchg as Hxhead_eq | Hxhead_neq.
		  ** (* CAS succeeded. Head pointer swung to x_n *)
			iAssert (⌜x_head' = x_head⌝)%I as "->".
			{
				iPoseProof (Abs_Reach_Concr with "Hxhead'_ar_γTail HγTail_pt_xtail'") as "[#Hconcr HγTail_pt_xtail']".
				iApply n_in_equal; try done.
				by iApply reach_from_is_node.
			}
			iAssert (⌜∃xs_queue', xs_queue = xs_queue' ++ [x_n]⌝)%I as "[%xs_queue_new ->]".
			{
				destruct xs_queue as [|x xs_rest].
				- (* Queue is not empty, as x_head doesn't point to none *)
				  rewrite Hxs_eq.
				  iDestruct "HisLL_xs" as "[Hxhead_out' _]".
				  iCombine "Hxhead_out Hxhead_out'" gives "[_ %Hcontra]".
				  simplify_eq.
				- destruct (exists_first (x :: xs_rest)) as [x_n' [xs_queue' Hxs_rest_queue_eq]]; first done.
				  iExists xs_queue'.
				  rewrite Hxs_rest_queue_eq in Hxs_eq *.
				  rewrite Hxs_eq.
				  rewrite <- app_assoc.
				  iPoseProof (isLL_and_chain with "HisLL_xs") as "[_ HisLL_chain_xs]".
				  iDestruct (isLL_chain_split with "HisLL_chain_xs") as "[_ ( #Hxn'_node & #Hxhead_out' & _)]".
				  iCombine "Hxhead_out Hxhead_out'" gives "[_ %Hxn_in_eq]".
				  iDestruct (n_in_equal with "[] [Hxn_node] [Hxn'_node]") as "%Hxn_xn'_eq"; try done.
				  by rewrite Hxn_xn'_eq.
			}
			iMod ("Hvs" $! xs_v with "[HAbst HP]") as "[(>-> & HAbst & HQ) | (%x_v & %xs_v' & >%Hxs_v_eq & HAbst_new & HQ) ]";
			[ by iFrame |
			(* The abstract state cannot be empty. Hence the first disjunct is impossible *)
			rewrite proj_val_split in Hconc_abst_eq;
			simpl in Hconc_abst_eq;
			exfalso;
			by apply (app_cons_not_nil (proj_val xs_queue_new) [] (n_val x_n)) |
			].
			rewrite Hxs_v_eq in Hconc_abst_eq.
			rewrite proj_val_split in Hconc_abst_eq.
			rewrite wrap_some_split in Hconc_abst_eq.
			apply list_last_eq in Hconc_abst_eq as [Hconc_abst_eq Hxn_xv_eq].
			rewrite Hxs_eq.
			iDestruct (isLL_split with "HisLL_xs") as "[HisLL_new _]".
			(* TODO: maybe make into lemma? *)
			iAssert (x_head ⤳ x_n)%I as "Hxhead_reach_xn".
			{
				rewrite {2}/reach least_fixpoint_unfold {1}/Reach' /Reach /=.
				iFrame "#". iRight. iExists x_n. iFrame "#".
				rewrite /curry.
				by iApply reach_refl.
			}
			iMod (Abs_Reach_Advance with "HγHead_pt_xhead' Hxhead_reach_xn") as "[HγHead_pt_xn #Hxn_ar_γHead]".
			iDestruct (reach_case with "Hxhead_reach_xtail") as "[-> | (%x_n' & Hxhead_out' & Hxn_reach_xtail) ]"; first contradiction.
			iAssert (⌜x_n' = x_n⌝)%I as "->".
			{
				iCombine "Hxhead_out Hxhead_out'" gives "[_ %Hxn_xn'_in_eq]".
				iApply n_in_equal; try done.
				by iApply reach_from_is_node.
			}
			iAssert (x_n⤳x_tail')%I as "#Hxn_reach_xtail'".
			{
				iApply (reach_trans with "Hxn_reach_xtail").
				by iDestruct (Abs_Reach_Concr with "Hxtail_ar_γTail HγTail_pt_xtail'") as "[Hxtail_reach_xtail' _]".
			}
			iMod (Abs_Reach_Abs with "Hxn_reach_xtail' HγTail_pt_xtail'") as "[#Hxn_ar_γTail HγTail_pt_xtail']".
			iModIntro.
			(* Close Invariant: 5 *)
			iSplitL "Hl_head Hl_tail HisLL_new HAbst_new HγHead_pt_xn HγTail_pt_xtail' HγLast_pt_xlast".
			{
			  iNext.
			  iExists xs_v'; iFrame "HAbst_new".
			  iExists (xs_queue_new ++ [x_n]), xs_queue_new, x_n, x_tail', x_last; iFrame.
			  iFrame "%#".
			  iSplit; first done.
			  iPureIntro.
			  rewrite Hxs_eq in HisLast_xlast.
			  rewrite <- app_assoc in HisLast_xlast.
			  by apply isLast_remove in HisLast_xlast.
			}
			wp_pures.
			iApply "HΦ".
			by rewrite Hxn_xv_eq.
		  ** (* CAS failed *)
			iModIntro.
			(* Close Invariant: 5 *)
			iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead' HγTail_pt_xtail' HγLast_pt_xlast".
			{
			  iNext.
			  iExists xs_v; iFrame "HAbst".
			  iExists xs, xs_queue, x_head', x_tail', x_last; iFrame.
			  iFrame "%#".
			}
			wp_pures.
			wp_lam.
			iApply ("IH" with "HP HΦ").
	- (* Inconsistent *)
	  wp_bind (! #(n_out x_head))%E.
	  (* Invariant Opening: 3 *)
	  iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead'_ar_γTail & HγTail_pt_xtail & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
	  iPoseProof (Abs_Reach_Concr with  "Hxhead_ar_γLast HγLast_pt_xlast") as "[#Hxhead_reach_xlast HγLast_pt_xlast]". 
	  (* TODO: find out how to handle both cases in unison *)
	  iDestruct (reach_case with "Hxhead_reach_xlast") as "[><- | (%x_m & Hxhead_out & Hxm_reach_xlast)]".
	  + destruct HisLast_xlast as [xs_rest ->].
	  	iDestruct "HisLL_xs" as "[Hxhead_out HisLL_chain_xs]".
		wp_load.
		iModIntro.
		(* Close Invariant: 3 *)
		iSplitL "Hl_head Hl_tail Hxhead_out HisLL_chain_xs HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
		{
			iNext.
			iExists xs_v; iFrame "HAbst".
			iExists (x_head :: xs_rest), xs_queue, x_head', x_tail', x_head; iFrame.
			iFrame "%#".
			by iExists xs_rest.
		}
		iClear (Hconc_abst_eq xs_v Hxs_eq x_head' x_tail' xs_queue) "Hxhead'_ar_γTail Hxtail'_ar_γLast Hxhead_reach_xlast".
		wp_let.
		wp_bind ((Fst ! #l_queue))%E.
		wp_load.
		wp_pures.
		wp_bind (Resolve ! #l_head #p #()).
		wp_apply (wp_resolve with "Hproph_p"); first done.
		(* Invariant Opening: 4 *)
		iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead'_ar_γTail & HγTail_pt_xtail & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
		wp_load.
		iModIntro.
		(* Close Invariant: 4 *)
		iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
		{
			iNext.
			iExists xs_v; iFrame "HAbst".
			iExists xs, xs_queue, x_head', x_tail', x_last; iFrame.
			iFrame "%#".
		}
		iIntros (pvs') "-> _".
		simpl in n.
		wp_pures.
		case_bool_decide; first contradiction.
		wp_if_false.
		wp_lam.
		iApply ("IH" with "HP HΦ").
	  + wp_load.
		iModIntro.
		(* Close Invariant: 3 *)
		iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
		{
			iNext.
			iExists xs_v; iFrame "HAbst".
			iExists xs, xs_queue, x_head', x_tail', x_last; iFrame.
			iFrame "%#".
		}
		iClear (Hconc_abst_eq xs_v Hxs_eq x_head' HisLast_xlast x_tail' x_last xs xs_queue) "Hxhead'_ar_γTail Hxm_reach_xlast Hxhead_reach_xlast Hxtail'_ar_γLast".
		wp_let.
		wp_bind ((Fst ! #l_queue))%E.
		wp_load.
		wp_pures.
		wp_bind (Resolve ! #l_head #p #()).
		wp_apply (wp_resolve with "Hproph_p"); first done.
		(* Invariant Opening: 4 *)
		iInv "Hqueue_inv" as "(%xs_v & HAbst & %xs & %xs_queue & %x_head' & %x_tail' & %x_last & >%Hxs_eq & HisLL_xs & >%HisLast_xlast & >%Hconc_abst_eq & >Hl_head & >Hl_tail & HγHead_pt_xhead & >#Hxhead'_ar_γTail & HγTail_pt_xtail & >#Hxtail'_ar_γLast & HγLast_pt_xlast)".
		wp_load.
		iModIntro.
		(* Close Invariant: 4 *)
		iSplitL "Hl_head Hl_tail HisLL_xs HAbst HγHead_pt_xhead HγTail_pt_xtail HγLast_pt_xlast".
		{
			iNext.
			iExists xs_v; iFrame "HAbst".
			iExists xs, xs_queue, x_head', x_tail', x_last; iFrame.
			iFrame "%#".
		}
		iIntros (pvs') "-> _".
		simpl in n.
		wp_pures.
		case_bool_decide; first contradiction.
		wp_if_false.
		wp_lam.
		iApply ("IH" with "HP HΦ").
Qed.

End proofs.

Notation "Q_γ ⤇● xs_v" := (own Q_γ.(γ_Abst) (●F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇● xs_v") : bi_scope.
Notation "Q_γ ⤇◯ xs_v" := (own Q_γ.(γ_Abst) (◯F (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇◯ xs_v") : bi_scope.
Notation "Q_γ ⤇[ q ] xs_v" := (own Q_γ.(γ_Abst) (◯F{ q } (to_agree xs_v)))
	(at level 20, format "Q_γ ⤇[ q ] xs_v") : bi_scope.
