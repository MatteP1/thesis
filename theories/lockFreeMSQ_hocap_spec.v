From stdpp Require Import countable.
From iris.algebra Require Import excl list agree gmap lib.frac_auth.
From iris.bi Require Import derived_laws.
From iris.heap_lang Require Import lang proofmode notation.
From iris.base_logic.lib Require Import invariants.
From MSQueue Require Import lockFreeMSQ_impl.
From MSQueue Require Import twoLockMSQ_common.
(* TODO: consider changing twolockMSQ_common to common. *)

Section proofs.

Definition linkedListUR : ucmra :=
	gmapUR nat (agreeR (prodO (prodO locO valO) locO)).

Fixpoint to_ll_go (i : nat) (xs : list (loc * val * loc)) : linkedListUR :=
  match xs with
  | [] => ∅
  | x :: xs' => <[i:=to_agree x]>(to_ll_go (S i) xs')
  end.
Definition to_ll : list (loc * val * loc) → linkedListUR := to_ll_go 0.

Context `{!heapGS Σ}.
Context `{!inG Σ (authR linkedListUR)}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.

Variable N : namespace.
Notation Ni := (N .@ "internal").

(* ===== Concurrent Specification for Two-lock M&S Queue ===== *)

(* Ghost variable names *)
Record Qgnames := {γ_Abst 	: gname;
				   γ_Snap 	: gname;
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

Notation current Q_γ xs := (own Q_γ.(γ_Snap) (● (to_ll (reverse xs)))).
Notation snapshot Q_γ xs := (own Q_γ.(γ_Snap) (◯ (to_ll (reverse xs)))).

Lemma get_snapshot : ∀ Q_γ xs,
	current Q_γ xs -∗
	current Q_γ xs ∗ snapshot Q_γ xs.
Proof.
	Admitted.

Lemma current_and_snapshot : ∀ Q_γ xs xs',
	current Q_γ xs -∗
	snapshot Q_γ xs' -∗
	∃xs'', ⌜xs = xs'' ++ xs'⌝.
Proof.
	Admitted.

Lemma current_update : ∀ Q_γ xs x,
	current Q_γ xs ==∗ current Q_γ (x :: xs).
Proof.
	Admitted.

Definition queue_invariant (l_head l_tail : loc) (Q_γ : Qgnames) : iProp Σ :=
	∃ xs_v, Q_γ ⤇● xs_v ∗ (* Abstract state *)
	∃ xs xs_queue xs_old (x_head x_tail: (loc * val * loc)), (* Concrete state *)
	current Q_γ xs ∗
	⌜xs = xs_queue ++ [x_head] ++ xs_old⌝ ∗
	isLL xs ∗
	(* Relation between concrete and abstract state *)
	⌜proj_val xs_queue = wrap_some xs_v⌝ ∗
	l_head ↦ #(n_in x_head) ∗
	l_tail ↦ #(n_in x_tail) ∗
	(⌜isLast x_tail xs⌝ ∨ ⌜isSndLast x_tail xs⌝).

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
	iMod (own_alloc (● (to_ll [(l_1_in, NONEV, l_1_out)]))) as (γ_Snap) "Hγ_Snap_curr".
	{
		apply auth_auth_valid.
		apply singleton_valid.
		rewrite <- agree_idemp.
		by apply to_agree_op_valid_L.
	}
	set (Queue_gnames := {| γ_Abst := γ_Abst;
							γ_Snap := γ_Snap
					|}).
	iMod (inv_alloc Ni _ (queue_invariant l_head l_tail Queue_gnames) with "[Hγ_Abst_auth Hγ_Snap_curr Hl_head Hl_tail Hl_1_in Hl_1_out]") as "#HqueueInv".
	{
		iNext. iExists []; iFrame.
		iExists [(l_1_in, NONEV, l_1_out)], [], [], (l_1_in, NONEV, l_1_out), (l_1_in, NONEV, l_1_out); iFrame.
		do 3 (iSplit; first done).
		iLeft.
		iFrame.
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

Lemma enqueue_spec v_q (v : val) (Q_γ : Qgnames) (P Q : iProp Σ) :
	□(∀xs_v, (Q_γ ⤇● xs_v ∗ P ={⊤ ∖ ↑Ni}=∗ ▷ (Q_γ ⤇● (v :: xs_v) ∗ Q))) -∗
	{{{ is_queue v_q Q_γ ∗ P}}}
		enqueue v_q v
	{{{ w, RET w; Q }}}.
Proof.
	Admitted.

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
