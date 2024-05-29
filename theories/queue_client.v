From iris.algebra Require Import list agree lib.frac_auth.
From iris.heap_lang Require Import lang proofmode notation spawn.
From iris.base_logic.lib Require Import invariants token.
From MSQueue Require Import queue_specs.

Section client.

Context `{!queue}.
Context `{!queueG Σ}.
Context `{!heapGS Σ}.
Context `{!inG Σ (frac_authR (agreeR (listO val)))}.
Context `{!spawnG Σ}.
Context `{!tokenG Σ}.

Definition unwrap : val :=
  λ: "w",
    match: "w" with
      NONE => #() #()
    | SOME "v" => "v"
    end.

Definition enqdeq : val :=
  λ: "v_q" "c",
    enqueue "v_q" "c" ;;
    unwrap (dequeue "v_q").

Definition queueAdd : val :=
  λ: "a" "b",
    let: "v_q" := initialize #() in
    let: "j" := spawn (λ: <>, enqdeq "v_q" "a") in
    let: "x" := enqdeq "v_q" "b" in
    let: "y" := spawn.join "j" in
    "x" + "y".

Variable Ns: namespace.
Notation Nqa := (N .@ "QueueAdd").

Record QAgnames := {  γ_D1     : gname;
                      γ_D2     : gname;
                      γ_A      : gname;
                      γ_B      : gname;
                    }.

(* ----- Tokens ----- *)
Definition TokD1 (g : QAgnames) := token g.(γ_D1).
Definition TokD2 (g : QAgnames) := token g.(γ_D2).
Definition TokA (g : QAgnames) := token g.(γ_A).
Definition TokB (g : QAgnames) := token g.(γ_B).

Definition contentsInv G Ga a b : iProp Σ :=
  (γ_Abst G) ⤇◯ [] ∗ TokD1 Ga ∗ TokD2 Ga ∨
  (γ_Abst G) ⤇◯ [a] ∗ TokA Ga ∗ (TokD1 Ga ∨ TokD2 Ga) ∨
  (γ_Abst G) ⤇◯ [b] ∗ TokB Ga ∗ (TokD1 Ga ∨ TokD2 Ga) ∨
  (γ_Abst G) ⤇◯ [a; b] ∗ TokA Ga ∗ TokB Ga ∨
  (γ_Abst G) ⤇◯ [b; a] ∗ TokB Ga ∗ TokA Ga.

Definition case_a_b v a b Ga : iProp Σ := ⌜v = #a⌝ ∗ TokA Ga ∨ ⌜v = #b⌝ ∗ TokB Ga.

Lemma enqdeq_spec : ∀(a b c : Z) Ga G (v_q : val),
  {{{ isQueue v_q G ∗ inv Nqa (contentsInv G Ga #a #b) ∗
              ((TokA Ga ∗ ⌜c = a⌝) ∨ (TokB Ga ∗ ⌜c = b⌝)) }}}
    enqdeq v_q #c
  {{{v, RET v; case_a_b v a b Ga }}}.
Proof.
  iIntros (a b c Ga G v_q Φ) "(#HisQueue & #Hinv & Hcase) HΦ".
  wp_lam.
  wp_pures.
  set (P := ((TokA Ga ∗ ⌜c = a⌝) ∨ (TokB Ga ∗ ⌜c = b⌝))%I).
  set (Q := (TokD1 Ga ∨ TokD2 Ga)%I).
  wp_apply (enqueue_spec v_q #c G P Q with "[] [Hcase]").
  (* Proving viewshift *)
  {
    iModIntro.
    iIntros (xs_v) "[Hauth Hcase]".
    iInv "Hinv" as "[(>Hfrag & >HTokD1 & >HTokD2) |
                    [(>Hfrag & >HTokA & >HTokD12) |
                    [(>Hfrag & >HTokB & >HTokD12) |
                    [(>Hfrag & >HTokA & >HTokB) |
                     (>Hfrag & >HTokB & >HTokA)]]]]";
    iDestruct "Hcase" as "[[HTokA' -> ]| [HTokB' ->]]";
    (* Most cases are impossible... *)
    try (by iCombine "HTokA HTokA'" gives "%Hcontra");
    try (by iCombine "HTokB HTokB'" gives "%Hcontra");
    (* The possible cases are handled similarly: *)
    (* Update the abstract state to include the newly enqueue element *)
    iPoseProof (queue_contents_auth_frag_agree with "Hauth Hfrag") as "<-";
    [ iMod (queue_contents_update _ _ _ [ #a ] with "Hauth Hfrag") as "[Hauth Hfrag]"
    | iMod (queue_contents_update _ _ _ [ #b ] with "Hauth Hfrag") as "[Hauth Hfrag]"
    | iMod (queue_contents_update _ _ _ [ #b ; #a ] with "Hauth Hfrag") as "[Hauth Hfrag]"
    | iMod (queue_contents_update _ _ _ [ #a ; #b ] with "Hauth Hfrag") as "[Hauth Hfrag]" ];
    iModIntro;
    unfold contentsInv;
    (* Close the invariant in the updated state *)
    [ iSplitL "HTokA' HTokD1 Hfrag" (* Can give up either D1 or D2 *)
    | iSplitL "HTokB' HTokD1 Hfrag" (* Can give up either D1 or D2 *)
    | iSplitL "HTokA HTokB' Hfrag"
    | iSplitL "HTokA' HTokB Hfrag" ];
    eauto 6 with iFrame.
  }
  (* Proving pre-condition of hocap enqueue spec *)
  { by iFrame. }
  iIntros (w) "HQ".
  wp_pures.
  clear w.
  wp_bind (dequeue v_q).
  set (P' := Q%I : iProp Σ).
  set (Q' := λ w, (⌜w = SOMEV #a⌝ ∗ TokA Ga ∨ ⌜w = SOMEV #b⌝ ∗ TokB Ga)%I : iProp Σ).
  wp_apply (dequeue_spec v_q G P' Q' with "[] [HQ]").
  (* Proving viewshift *)
  {
    iModIntro.
    iIntros (xs_v) "[Hauth HP']".
    iRight.
    iInv "Hinv" as "[(>Hfrag & >HTokD1 & >HTokD2) |
                    [(>Hfrag & >HTokA & [>HTokD1 | >HTokD2]) |
                    [(>Hfrag & >HTokB & [>HTokD1 | >HTokD2]) |
                    [(>Hfrag & >HTokA & >HTokB) |
                     (>Hfrag & >HTokB & >HTokA)]]]]";
    iDestruct "HP'" as "[HTokD1' | HTokD2']";
    (* Most cases are impossible... *)
    try (by iCombine "HTokD1 HTokD1'" gives "%Hcontra");
    try (by iCombine "HTokD2 HTokD2'" gives "%Hcontra");
    iPoseProof (queue_contents_auth_frag_agree with "Hauth Hfrag") as "<-";
    [ iMod (queue_contents_update _ _ _ [ ] with "Hauth Hfrag") as "[Hauth Hfrag]"
    | iMod (queue_contents_update _ _ _ [ ] with "Hauth Hfrag") as "[Hauth Hfrag]"
    | iMod (queue_contents_update _ _ _ [ ] with "Hauth Hfrag") as "[Hauth Hfrag]"
    | iMod (queue_contents_update _ _ _ [ ] with "Hauth Hfrag") as "[Hauth Hfrag]"
    | iMod (queue_contents_update _ _ _ [ #a ] with "Hauth Hfrag") as "[Hauth Hfrag]"
    | iMod (queue_contents_update _ _ _ [ #a ] with "Hauth Hfrag") as "[Hauth Hfrag]"
    | iMod (queue_contents_update _ _ _ [ #b ] with "Hauth Hfrag") as "[Hauth Hfrag]"
    | iMod (queue_contents_update _ _ _ [ #b ] with "Hauth Hfrag") as "[Hauth Hfrag]" ];
    iModIntro;
    iFrame "Hauth";
    unfold Q', contentsInv;
    (* Close the invariant in the updated state *)
    [ iSplitL "HTokD1 HTokD2' Hfrag"
    | iSplitL "HTokD1' HTokD2 Hfrag"
    | iSplitL "HTokD1 HTokD2' Hfrag"
    | iSplitL "HTokD1' HTokD2 Hfrag"
    | iSplitL "HTokD1' HTokA Hfrag"
    | iSplitL "HTokD2' HTokA Hfrag"
    | iSplitL "HTokD1' HTokB Hfrag"
    | iSplitL "HTokD2' HTokB Hfrag" ];
    eauto 7 with iFrame.
  }
  (* Proving pre-condition of hocap dequeue spec *)
  { by iFrame. }
  iIntros (w) "[[-> HTokA] | [-> HTokB]]";
  wp_lam;
  wp_pures;
  iApply "HΦ";
  [iLeft | iRight];
  by iFrame.
Qed.

Lemma queueAdd_spec : ∀(a b : Z),
  {{{ True }}} queueAdd #a #b {{{v, RET v; ⌜v = #(a + b)⌝}}}.
Proof.
  iIntros (a b Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  iMod token_alloc as (γ_D1) "Hγ_D1".
  iMod token_alloc as (γ_D2) "Hγ_D2".
  iMod token_alloc as (γ_A) "Hγ_A".
  iMod token_alloc as (γ_B) "Hγ_B".
  set (Ga := {| γ_D1 := γ_D1;
                γ_D2 := γ_D2;
                γ_A := γ_A;
                γ_B := γ_B;
              |}).
  wp_apply (initialize_spec); first done.
  iIntros (v_q G) "[#HisQueue Hfrag]".
  iMod (inv_alloc Nqa _ (contentsInv G Ga #a #b) with "[Hγ_D1 Hγ_D2 Hfrag]") as "#HqaInv".
  { iNext. iLeft. iFrame. }
  wp_pures.
  wp_apply (spawn_spec Ns (λ v, case_a_b v a b Ga) _ with "[Hγ_A]").
  - wp_lam.
    wp_apply (enqdeq_spec a b a Ga G v_q with "[HisQueue Hγ_A]"); auto.
  - iIntros (jloc) "Hjhandle".
    wp_pures.
    wp_apply (enqdeq_spec a b b Ga G v_q with "[Hγ_B]"); first iFrame "#"; auto.
    iIntros (x) "Hcase".
    wp_pures.
    wp_apply (join_spec with "Hjhandle").
    iIntros (y) "Hcase'".
    wp_pures.
    iDestruct "Hcase" as "[[-> HTokA]|[-> HTokB]]";
    iDestruct "Hcase'" as "[[-> HTokA']|[-> HTokB']]"; 
    [ by iCombine "HTokA HTokA'" gives "%Hcontra" | |
    | by iCombine "HTokB HTokB'" gives "%Hcontra" ];
    wp_pures;
    iModIntro;
    iApply "HΦ"; first done.
    by rewrite Z.add_comm.
Qed.

End client.