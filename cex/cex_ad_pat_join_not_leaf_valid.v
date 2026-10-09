(** ⚠️ THE EMBEDDED SUBTYPING PREMISE OF [ad_pat] / [ad_sd_typing] IS NOT
    LEAF-VALID, SO thm:complete-skeleton-inference AND thm:complete-type-
    inference CANNOT BE STATED OVER THE PLAIN JUDGEMENTS.

    Section D, scouting item 1 (docs/HANDOFF-section-d.md §6.1 / §6.2).

    THE SITUATION.  [a_sub_complete] (thm:complete-subtyping) takes its
    declarative join as [ad_pat_sub_fuel] — the LEAF-VALID mirror, which carries
    at every consistency leaf the subject-refinement datum
    [{{ Θ ⨟ ∅ ⊢ᵣₚ ⌊R⌋ˢ ⊳ ⌊Q⌋ }}ad].  That is the third solution condition of the
    paper's own AUGMENTED thm:complete-consistency (consistency-proofs.tex:
    2230-2242), which [a_consis_complete] also carries; subtyping needs it
    at the LEAVES rather than at the root because at the root it is vacuous
    (cex_p7_univ_ghost_r_vacuous.v, cex_p7_third_premise_forall.v).

    But [ad_pat] / [ad_sd_typing] (algo_decl/def_typing.v)
    embed the PLAIN [ad_pat_sub] in their Unit / Var / Anno rows.  So a
    completeness proof that inducts on one of those judgements arrives at a
    base row holding a plain join and cannot invoke thm:complete-subtyping.

    THE FINDING BELOW: the gap is real, not a bookkeeping artefact.  The
    CAPTURE configuration of docs/DESIGN-subtyping.md §3.1 —

        subject  ∀X.◇      counterpart  ∀ˢX.X

    — has a plain [ad_pat_sub] derivation (§1) and NO [ad_pat_sub_fuel] one
    (§2), and it is reachable from [ad_pat] as [P-Var] at an entry
    [x : ∀X.◇] (§3).  Consistency's ∀-rows push the rigid [X] into Θ, so the
    ghost may be FILLED with it; refinement's ∀-row pushes it into Δ and
    [ad_refine_pskl__ghost]'s fill is Δ-free BY RULE — so the leaf datum fails
    exactly where the paper's no-capture discipline bites.

    CONSEQUENCE.  For the completeness direction the embedded premise must be
    the leaf-valid one, i.e. the "solution to the skeleton/type inference
    problem" must carry the leaf data, exactly as the paper's own solution
    notion for CONSISTENCY already does.  Registered in docs/PAPER-GAPS.md. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.def_typing.

Set Implicit Arguments.

(** the capture configuration: subject [∀X.◇], counterpart [∀ˢX.X] *)
Definition capR : uskl := uskl_all_syn uskl_ghost.
Definition capQ : bskl := bskl_all_syn (bskl_var_b 0).
Definition capP : pskl := pskl_all_syn pskl_ghost.

Lemma cap_erase : uskl_to_pskl capR = capP.
Proof. reflexivity. Qed.

Lemma cap_target_erase : bskl_to_pskl capQ = pskl_all_syn (pskl_var_b 0).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  §1  The PLAIN join exists (at either sort)                            *)
(* ===================================================================== *)

Lemma cap_is_sskl : is_sskl capQ.
Proof.
  apply is_sskl__all with (L := empty). intros α Hα. cbn. apply is_sskl__var.
Qed.

(** ⭐ Consistency's ∀-row puts the rigid [α] into **Θ**, so the ghost's fill
    [ad_pat_consis__ghost] — which demands the fill Θ-well-scoped — may pick
    [α] itself.  This is the capture the refinement judgement forbids. *)
Lemma cap_consis : forall Θ, {{ empty ⨟ Θ ⊢ˢ capR ∼ capQ }}ad.
Proof.
  intros Θ. apply ad_pat_consis__forall_syn with (L := empty).
  intros α Hα. cbn.
  apply (ad_pat_consis__ghost (P := pskl_var_f α)); [ reflexivity | ].
  apply a_wf_pskl__var. unfold a_binds_tvar. eauto.
Qed.

(** ⚠️ RETRACTED 2026-08-12 — AND THAT IS THE POINT.  Until then this section
    proved

      cap_plain : forall NM Θ, {{ empty ⨟ Θ ⊢ˢ[ NM | mode_ti ] capR ⩽ capQ }}ad

    by [ad_pat_sub__infer] on [cap_consis] + [cap_is_sskl] — the PLAIN join
    derived the capture pair, and only the leaf-valid mirror rejected it.  That
    asymmetry is gone: [ad_pat_sub]'s four consistency-leaf rows now carry the
    paper's presupposition (declarative.tex:2074) themselves, exactly as
    [d_pat_sub] has since 2026-08-11, so the plain relation rejects the pair
    for the same reason §2 does — [cap_no_refine].

    What the file still shows is the reason the presupposition has to be ON THE
    RULE and cannot be left to a mirror: §2's refutation is about the
    REFINEMENT, and no amount of consistency reasoning recovers it. *)

(* ===================================================================== *)
(*  §2  NO leaf-valid join exists                                         *)
(* ===================================================================== *)

(** ⭐ Refinement's ∀-row puts the rigid into **Δ** (as well as Θ), and
    [ad_refine_pskl__ghost]'s fill must avoid Δ — so the ghost can never be
    filled with the rigid itself.  The only other row with a ghost on the left
    is the flexible lookup, which needs the rigid to be a defined flexible. *)
Lemma cap_ghost_no_fill : forall Θ α,
  ~ (exists τ, binds α (abind_flex_mono_def τ) Θ) ->
  ~ ({{ Θ ⨟ (add α empty) ⊢ᵣₚ pskl_ghost ⊳ (pskl_var_f α) }}ad).
Proof.
  intros Θ α Hα H. inversion H; subst.
  - (* __ghost : the fill would mention the Δ-variable [α] *)
    clear Hα H. simpl in *.
    match goal with Hd : _ |- False =>
      assert (Hin : α `in` empty) by (apply Hd; fsetdec); fsetdec end.
  - (* __flex_r : [α] would have to be a defined flexible of Θ *)
    apply Hα. eauto.
Qed.

Lemma cap_no_refine : forall Θ,
  ~ ({{ Θ ⨟ empty ⊢ᵣₚ capP ⊳ (bskl_to_pskl capQ) }}ad).
Proof.
  intros Θ H. unfold capP, capQ in H. cbn in H.
  inversion H; subst.
  match goal with
  | Hf : forall α, α `notin` ?L -> _ |- _ =>
      pick fresh β for (L `union` dom Θ);
      pose proof (Hf β ltac:(clear - Fr; fsetdec)) as Hβ; cbn in Hβ
  end.
  eapply cap_ghost_no_fill; [ | exact Hβ ].
  intros [τ Hb].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb']; [ discriminate | ].
  apply binds_In in Hb'. clear - Hb' Fr; fsetdec.
Qed.

(** ⚙ Stated over the PLAIN relation since 2026-08-12: [ad_pat_sub] carries
    the leaf datum itself, so the refutation no longer has to detour through
    the fuelled mirror — and [ad_pat] embeds the plain relation now. *)
Lemma cap_no_join : forall NM Θ,
  ~ ({{ empty ⨟ Θ ⊢ˢ[ NM | mode_ti ] capR ⩽ capQ }}ad).
Proof.
  intros NM Θ H. inversion H; subst; try congruence.
  (* the only row concluding at [mode_ti] is [__infer]; the refinement half of
     its JOIN is exactly the refinement refuted above *)
  match goal with
  | Hj : {{ _ ⨟ _ ⊢ˢ _ ∼ᵣ _ }}ad |- _ => destruct Hj as [_ Hr]
  end.
  eapply cap_no_refine; exact Hr.
Qed.

(* ===================================================================== *)
(*  §3  … and the configuration WAS reachable from [ad_pat] — which is     *)
(*  why the rule had to change                                             *)
(*                                                                        *)
(*  ⭐ UPDATED 2026-08-07, and again 2026-08-12 (see the retractions).      *)
(*  When [ad_pat]'s base rows embedded the PLAIN                          *)
(*  [ad_pat_sub], this section derived                                     *)
(*      x : ∀X.◇  ⊢ˢ[TI]  x  ⦂  ∀ˢX.X                                      *)
(*  by [P-Var] on §1's plain join — a judgement thm:complete-skeleton-      *)
(*  inference could say NOTHING about, since §2 refutes its leaf datum.    *)
(*  The rules now embed [ad_pat_sub_v], so the same derivation is REJECTED  *)
(*  (§3a), and the two halves the rule change rests on are §3b:            *)
(*  everything BUT the join still goes through, so the leaf datum is the   *)
(*  one and only thing that excludes the configuration.                    *)
(* ===================================================================== *)

(** §3a — [P-Var] can no longer reach the capture configuration. *)
Lemma cap_not_reachable : forall x,
  ~ ({{ ((x ~ abind_var_skl capP) ++ nil) ⊢ˢ[ mode_ti ] (exp_var_f x) ⦂ capQ }}ad).
Proof.
  intros x H. inversion H; subst.
  (* the singleton context pins the bound skeleton to [capP] *)
  assert (Hb : b = abind_var_skl capP)
    by (clear - H1; cbn in H1; destruct H1 as [Heq | Habs];
        [ congruence | contradiction ]).
  subst b. cbn in H2. inversion H2; subst.
  (* the join premise sits one hypothesis later since the base rows gained
     the counterpart-wf premise (hand-off §5) *)
  cbn [pskl_to_bskl_syn bskl_to_uskl] in H6.
  (* ⚙ [NM]/[Θ] are strict-implicit here (Set Implicit Arguments) *)
  exact (cap_no_join H6).
Qed.

(** §3b — and it is ONLY the leaf datum that rejects it: the context entry,
    the lookup and the plain join are all still there. *)
Lemma cap_entry_wf : forall x,
  binds x (abind_var_skl capP) ((x ~ abind_var_skl capP) ++ nil)
  /\ abind_to_pskl (abind_var_skl capP) = Some capP.
Proof. intros x. split; [ cbn; left; reflexivity | reflexivity ]. Qed.

(** ⚠️ [cap_var_plain_join] RETRACTED 2026-08-12 with [cap_plain] above: it
    read the join off the plain relation, which no longer derives the pair.
    §3b's claim survives in the pieces that DO still hold — [cap_entry_wf]
    above for the entry and the lookup, and [cap_consis] / [cap_is_sskl] in §1
    for every premise of [__infer] EXCEPT the refinement.  So the leaf datum
    remains the one and only thing that excludes the configuration; it is now
    simply demanded by the rule instead of by a mirror. *)
