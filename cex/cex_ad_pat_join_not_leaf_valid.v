(** ⚠️ THE EMBEDDED SUBTYPING PREMISE OF [ad_pat] / [ad_sd_typing] IS NOT
    LEAF-VALID, SO thm:complete-skeleton-inference AND thm:complete-type-
    inference CANNOT BE STATED OVER THE PLAIN JUDGEMENTS.

    Section D, scouting item 1 (docs/HANDOFF-section-d.md §6.1 / §6.2).

    THE SITUATION.  [a_sub_complete_thm] (thm:complete-subtyping) takes its
    declarative join as [ad_pat_sub_gv] — the LEAF-VALID mirror, which carries
    at every consistency leaf the subject-refinement datum
    [Θ ⨟ ∅ ⊢ᵣₚᵃ ⌊R⌋ˢ ⊳ ⌊Q⌋].  That is the third solution condition of the
    paper's own AUGMENTED thm:complete-consistency (consistency-proofs.tex:
    2230-2242), which [a_consis_complete_thm] also carries; subtyping needs it
    at the LEAVES rather than at the root because at the root it is vacuous
    (cex_p7_univ_ghost_r_vacuous.v, cex_p7_third_premise_forall.v).

    But [ad_pat] / [ad_sd_typing] (decorated_algo/def_decl_algo_typing.v)
    embed the PLAIN [ad_pat_sub] in their Unit / Var / Anno rows.  So a
    completeness proof that inducts on one of those judgements arrives at a
    base row holding a plain join and cannot invoke thm:complete-subtyping.

    THE FINDING BELOW: the gap is real, not a bookkeeping artefact.  The
    CAPTURE configuration of docs/DESIGN-subtyping.md §3.1 —

        subject  ∀X.◇      counterpart  ∀ˢX.X

    — has a plain [ad_pat_sub] derivation (§1) and NO [ad_pat_sub_gv] one
    (§2), and it is reachable from [ad_pat] as [P-Var] at an entry
    [x : ∀X.◇] (§3).  Consistency's ∀-rows push the rigid [X] into Θ, so the
    ghost may be FILLED with it; refinement's ∀-row pushes it into Δ and
    [ad_refine_pskl__hole]'s fill is Δ-free BY RULE — so the leaf datum fails
    exactly where the paper's no-capture discipline bites.

    CONSEQUENCE.  For the completeness direction the embedded premise must be
    the leaf-valid one, i.e. the "solution to the skeleton/type inference
    problem" must carry the leaf data, exactly as the paper's own solution
    notion for CONSISTENCY already does.  Registered in docs/PAPER-GAPS.md. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_sub_hyg.
Require Import src.frost.decorated_algo.def_decl_algo_typing.

Set Implicit Arguments.

(** the capture configuration: subject [∀X.◇], counterpart [∀ˢX.X] *)
Definition capR : uskl := uskl_all_syn uskl_hole.
Definition capQ : bskl := bskl_all_syn (bskl_var_b 0).
Definition capP : pskl := pskl_all_syn pskl_hole.

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
    [ad_pat_consis__hole] — which demands the fill Θ-well-scoped — may pick
    [α] itself.  This is the capture the refinement judgement forbids. *)
Lemma cap_consis : forall Θ, empty ⨟ Θ ⊢ₛᵃ capR ∼ capQ.
Proof.
  intros Θ. apply ad_pat_consis__forall_syn with (L := empty).
  intros α Hα. cbn.
  apply (ad_pat_consis__hole (P := pskl_var_f α)); [ reflexivity | ].
  apply a_wf_pskl__var. right. unfold a_binds_tvar. eauto.
Qed.

Lemma cap_plain : forall NM Θ, empty ⨟ Θ ⊢ₛᵃ[ NM | mode_ti ] capR ⩽ capQ.
Proof.
  intros NM Θ. apply ad_pat_sub__infer;
    [ reflexivity | apply cap_consis | apply cap_is_sskl ].
Qed.

(* ===================================================================== *)
(*  §2  NO leaf-valid join exists                                         *)
(* ===================================================================== *)

(** ⭐ Refinement's ∀-row puts the rigid into **Δ**, and
    [ad_refine_pskl__hole]'s fill must be well-scoped in Θ ALONE — so ANY Θ
    that does not already contain the rigid refutes the fill. *)
Lemma cap_hole_no_fill : forall Θ α,
  α `notin` dom Θ ->
  ~ (Θ ⨟ (add α empty) ⊢ᵣₚᵃ pskl_hole ⊳ (pskl_var_f α)).
Proof.
  intros Θ α Hα H. inversion H; subst.
  - (* __hole : the fill would have to be well-scoped in Θ alone *)
    match goal with Hw : _ ⨟ _ ⊢ₚₛᵃ _ |- _ => inversion Hw; subst end.
    match goal with Hd : _ \/ _ |- _ => destruct Hd as [Hin | Hb] end.
    + clear - Hin; fsetdec.
    + destruct Hb as [Hb | [Hb | [? Hb]]]; apply binds_In in Hb;
        clear - Hb Hα; fsetdec.
  - (* __flex_r : [α] would have to be a flexible of Θ *)
    match goal with Hb : binds _ _ _ |- _ =>
      apply binds_In in Hb; clear - Hb Hα; fsetdec end.
Qed.

Lemma cap_no_refine : forall Θ,
  ~ (Θ ⨟ empty ⊢ᵣₚᵃ capP ⊳ (bskl_to_pskl capQ)).
Proof.
  intros Θ H. unfold capP, capQ in H. cbn in H.
  inversion H; subst.
  match goal with
  | Hf : forall α, α `notin` ?L -> _ |- _ =>
      pick fresh β for (L `union` dom Θ);
      pose proof (Hf β ltac:(clear - Fr; fsetdec)) as Hβ; cbn in Hβ
  end.
  eapply cap_hole_no_fill; [ | exact Hβ ]. clear - Fr; fsetdec.
Qed.

Lemma cap_no_gv : forall NM Θ,
  ~ (exists n, ad_pat_sub_gv n NM mode_ti empty Θ capR capQ).
Proof.
  intros NM Θ [n H]. inversion H; subst; try congruence.
  (* the only row concluding at [mode_ti] is [__infer]; its leaf datum is
     exactly the refinement refuted above *)
  eapply cap_no_refine; eassumption.
Qed.

(* ===================================================================== *)
(*  §3  … and the configuration is REACHABLE from [ad_pat]                *)
(*                                                                        *)
(*  ⚠️ This is what forces the rule change of hand-off §6.2: as long as     *)
(*  [ad_pat]'s base rows embed the PLAIN [ad_pat_sub], the judgement below *)
(*  is derivable and thm:complete-skeleton-inference can say NOTHING about *)
(*  it, because §2 refutes its leaf datum.  Once the rows embed            *)
(*  [ad_pat_sub_v] this derivation disappears — which is the point.        *)
(* ===================================================================== *)

Lemma cap_reachable : forall x,
  ((x ~ abind_var_skl capP) ++ nil) ⊢ᵃ[ mode_ti ] (exp_var_f x) ⇨ capQ.
Proof.
  intros x.
  apply ad_pat__var with (P := capP) (b := abind_var_skl capP);
    [ eauto | reflexivity | ].
  cbn [pskl_to_bskl_syn bskl_to_uskl].
  apply cap_plain.
Qed.
