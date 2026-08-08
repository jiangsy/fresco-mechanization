(** COMPLETENESS OF TYPE INFERENCE (section D, thm:complete-type-inference)
    — the landing file for theorem 4 and its kit.

    So far: [a_typing_rename_tm], theorem 4's K6 — the binder rows of
    [a_typing] are cofinite in the term variable and share their outputs
    across the family, so completeness must generate the family from the
    IH's one fresh instance.  Same HYBRID as [a_pat_rename_tm]
    (prop_completeness_pat.v): SWAP the type-level data, SUBSTITUTE in the
    term.

    ⭐ MEASURE SETTLED (2026-08-07 scouting): plain STRUCTURAL induction on
    [ad_sd_typing] suffices — NO height mirror [ad_sd_typing_n].  Every IH
    application in the paper's proof (proofs.tex:617-1395) is on a direct
    premise derivation, and the force that broke structural induction in
    theorem 3 — the binder entry being only ⪯-related to the rule's, needing
    [ad_ctx_precise_pat] on the DERIVATION — has no typing analogue:
    [a_inc__var] relates term entries up to [≡ᵗ] BY RULE (def_meta.v), which
    absorbs exactly the [θ''A' ≡ᵗ A] discrepancy the binder cases produce
    ("precision on types is equivalence", literally).  The [_step] rows'
    same-term recursion only kills [size_exp], which is not needed.

    The statement is [typ_complete_concl] below, factored like
    [pat_complete_concl]; the base rows feed [a_sub_complete_thm] at TY,
    with the run's output packaged as a painted [ptyp] by
    [a_sub_ty_ghost_free_output] (prop_ty_core.v) and the optimality
    conclusion converted by [ad_precise_painting_tyequiv]'s idiom (a
    precision between two type paintings IS a type equivalence, via
    [ad_refine_syn_inh_tyequiv]).

    ⛔ Still owed: the Var/Anno base rows (Anno consumes prop_ty_core's
    [a_typing_tc_rigid_output]), Freeze, the binder rows (term-binder
    family via [a_typing_rename_tm]; the two tvar-[_step] rows need a
    tvar family generation), App (invokes THEOREM 3), the glue, and
    §6.3's #2/#3 rule-level obligations. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_sub_hyg.
Require Import src.frost.decorated_algo.def_decl_algo_typing.
Require Import src.frost.decorated_algo.prop_ctx_mono.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.decorated_algo.prop_decorate.
Require Import src.frost.algo.prop_sub_msubst_equiv.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.prop_completeness_sub_gen.
Require Import src.frost.algo.prop_completeness_sub.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_completeness_consis.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_consis_rename.
Require Import src.frost.algo.prop_soundness_consis.
Require Import src.frost.algo.prop_wf_output.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_solve_sub.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Require Import src.frost.algo.prop_soundness_sub.
Require Import src.frost.algo.prop_soundness_pat.
Require Import src.frost.algo.prop_suffix_erase.
Require Import src.frost.algo.prop_soundness_typing.
Require Import src.frost.algo.prop_precise_sub.
Require Import src.frost.algo.prop_completeness_pat.
Require Import src.frost.algo.prop_ty_core.
Require Import src.frost.algo.prop_ty_scope.


(* ===================================================================== *)
(*  THEOREM 4 — the statement, factored like [pat_complete_concl]         *)
(* ===================================================================== *)

Definition typ_complete_concl (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (κ : metasubst) (Θ : aenv) (B : btyp) : Prop :=
  exists A1 Θ1,
    a_typing M Θ0 P0 e A1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B)).

(* ===================================================================== *)
(*  The two tails every base row shares                                   *)
(* ===================================================================== *)

(** The counterpart's wf, read off the fused rule's join: scope from
    [ad_pat_sub_target_wf], ghost-freeness structural (it is a [btyp]'s
    erasure). *)
Lemma typ_counterpart_wf : forall NM M Ψ Θ R (B : btyp),
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ (btyp_to_bskl B) ->
  Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B)).
Proof.
  intros NM M Ψ Θ R B Hj.
  rewrite bskl_to_pskl_btyp.
  apply a_wf_ptyp_to_wf_pskl.
  eapply a_wf_ptyp_of_scope_pskl;
    [ | rewrite <- bskl_to_pskl_btyp; reflexivity ].
  eapply ad_pat_sub_target_wf. exact Hj.
Qed.

(** The optimality tail every base row shares: a PRECISION between two
    type paintings IS the type equivalence the conclusion carries. *)
Lemma typ_opt_tail : forall Θ ζ A1 (B : btyp),
  a_wf_aenv Θ ->
  Θ ⨟ empty ⊢ₚᵣᵃ
    (bskl_to_pskl (msubst_bskl ζ (pskl_to_bskl_syn (ptyp_to_pskl A1))))
    ⊑ (bskl_to_pskl (btyp_to_bskl B)) ->
  Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B).
Proof.
  intros Θ ζ A1 B HwfΘ Hprec.
  rewrite msubst_bskl_syn_erase, msubst_pskl_embed_ptyp, bskl_to_pskl_btyp
    in Hprec.
  unfold ad_precise in Hprec.
  rewrite (pskl_to_bskl_inh_ptyp (btyp_to_ptyp B)) in Hprec.
  pose proof (ad_refine_syn_inh_tyequiv Hprec HwfΘ
                (msubst_ptyp ζ A1) (ptyp_to_btyp_inh (btyp_to_ptyp B))
                eq_refl eq_refl) as Heqc.
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh in Heqc.
  exact Heqc.
Qed.

(* ===================================================================== *)
(*  The Unit base row                                                     *)
(* ===================================================================== *)

Lemma a_typing_complete_unit : forall M Θ0 P0 κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  Θ ⊢ˢᵃ[ M ] exp_unit ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl M Θ0 P0 exp_unit κ Θ B.
Proof.
  intros M Θ0 P0 κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub_v _ _ _ _ _ _ |- _ => destruct H as [njoin Hjoin]
  end.
  assert (HwfQ : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B)))
    by (eapply typ_counterpart_wf;
        exact (ad_pat_sub_of_v (ex_intro _ njoin Hjoin))).
  destruct (@a_sub_complete_thm njoin a_sub_mode_ty M Θ0 P0
              pskl_unit (ptyp_to_uskl_syn ptyp_unit) Θ κ (btyp_to_bskl B)
              Hwf0 HwfΘ HwfP0
              ltac:(apply a_wf_pskl__unit)
              ltac:(intros Hc; discriminate)
              ltac:(intros _; exact Hmod)
              Hinc
              (slack_unit Θ κ)
              Hjoin Href HwfQ
              ltac:(intros _; rewrite <- pskl_to_uskl_ptyp;
                    apply pskl_to_uskl_ptyp_ghost_free; apply lc_ptyp_unit))
    as [P1 [Θ1 [Hrun Hopt]]].
  (* the run's output is a painted type (T4-K1) *)
  assert (HgfP1 : pskl_ghost_free P1)
    by (eapply a_sub_ty_ghost_free_output; [ exact Hrun | exact I ]).
  destruct (pskl_ghost_free_to_ptyp P1 HgfP1) as [A1 ->].
  exists A1, Θ1. split; [ apply a_typing__unit; exact Hrun | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  apply typ_opt_tail; [ exact HwfΘ | exact Hprec ].
Qed.

(* ===================================================================== *)
(*  The Var base row                                                      *)
(* ===================================================================== *)

Lemma a_typing_complete_var : forall M Θ0 P0 x κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  Θ ⊢ˢᵃ[ M ] (exp_var_f x) ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl M Θ0 P0 (exp_var_f x) κ Θ B.
Proof.
  intros M Θ0 P0 x κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub_v _ _ _ _ _ _ |- _ => destruct H as [njoin Hjoin]
  end.
  match goal with
  | H : binds x (abind_var_typ _) Θ |- _ => rename H into Hb
  end.
  (* K2 : the entry's preimage, with its ≡ᵗ slack *)
  destruct (@a_inc_binds_var_typ_rev Θ0 κ Θ x A Hinc Hwf0 Hb) as [A0 [Hb0 Heq]].
  assert (HwfA0 : a_wf_ptyp Θ0 A0)
    by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
  assert (HwfA : a_wf_ptyp Θ A)
    by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
  destruct (@a_sub_complete_thm njoin a_sub_mode_ty M Θ0 P0
              (ptyp_to_pskl A0) (ptyp_to_uskl_syn A) Θ κ (btyp_to_bskl B)
              Hwf0 HwfΘ HwfP0
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA0)
              ltac:(intros Hc; discriminate)
              ltac:(intros _; exact Hmod)
              Hinc
              ltac:(rewrite pskl_to_uskl_ptyp, <- msubst_ptyp_to_uskl_syn;
                    apply a_tyequiv_to_uskl; [ exact Heq | exact HwfΘ ])
              Hjoin Href
              ltac:(eapply typ_counterpart_wf;
                    exact (ad_pat_sub_of_v (ex_intro _ njoin Hjoin)))
              ltac:(intros _; rewrite <- pskl_to_uskl_ptyp;
                    apply pskl_to_uskl_ptyp_ghost_free;
                    eapply a_wf_ptyp_lc; exact HwfA))
    as [P1 [Θ1 [Hrun Hopt]]].
  assert (HgfP1 : pskl_ghost_free P1)
    by (eapply a_sub_ty_ghost_free_output;
        [ exact Hrun | apply ptyp_to_pskl_ghost_free ]).
  destruct (pskl_ghost_free_to_ptyp P1 HgfP1) as [A1 ->].
  exists A1, Θ1.
  split; [ eapply a_typing__var; [ exact Hb0 | exact Hrun ] | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  apply typ_opt_tail; [ exact HwfΘ | exact Hprec ].
Qed.

(* ===================================================================== *)
(*  The Anno base row — TWO stages: the body at [(TC, ⌈A⌉)] (the IH),     *)
(*  then the fused subtyping ([a_sub_complete_thm]).  ⭐ The body run      *)
(*  returns the annotation ITSELF ([a_typing_tc_rigid_output],            *)
(*  prop_ty_core.v) — the fact [AT-Anno]'s premise demands and the        *)
(*  paper's Anno case asserts by metavariable pun.  The optimality glues  *)
(*  the two factorings by [a_inc_equiv_glue]; the dom side condition is   *)
(*  [a_inc_id_flex_preserve] at the body run's own identity increase.     *)
(* ===================================================================== *)

Lemma a_typing_complete_anno : forall M Θ0 P0 e A κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_anno e A) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_anno e A) ->
  (forall M' Θ0' P0' κ' Θ' B',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp e ->
     Θ' ⊢ˢᵃ[ M' ] e ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' e κ' Θ' B') ->
  Θ ⊢ˢᵃ[ M ] (exp_anno e A) ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl M Θ0 P0 (exp_anno e A) κ Θ B.
Proof.
  intros M Θ0 P0 e A κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hskl Hlc IH Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub_v _ _ _ _ _ _ |- _ => destruct H as [njoin Hjoin]
  end.
  match goal with
  | H : ad_sd_typing mode_tc Θ e _ |- _ => rename H into Hde
  end.
  simpl in Hrig.
  assert (Hrige : forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (HrigA : forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlce : lc_exp e) by (inversion Hlc; assumption).
  assert (HlcA : lc_ptyp A) by (inversion Hlc; assumption).
  assert (HwfA0 : a_wf_ptyp Θ0 A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA; exact Hα ]).
  assert (HwfAΘ : a_wf_ptyp Θ A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA
        | intros α Hα; left; eapply a_inc_binds_tvar;
            [ exact Hinc | apply HrigA; exact Hα ] ]).
  assert (HmsA : msubst_ptyp κ A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc | exact Hwf0 | exact HrigA ]).
  assert (HwfpA0 : Θ0 ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl A))
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfA0).
  (* ---- 1. the BODY stage, by the IH at (TC, ⌈A⌉) ---- *)
  destruct (IH mode_tc Θ0 (ptyp_to_pskl A) κ Θ (ptyp_to_btyp_inh A)
              Hwf0 HwfΘ HwfpA0
              (a_ty_mode_compat__tc A)
              Hinc Hrige Hskl Hlce Hde
              ltac:(rewrite msubst_pskl_embed_ptyp, HmsA,
                      <- (pskl_to_bskl_inh_ptyp A);
                    apply ad_refine_syn_refl_inh;
                    apply a_wf_ptyp_to_wf_pskl; exact HwfAΘ))
    as [A1' [Θmid [HrunB HoptB]]].
  (* ⭐ the run returned the ANNOTATION ITSELF (prop_ty_core) *)
  assert (HA1' : A1' = A).
  { eapply a_typing_tc_rigid_output; [ exact HrunB | ].
    intros α Hα.
    pose proof (a_wf_aenv_uniq Hwf0) as Hu.
    split; [ apply HrigA; exact Hα | ].
    split.
    - intros Hb.
      pose proof (binds_unique _ _ _ _ _ Hb (HrigA α Hα) Hu) as Hc.
      discriminate Hc.
    - intros τ Hb.
      pose proof (binds_unique _ _ _ _ _ Hb (HrigA α Hα) Hu) as Hc.
      discriminate Hc. }
  subst A1'.
  (* the run's own identity increase + the mid context's wf *)
  assert (Hexpe : a_wf_exp Θ0 e)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlce | intros α Hα; left; apply Hrige; exact Hα ]).
  destruct (a_typing_sound HrunB Hwf0 Hskl HwfpA0
              (a_ty_mode_compat__tc A) Hexpe)
    as [HleB [Hwfmid _]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (HoptB κb Hidb Hincb) as [ζb [Hζb [Heqvb _]]].
  assert (HrigMid : forall α, α `in` ftvar_in_ptyp A ->
             binds α abind_tvar Θmid)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincb | apply HrigA; exact Hα ]).
  assert (HwfAmid : a_wf_ptyp Θmid A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigMid; exact Hα ]).
  assert (HmsAζb : msubst_ptyp ζb A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζb | exact Hwfmid | exact HrigMid ]).
  assert (HwfP0mid : Θmid ⨟ empty ⊢ₚₛᵃ P0).
  { pose proof (a_wf_pskl_msubst_inc Hincb Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id P0 Hidb) in Hw. exact Hw. }
  (* ---- 2. transport the refinement to ζb ---- *)
  assert (Hσ : msubst_compose ζb κb ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hincb | exact Hwf0 | exact Hwfmid | exact Hζb ]).
  assert (HwfQ : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B)))
    by (eapply typ_counterpart_wf;
        exact (ad_pat_sub_of_v (ex_intro _ njoin Hjoin))).
  assert (Hpp : Θ ⨟ empty ⊢ₚᵣᵃ (msubst_pskl (msubst_compose ζb κb) P0)
                  ⊑ (msubst_pskl κ P0)).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
      | exact Heqvb | clear; fsetdec ]. }
  assert (HrefT : Θ ⨟ empty ⊢ᵣᵃ
                    (pskl_to_bskl_inh (msubst_pskl (msubst_compose ζb κb) P0))
                    ⊳ (btyp_to_bskl B)).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact Href | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQ ]. }
  assert (Hms : msubst_pskl (msubst_compose ζb κb) P0 = msubst_pskl ζb P0).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwfmid | exact Hidb | exact Hincb | exact Hζb
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfP0 | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ] ]. }
  rewrite Hms in HrefT.
  (* ---- 3. the SUB stage ---- *)
  destruct (@a_sub_complete_thm njoin a_sub_mode_ty M Θmid P0
              (ptyp_to_pskl A) (ptyp_to_uskl_syn A) Θ ζb (btyp_to_bskl B)
              Hwfmid HwfΘ HwfP0mid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAmid)
              ltac:(intros Hc; discriminate)
              ltac:(intros _; exact Hmod)
              Hζb
              ltac:(rewrite pskl_to_uskl_ptyp, <- msubst_ptyp_to_uskl_syn,
                      HmsAζb;
                    apply a_uskl_tyequiv_refl;
                    rewrite <- pskl_to_uskl_ptyp; apply pskl_to_uskl_lc;
                    apply lc_ptyp_to_pskl; exact HlcA)
              Hjoin HrefT HwfQ
              ltac:(intros _; rewrite <- pskl_to_uskl_ptyp;
                    apply pskl_to_uskl_ptyp_ghost_free; exact HlcA))
    as [P1 [Θ2 [HrunS HoptS]]].
  assert (HgfP1 : pskl_ghost_free P1)
    by (eapply a_sub_ty_ghost_free_output;
        [ exact HrunS | apply ptyp_to_pskl_ghost_free ]).
  destruct (pskl_ghost_free_to_ptyp P1 HgfP1) as [B1 ->].
  (* ---- 4. the run ---- *)
  exists B1, Θ2.
  split; [ eapply a_typing__anno; [ exact HrunB | exact HrunS ] | ].
  (* ---- 5. optimality: glue the two stages ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincb | exact Hid1 | exact Hidb ]).
  destruct (proj1 a_sub_output_wf_bundle _ _ _ _ _ _ _ HrunS
              Hwfmid HwfP0mid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAmid))
    as [HleS [Hwf2 _]].
  destruct HleS as [[κs [Hids Hincs]] _].
  destruct (HoptS κs Hids Hincs) as [ζs [Hζs [Heqvs Hprecs]]].
  exists ζs.
  split; [ exact Hζs | ].
  split.
  { assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζs κb) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θmid) (Θfin := Θ2) (κ1b := κs) (ζ1 := ζb);
        [ exact Hwf0 | exact Hwfmid | exact Hwf2 | exact HwfΘ
        | exact Hidb | exact Hids
        | intros α Hα;
          pose proof (a_inc_dom_flex Hincb Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hincs | exact Hwfmid
            | eapply a_inc_id_flex_preserve;
                [ exact Hincb | exact Hidb | exact Hwf0 | exact Hfα ] ]
        | exact Hincb | exact Hincs | exact Hζb | exact Hζs
        | exact Heqvb | exact Heqvs ]. }
    rewrite Heqκ. exact Hglue. }
  apply typ_opt_tail; [ exact HwfΘ | exact Hprecs ].
Qed.

(* ===================================================================== *)
(*  The Freeze row's kit: coercion composite, the [≡ᵗ]→[≡ˢ] embedding,    *)
(*  wf transport along [≡ᵗ], and K1's typing analogue (target wf,         *)
(*  bottom-up).                                                            *)
(* ===================================================================== *)

(** The syn twin of [pskl_to_bskl_inh_ptyp]. *)
Lemma pskl_to_bskl_syn_ptyp : forall A,
  pskl_to_bskl_syn (ptyp_to_pskl A) = btyp_to_bskl (ptyp_to_btyp_syn A).
Proof. induction A; simpl; f_equal; auto. Qed.

(* [a_tyequiv_embed_pskl] moved to prop_soundness_typing.v (2026-08-08). *)

(** Well-formedness transports along [≡ᵗ], both ways (the flex-def row
    swaps a variable for its definition, both wf in a wf context).  Stated
    over any binds-including context so the ∀ row's extension composes. *)
Lemma a_tyequiv_wf_iff : forall Θ A B,
  Θ ⊢ A ≡ᵗ B ->
  forall Θ',
  (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  (a_wf_ptyp Θ' A -> a_wf_ptyp Θ' B) /\
  (a_wf_ptyp Θ' B -> a_wf_ptyp Θ' A).
Proof.
  intros Θ A B H; induction H; intros Θ' Hincl Hwf'.
  - split; intros HA; exact HA.
  - destruct (IHa_tyequiv Θ' Hincl Hwf') as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - destruct (IHa_tyequiv1 Θ' Hincl Hwf') as [H1l H1r].
    destruct (IHa_tyequiv2 Θ' Hincl Hwf') as [H2l H2r].
    split;
      [ intros HA; exact (H2l (H1l HA))
      | intros HC; exact (H1r (H2r HC)) ].
  - split.
    + intros _. eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | ].
      apply Hincl. exact H.
    + intros _. apply a_wf_ptyp__var.
      right; right. exists τ. apply Hincl. exact H.
  - split; intros HA; inversion HA; subst;
      apply a_wf_ptyp__arrow;
      first [ eapply (proj1 (IHa_tyequiv1 Θ' Hincl Hwf')); eassumption
            | eapply (proj2 (IHa_tyequiv1 Θ' Hincl Hwf')); eassumption
            | eapply (proj1 (IHa_tyequiv2 Θ' Hincl Hwf')); eassumption
            | eapply (proj2 (IHa_tyequiv2 Θ' Hincl Hwf')); eassumption ].
  - split; intros HA; inversion HA; subst;
    match goal with
    | Hfam : forall α, α `notin` ?L1 ->
               a_wf_ptyp _ (open_ptyp_wrt_ptyp _ _) |- _ =>
        apply a_wf_ptyp__all with (L := L `union` L1 `union` dom Θ');
        intros α Hα;
        (assert (Hwfx : a_wf_aenv ((α ~ abind_tvar) ++ Θ'))
          by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]));
        (assert (Hinclx : forall x (b : abind),
                   binds x b Θ -> binds x b ((α ~ abind_tvar) ++ Θ'))
          by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb));
        first
          [ eapply (proj1 (H0 α ltac:(clear - Hα; fsetdec) _ Hinclx Hwfx));
            apply Hfam; clear - Hα; fsetdec
          | eapply (proj2 (H0 α ltac:(clear - Hα; fsetdec) _ Hinclx Hwfx));
            apply Hfam; clear - Hα; fsetdec ]
    end.
Qed.

(** Strip a TERM entry off a type's wf (term entries are invisible to
    [a_binds_tvar]). *)
Lemma a_wf_ptyp_strip_tm_cons : forall x A0 Θ A,
  a_wf_ptyp ((x ~ abind_var_typ A0) ++ Θ) A ->
  a_wf_ptyp Θ A.
Proof.
  intros x A0 Θ A HwfA.
  apply a_wf_ptyp_of_lc_tvarish;
    [ eapply a_wf_ptyp_lc; exact HwfA | ].
  intros α Hα.
  pose proof (a_wf_ptyp_ftv_tvarish HwfA Hα) as Ht.
  destruct Ht as [Hr | [Hm | [τ Hd]]].
  - left. destruct (binds_cons_1 _ _ _ _ _ _ Hr) as [[_ Heq] | Hr'];
      [ discriminate Heq | exact Hr' ].
  - right; left.
    destruct (binds_cons_1 _ _ _ _ _ _ Hm) as [[_ Heq] | Hm'];
      [ discriminate Heq | exact Hm' ].
  - right; right. exists τ.
    destruct (binds_cons_1 _ _ _ _ _ _ Hd) as [[_ Heq] | Hd'];
      [ discriminate Heq | exact Hd' ].
Qed.

(** ⭐ K1's typing analogue, BOTTOM-UP: a syntax-directed typing's TARGET
    type is well formed (the base rows read it off their joins, the ≡ᵗ
    premises transport it, the binder rows strip their term entry). *)
Lemma ad_sd_typing_target_wf : forall M Θ e (B : btyp),
  Θ ⊢ˢᵃ[ M ] e ⦂ B ->
  a_wf_aenv Θ ->
  a_wf_ptyp Θ (btyp_to_ptyp B).
Proof.
  intros M Θ e B H; induction H; intros Hwf;
    try match goal with
        | Hj : ad_pat_sub_v _ _ _ _ _ _ |- _ =>
            destruct Hj as [n Hj];
            eapply a_wf_ptyp_of_scope_pskl;
              [ | rewrite <- bskl_to_pskl_btyp; reflexivity ];
            eapply ad_pat_sub_target_wf; exact (ad_pat_sub_of_gv Hj)
        end.
  - (* freeze *)
    rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
    specialize (IHad_sd_typing Hwf).
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in IHad_sd_typing.
    eapply (proj1 (a_tyequiv_wf_iff H0 (fun x b h => h) Hwf)).
    exact IHad_sd_typing.
  - (* abs_check_step *)
    simpl.
    apply a_wf_ptyp__all with (L := L `union` dom Θ).
    intros α Hα.
    rewrite <- btyp_to_ptyp_open.
    apply H1; [ clear - Hα; fsetdec | ].
    apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ].
  - (* abs_check_base *)
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite btyp_to_ptyp_ptyp_to_btyp_inh. exact H.
    + eapply a_wf_ptyp_strip_tm_cons with (x := x) (A0 := A).
      apply H2; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H | exact Hwf ].
  - (* abs_anno_check_step *)
    simpl.
    apply a_wf_ptyp__all with (L := L `union` dom Θ).
    intros α Hα.
    rewrite <- btyp_to_ptyp_open.
    apply H1; [ clear - Hα; fsetdec | ].
    apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ].
  - (* abs_anno_check_base *)
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
      eapply (proj1 (a_tyequiv_wf_iff H0 (fun y b h => h) Hwf)).
      exact H.
    + eapply a_wf_ptyp_strip_tm_cons with (x := x) (A0 := A).
      apply H3; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H | exact Hwf ].
  - (* abs *)
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite btyp_to_ptyp_ptyp_to_btyp_inh. exact H0.
    + eapply a_wf_ptyp_strip_tm_cons with (x := x) (A0 := A).
      apply H3; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H0 | exact Hwf ].
  - (* abs_anno *)
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite H2.
      eapply (proj1 (a_tyequiv_wf_iff H1 (fun y b h => h) Hwf)).
      exact H0.
    + eapply a_wf_ptyp_strip_tm_cons with (x := x) (A0 := A).
      apply H5; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H0 | exact Hwf ].
  - (* app *)
    specialize (IHad_sd_typing1 Hwf).
    simpl in IHad_sd_typing1.
    inversion IHad_sd_typing1; subst.
    assumption.
Qed.


(* ===================================================================== *)
(*  The Freeze row — TWO stages: the body at [(TI, ◇)] (the IH), then     *)
(*  the consistency stage ([a_consis_complete_thm]) with the subject      *)
(*  transported along [≡ˢ] to the declarative types.  The conclusion's    *)
(*  [≡ᵗ] comes from the consis run's own subject-≡-input                  *)
(*  ([a_consis_chk_tyequiv]) pushed through the witnesses.                *)
(* ===================================================================== *)

Lemma a_typing_complete_freeze : forall Θ0 P0 e κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_freeze e) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_freeze e) ->
  (forall M' Θ0' P0' κ' Θ' B',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp e ->
     Θ' ⊢ˢᵃ[ M' ] e ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' e κ' Θ' B') ->
  Θ ⊢ˢᵃ[ mode_tc ] (exp_freeze e) ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl mode_tc Θ0 P0 (exp_freeze e) κ Θ B.
Proof.
  intros Θ0 P0 e κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hskl Hlc IH Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_sd_typing mode_ti Θ e (ptyp_to_btyp_syn ?BB) |- _ =>
      rename H into Hde; rename BB into B0
  end.
  match goal with
  | H : Θ ⊢ B0 ≡ᵗ ?AA |- _ => rename H into Heq0; rename AA into A
  end.
  inversion Hmod; subst.
  match goal with
  | |- typ_complete_concl _ _ (ptyp_to_pskl ?AP) _ _ _ _ => rename AP into Ap
  end.
  simpl in Hrig.
  assert (Hlce : lc_exp e) by (inversion Hlc; assumption).
  (* wf of the two declarative types at Θ, off the derivation (K1-typing) *)
  assert (HwfB0 : a_wf_ptyp Θ B0).
  { pose proof (ad_sd_typing_target_wf Hde HwfΘ) as Hw.
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hw. exact Hw. }
  assert (HwfA : a_wf_ptyp Θ A)
    by (eapply (proj1 (a_tyequiv_wf_iff Heq0 (fun x b h => h) HwfΘ));
        exact HwfB0).
  (* ---- 1. the BODY stage at (TI, ◇) ---- *)
  destruct (IH mode_ti Θ0 pskl_hole κ Θ (ptyp_to_btyp_syn B0)
              Hwf0 HwfΘ (a_wf_pskl__hole _ _) a_ty_mode_compat__ti Hinc
              Hrig Hskl Hlce Hde
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    rewrite <- pskl_to_bskl_syn_ptyp;
                    apply ad_refine_syn__hole;
                    apply a_wf_ptyp_to_wf_pskl; exact HwfB0))
    as [B' [Θmid [HrunB HoptB]]].
  assert (Hexpe : a_wf_exp Θ0 e)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlce | intros α Hα; left; apply Hrig; exact Hα ]).
  destruct (a_typing_sound HrunB Hwf0 Hskl (a_wf_pskl__hole _ _)
              a_ty_mode_compat__ti Hexpe)
    as [HleB [Hwfmid [HwfB'mid _]]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (HoptB κb Hidb Hincb) as [ζb [Hζb [Heqvb HeqB']]].
  rewrite btyp_to_ptyp_ptyp_to_btyp_syn in HeqB'.
  assert (HeqAll : Θ ⊢ (msubst_ptyp ζb B') ≡ᵗ A)
    by (eapply a_tyequiv__trans; [ exact HeqB' | exact Heq0 ]).
  assert (HwfApmid : Θmid ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl Ap)).
  { pose proof (a_wf_pskl_msubst_inc Hincb Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id _ Hidb) in Hw. exact Hw. }
  (* ---- 2. the transports for the consistency stage ---- *)
  assert (Hσ : msubst_compose ζb κb ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hincb | exact Hwf0 | exact Hwfmid | exact Hζb ]).
  set (Qb := btyp_to_bskl (ptyp_to_btyp_inh A)) in *.
  assert (HwfQb : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qb)).
  { unfold Qb. rewrite bskl_to_pskl_btyp, btyp_to_ptyp_ptyp_to_btyp_inh.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA. }
  assert (Hpp : Θ ⨟ empty ⊢ₚᵣᵃ
                  (msubst_pskl (msubst_compose ζb κb) (ptyp_to_pskl Ap))
                  ⊑ (msubst_pskl κ (ptyp_to_pskl Ap))).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
      | exact Heqvb | clear; fsetdec ]. }
  assert (HrefT : Θ ⨟ empty ⊢ᵣᵃ
                    (pskl_to_bskl_inh
                       (msubst_pskl (msubst_compose ζb κb) (ptyp_to_pskl Ap)))
                    ⊳ Qb).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact Href | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQb ]. }
  assert (Hms : msubst_pskl (msubst_compose ζb κb) (ptyp_to_pskl Ap)
                = msubst_pskl ζb (ptyp_to_pskl Ap)).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwfmid | exact Hidb | exact Hincb | exact Hζb
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfP0 | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ] ]. }
  rewrite Hms in HrefT.
  assert (Heqs : Θ ⊢ (ptyp_to_pskl (msubst_ptyp ζb B')) ≡ˢ (ptyp_to_pskl A))
    by (apply a_tyequiv_embed_pskl; exact HeqAll).
  assert (Hjoin : empty ⨟ Θ ⊢ₛᵃ
                    (pskl_to_uskl (msubst_pskl ζb (ptyp_to_pskl B'))) ∼ Qb).
  { rewrite msubst_pskl_embed_ptyp.
    eapply (proj2 (skl_tyequiv_consis_transport Heqs HwfΘ
                     (fun x b h => h))).
    rewrite pskl_to_uskl_ptyp.
    apply (ad_pat_consis_syn_bid HwfA (ptyp_to_btyp_inh A)
             (btyp_to_ptyp_ptyp_to_btyp_inh A)). }
  assert (Hrp : ad_refine_pskl_f empty Θ empty
                  (msubst_pskl ζb (ptyp_to_pskl B')) (bskl_to_pskl Qb)).
  { rewrite msubst_pskl_embed_ptyp.
    eapply (proj2 (skl_tyequiv_refine_pskl_f_transport Heqs HwfΘ
                     (fun x b h => h))).
    unfold Qb. rewrite bskl_to_pskl_btyp, btyp_to_ptyp_ptyp_to_btyp_inh.
    apply ad_refine_pskl_f_of_plain.
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA. }
  (* ---- 3. the consistency stage ---- *)
  destruct (a_consis_complete_thm Hwfmid HwfApmid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfB'mid)
              Hζb HwfΘ Hjoin
              ltac:(apply ad_refine_syn_f_of_plain; exact HrefT)
              Hrp)
    as [Qc [Θ2 [HcRun HoptC]]].
  (* ---- 4. the run ---- *)
  exists Ap, Θ2.
  split;
    [ eapply a_typing__freeze; [ exact HrunB | exists Qc; exact HcRun ] | ].
  (* ---- 5. optimality: glue the two stages ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincb | exact Hid1 | exact Hidb ]).
  destruct (a_consis_isub_wf_nil HcRun Hwfmid HwfApmid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfB'mid))
    as [HleC Hwf2].
  destruct HleC as [[κs [Hids Hincs]] _].
  destruct (HoptC κs Hids Hincs) as [ζs [Hζs [Heqvs _]]].
  exists ζs.
  split; [ exact Hζs | ].
  split.
  { assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζs κb) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θmid) (Θfin := Θ2) (κ1b := κs) (ζ1 := ζb);
        [ exact Hwf0 | exact Hwfmid | exact Hwf2 | exact HwfΘ
        | exact Hidb | exact Hids
        | intros α Hα;
          pose proof (a_inc_dom_flex Hincb Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hincs | exact Hwfmid
            | eapply a_inc_id_flex_preserve;
                [ exact Hincb | exact Hidb | exact Hwf0 | exact Hfα ] ]
        | exact Hincb | exact Hincs | exact Hζb | exact Hζs
        | exact Heqvb | exact Heqvs ]. }
    rewrite Heqκ. exact Hglue. }
  (* the ≡ᵗ conclusion via the run's own subject-≡-input *)
  assert (HwfApP : a_wf_ptyp Θmid Ap).
  { eapply a_wf_ptyp_of_scope_pskl; [ | reflexivity ].
    eapply a_wf_pskl_to_a_scope_pskl;
      [ exact HwfApmid | intros z b Hb; exact Hb
      | intros α Hα; clear - Hα; fsetdec ]. }
  assert (HeqIO : Θ2 ⊢ B' ≡ᵗ Ap)
    by (eapply a_consis_chk_tyequiv;
        [ exists Qc; exact HcRun | exact Hwfmid | exact HwfApP
        | exact HwfB'mid ]).
  assert (HeqIOΘ : Θ ⊢ (msubst_ptyp ζs B') ≡ᵗ (msubst_ptyp ζs Ap))
    by (eapply a_tyequiv_msubst; [ exact HeqIO | exact Hwf2 | exact Hζs ]).
  assert (HmsB' : msubst_ptyp (msubst_compose ζs κs) B' = msubst_ptyp ζs B')
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwfmid | exact Hwf2 | exact Hids | exact Hincs | exact Hζs
        | exact HwfB'mid ]).
  assert (HeqW : Θ ⊢ (msubst_ptyp ζb B') ≡ᵗ (msubst_ptyp ζs B')).
  { rewrite <- HmsB'.
    apply (@a_inc_equiv_msubst_ptyp B' Θmid ζb (msubst_compose ζs κs) Θ
             HwfB'mid Heqvs Hwfmid
             ltac:(eapply a_inc_msubst_lc; exact Hζb)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζs
                   | exact (is_id_msubst_values_lc Hids) ])). }
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact HeqIOΘ | ].
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact HeqW | exact HeqAll ].
Qed.

(* ===================================================================== *)
(*  The App row's glue helper                                             *)
(* ===================================================================== *)

(** Composing two IDENTITY metasubstitutions is the inner one VERBATIM
    (each entry (α, `α) maps to (α, κc·`α) = (α, `α)). *)
Lemma msubst_compose_id_id : forall κb κc,
  is_id_msubst κb ->
  is_id_msubst κc ->
  msubst_compose κc κb = κb.
Proof.
  intros κb κc Hb Hc.
  induction κb as [ | [α τ] κb' IH ]; [ reflexivity | ].
  apply is_id_msubst_inv in Hb as [-> Hb'].
  unfold msubst_compose in *. simpl.
  rewrite (IH Hb'). f_equal. f_equal.
  clear IH Hb'.
  induction κc as [ | [β σ] κc' IHc ]; [ reflexivity | ].
  apply is_id_msubst_inv in Hc as [-> Hc'].
  simpl. destruct (α == β) as [-> | Hne]; [ reflexivity | exact (IHc Hc') ].
Qed.

(* ===================================================================== *)
(*  The App row — THREE stages: the argument's SKELETON (THEOREM 3, at    *)
(*  (TC, ◇)), the function (the e1 IH at (fn M, P' → P0) — its domain     *)
(*  refinement is the paper's lemma:precision-preserves-refinement step,  *)
(*  its output a SYNTACTIC arrow by [a_typing_fn_arrow_shape]), and the   *)
(*  argument's CHECK (the e2 IH at (TC, ⌈Af⌉), the refinement subject-    *)
(*  transported along ≡ˢ).  The optimality glues all three factorings:    *)
(*  inner glue on stages 2+3, then the outer one with the composed        *)
(*  identity collapsed by [msubst_compose_id_id].                          *)
(* ===================================================================== *)

Lemma a_typing_complete_app : forall M Θ0 P0 e1 e2 κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_app e1 e2) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_app e1 e2) ->
  (* the e1 IH *)
  (forall M' Θ0' P0' κ' Θ' B',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp e1 ->
     Θ' ⊢ˢᵃ[ M' ] e1 ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' e1 κ' Θ' B') ->
  (* the e2 IH *)
  (forall M' Θ0' P0' κ' Θ' B',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp e2 ->
     Θ' ⊢ˢᵃ[ M' ] e2 ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' e2 κ' Θ' B') ->
  Θ ⊢ˢᵃ[ M ] (exp_app e1 e2) ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl M Θ0 P0 (exp_app e1 e2) κ Θ B.
Proof.
  intros M Θ0 P0 e1 e2 κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hskl HsklT
         Hlc IH1 IH2 Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat mode_tc Θ e2 (pskl_to_bskl_syn ?PP) |- _ =>
      rename H into Hd2s; rename PP into P
  end.
  match goal with
  | H : Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl ?BB) |- _ =>
      rename H into HrefP; rename BB into B1
  end.
  match goal with
  | H : ad_sd_typing (mode_fn M) Θ e1 (btyp_arrow B1 ?BB) |- _ =>
      rename H into Hd1; rename BB into B2
  end.
  match goal with
  | H : Θ ⊢ (btyp_to_ptyp B1) ≡ᵗ ?AA |- _ =>
      rename H into HeqA2; rename AA into A2
  end.
  match goal with
  | H : ad_sd_typing mode_tc Θ e2 (ptyp_to_btyp_inh A2) |- _ =>
      rename H into Hd2
  end.
  simpl in Hrig.
  assert (Hrig1 : forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hrig2 : forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlc1 : lc_exp e1) by (inversion Hlc; assumption).
  assert (Hlc2 : lc_exp e2) by (inversion Hlc; assumption).
  assert (Hexp2 : a_wf_exp Θ0 e2)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc2 | intros α Hα; left; apply Hrig2; exact Hα ]).
  (* the fn premise's target is wf — components pulled by inversion *)
  assert (HwfArr : a_wf_ptyp Θ (btyp_to_ptyp (btyp_arrow B1 B2)))
    by (eapply ad_sd_typing_target_wf; [ exact Hd1 | exact HwfΘ ]).
  simpl in HwfArr.
  inversion HwfArr; subst.
  match goal with
  | H1 : a_wf_ptyp Θ (btyp_to_ptyp B1),
    H2 : a_wf_ptyp Θ (btyp_to_ptyp B2) |- _ =>
      rename H1 into HwfB1; rename H2 into HwfB2
  end.
  assert (HwfP : Θ ⨟ empty ⊢ₚₛᵃ P).
  { pose proof (ad_pat_target_wf Hd2s HwfΘ) as Hw.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw. exact Hw. }
  (* ---- 1. the SKELETON stage : THEOREM 3 at (TC, ◇) ---- *)
  destruct (@a_pat_complete e2 mode_tc Θ0 pskl_hole κ Θ (pskl_to_bskl_syn P)
              Hwf0 HwfΘ (a_wf_pskl__hole _ _) a_sk_mode_compat__tc Hinc
              Hrig2 Hskl HsklT Hlc2 Hd2s
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    apply ad_refine_syn__hole; exact HwfP))
    as [P' [Θ1' [Hrun1 Hopt1]]].
  destruct (a_pat_sound Hrun1 Hwf0 Hskl (a_wf_pskl__hole _ _)
              a_sk_mode_compat__tc Hexp2)
    as [Hle1 [Hwf1 _]].
  destruct Hle1 as [[κ1b [Hid1b Hinc1b]] _].
  destruct (Hopt1 κ1b Hid1b Hinc1b) as [ζ1 [Hζ1 [Heqv1 Hprec1]]].
  rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec1.
  (* ---- 2. the FUNCTION stage : IH1 at (fn M, P' → P0) ---- *)
  assert (HwfP' : Θ1' ⨟ empty ⊢ₚₛᵃ P')
    by (eapply a_pat_output_wf;
        [ exact Hrun1 | exact Hwf0 | exact Hskl
        | apply a_wf_pskl__hole | apply a_sk_mode_compat__tc | exact Hexp2 ]).
  assert (HwfP0m : Θ1' ⨟ empty ⊢ₚₛᵃ P0).
  { pose proof (a_wf_pskl_msubst_inc Hinc1b Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id P0 Hid1b) in Hw. exact Hw. }
  assert (Hskl1 : forall y Ps, binds y (abind_var_skl Ps) Θ1' ->
             Θ1' ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    assert (Hb0 : binds y (abind_var_skl Ps) Θ0)
      by (eapply a_pat_tm_ge; [ exact Hrun1 | exact I | exact Hb ]).
    pose proof (a_wf_pskl_msubst_inc Hinc1b Hwf0 (Hskl _ _ Hb0)
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id Ps Hid1b) in Hw. exact Hw. }
  assert (Hrig1m : forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ1')
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hinc1b | apply Hrig1; exact Hα ]).
  (* the codomain refinement, transported to ζ1 (the Anno idiom) *)
  assert (Hσ1 : msubst_compose ζ1 κ1b ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hinc1b | exact Hwf0 | exact Hwf1 | exact Hζ1 ]).
  assert (HwfQ2 : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B2))).
  { rewrite bskl_to_pskl_btyp.
    apply a_wf_ptyp_to_wf_pskl. exact HwfB2. }
  assert (Hpp1 : Θ ⨟ empty ⊢ₚᵣᵃ
                   (msubst_pskl (msubst_compose ζ1 κ1b) P0)
                   ⊑ (msubst_pskl κ P0)).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ1
      | exact Heqv1 | clear; fsetdec ]. }
  assert (Hcod : Θ ⨟ empty ⊢ᵣᵃ
                   (pskl_to_bskl_inh (msubst_pskl (msubst_compose ζ1 κ1b) P0))
                   ⊳ (btyp_to_bskl B2)).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp1 | exact Href | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQ2 ]. }
  assert (Hms1 : msubst_pskl (msubst_compose ζ1 κ1b) P0 = msubst_pskl ζ1 P0).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwf1 | exact Hid1b | exact Hinc1b | exact Hζ1
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfP0 | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ] ]. }
  rewrite Hms1 in Hcod.
  (* the domain refinement : precision preserves the rule's own (paper's
     lemma:precision-preserves-refinement, verbatim) *)
  assert (HwfB1e : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B1))).
  { rewrite bskl_to_pskl_btyp.
    apply a_wf_ptyp_to_wf_pskl. exact HwfB1. }
  assert (Hdom : Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl ζ1 P'))
                   ⊳ (btyp_to_bskl B1)).
  { eapply ad_precise_preserves_refine;
      [ exact Hprec1 | exact HrefP | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfB1e ]. }
  destruct (IH1 (mode_fn M) Θ1' (pskl_arrow P' P0) ζ1 Θ (btyp_arrow B1 B2)
              Hwf1 HwfΘ
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP' | exact HwfP0m ])
              ltac:(apply a_ty_mode_compat__fn; exact Hmod)
              Hζ1 Hrig1m Hskl1 HsklT Hlc1 Hd1
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh btyp_to_bskl];
                    apply ad_refine_syn__arrow; [ exact Hdom | exact Hcod ]))
    as [C [Θ2' [Hrun2 Hopt2]]].
  (* the output is a SYNTACTIC arrow *)
  pose proof (a_typing_fn_arrow_shape Hrun2) as Hshape.
  inversion Hshape; subst.
  match goal with
  | Hs : fn_arrow_shape M ?BB |- _ => idtac
  end.
  match goal with
  | H : a_typing (mode_fn M) Θ1' _ e1 (ptyp_arrow ?AA ?BB) _ |- _ =>
      rename AA into Af; rename BB into Bf
  end.
  (* soundness of the function run *)
  assert (Hexp1 : a_wf_exp Θ1' e1)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc1 | intros α Hα; left; apply Hrig1m; exact Hα ]).
  destruct (a_typing_sound Hrun2 Hwf1 Hskl1
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP' | exact HwfP0m ])
              ltac:(apply a_ty_mode_compat__fn; exact Hmod)
              Hexp1)
    as [Hle2 [Hwf2 [HwfC _]]].
  destruct Hle2 as [[κ2b [Hid2b Hinc2b]] _].
  destruct (Hopt2 κ2b Hid2b Hinc2b) as [ζ2 [Hζ2 [Heqv2 Heq2]]].
  simpl in Heq2.
  (* invert the arrow equivalence *)
  inversion HwfC; subst.
  match goal with
  | H1 : a_wf_ptyp Θ2' Af, H2 : a_wf_ptyp Θ2' Bf |- _ =>
      rename H1 into HwfAf; rename H2 into HwfBf
  end.
  destruct (a_tyequiv_arrow_inv HwfΘ
              ltac:(eapply msubst_ptyp_lc;
                    [ exact Hζ2 | eapply a_wf_ptyp_lc; exact HwfAf ])
              ltac:(eapply msubst_ptyp_lc;
                    [ exact Hζ2 | eapply a_wf_ptyp_lc; exact HwfBf ])
              ltac:(eapply a_wf_ptyp_lc; exact HwfB1)
              ltac:(eapply a_wf_ptyp_lc; exact HwfB2)
              Heq2)
    as [HeqDom HeqCod].
  (* ---- 3. the ARGUMENT stage : IH2 at (TC, ⌈Af⌉) ---- *)
  assert (HwfA2 : a_wf_ptyp Θ A2)
    by (eapply (proj1 (a_tyequiv_wf_iff HeqA2 (fun x b h => h) HwfΘ));
        exact HwfB1).
  assert (Hrig2m : forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ2')
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hinc2b
        | eapply a_inc_binds_tvar;
            [ exact Hinc1b | apply Hrig2; exact Hα ] ]).
  assert (Hskl2 : forall y Ps, binds y (abind_var_skl Ps) Θ2' ->
             Θ2' ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    assert (Hb1 : binds y (abind_var_skl Ps) Θ1')
      by (exact (a_typing_tm_ge Hrun2 y (abind_var_skl Ps) I Hb)).
    pose proof (a_wf_pskl_msubst_inc Hinc2b Hwf1 (Hskl1 _ _ Hb1)
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id Ps Hid2b) in Hw. exact Hw. }
  assert (Hexp2m : a_wf_exp Θ2' e2)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc2 | intros α Hα; left; apply Hrig2m; exact Hα ]).
  assert (HeqChain : Θ ⊢ (msubst_ptyp ζ2 Af) ≡ᵗ A2)
    by (eapply a_tyequiv__trans; [ exact HeqDom | exact HeqA2 ]).
  assert (Heqs : Θ ⊢ (ptyp_to_pskl (msubst_ptyp ζ2 Af)) ≡ˢ (ptyp_to_pskl A2))
    by (apply a_tyequiv_embed_pskl; exact HeqChain).
  assert (Href3 : Θ ⨟ empty ⊢ᵣᵃ
                    (pskl_to_bskl_inh (msubst_pskl ζ2 (ptyp_to_pskl Af)))
                    ⊳ (btyp_to_bskl (ptyp_to_btyp_inh A2))).
  { rewrite msubst_pskl_embed_ptyp, <- (pskl_to_bskl_inh_ptyp A2).
    eapply ad_refine_syn_f_forget.
    eapply (proj2 (skl_tyequiv_refine_syn_f_transport Heqs HwfΘ
                     (fun x b h => h))).
    apply ad_refine_syn_f_of_plain.
    apply ad_refine_syn_refl_inh.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA2. }
  destruct (IH2 mode_tc Θ2' (ptyp_to_pskl Af) ζ2 Θ (ptyp_to_btyp_inh A2)
              Hwf2 HwfΘ
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAf)
              (a_ty_mode_compat__tc Af)
              Hζ2 Hrig2m Hskl2 HsklT Hlc2 Hd2 Href3)
    as [A3 [Θ3' [Hrun3 Hopt3]]].
  (* ---- 4. the run ---- *)
  exists Bf, Θ3'.
  split.
  { eapply a_typing__app; [ exact Hrun1 | exact Hrun2 | exact Hrun3 ]. }
  (* ---- 5. optimality : the TRIPLE glue ---- *)
  intros κ1 Hκid Hκinc.
  assert (Heqκ : κ1 = κ1b)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hκinc | exact Hinc1b | exact Hκid | exact Hid1b ]).
  destruct (a_typing_sound Hrun3 Hwf2 Hskl2
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAf)
              (a_ty_mode_compat__tc Af) Hexp2m)
    as [Hle3 [Hwf3 _]].
  destruct Hle3 as [[κ3b [Hid3b Hinc3b]] _].
  destruct (Hopt3 κ3b Hid3b Hinc3b) as [ζ3 [Hζ3 [Heqv3 _]]].
  exists ζ3.
  split; [ exact Hζ3 | ].
  split.
  { (* inner glue: stages 2+3 *)
    assert (Hglue23 : a_inc_equiv Θ1' ζ1 (msubst_compose ζ3 κ2b) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θ2') (Θfin := Θ3') (κ1b := κ3b) (ζ1 := ζ2);
        [ exact Hwf1 | exact Hwf2 | exact Hwf3 | exact HwfΘ
        | exact Hid2b | exact Hid3b
        | intros α Hα;
          pose proof (a_inc_dom_flex Hinc2b Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hinc3b | exact Hwf2
            | eapply a_inc_id_flex_preserve;
                [ exact Hinc2b | exact Hid2b | exact Hwf1 | exact Hfα ] ]
        | exact Hinc2b | exact Hinc3b | exact Hζ2 | exact Hζ3
        | exact Heqv2 | exact Heqv3 ]. }
    (* outer glue: stage 1 + the combined tail; the composed identity
       collapses to the inner one VERBATIM ([msubst_compose_id_id]) *)
    assert (Hinc23 : msubst_compose κ3b κ2b ∷ Θ1' ⊑ Θ3')
      by (eapply a_inc_compose;
          [ exact Hinc2b | exact Hwf1 | exact Hwf2 | exact Hinc3b ]).
    rewrite (msubst_compose_id_id Hid2b Hid3b) in Hinc23.
    assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζ3 κ1b) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θ1') (Θfin := Θ3') (κ1b := κ2b) (ζ1 := ζ1);
        [ exact Hwf0 | exact Hwf1 | exact Hwf3 | exact HwfΘ
        | exact Hid1b | exact Hid2b
        | intros α Hα;
          pose proof (a_inc_dom_flex Hinc1b Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hinc23 | exact Hwf1
            | eapply a_inc_id_flex_preserve;
                [ exact Hinc1b | exact Hid1b | exact Hwf0 | exact Hfα ] ]
        | exact Hinc1b | exact Hinc23 | exact Hζ1 | exact Hζ3
        | exact Heqv1 | exact Hglue23 ]. }
    rewrite Heqκ. exact Hglue. }
  (* ---- 6. the ≡ᵗ conclusion : the codomain pushed ζ2 → ζ3 ---- *)
  assert (HmsBf : msubst_ptyp (msubst_compose ζ3 κ3b) Bf = msubst_ptyp ζ3 Bf)
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwf2 | exact Hwf3 | exact Hid3b | exact Hinc3b | exact Hζ3
        | exact HwfBf ]).
  assert (HeqW : Θ ⊢ (msubst_ptyp ζ2 Bf) ≡ᵗ (msubst_ptyp ζ3 Bf)).
  { rewrite <- HmsBf.
    apply (@a_inc_equiv_msubst_ptyp Bf Θ2' ζ2 (msubst_compose ζ3 κ3b) Θ
             HwfBf Heqv3 Hwf2
             ltac:(eapply a_inc_msubst_lc; exact Hζ2)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζ3
                   | exact (is_id_msubst_values_lc Hid3b) ])). }
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact HeqW | exact HeqCod ].
Qed.

(* ===================================================================== *)
(*  §6.3 #3 — guess^TY EXISTENCE with an AVOID SET.  Completeness         *)
(*  CHOOSES the block, so this settles [AT-Abs]'s [uniq (αs ++ Θ1)]       *)
(*  premise; the "two independent generators" gap closes because the      *)
(*  arrow case feeds the first half's names into the second's avoid set.  *)
(* ===================================================================== *)

(** Two uniq lists with disjoint domains append to a uniq list. *)
Lemma uniq_app_of : forall (Ξ1 Ξ2 : aenv),
  uniq Ξ1 -> uniq Ξ2 ->
  (forall α, α `in` dom Ξ1 -> α `notin` dom Ξ2) ->
  uniq (Ξ1 ++ Ξ2).
Proof.
  intros Ξ1; induction Ξ1 as [ | [α b] Ξ1' IH ]; intros Ξ2 Hu1 Hu2 Hdj;
    [ exact Hu2 | ].
  inversion Hu1; subst.
  simpl_env. apply uniq_cons.
  - apply IH; [ assumption | exact Hu2 | ].
    intros β Hβ. apply Hdj. simpl. clear - Hβ; fsetdec.
  - rewrite dom_app.
    assert (Hα2 : α `notin` dom Ξ2)
      by (apply Hdj; simpl; clear; fsetdec).
    match goal with
    | Hn : α `notin` dom Ξ1' |- _ => clear - Hn Hα2; fsetdec
    end.
Qed.

(** ⭐ [guess^TY] EXISTENCE, with an AVOID SET: completeness CHOOSES the
    block, so an avoid-set-indexed generator settles [AT-Abs]'s
    [uniq (αs ++ Θ1)] premise (hand-off §6.3 #3; the "two independent
    generators" gap is closed by feeding the first half's names into the
    second half's avoid set at the arrow). *)
Lemma a_guess_mono_exists : forall P Θ L,
  lc_pskl P ->
  exists Ξ A,
    a_guess_mono Θ P Ξ A /\
    a_decls Ξ /\ uniq Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L).
Proof.
  intros P Θ L Hlc; revert Θ L; induction Hlc; intros Θ L.
  - (* unit *)
    exists nil, ptyp_unit. repeat split;
      [ apply a_guess_mono__unit | apply a_decls__nil | apply uniq_nil
      | intros β Hβ; simpl in Hβ; clear - Hβ; fsetdec ].
  - (* var_f *)
    exists nil, (ptyp_var_f α). repeat split;
      [ apply a_guess_mono__var | apply a_decls__nil | apply uniq_nil
      | intros β Hβ; simpl in Hβ; clear - Hβ; fsetdec ].
  - (* arrow *)
    destruct (IHHlc1 Θ L) as [Ξ1 [A [Hg1 [Hd1 [Hu1 Hav1]]]]].
    destruct (IHHlc2 Θ (L `union` dom Ξ1)) as [Ξ2 [B [Hg2 [Hd2 [Hu2 Hav2]]]]].
    exists (Ξ1 ++ Ξ2), (ptyp_arrow A B).
    repeat split.
    + apply a_guess_mono__arrow; [ exact Hg1 | exact Hg2 ].
    + clear - Hd1 Hd2. induction Hd1; simpl_env;
        [ exact Hd2 | apply a_decls__cons; assumption ].
    + apply uniq_app_of; [ exact Hu1 | exact Hu2 | ].
      intros α Hα Hα2.
      pose proof (Hav2 α Hα2) as Hn. clear - Hn Hα; fsetdec.
    + intros α Hα. rewrite dom_app in Hα.
      destruct (AtomSetImpl.union_1 Hα) as [H1 | H2];
        [ apply Hav1; exact H1 | apply Hav2 in H2; clear - H2; fsetdec ].
  - (* all *)
    destruct (atom_fresh (ftvar_in_aenv Θ `union` ftvar_in_pskl P1 `union` L))
      as [β Hβ].
    destruct (H0 β ((β ~ abind_tvar) ++ Θ) L) as [Ξ [A [Hg [Hd [Hu Hav]]]]].
    exists Ξ, (ptyp_all (close_ptyp_wrt_ptyp β A)).
    repeat split;
      [ apply a_guess_mono__forall;
          [ clear - Hβ; fsetdec | exact Hg ]
      | exact Hd | exact Hu | exact Hav ].
  - (* hole *)
    destruct (atom_fresh (ftvar_in_aenv Θ `union` L)) as [α Hα].
    exists ((α ~ abind_flex_mono) ++ nil), (ptyp_var_f α).
    repeat split;
      [ apply a_guess_mono__hole; clear - Hα; fsetdec
      | apply a_decls__cons; apply a_decls__nil
      | apply uniq_cons; [ apply uniq_nil | simpl; clear; fsetdec ]
      | intros β Hβ; simpl in Hβ;
        assert (β = α) by (clear - Hβ; fsetdec); subst;
        clear - Hα; fsetdec ].
  - (* tophole *)
    destruct (IHHlc Θ L) as [Ξ [A [Hg [Hd [Hu Hav]]]]].
    exists Ξ, A.
    repeat split;
      [ apply a_guess_mono__tophole; exact Hg
      | exact Hd | exact Hu | exact Hav ].
Qed.

(* ===================================================================== *)
(*  THE GUESS-COMPLETENESS KIT — the Abs row's heart.  The paper's own    *)
(*  proof marks its ⑯⑰ step "WT: A bit sketchy"; [a_guess_mono_complete]  *)
(*  below is that step made explicit.                                      *)
(* ===================================================================== *)

(** Embedding commutes with closing (the [ptyp] mirror of
    [pskl_to_bskl_syn_close]). *)
Lemma ptyp_to_pskl_close_rec : forall A α k,
  ptyp_to_pskl (close_ptyp_wrt_ptyp_rec k α A)
  = close_pskl_wrt_pskl_rec k α (ptyp_to_pskl A).
Proof.
  induction A; intros; simpl; f_equal; auto;
    repeat match goal with
    | |- context [ if ?t then _ else _ ] => destruct t
    | |- context [ lt_ge_dec ?a ?b ] => destruct (lt_ge_dec a b)
    end; reflexivity.
Qed.

Lemma ptyp_to_pskl_close : forall A α,
  ptyp_to_pskl (close_ptyp_wrt_ptyp α A)
  = close_pskl_wrt_pskl α (ptyp_to_pskl A).
Proof. intros; apply ptyp_to_pskl_close_rec. Qed.

(** A ghost-free skeleton guesses to ITSELF: no block, the type is the
    skeleton's own reading. *)
Lemma a_guess_mono_ghost_free_id : forall Θg P blk A',
  a_guess_mono Θg P blk A' ->
  pskl_ghost_free P ->
  blk = nil /\ ptyp_to_pskl A' = P.
Proof.
  intros Θg P blk A' H; induction H; intros Hg; simpl in Hg;
    try contradiction.
  - (* var *) split; reflexivity.
  - (* unit *) split; reflexivity.
  - (* arrow *)
    destruct Hg as [Hg1 Hg2].
    destruct (IHa_guess_mono1 Hg1) as [-> HA].
    destruct (IHa_guess_mono2 Hg2) as [-> HB].
    split; [ reflexivity | simpl; rewrite HA, HB; reflexivity ].
  - (* forall *)
    destruct (IHa_guess_mono ltac:(apply pskl_ghost_free_open; exact Hg))
      as [-> HA].
    split; [ reflexivity | ].
    simpl. f_equal.
    rewrite ptyp_to_pskl_close.
    rewrite HA.
    apply close_pskl_wrt_pskl_open_pskl_wrt_pskl.
    match goal with
    | Hfr : β `notin` _ |- _ => clear - Hfr; fsetdec
    end.
Qed.

(** A [btyp] painting that IS a syn painting names a MONOTYPE (the two
    colourings clash at any ∀, and a painting has no ghosts). *)
Lemma syn_painting_ityp_inv : forall (Bt : btyp) Pf,
  btyp_to_bskl Bt = pskl_to_bskl_syn Pf ->
  is_ityp Bt ->
  exists τ, mono_ptyp τ /\ Pf = ptyp_to_pskl τ /\ btyp_to_ptyp Bt = τ.
Proof.
  intros Bt; induction Bt; intros Pf Heq Hit; simpl in Heq;
    destruct Pf; simpl in Heq; try discriminate; inversion Hit; subst.
  - exists ptyp_unit.
    split; [ apply mono_ptyp__unit | split; reflexivity ].
  - inversion Heq; subst.
    eexists.
    split; [ apply mono_ptyp__var | split; reflexivity ].
  - inversion Heq; subst.
    match goal with
    | H1 : btyp_to_bskl Bt1 = pskl_to_bskl_syn ?p1,
      H2 : btyp_to_bskl Bt2 = pskl_to_bskl_syn ?p2 |- _ =>
        destruct (IHBt1 _ H1 ltac:(assumption)) as [τ1 [Hm1 [-> He1]]];
        destruct (IHBt2 _ H2 ltac:(assumption)) as [τ2 [Hm2 [-> He2]]]
    end.
    exists (ptyp_arrow τ1 τ2).
    split; [ apply mono_ptyp__arrow; assumption | ].
    split; [ reflexivity | simpl; rewrite He1, He2; reflexivity ].
Qed.

(** …and a monotype's syn painting is (vacuously) inherited. *)
Lemma mono_ptyp_to_btyp_syn_ityp : forall τ,
  mono_ptyp τ ->
  is_ityp (ptyp_to_btyp_syn τ).
Proof.
  intros τ Hm; induction Hm; simpl.
  - apply is_ityp__unit.
  - apply is_ityp__var.
  - apply is_ityp__arrow; assumption.
Qed.

(** Ghost-freeness is decidable. *)
Lemma pskl_ghost_free_dec : forall P,
  sumbool (pskl_ghost_free P) (~ pskl_ghost_free P).
Proof.
  induction P; simpl; auto.
  destruct IHP1; destruct IHP2; [ left; split; assumption | | | ];
    right; intros [H1 H2]; contradiction.
Qed.

(** Looking up past a block the atom avoids. *)
Lemma msubst_lookup_app_notin : forall (ζ κ : metasubst) α,
  α `notin` dom ζ ->
  msubst_lookup (ζ ++ κ) α = msubst_lookup κ α.
Proof.
  intros ζ; induction ζ as [ | [β τ] ζ' IH ]; intros κ α Hα;
    [ reflexivity | ].
  simpl in *.
  destruct (α == β) as [-> | Hne]; [ exfalso; clear - Hα; fsetdec | ].
  apply IH. clear - Hα; fsetdec.
Qed.

(** ⭐ The GHOST-FREE shortcut: a ghost-free subtree guesses to itself, and
    a refinement between two ghost-free paintings IS the equivalence. *)
Lemma a_guess_mono_complete_ghost_free : forall Θ Δ κ P (Bt : btyp) Θg blk A',
  pskl_ghost_free P ->
  ad_refine_syn Θ Δ (pskl_to_bskl_inh (msubst_pskl κ P)) (btyp_to_bskl Bt) ->
  a_wf_aenv Θ ->
  a_guess_mono Θg P blk A' ->
  blk = nil /\ Θ ⊢ (msubst_ptyp κ A') ≡ᵗ (btyp_to_ptyp Bt).
Proof.
  intros Θ Δ κ P Bt Θg blk A' Hgf Href HwfΘ Hg.
  destruct (a_guess_mono_ghost_free_id Hg Hgf) as [-> HPA].
  split; [ reflexivity | ].
  rewrite <- HPA in Href.
  rewrite msubst_pskl_embed_ptyp in Href.
  exact (ad_refine_syn_inh_tyequiv Href HwfΘ
           (msubst_ptyp κ A') Bt eq_refl eq_refl).
Qed.

(** Stacking a block of guessed flexibles onto an increase. *)
Lemma a_inc_extend_flex_block : forall (blk : aenv) (ζg κ : metasubst) Θ1 Θ,
  κ ∷ Θ1 ⊑ Θ ->
  List.map fst ζg = List.map fst blk ->
  a_decls blk ->
  (forall α τ, In (α, τ) ζg -> mono_ptyp τ /\ a_wf_ptyp Θ τ) ->
  (ζg ++ κ) ∷ (blk ++ Θ1) ⊑ Θ.
Proof.
  intros blk; induction blk as [ | [α b] blk' IH ];
    intros ζg κ Θ1 Θ Hinc Hmap Hd Hwf.
  - destruct ζg; simpl in Hmap; [ exact Hinc | discriminate ].
  - destruct ζg as [ | [α' τ] ζg' ]; simpl in Hmap; [ discriminate | ].
    inversion Hmap; subst α'.
    inversion Hd; subst.
    simpl_env.
    apply a_inc__flex.
    + apply IH; try assumption.
      intros β τ2 Hin. apply (Hwf β τ2). right. exact Hin.
    + assert (Hin : In (α, τ) ((α, τ) :: ζg')) by (left; reflexivity).
      exact (proj2 (Hwf _ _ Hin)).
    + assert (Hin : In (α, τ) ((α, τ) :: ζg')) by (left; reflexivity).
      exact (proj1 (Hwf _ _ Hin)).
Qed.

(** The one place the subject's head is NOT the input's: a FLEXIBLE input
    variable, whose κ-image (a monotype) is what the refinement sees.  The
    guess is the identity there, and the refinement between the image's
    painting and the target IS the equivalence. *)
Lemma guess_complete_var_image : forall Θ Δ κ β (Bt : btyp) Θg blk A',
  ad_refine_syn Θ Δ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β)))
    (btyp_to_bskl Bt) ->
  a_wf_aenv Θ ->
  a_guess_mono Θg (pskl_var_f β) blk A' ->
  blk = nil /\ Θ ⊢ (msubst_ptyp κ A') ≡ᵗ (btyp_to_ptyp Bt).
Proof.
  intros Θ Δ κ β Bt Θg blk A' Href HwfΘ Hg.
  inversion Hg; subst.
  split; [ reflexivity | ].
  change (pskl_var_f β) with (ptyp_to_pskl (ptyp_var_f β)) in Href.
  rewrite msubst_pskl_embed_ptyp in Href.
  exact (ad_refine_syn_inh_tyequiv Href HwfΘ
           (msubst_ptyp κ (ptyp_var_f β)) Bt eq_refl eq_refl).
Qed.

(** A monotype's embedding is never a ghost or a quantifier. *)
Lemma mono_embed_no_tophole : forall τ P1,
  mono_ptyp τ -> ptyp_to_pskl τ <> pskl_tophole P1.
Proof. intros τ P1 Hm; destruct Hm; simpl; discriminate. Qed.

Lemma mono_embed_no_all : forall τ P1,
  mono_ptyp τ -> ptyp_to_pskl τ <> pskl_all_syn P1.
Proof. intros τ P1 Hm; destruct Hm; simpl; discriminate. Qed.

Lemma mono_embed_no_hole : forall τ,
  mono_ptyp τ -> ptyp_to_pskl τ <> pskl_hole.
Proof. intros τ Hm; destruct Hm; simpl; discriminate. Qed.

(** An in-domain lookup through an increase is a Θ-wf image. *)
Lemma a_inc_lookup_in_wf : forall Θ1 κg Θ β,
  κg ∷ Θ1 ⊑ Θ ->
  β `in` dom κg ->
  a_wf_ptyp Θ (msubst_lookup κg β).
Proof.
  intros Θ1 κg Θ β Hinc; induction Hinc; intros Hd; simpl in *.
  - exfalso; clear - Hd; fsetdec.
  - destruct (β == α) as [-> | Hne]; [ assumption | ].
    apply IHHinc. clear - Hd Hne; fsetdec.
  - destruct (β == α) as [-> | Hne]; [ assumption | ].
    apply IHHinc. clear - Hd Hne; fsetdec.
  - eapply a_wf_ptyp_weaken;
      [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
      | apply IHHinc; exact Hd ].
  - eapply a_wf_ptyp_weaken;
      [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
      | apply IHHinc; exact Hd ].
  - eapply a_wf_ptyp_weaken;
      [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
      | apply IHHinc; exact Hd ].
Qed.

(** A fresh atom stays out of a κ-image (the entries are Θ-scoped). *)
Lemma msubst_ptyp_ftv_notin_inc : forall A (κg : metasubst) Θ1 Θ α0,
  κg ∷ Θ1 ⊑ Θ ->
  α0 `notin` ftvar_in_ptyp A ->
  α0 `notin` dom Θ ->
  α0 `notin` ftvar_in_ptyp (msubst_ptyp κg A).
Proof.
  intros A; induction A; intros κg Θ1 Θ α0 Hinc HA Hd; simpl in *;
    try solve [ fsetdec
              | intros Hc; apply (IHA _ _ _ _ Hinc HA Hd); exact Hc ].
  - (* var β *)
    destruct (AtomSetProperties.In_dec α (dom κg)) as [Hin | Hni].
    + pose proof (a_inc_lookup_in_wf Hinc Hin) as Hwfl.
      intros Hc.
      pose proof (a_wf_ptyp_ftv_tvarish Hwfl Hc) as Ht.
      destruct Ht as [Hr | [Hm | [τ Hdf]]];
        [ apply binds_In in Hr; clear - Hd Hr; fsetdec
        | apply binds_In in Hm; clear - Hd Hm; fsetdec
        | apply binds_In in Hdf; clear - Hd Hdf; fsetdec ].
    + rewrite msubst_lookup_notin; [ | exact Hni ].
      simpl. clear - HA; fsetdec.
  - (* arrow *)
    intros Hc.
    assert (HA1 : α0 `notin` ftvar_in_ptyp A1) by (clear - HA; fsetdec).
    assert (HA2 : α0 `notin` ftvar_in_ptyp A2) by (clear - HA; fsetdec).
    destruct (union_1 Hc) as [H1 | H2];
      [ exact (IHA1 _ _ _ _ Hinc HA1 Hd H1)
      | exact (IHA2 _ _ _ _ Hinc HA2 Hd H2) ].
Qed.

Lemma msubst_lookup_app_agree : forall (ζ X Y : metasubst) α,
  msubst_lookup X α = msubst_lookup Y α ->
  msubst_lookup (ζ ++ X) α = msubst_lookup (ζ ++ Y) α.
Proof.
  intros ζ; induction ζ as [ | [β τ] ζ' IH ]; intros X Y α Hxy;
    [ exact Hxy | ].
  simpl. destruct (α == β); [ reflexivity | apply IH; exact Hxy ].
Qed.

Lemma map_fst_eq_dom : forall (ζ : metasubst) (blk : aenv),
  List.map fst ζ = List.map fst blk ->
  dom ζ [=] dom blk.
Proof.
  intros ζ; induction ζ as [ | [α τ] ζ' IH ]; intros blk Hmap;
    destruct blk as [ | [β b] blk' ]; simpl in Hmap; try discriminate.
  - simpl. fsetdec.
  - inversion Hmap; subst. simpl.
    pose proof (IH _ H1). fsetdec.
Qed.

(** The composite that is never a syn painting's ∀-free companion. *)
Lemma ptyp_to_bskl_syn_via_pskl : forall τ,
  ptyp_to_bskl_syn τ = pskl_to_bskl_syn (ptyp_to_pskl τ).
Proof. induction τ; simpl; f_equal; auto. Qed.

(** ⭐⭐ GUESS-COMPLETENESS — the paper's Abs step ⑯⑰, which its authors
    flag as "a bit sketchy", made explicit.  If the κ-image of [P] refines
    to (the painting of) an INHERITED type [Bt], the ghost fills are
    Δ-free Θ-monotypes — refinement's ∀ rows keep binders in Δ while
    [__hole]'s fill is wf at [Θ ⨟ ∅] — and they assemble into a block
    substitution under which guess^TY's output is EQUIVALENT to the
    target.  Induction on the REFINEMENT (its flex rows recurse at the
    same [P]); the input's flexible variables are invisible (their images
    are monotypes, [guess_complete_var_image]); the ∀ row takes ONE fresh
    instance ([a_guess_mono_open_at]) and re-generates the ≡ᵗ family by
    the α0 ⇄ α transposition. *)
Lemma a_guess_mono_complete : forall Θ Δ Qs Qt,
  ad_refine_syn Θ Δ Qs Qt ->
  forall P0 (Bt : btyp) Θg blk A' κ Θ1,
  a_wf_aenv Θ ->
  Qs = pskl_to_bskl_inh (msubst_pskl κ P0) ->
  Qt = btyp_to_bskl Bt ->
  is_ityp Bt ->
  a_guess_mono Θg P0 blk A' ->
  κ ∷ Θ1 ⊑ Θ ->
  uniq blk ->
  (forall α, α `in` dom blk ->
     α `notin` ftvar_in_pskl P0 `union` dom κ
       `union` dom Θ `union` ftvar_in_aenv Θ) ->
  exists ζg,
    List.map fst ζg = List.map fst blk /\
    (forall α τ, In (α, τ) ζg -> mono_ptyp τ /\ a_wf_ptyp Θ τ) /\
    Θ ⊢ (msubst_ptyp (ζg ++ κ) A') ≡ᵗ (btyp_to_ptyp Bt).
Proof.
  intros Θ Δ Qs Qt Href.
  (* the two head-generic moves, packaged: *)
  (* [var_image_case] — the input head is a flexible/rigid VARIABLE; its
     κ-image is what the row sees, and the guess is the identity there *)
  (* [mono_clash] — a variable input's image is a MONOTYPE, whose painting
     never matches a ghost/quantifier subject *)
  induction Href;
    intros P0 Bt Θg blk A' κ Θ1 HwfΘ HeqS HeqT Hit Hg Hinc Huq Hav.
  - (* unit *)
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    + (* unit head *)
      inversion Hg; subst.
      destruct Bt; simpl in HeqT; try discriminate.
      exists nil. split; [ reflexivity | ].
      split; [ intros α2 τ2 Hin; inversion Hin | ].
      simpl. apply a_tyequiv__refl. apply lc_ptyp_unit.
    + (* var head : the image *)
      assert (Href' : ad_refine_syn Θ Δ
                (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f βv)))
                (btyp_to_bskl Bt))
        by (simpl; rewrite <- HeqS, <- HeqT; apply ad_refine_syn__unit).
      destruct (@guess_complete_var_image Θ Δ κ βv Bt Θg blk A' Href' HwfΘ Hg) as [-> Heqc].
      exists nil; split;
        [ reflexivity
        | split; [ intros α2 τ2 Hin; inversion Hin | exact Heqc ] ].
  - (* var *)
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    assert (Href' : ad_refine_syn Θ Δ
              (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f βv)))
              (btyp_to_bskl Bt))
      by (simpl; rewrite <- HeqS, <- HeqT;
          apply ad_refine_syn__var; assumption).
    destruct (@guess_complete_var_image Θ Δ κ βv Bt Θg blk A' Href' HwfΘ Hg) as [-> Heqc].
    exists nil; split;
      [ reflexivity
      | split; [ intros α2 τ2 Hin; inversion Hin | exact Heqc ] ].
  - (* arrow *)
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    + (* var head *)
      assert (Href' : ad_refine_syn Θ Δ
                (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f βv)))
                (btyp_to_bskl Bt))
        by (simpl; rewrite <- HeqS, <- HeqT;
            apply ad_refine_syn__arrow; assumption).
      destruct (@guess_complete_var_image Θ Δ κ βv Bt Θg blk A' Href' HwfΘ Hg) as [-> Heqc].
      exists nil; split;
        [ reflexivity
        | split; [ intros α2 τ2 Hin; inversion Hin | exact Heqc ] ].
    + (* arrow head *)
      inversion HeqS; subst Q1 Q2.
      destruct Bt as [ | n | γ | B1 B2 | B0 | B0 ]; simpl in HeqT;
        try discriminate HeqT.
      inversion HeqT; subst P1 P2.
      inversion Hit; subst.
      inversion Hg; subst.
      match goal with
      | H1 : a_guess_mono _ Pa ?X1 ?AA, H2 : a_guess_mono _ Pb ?X2 ?BB |- _ =>
          rename H1 into Hg1; rename H2 into Hg2;
          rename X1 into Ξ1; rename X2 into Ξ2;
          rename AA into A1; rename BB into A2
      end.
      assert (Hu1 : uniq Ξ1) by (clear - Huq; solve_uniq).
      assert (Hu2 : uniq Ξ2) by (clear - Huq; solve_uniq).
      destruct (IHHref1 Pa B1 Θg Ξ1 A1 κ Θ1 HwfΘ eq_refl eq_refl
                  ltac:(assumption) Hg1 Hinc Hu1
                  ltac:(intros α Hα; simpl in Hav;
                        pose proof (Hav α ltac:(rewrite dom_app;
                                                clear - Hα; fsetdec)) as Hn;
                        clear - Hn; fsetdec))
        as [ζg1 [Hmap1 [Hent1 Heqc1]]].
      destruct (IHHref2 Pb B2 Θg Ξ2 A2 κ Θ1 HwfΘ eq_refl eq_refl
                  ltac:(assumption) Hg2 Hinc Hu2
                  ltac:(intros α Hα; simpl in Hav;
                        pose proof (Hav α ltac:(rewrite dom_app;
                                                clear - Hα; fsetdec)) as Hn;
                        clear - Hn; fsetdec))
        as [ζg2 [Hmap2 [Hent2 Heqc2]]].
      pose proof (map_fst_eq_dom _ _ Hmap1) as Hd1.
      pose proof (map_fst_eq_dom _ _ Hmap2) as Hd2.
      pose proof (a_guess_mono_ftv Hg1) as Hftv1.
      pose proof (a_guess_mono_ftv Hg2) as Hftv2.
      assert (Hdisj : dom Ξ1 ∩ dom Ξ2 [=] empty)
        by (clear - Huq; solve_uniq).
      exists (ζg1 ++ ζg2).
      split; [ rewrite !List.map_app, Hmap1, Hmap2; reflexivity | ].
      split.
      { intros α τ Hin.
        apply in_app_or in Hin as [Hin | Hin];
          [ exact (Hent1 _ _ Hin) | exact (Hent2 _ _ Hin) ]. }
      simpl.
      apply a_tyequiv__arrow.
      * rewrite app_assoc.
        erewrite (msubst_ptyp_agree (ζg1 ++ ζg2 ++ κ) (ζg1 ++ κ));
          [ exact Heqc1 | ].
        intros α Hα.
        apply msubst_lookup_app_agree.
        apply msubst_lookup_app_notin.
        assert (HαP : α `in` ftvar_in_pskl Pa `union` dom Ξ1)
          by (clear - Hα Hftv1; fsetdec).
        intros Hc. rewrite Hd2 in Hc.
        simpl in Hav.
        pose proof (Hav α ltac:(rewrite dom_app; clear - Hc; fsetdec)) as Hn.
        clear - Hn HαP Hc Hdisj. fsetdec.
      * rewrite app_assoc.
        erewrite (msubst_ptyp_agree (ζg1 ++ ζg2 ++ κ) (ζg2 ++ κ));
          [ exact Heqc2 | ].
        intros α Hα.
        apply msubst_lookup_app_notin.
        assert (HαP : α `in` ftvar_in_pskl Pb `union` dom Ξ2)
          by (clear - Hα Hftv2; fsetdec).
        intros Hc. rewrite Hd1 in Hc.
        simpl in Hav.
        pose proof (Hav α ltac:(rewrite dom_app; clear - Hc; fsetdec)) as Hn.
        clear - Hn HαP Hc Hdisj. fsetdec.
  - (* all *)
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    + (* var head : a monotype image is never a quantifier *)
      exfalso.
      pose proof (a_inc_lookup_mono βv Hinc) as Hm.
      destruct Hm; simpl in HeqS; discriminate HeqS.
    + (* all head *)
      inversion HeqS; subst Q.
      destruct Bt as [ | n | γ | B1 B2 | B0 | B0 ]; simpl in HeqT;
        try discriminate HeqT.
      inversion HeqT; subst P.
      inversion Hit; subst.
      match goal with
      | Hfam : forall α, α `notin` ?LL ->
                 is_ityp (open_btyp_wrt_btyp _ _) |- _ =>
          rename Hfam into Hit1; rename LL into L2
      end.
      inversion Hg; subst.
      match goal with
      | Hg1 : a_guess_mono ((?bb ~ abind_tvar) ++ _) _ _ ?AA,
        Hfr : ?bb `notin` _ |- _ =>
          rename Hg1 into Hg0; rename Hfr into Hfrβ;
          rename bb into β; rename AA into A0
      end.
      destruct (atom_fresh (L `union` L2 `union` dom blk
                  `union` ftvar_in_pskl Pw `union` ftvar_in_aenv Θg
                  `union` dom κ `union` dom Θ `union` ftvar_in_aenv Θ
                  `union` ftvar_in_ptyp (close_ptyp_wrt_ptyp β A0)
                  `union` ftvar_in_btyp B0 `union` singleton β)) as [α0 Hα0].
      assert (Hgα0 : a_guess_mono ((α0 ~ abind_tvar) ++ Θg)
                       (open_pskl_wrt_pskl Pw (pskl_var_f α0)) blk
                       (open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp β A0)
                          (ptyp_var_f α0))).
      { apply a_guess_mono_open_at;
          [ apply a_guess_mono__forall with (β := β);
              [ exact Hfrβ | exact Hg0 ]
          | clear - Hα0; fsetdec ]. }
      destruct (H0 α0 ltac:(clear - Hα0; fsetdec)
                  (open_pskl_wrt_pskl Pw (pskl_var_f α0))
                  (open_btyp_wrt_btyp B0 (btyp_var_f α0))
                  ((α0 ~ abind_tvar) ++ Θg) blk
                  (open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp β A0)
                     (ptyp_var_f α0))
                  κ Θ1 HwfΘ
                  ltac:(assert (Hfr0 : α0 `notin` dom κ)
                          by (clear - Hα0; fsetdec);
                        rewrite (@msubst_pskl_open Θ1 κ Θ Pw α0 Hinc Hfr0);
                        rewrite pskl_to_bskl_inh_open; reflexivity)
                  ltac:(rewrite btyp_to_bskl_open; reflexivity)
                  (Hit1 α0 ltac:(clear - Hα0; fsetdec))
                  Hgα0 Hinc Huq
                  ltac:(intros α Hα;
                        pose proof (Hav α Hα) as Hn;
                        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                      Pw (pskl_var_f α0)) as Hup;
                        simpl in Hup, Hn;
                        assert (Hne : α <> α0)
                          by (intros ->; clear - Hα Hα0; fsetdec);
                        clear - Hn Hup Hne; fsetdec))
        as [ζg [Hmap [Hent Heqc0]]].
      exists ζg.
      split; [ exact Hmap | ].
      split; [ exact Hent | ].
      assert (Hincg : (ζg ++ κ) ∷ (blk ++ Θ1) ⊑ Θ)
        by (apply a_inc_extend_flex_block;
            [ exact Hinc | exact Hmap
            | eapply a_guess_mono_decls; exact Hg0 | exact Hent ]).
      pose proof (map_fst_eq_dom _ _ Hmap) as Hdζ.
      assert (Hfrg : α0 `notin` dom (ζg ++ κ))
        by (rewrite dom_app; rewrite Hdζ; clear - Hα0; fsetdec).
      rewrite (@msubst_ptyp_open (blk ++ Θ1) (ζg ++ κ) Θ
                 (close_ptyp_wrt_ptyp β A0) α0 Hincg Hfrg)
        in Heqc0.
      rewrite btyp_to_ptyp_open in Heqc0.
      simpl.
      set (X := msubst_ptyp (ζg ++ κ) (close_ptyp_wrt_ptyp β A0)) in *.
      apply a_tyequiv__all with
        (L := ftvar_in_ptyp X `union` ftvar_in_ptyp (btyp_to_ptyp B0)
                `union` singleton α0 `union` dom Θ `union` ftvar_in_aenv Θ).
      intros α Hα.
      pose proof (a_tyequiv_swap α0 α _ _ _ Heqc0) as Hsw.
      assert (Hfe1 : α0 `notin` (dom Θ `union` ftvar_in_aenv Θ))
        by (clear - Hα0; fsetdec).
      assert (Hfe2 : α `notin` (dom Θ `union` ftvar_in_aenv Θ))
        by (clear - Hα; fsetdec).
      rewrite (@swap_aenv_fresh_eq α0 α Θ Hfe1 Hfe2) in Hsw.
      rewrite !swap_ptyp_open in Hsw.
      cbn [swap_ptyp] in Hsw.
      rewrite swap_atom_l in Hsw.
      rewrite (swap_ptyp_fresh_id α0 α X) in Hsw;
        [ | | clear - Hα; fsetdec ].
      2:{ (* α0 avoids X : it avoids the closed body and the Θ-scoped
             images *)
        unfold X.
        eapply msubst_ptyp_ftv_notin_inc;
          [ exact Hincg | clear - Hα0; fsetdec | clear - Hα0; fsetdec ]. }
      rewrite (swap_ptyp_fresh_id α0 α (btyp_to_ptyp B0)) in Hsw;
        [ | | clear - Hα; fsetdec ].
      2:{ rewrite ftvar_in_ptyp_btyp_to_ptyp. clear - Hα0; fsetdec. }
      exact Hsw.
  - (* hole *)
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    + (* var head : a monotype image is never a ghost *)
      exfalso.
      pose proof (a_inc_lookup_mono βv Hinc) as Hm.
      destruct Hm; simpl in HeqS; discriminate HeqS.
    + (* hole head : the fill is a monotype *)
      inversion Hg; subst.
      destruct (@syn_painting_ityp_inv Bt P (eq_sym HeqT) Hit)
        as [τ [Hmτ [-> Hbtτ]]].
      assert (Hwfτ : a_wf_ptyp Θ τ).
      { eapply a_wf_ptyp_of_scope_pskl; [ | reflexivity ].
        eapply a_wf_pskl_to_a_scope_pskl;
          [ eassumption | intros z b Hb; exact Hb
          | intros α2 Hα2; clear - Hα2; fsetdec ]. }
      eexists ((_, τ) :: nil).
      split; [ reflexivity | ].
      split.
      { intros α2 τ2 Hin.
        destruct Hin as [Heq2 | []].
        inversion Heq2; subst. split; assumption. }
      simpl.
      destruct (α == α) as [_ | Hc]; [ | exfalso; apply Hc; reflexivity ].
      rewrite Hbtτ.
      apply a_tyequiv__refl. eapply a_wf_ptyp_lc; exact Hwfτ.
  - (* tophole_remove *)
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    + (* var head : a monotype image is never a ghost *)
      exfalso.
      pose proof (a_inc_lookup_mono βv Hinc) as Hm.
      destruct Hm; simpl in HeqS; discriminate HeqS.
    + (* tophole head *)
      inversion HeqS; subst Q.
      inversion Hg; subst.
      match goal with
      | Hg1 : a_guess_mono _ Pt _ _ |- _ => rename Hg1 into Hg0
      end.
      destruct (IHHref Pt Bt Θg blk A' κ Θ1 HwfΘ eq_refl eq_refl Hit Hg0
                  Hinc Huq
                  ltac:(intros α Hα; exact (Hav α Hα)))
        as [ζg [Hmap [Hent Heqc]]].
      exists ζg. split; [ exact Hmap | split; [ exact Hent | exact Heqc ] ].
  - (* tophole_fill : an inherited target has no syn quantifier *)
    destruct Bt; simpl in HeqT; try discriminate HeqT.
    inversion Hit.
  - (* tophole_keep : a btyp painting is never a ghost *)
    destruct Bt; simpl in HeqT; discriminate HeqT.
  - (* flex_l : only a variable input paints to a bare variable *)
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    assert (Href' : ad_refine_syn Θ Δ
              (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f βv)))
              (btyp_to_bskl Bt))
      by (simpl; rewrite <- HeqS, <- HeqT;
          eapply ad_refine_syn__flex_l; eassumption).
    destruct (@guess_complete_var_image Θ Δ κ βv Bt Θg blk A' Href' HwfΘ Hg) as [-> Heqc].
    exists nil; split;
      [ reflexivity
      | split; [ intros α2 τ2 Hin; inversion Hin | exact Heqc ] ].
  - (* flex_r : unfold the target's definition and recurse (any input) *)
    destruct Bt as [ | n | γ | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate HeqT.
    inversion HeqT; subst γ.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    destruct (IHHref P0 (ptyp_to_btyp_syn τ) Θg blk A' κ Θ1 HwfΘ HeqS
                ltac:(rewrite <- pskl_to_bskl_syn_ptyp,
                        <- ptyp_to_bskl_syn_via_pskl; reflexivity)
                (mono_ptyp_to_btyp_syn_ityp Hmτ)
                Hg Hinc Huq Hav)
      as [ζg [Hmap [Hent Heqc]]].
    exists ζg. split; [ exact Hmap | split; [ exact Hent | ] ].
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Heqc.
    simpl.
    eapply a_tyequiv__trans;
      [ exact Heqc
      | apply a_tyequiv__sym; apply a_tyequiv__flex_def; assumption ].
Qed.

(* ===================================================================== *)
(*  Strip/extend helpers for the binder-row optimality                    *)
(* ===================================================================== *)

Lemma is_id_msubst_app_r : forall (κp κ0 : metasubst),
  is_id_msubst (κp ++ κ0) -> is_id_msubst κ0.
Proof.
  intros κp; induction κp as [ | [α τ] κp' IH ]; intros κ0 H;
    [ exact H | ].
  apply is_id_msubst_inv in H as [_ H]. exact (IH _ H).
Qed.

Lemma app_inj_prefix : forall (A : Type) (l1 l2 l3 l4 : list A),
  l1 ++ l2 = l3 ++ l4 -> length l1 = length l3 -> l1 = l3 /\ l2 = l4.
Proof.
  intros A l1; induction l1 as [ | a l1' IH ]; intros l2 l3 l4 Heq Hlen;
    destruct l3 as [ | c l3' ]; simpl in *; try discriminate Hlen.
  - split; [ reflexivity | exact Heq ].
  - inversion Heq; subst.
    destruct (IH _ _ _ H1 ltac:(clear - Hlen; lia)) as [-> ->].
    split; reflexivity.
Qed.

(** Strip a block of flexible DECLARATIONS off an increase's source. *)
Lemma a_inc_strip_decls_head : forall (blk : aenv) (κ : metasubst) Θ0 Θ,
  a_decls blk ->
  κ ∷ (blk ++ Θ0) ⊑ Θ ->
  exists κp κ0,
    κ = κp ++ κ0 /\ length κp = length blk /\ κ0 ∷ Θ0 ⊑ Θ.
Proof.
  intros blk; induction blk as [ | [α b] blk' IH ]; intros κ Θ0 Θ Hd Hinc.
  - exists nil, κ.
    split; [ reflexivity | split; [ reflexivity | exact Hinc ] ].
  - inversion Hd; subst.
    simpl_env in Hinc.
    pose proof (@a_inc_strip_flex_mid nil α (blk' ++ Θ0) κ Θ
                  a_decls__nil Hinc) as Hstrip.
    destruct Hstrip
      as [κ1 [τ [κ2 [Heqκ [Hlen1 [_ [_ [Hwfτ [Hmτ Hinc2]]]]]]]]].
    destruct κ1 as [ | p κ1' ]; [ | simpl in Hlen1; discriminate Hlen1 ].
    simpl in Heqκ. subst κ.
    match goal with
    | Hd' : a_decls blk' |- _ =>
        destruct (IH _ _ _ Hd' Hinc2) as [κp [κ0 [-> [Hlen Hinc0]]]]
    end.
    exists ((α, τ) :: κp), κ0.
    split; [ reflexivity | ].
    split; [ simpl; rewrite Hlen; reflexivity | exact Hinc0 ].
Qed.

(** …and off a metasubstitution equivalence's source. *)
Lemma a_inc_equiv_strip_decls_head : forall (blk : aenv) Θ0 κ1 κ2 Θ,
  a_decls blk ->
  a_inc_equiv (blk ++ Θ0) κ1 κ2 Θ ->
  exists κ1p κ1t κ2p κ2t,
    κ1 = κ1p ++ κ1t /\ κ2 = κ2p ++ κ2t /\
    length κ1p = length blk /\ length κ2p = length blk /\
    a_inc_equiv Θ0 κ1t κ2t Θ.
Proof.
  intros blk; induction blk as [ | [α b] blk' IH ]; intros Θ0 κ1 κ2 Θ Hd Heqv.
  - exists nil, κ1, nil, κ2.
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ reflexivity | ]. split; [ reflexivity | exact Heqv ].
  - inversion Hd; subst.
    simpl_env in Heqv.
    inversion Heqv; subst.
    match goal with
    | Hd' : a_decls blk' |- _ =>
        match goal with
        | Hi : a_inc_equiv _ _ _ _ |- _ =>
            destruct (IH _ _ _ _ Hd' Hi)
              as [κ1p [κ1t [κ2p [κ2t [-> [-> [Hl1 [Hl2 Heqv0]]]]]]]]
        end
    end.
    eexists ((_, _) :: κ1p), κ1t, ((_, _) :: κ2p), κ2t.
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ simpl; rewrite Hl1; reflexivity | ].
    split; [ simpl; rewrite Hl2; reflexivity | exact Heqv0 ].
Qed.

(** The inherited painting of a type is (vacuously) inherited. *)
Lemma ptyp_to_btyp_inh_ityp : forall A,
  lc_ptyp A -> is_ityp (ptyp_to_btyp_inh A).
Proof.
  intros A Hlc; induction Hlc; simpl.
  - apply is_ityp__unit.
  - apply is_ityp__var.
  - apply is_ityp__arrow; assumption.
  - apply is_ityp__all with (L := empty).
    intros α _.
    rewrite <- ptyp_to_btyp_inh_open.
    auto.
Qed.

(** A declarations block's member is its flexible entry. *)
Lemma a_decls_in_dom_binds : forall (blk : aenv) α,
  a_decls blk -> α `in` dom blk -> binds α abind_flex_mono blk.
Proof.
  intros blk α Hd; induction Hd; intros Hin; simpl in Hin;
    [ exfalso; clear - Hin; fsetdec | ].
  destruct (α == α1) as [-> | Hne];
    [ apply binds_app_2; unfold binds; simpl; auto
    | apply binds_app_3; apply IHHd; clear - Hin Hne; fsetdec ].
Qed.

(** A fresh declarations block extends a wf context. *)
Lemma a_wf_aenv_decls_app : forall (blk : aenv) Θ0,
  a_decls blk ->
  uniq blk ->
  (forall α, α `in` dom blk -> α `notin` dom Θ0) ->
  a_wf_aenv Θ0 ->
  a_wf_aenv (blk ++ Θ0).
Proof.
  intros blk Θ0 Hd; induction Hd; intros Huq Hfr Hwf;
    [ exact Hwf | ].
  inversion Huq; subst.
  simpl_env.
  apply a_wf_aenv__flex.
  - rewrite dom_app.
    assert (Hn1 : α1 `notin` dom Ξ) by assumption.
    assert (Hn2 : α1 `notin` dom Θ0)
      by (apply Hfr; simpl; clear; fsetdec).
    clear - Hn1 Hn2; fsetdec.
  - apply IHHd; [ assumption | | exact Hwf ].
    intros α Hα. apply Hfr. simpl. clear - Hα; fsetdec.
Qed.

(* ===================================================================== *)
(*  The Abs row — the split is the IDENTITY (the input is ◇ or the        *)
(*  arrow), guess^TY's block is CHOSEN with an avoid set                  *)
(*  ([a_guess_mono_exists]), its fills come from [a_guess_mono_complete]  *)
(*  (the paper's ⑯⑰), the binder's ≡ᵗ discrepancy is absorbed by          *)
(*  [a_inc__var] (the measure-scouting insight), and the optimality       *)
(*  strips the term entry and the block off the body's witnesses.         *)
(* ===================================================================== *)

Lemma a_typing_complete_abs : forall M Θ0 P0 e κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat M P0 ->
  M <> mode_tc ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_abs e) ->
  (forall x M' Θ0' P0' κ' Θ' B',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
        binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     Θ' ⊢ˢᵃ[ M' ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' (open_exp_wrt_exp e (exp_var_f x))
       κ' Θ' B') ->
  Θ ⊢ˢᵃ[ M ] (exp_abs e) ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl M Θ0 P0 (exp_abs e) κ Θ B.
Proof.
  intros M Θ0 P0 e κ Θ B Hwf0 HwfΘ HwfP0 Hmod HMne Hinc Hrig Hskl HsklT
         Hlc IH Hd Href.
  inversion Hd; subst; [ exfalso; auto | exfalso; auto | ].
  match goal with
  | H : forall x, x `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : a_wf_ptyp Θ ?AA |- _ => rename H into HwfA; rename AA into A
  end.
  match goal with
  | H : mod_comp_ty _ _ |- _ => rename H into Hmc
  end.
  match goal with
  | |- typ_complete_concl _ _ _ _ _ _ (btyp_arrow _ ?BB) => rename BB into Bc
  end.
  simpl in Hrig.
  assert (Hlce : forall x, lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (intros x; inversion Hlc; auto).
  (* ---- 1. the split is the IDENTITY (the input is ◇ or the arrow) ---- *)
  (* P and Q name the split halves in both compat cases *)
  assert (Hshape : exists P Q,
      Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ0 /\
      a_ty_mode_compat (decr_mode M) Q /\
      (Θ0 ⨟ empty ⊢ₚₛᵃ P) /\ (Θ0 ⨟ empty ⊢ₚₛᵃ Q) /\
      (Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P))
         ⊳ (btyp_to_bskl (ptyp_to_btyp_inh A))) /\
      (Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ Q))
         ⊳ (btyp_to_bskl Bc))).
  { inversion Hmod; subst.
    - (* TI : ◇ splits into ◇ → ◇ *)
      exists pskl_hole, pskl_hole.
      cbn [msubst_pskl pskl_to_bskl_inh] in Href |- *.
      inversion Href; subst.
      match goal with
      | Hp : pskl_to_bskl_syn ?PF = _, Hw : _ ⨟ empty ⊢ₚₛᵃ ?PF |- _ =>
          destruct PF; simpl in Hp; try discriminate;
          inversion Hp; subst; inversion Hw; subst
      end.
      cbn [decr_mode].
      repeat split; try apply a_split__hole; try apply a_wf_pskl__hole;
        [ apply a_ty_mode_compat__ti | | ].
      + first [ apply ad_refine_syn__hole; assumption
              | match goal with
                | Hpa : pskl_to_bskl_syn _ = btyp_to_bskl _ |- _ =>
                    rewrite <- Hpa; apply ad_refine_syn__hole; assumption
                end ].
      + first [ apply ad_refine_syn__hole; assumption
              | match goal with
                | Hpb : pskl_to_bskl_syn _ = btyp_to_bskl Bc |- _ =>
                    rewrite <- Hpb; apply ad_refine_syn__hole; assumption
                end ].
    - (* TC : excluded by the rule's own mode side condition *)
      exfalso; apply HMne; reflexivity.
    - (* FN : the arrow splits into its halves *)
      match goal with
      | |- exists _ _, (a_split _ (pskl_arrow ?PP ?QQ) _ _ _) /\ _ =>
          exists PP, QQ
      end.
      cbn [msubst_pskl pskl_to_bskl_inh] in Href.
      inversion Href; subst.
      inversion HwfP0; subst.
      cbn [decr_mode].
      repeat split; try apply a_split__arrow; try assumption.
  }
  destruct Hshape as [P [Q [Hsplit [HmodQ [HwfP [HwfQ [HrefD HrefC]]]]]]].
  (* ---- 2. the GUESS of the domain, with its avoid set ---- *)
  destruct (@a_guess_mono_exists P Θ0
              (dom Θ0 `union` ftvar_in_aenv Θ0
                 `union` dom Θ `union` ftvar_in_aenv Θ
                 `union` dom κ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                 `union` fvar_in_exp e `union` ftvar_in_exp e)
              ltac:(eapply a_wf_pskl_lc; exact HwfP))
    as [blk [A' [Hguess [Hdecls [Huqb Havb]]]]].
  (* ---- 3. the fills : the paper's "sketchy" ⑯⑰ ---- *)
  destruct (@a_guess_mono_complete Θ empty _ _ HrefD
              P (ptyp_to_btyp_inh A) Θ0 blk A' κ Θ0 HwfΘ eq_refl eq_refl
              (ptyp_to_btyp_inh_ityp (a_wf_ptyp_lc HwfA))
              Hguess Hinc Huqb
              ltac:(intros α Hα;
                    pose proof (Havb α Hα) as Hn; clear - Hn; fsetdec))
    as [ζg [Hmap [Hents HeqA']]].
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh in HeqA'.
  set (κg := ζg ++ κ) in *.
  assert (Hincg : κg ∷ (blk ++ Θ0) ⊑ Θ)
    by (apply a_inc_extend_flex_block;
        [ exact Hinc | exact Hmap | exact Hdecls | exact Hents ]).
  pose proof (map_fst_eq_dom _ _ Hmap) as Hdζ.
  (* ⑱ : the codomain refinement is untouched by the fills *)
  assert (HrefCg : Θ ⨟ empty ⊢ᵣᵃ
                     (pskl_to_bskl_inh (msubst_pskl κg Q))
                     ⊳ (btyp_to_bskl Bc)).
  { assert (Hag : msubst_pskl κg Q = msubst_pskl κ Q).
    { apply msubst_pskl_agree.
      intros α Hα.
      apply msubst_lookup_app_notin.
      rewrite Hdζ.
      intros Hc.
      pose proof (Havb α Hc) as Hn. clear - Hn Hα; fsetdec. }
    rewrite Hag. exact HrefC. }
  (* ---- 4. one fresh binder and the block-extended contexts ---- *)
  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` dom blk
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A `union` ftvar_in_ptyp A'
                          `union` ftvar_in_pskl P `union` ftvar_in_pskl Q))
    as [x Hx].
  assert (Hwfblk : a_wf_aenv (blk ++ Θ0)).
  { apply a_wf_aenv_decls_app; [ exact Hdecls | exact Huqb | | exact Hwf0 ].
    intros α Hα. pose proof (Havb α Hα) as Hn. clear - Hn; fsetdec. }
  assert (HwfA' : a_wf_ptyp (blk ++ Θ0) A').
  { apply a_wf_ptyp_of_lc_tvarish;
      [ eapply a_guess_mono_lc; exact Hguess | ].
    intros α Hα.
    pose proof (a_guess_mono_ftv Hguess) as Hsub.
    destruct (AtomSetProperties.In_dec α (dom blk)) as [Hin | Hni].
    - right; left. apply binds_app_2.
      apply a_decls_in_dom_binds; [ exact Hdecls | exact Hin ].
    - assert (HαP : α `in` ftvar_in_pskl P) by (clear - Hα Hsub Hni; fsetdec).
      destruct (a_wf_pskl_ftv_tvarish HwfP HαP) as [Hc | Ht];
        [ exfalso; clear - Hc; fsetdec | ].
      destruct Ht as [Hr | [Hm | [τ Hdf]]];
        [ left; apply binds_app_3; exact Hr
        | right; left; apply binds_app_3; exact Hm
        | right; right; exists τ; apply binds_app_3; exact Hdf ]. }
  assert (Hwf0x : a_wf_aenv ((x ~ abind_var_typ A') ++ blk ++ Θ0))
    by (apply a_wf_aenv__var_typ;
        [ rewrite dom_app; clear - Hx; fsetdec | exact HwfA' | exact Hwfblk ]).
  assert (HwfΘx : a_wf_aenv ((x ~ abind_var_typ A) ++ Θ))
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (Hincx : κg ∷ ((x ~ abind_var_typ A') ++ blk ++ Θ0)
                    ⊑ ((x ~ abind_var_typ A) ++ Θ)).
  { apply (@a_inc__var (blk ++ Θ0) κg Θ nil x A' A);
      [ exact Hincg
      | apply a_tyequiv__sym; exact HeqA'
      | apply a_suffix__nil ]. }
  (* the side data for the IH *)
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (apply Hlce).
  assert (Hrigx : forall α,
             α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
             binds α abind_tvar ((x ~ abind_var_typ A') ++ blk ++ Θ0)).
  { intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup.
    apply binds_cons_3. apply binds_app_3. apply Hrig.
    clear - Hα Hup; fsetdec. }
  assert (Hsklx : forall y Ps,
             binds y (abind_var_skl Ps) ((x ~ abind_var_typ A') ++ blk ++ Θ0) ->
             ((x ~ abind_var_typ A') ++ blk ++ Θ0) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
      [ discriminate Heq | ].
    apply binds_app_1 in Hb' as [Hb' | Hb'].
    { exfalso.
      pose proof (@a_decls_binds_flex blk y (abind_var_skl Ps) Hdecls Hb') as Hc.
      discriminate Hc. }
    eapply a_wf_pskl_mono; [ eapply Hskl; exact Hb' | ].
    intros α c _ Hc. apply binds_cons_3. apply binds_app_3. exact Hc. }
  assert (HsklTx : forall y Ps,
             binds y (abind_var_skl Ps) ((x ~ abind_var_typ A) ++ Θ) ->
             ((x ~ abind_var_typ A) ++ Θ) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
      [ discriminate Heq | ].
    eapply a_wf_pskl_mono; [ eapply HsklT; exact Hb' | ].
    intros α c _ Hc. apply binds_cons_3. exact Hc. }
  assert (HwfQx : ((x ~ abind_var_typ A') ++ blk ++ Θ0) ⨟ empty ⊢ₚₛᵃ Q)
    by (eapply a_wf_pskl_mono;
        [ exact HwfQ
        | intros α c _ Hc; apply binds_cons_3; apply binds_app_3; exact Hc ]).
  (* ---- 5. the IH, once ---- *)
  destruct (IH x (decr_mode M) ((x ~ abind_var_typ A') ++ blk ++ Θ0) Q κg
              ((x ~ abind_var_typ A) ++ Θ) Bc
              Hwf0x HwfΘx HwfQx HmodQ Hincx Hrigx Hsklx HsklTx Hlcbody
              (Hbody x ltac:(clear - Hx; fsetdec))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact HrefCg
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [B' [Θout [HrunB HoptB]]].
  (* ---- 6. the body run's identity increase shapes the output ---- *)
  assert (Hexpx : a_wf_exp ((x ~ abind_var_typ A') ++ blk ++ Θ0)
                    (open_exp_wrt_exp e (exp_var_f x))).
  { apply a_wf_exp_of_tvarish; [ exact Hlcbody | ].
    intros α Hα. left. apply Hrigx. exact Hα. }
  destruct (a_typing_sound HrunB Hwf0x Hsklx HwfQx HmodQ Hexpx)
    as [HleB [HwfOut [HwfB'out _]]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (a_inc_var_inv Hincb) as [Ξ [A'' [Θ2 [-> [_ [Hsuf Hincb']]]]]].
  assert (HuOut : uniq (Ξ ++ (x ~ abind_var_typ A'') ++ Θ2))
    by (apply a_wf_aenv_uniq; exact HwfOut).
  assert (Hbx1 : binds x (abind_var_typ A')
                   (Ξ ++ (x ~ abind_var_typ A'') ++ Θ2))
    by (eapply a_typing_tm_le;
        [ exact HrunB | exact I | unfold binds; simpl; auto ]).
  assert (HA'' : abind_var_typ A' = abind_var_typ A'')
    by (eapply binds_mid_eq; [ exact Hbx1 | exact HuOut ]).
  inversion HA''; subst A''.
  (* ---- 7. the freshness pack ---- *)
  assert (HxΞ : x `notin` (dom Ξ `union` ftvar_in_aenv Ξ))
    by (eapply a_wf_aenv_notin_ftv_tm_prefix;
        [ exact Hsuf | exact HwfOut | exact I ]).
  assert (HxΘ2 : x `notin` (dom Θ2 `union` ftvar_in_aenv Θ2))
    by (eapply a_wf_aenv_notin_ftv_tm_below; exact HwfOut).
  assert (HxB' : x `notin` ftvar_in_ptyp B').
  { intros Hc.
    pose proof (a_wf_ptyp_ftv_tvarish HwfB'out Hc) as Ht.
    destruct Ht as [Hr | [Hm | [τ Hdf]]].
    - pose proof (binds_mid_eq _ _ _ _ _ _ Hr HuOut) as Hcc.
      discriminate Hcc.
    - pose proof (binds_mid_eq _ _ _ _ _ _ Hm HuOut) as Hcc.
      discriminate Hcc.
    - pose proof (binds_mid_eq _ _ _ _ _ _ Hdf HuOut) as Hcc.
      discriminate Hcc. }
  (* the declarations block mentions only its own names *)
  assert (Hftvblk : ftvar_in_aenv blk [<=] dom blk)
    by (clear - Hdecls; induction Hdecls; simpl; fsetdec).
  (* ---- 8. the run ---- *)
  exists (ptyp_arrow A' B'), (Ξ ++ Θ2).
  split.
  { eapply a_typing__abs with (x := x) (Ξ := Ξ) (Θ2 := Θ2)
      (P := P) (Q := Q) (αs := blk) (Θ1 := Θ0).
    - exact HMne.
    - exact Hsplit.
    - exact Hguess.
    - apply uniq_app_of;
        [ exact Huqb | apply a_wf_aenv_uniq; exact Hwf0
        | intros α Hα Hc;
          pose proof (Havb α Hα) as Hn;
          assert (Hd0 : α `in` dom Θ0) by (clear - Hc; fsetdec);
          clear - Hn Hd0; fsetdec ].
    - exact Hsuf.
    - rewrite !dom_app. clear - Hx HxΞ HxΘ2. solve_notin.
    - exact HrunB. }
  (* ---- 9. optimality ---- *)
  intros κ1 Hid1 Hinc1.
  (* the body's witness, target-weakened across the suffix, is THE id *)
  assert (Hlcfin : lc_aenv (Ξ ++ (x ~ abind_var_typ A') ++ Θ2))
    by (apply a_wf_aenv_lc_aenv; exact HwfOut).
  assert (Hinc1b : κb ∷ ((x ~ abind_var_typ A') ++ blk ++ Θ0)
                     ⊑ (Ξ ++ (x ~ abind_var_typ A') ++ Θ2)).
  { apply (@a_inc__var (blk ++ Θ0) κb Θ2 Ξ x A' A');
      [ exact Hincb'
      | rewrite (msubst_ptyp_id A' Hidb);
        apply a_tyequiv__refl; eapply a_guess_mono_lc; exact Hguess
      | exact Hsuf ]. }
  destruct (HoptB κb Hidb Hinc1b) as [ζb [Hζb [Heqvb Heqcb]]].
  assert (Hζbs : ζb ∷ (Ξ ++ Θ2) ⊑ Θ).
  { exact (@a_inc_strip_tm_head Ξ x (abind_var_typ A') (abind_var_typ A)
             Θ2 ζb Θ Hsuf
             (fun h : abind_is_ty (abind_var_typ A') => h)
             (fun h : abind_is_ty (abind_var_typ A) => h)
             HwfOut HwfΘx Hζb). }
  assert (Heqvbs : a_inc_equiv (blk ++ Θ0) κg (msubst_compose ζb κb) Θ)
    by (eapply a_inc_equiv_strip_var_typ_head; [ exact Heqvb | exact I ]).
  (* split the body id and the equivalence along the block *)
  destruct (@a_inc_strip_decls_head blk κb Θ0 Θ2 Hdecls Hincb')
    as [κbp [κbt [Heqκb [Hlenb Hincbt]]]].
  destruct (@a_inc_equiv_strip_decls_head blk Θ0 κg (msubst_compose ζb κb) Θ Hdecls Heqvbs)
    as [κ1p [κ1t [κ2p [κ2t [Hspl1 [Hspl2 [Hl1 [Hl2 Heqv0]]]]]]]].
  (* the equivalence's left tail is the caller's κ *)
  assert (Hlenζg : length ζg = length blk).
  { pose proof (f_equal (@length atom) Hmap) as Hl.
    rewrite !List.length_map in Hl. exact Hl. }
  (* identify the tails *)
  destruct (app_inj_prefix _ _ _ _ Hspl1
              ltac:(rewrite Hl1; exact Hlenζg))
    as [Heqp1 Heqt1].
  assert (Hκ1t : κ1t = κ) by (clear - Heqt1; congruence).
  subst κ1t.
  (* the right side splits along the compose of the body id's split *)
  rewrite Heqκb in Hspl2.
  unfold msubst_compose in Hspl2.
  rewrite List.map_app in Hspl2.
  destruct (app_inj_prefix _ _ _ _ Hspl2
              ltac:(rewrite Hl2, List.length_map; exact Hlenb))
    as [Heqp2 Heqt2].
  (* the caller's id is the body id's tail *)
  assert (Hidbt : is_id_msubst κbt)
    by (rewrite Heqκb in Hidb; eapply is_id_msubst_app_r; exact Hidb).
  assert (Heqκ1 : κ1 = κbt)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincbt | exact Hid1 | exact Hidbt ]).
  exists ζb.
  split; [ exact Hζbs | ].
  split.
  { rewrite Heqκ1.
    unfold msubst_compose.
    rewrite Heqt2.
    exact Heqv0. }
  (* the arrow equivalence : ⑰ pushed to ζb on the domain, the body's on
     the codomain (term entry stripped) *)
  assert (Hwffin : a_wf_aenv (Ξ ++ Θ2))
    by (exact (@a_wf_aenv_strip_tm_mid Ξ x (abind_var_typ A') Θ2
                 (fun h : abind_is_ty (abind_var_typ A') => h) HwfOut)).
  assert (HwfA'x : a_wf_ptyp ((x ~ abind_var_typ A') ++ blk ++ Θ0) A')
    by (eapply a_wf_ptyp_weaken;
        [ intros y c Hc; apply binds_cons_3; exact Hc | exact HwfA' ]).
  assert (Hpush : Θ ⊢ (msubst_ptyp κg A') ≡ᵗ
                    (msubst_ptyp (msubst_compose ζb κb) A')).
  { apply (@a_inc_equiv_msubst_ptyp A' (blk ++ Θ0) κg
             (msubst_compose ζb κb) Θ HwfA' Heqvbs Hwfblk
             ltac:(eapply a_inc_msubst_lc; exact Hincg)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζbs
                   | exact (is_id_msubst_values_lc Hidb) ])). }
  assert (Hlcfin2 : lc_aenv Θ2)
    by (apply a_wf_aenv_lc_aenv;
        eapply a_wf_aenv_app_r with (Θp := Ξ ++ (x ~ abind_var_typ A'));
        simpl_env; exact HwfOut).
  destruct (a_inc_weaken_suffix_target Hincb' Hidb Hlcfin2 Hsuf)
    as [κb2 [Hidb2 Hincb2]].
  assert (Heqκb2 : κb2 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hincb2 | exact Hincb' | exact Hidb2 | exact Hidb ]).
  subst κb2.
  assert (Hcid : msubst_ptyp (msubst_compose ζb κb) A' = msubst_ptyp ζb A')
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwfblk | exact Hwffin | exact Hidb | exact Hincb2
        | exact Hζbs | exact HwfA' ]).
  rewrite Hcid in Hpush.
  simpl.
  apply a_tyequiv__arrow.
  - rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
    eapply a_tyequiv__trans;
      [ apply a_tyequiv__sym; exact Hpush | exact HeqA' ].
  - eapply prop_ctx_mono.a_tyequiv_mono;
      [ exact Heqcb
      | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ A) Θ);
        intros h; exact h ].
Qed.

(* --- the AbsAnno row -------------------------------------------------- *)

Lemma a_typing_complete_abs_anno : forall M Θ0 P0 A e κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat M P0 ->
  M <> mode_tc ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_abs_anno A e) ->
  (forall x M' Θ0' P0' κ' Θ' B',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
        binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     Θ' ⊢ˢᵃ[ M' ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' (open_exp_wrt_exp e (exp_var_f x))
       κ' Θ' B') ->
  Θ ⊢ˢᵃ[ M ] (exp_abs_anno A e) ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl M Θ0 P0 (exp_abs_anno A e) κ Θ B.
Proof.
  intros M Θ0 P0 A e κ Θ B Hwf0 HwfΘ HwfP0 Hmod HMne Hinc Hrig Hskl HsklT
         Hlc IH Hd Href.
  inversion Hd; subst; [ exfalso; auto | exfalso; auto | ].
  match goal with
  | H : forall x, x `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  (* ⚙ [subst] consumed the rule's [btyp_to_ptyp B1 = A'] equation and
     [A'] with it — the ≡ᵗ premise now reads [Θ ⊢ A ≡ᵗ ⌊B1⌋]. *)
  match goal with
  | H : Θ ⊢ A ≡ᵗ (btyp_to_ptyp ?BB) |- _ =>
      rename H into HeqAA'; rename BB into B1
  end.
  set (A' := btyp_to_ptyp B1) in *.
  match goal with
  | |- typ_complete_concl _ _ _ _ _ _ (btyp_arrow _ ?BB) => rename BB into B2
  end.
  match goal with
  | H : a_wf_ptyp Θ A |- _ => rename H into HwfA
  end.
  simpl in Hrig.
  assert (HrigA : forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlce : forall x, lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (intros x; inversion Hlc; auto).
  assert (HlcA : lc_ptyp A) by (inversion Hlc; assumption).
  assert (HwfA0 : a_wf_ptyp Θ0 A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA; exact Hα ]).
  assert (HmsA : msubst_ptyp κ A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc | exact Hwf0 | exact HrigA ]).
  assert (HwfA' : a_wf_ptyp Θ A')
    by (eapply (proj1 (a_tyequiv_wf_iff HeqAA' (fun x b h => h) HwfΘ));
        exact HwfA).
  assert (HB1 : btyp_to_ptyp B1 = A') by reflexivity.
  (* ---- 1. the split is the identity ---- *)
  assert (Hshape : exists P Q,
      Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ0 /\
      a_ty_mode_compat (decr_mode M) Q /\
      (Θ0 ⨟ empty ⊢ₚₛᵃ P) /\ (Θ0 ⨟ empty ⊢ₚₛᵃ Q) /\
      (Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P))
         ⊳ (btyp_to_bskl B1)) /\
      (Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ Q))
         ⊳ (btyp_to_bskl B2))).
  { inversion Hmod; subst.
    - exists pskl_hole, pskl_hole.
      cbn [msubst_pskl pskl_to_bskl_inh] in Href |- *.
      inversion Href; subst.
      match goal with
      | Hp : pskl_to_bskl_syn ?PF = _, Hw : _ ⨟ empty ⊢ₚₛᵃ ?PF |- _ =>
          destruct PF; simpl in Hp; try discriminate;
          inversion Hp; subst; inversion Hw; subst
      end.
      cbn [decr_mode].
      repeat split; try apply a_split__hole; try apply a_wf_pskl__hole;
        [ apply a_ty_mode_compat__ti | | ].
      + first [ apply ad_refine_syn__hole; assumption
              | match goal with
                | Hpa : pskl_to_bskl_syn _ = btyp_to_bskl _ |- _ =>
                    rewrite <- Hpa; apply ad_refine_syn__hole; assumption
                end ].
      + first [ apply ad_refine_syn__hole; assumption
              | match goal with
                | Hpb : pskl_to_bskl_syn _ = btyp_to_bskl B2 |- _ =>
                    rewrite <- Hpb; apply ad_refine_syn__hole; assumption
                end ].
    - exfalso; apply HMne; reflexivity.
    - match goal with
      | |- exists _ _, (a_split _ (pskl_arrow ?PP ?QQ) _ _ _) /\ _ =>
          exists PP, QQ
      end.
      cbn [msubst_pskl pskl_to_bskl_inh] in Href.
      inversion Href; subst.
      inversion HwfP0; subst.
      cbn [decr_mode].
      repeat split; try apply a_split__arrow; try assumption.
  }
  destruct Hshape as [P [Q [Hsplit [HmodQ [HwfP [HwfQ [HrefD HrefC]]]]]]].
  (* ---- 2. the annotation's consistency stage ---- *)
  assert (HwfpA0 : Θ0 ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl A))
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfA0).
  assert (Heqs : Θ ⊢ (ptyp_to_pskl A) ≡ˢ (ptyp_to_pskl A'))
    by (apply a_tyequiv_embed_pskl; exact HeqAA').
  assert (Hjoin : empty ⨟ Θ ⊢ₛᵃ
                    (pskl_to_uskl (msubst_pskl κ (ptyp_to_pskl A)))
                    ∼ (btyp_to_bskl B1)).
  { rewrite msubst_pskl_embed_ptyp, HmsA.
    eapply (proj2 (skl_tyequiv_consis_transport Heqs HwfΘ
                     (fun x b h => h))).
    rewrite pskl_to_uskl_ptyp.
    apply (ad_pat_consis_syn_bid HwfA' B1 HB1). }
  assert (Hrp : ad_refine_pskl_f empty Θ empty
                  (msubst_pskl κ (ptyp_to_pskl A))
                  (bskl_to_pskl (btyp_to_bskl B1))).
  { rewrite msubst_pskl_embed_ptyp, HmsA.
    rewrite bskl_to_pskl_btyp, HB1.
    eapply (proj2 (skl_tyequiv_refine_pskl_f_transport Heqs HwfΘ
                     (fun x b h => h))).
    apply ad_refine_pskl_f_of_plain.
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA'. }
  destruct (a_consis_complete_thm Hwf0 HwfP HwfpA0 Hinc HwfΘ Hjoin
              ltac:(apply ad_refine_syn_f_of_plain; exact HrefD)
              Hrp)
    as [Qc [Θmid [HcRun HoptC]]].
  destruct (a_consis_isub_wf_nil HcRun Hwf0 HwfP HwfpA0) as [HleC Hwfmid].
  destruct HleC as [[κc [Hidc Hincc]] _].
  destruct (HoptC κc Hidc Hincc) as [ζc [Hζc [Heqvc _]]].
  (* ---- 3. the binder and its side data ---- *)
  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` dom Θmid `union` ftvar_in_aenv Θmid
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A
                          `union` ftvar_in_pskl P `union` ftvar_in_pskl Q))
    as [x Hx].
  assert (HrigMid : forall α, α `in` ftvar_in_ptyp A ->
             binds α abind_tvar Θmid)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincc | apply HrigA; exact Hα ]).
  assert (HwfAmid : a_wf_ptyp Θmid A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigMid; exact Hα ]).
  assert (Hwf0x : a_wf_aenv ((x ~ abind_var_typ A) ++ Θmid))
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAmid | exact Hwfmid ]).
  assert (HwfΘx : a_wf_aenv ((x ~ abind_var_typ A) ++ Θ))
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (HmsAζc : msubst_ptyp ζc A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζc | exact Hwfmid | exact HrigMid ]).
  assert (Hincx : ζc ∷ ((x ~ abind_var_typ A) ++ Θmid)
                    ⊑ ((x ~ abind_var_typ A) ++ Θ)).
  { apply (@a_inc__var Θmid ζc Θ nil x A A);
      [ exact Hζc
      | rewrite HmsAζc; apply a_tyequiv__refl; exact HlcA
      | apply a_suffix__nil ]. }
  (* the codomain refinement at ζc (the Anno idiom) *)
  assert (Hσ : msubst_compose ζc κc ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hincc | exact Hwf0 | exact Hwfmid | exact Hζc ]).
  assert (HwfQB2 : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B2))).
  { pose proof (ad_sd_typing_target_wf Hd HwfΘ) as Hw.
    simpl in Hw. inversion Hw; subst.
    rewrite bskl_to_pskl_btyp.
    apply a_wf_ptyp_to_wf_pskl. assumption. }
  assert (Hpp : Θ ⨟ empty ⊢ₚᵣᵃ
                  (msubst_pskl (msubst_compose ζc κc) Q)
                  ⊑ (msubst_pskl κ Q)).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfQ | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
      | exact Heqvc | clear; fsetdec ]. }
  assert (HrefCζ : Θ ⨟ empty ⊢ᵣᵃ
                     (pskl_to_bskl_inh
                        (msubst_pskl (msubst_compose ζc κc) Q))
                     ⊳ (btyp_to_bskl B2)).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact HrefC | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQB2 ]. }
  assert (HmsQ : msubst_pskl (msubst_compose ζc κc) Q = msubst_pskl ζc Q).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwfmid | exact Hidc | exact Hincc | exact Hζc
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfQ | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ] ]. }
  rewrite HmsQ in HrefCζ.
  (* the remaining IH side data *)
  assert (Hrigx : forall α,
             α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
             binds α abind_tvar ((x ~ abind_var_typ A) ++ Θmid)).
  { intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup.
    apply binds_cons_3. eapply a_inc_binds_tvar;
      [ exact Hincc | apply Hrig; clear - Hα Hup; fsetdec ]. }
  assert (Hsklmid : forall y Ps, binds y (abind_var_skl Ps) Θmid ->
             Θmid ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    assert (Hb0 : binds y (abind_var_skl Ps) Θ0)
      by (eapply a_consis_tm_ge; [ exact HcRun | exact I | exact Hb ]).
    pose proof (a_wf_pskl_msubst_inc Hincc Hwf0 (Hskl _ _ Hb0)
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id Ps Hidc) in Hw. exact Hw. }
  assert (Hsklx : forall y Ps,
             binds y (abind_var_skl Ps) ((x ~ abind_var_typ A) ++ Θmid) ->
             ((x ~ abind_var_typ A) ++ Θmid) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
      [ discriminate Heq | ].
    eapply a_wf_pskl_mono; [ eapply Hsklmid; exact Hb' | ].
    intros α c _ Hc. apply binds_cons_3. exact Hc. }
  assert (HsklTx : forall y Ps,
             binds y (abind_var_skl Ps) ((x ~ abind_var_typ A) ++ Θ) ->
             ((x ~ abind_var_typ A) ++ Θ) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
      [ discriminate Heq | ].
    eapply a_wf_pskl_mono; [ eapply HsklT; exact Hb' | ].
    intros α c _ Hc. apply binds_cons_3. exact Hc. }
  assert (HwfQmid : Θmid ⨟ empty ⊢ₚₛᵃ Q).
  { pose proof (a_wf_pskl_msubst_inc Hincc Hwf0 HwfQ
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id Q Hidc) in Hw. exact Hw. }
  (* ---- 4. the IH, once ---- *)
  destruct (IH x (decr_mode M) ((x ~ abind_var_typ A) ++ Θmid) Q ζc
              ((x ~ abind_var_typ A) ++ Θ) B2
              Hwf0x HwfΘx
              ltac:(eapply a_wf_pskl_mono;
                    [ exact HwfQmid
                    | intros α c _ Hc; apply binds_cons_3; exact Hc ])
              HmodQ Hincx Hrigx Hsklx HsklTx (Hlce x)
              (Hbody x ltac:(clear - Hx; fsetdec))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact HrefCζ
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [B' [Θout [HrunB HoptB]]].
  (* ---- 5. the body run's identity increase shapes the output ---- *)
  assert (Hexpx : a_wf_exp ((x ~ abind_var_typ A) ++ Θmid)
                    (open_exp_wrt_exp e (exp_var_f x))).
  { apply a_wf_exp_of_tvarish; [ exact (Hlce x) | ].
    intros α Hα. left. apply Hrigx. exact Hα. }
  assert (HwfQx : ((x ~ abind_var_typ A) ++ Θmid) ⨟ empty ⊢ₚₛᵃ Q)
    by (eapply a_wf_pskl_mono;
        [ exact HwfQmid
        | intros α c _ Hc; apply binds_cons_3; exact Hc ]).
  destruct (a_typing_sound HrunB Hwf0x Hsklx HwfQx HmodQ Hexpx)
    as [HleB [HwfOut [HwfB'out _]]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (a_inc_var_inv Hincb) as [Ξ [A'' [Θ3 [-> [_ [Hsuf Hincb']]]]]].
  assert (HuOut : uniq (Ξ ++ (x ~ abind_var_typ A'') ++ Θ3))
    by (apply a_wf_aenv_uniq; exact HwfOut).
  assert (Hbx1 : binds x (abind_var_typ A)
                   (Ξ ++ (x ~ abind_var_typ A'') ++ Θ3))
    by (eapply a_typing_tm_le;
        [ exact HrunB | exact I | unfold binds; simpl; auto ]).
  assert (HA'' : abind_var_typ A = abind_var_typ A'')
    by (eapply binds_mid_eq; [ exact Hbx1 | exact HuOut ]).
  inversion HA''; subst A''.
  (* ---- 6. the freshness pack ---- *)
  assert (HxΞ : x `notin` (dom Ξ `union` ftvar_in_aenv Ξ))
    by (eapply a_wf_aenv_notin_ftv_tm_prefix;
        [ exact Hsuf | exact HwfOut | exact I ]).
  assert (HxΘ3 : x `notin` (dom Θ3 `union` ftvar_in_aenv Θ3))
    by (eapply a_wf_aenv_notin_ftv_tm_below; exact HwfOut).
  assert (HxB' : x `notin` ftvar_in_ptyp B').
  { intros Hc.
    pose proof (a_wf_ptyp_ftv_tvarish HwfB'out Hc) as Ht.
    destruct Ht as [Hr | [Hm | [τ Hdf]]].
    - pose proof (binds_mid_eq _ _ _ _ _ _ Hr HuOut) as Hcc.
      discriminate Hcc.
    - pose proof (binds_mid_eq _ _ _ _ _ _ Hm HuOut) as Hcc.
      discriminate Hcc.
    - pose proof (binds_mid_eq _ _ _ _ _ _ Hdf HuOut) as Hcc.
      discriminate Hcc. }
  (* ---- 7. the run ---- *)
  exists (ptyp_arrow A B'), (Ξ ++ Θ3).
  split.
  { eapply a_typing__abs_anno with (x := x) (Ξ := Ξ) (Θ3 := Θ3)
      (P := P) (Θ1 := Θ0) (Θ2 := Θmid).
    - exact HMne.
    - exact Hsplit.
    - exists Qc; exact HcRun.
    - exact Hsuf.
    - rewrite !dom_app. clear - Hx HxΞ HxΘ3. solve_notin.
    - exact HrunB. }
  (* ---- 8. optimality : glue the two stages ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κc)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincc | exact Hid1 | exact Hidc ]).
  assert (Hinc1b : κb ∷ ((x ~ abind_var_typ A) ++ Θmid)
                     ⊑ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3)).
  { apply (@a_inc__var Θmid κb Θ3 Ξ x A A);
      [ exact Hincb'
      | rewrite (msubst_ptyp_id A Hidb);
        apply a_tyequiv__refl; exact HlcA
      | exact Hsuf ]. }
  destruct (HoptB κb Hidb Hinc1b) as [ζb [Hζb [Heqvb Heqcb]]].
  assert (Hζbs : ζb ∷ (Ξ ++ Θ3) ⊑ Θ).
  { exact (@a_inc_strip_tm_head Ξ x (abind_var_typ A) (abind_var_typ A)
             Θ3 ζb Θ Hsuf
             (fun h : abind_is_ty (abind_var_typ A) => h)
             (fun h : abind_is_ty (abind_var_typ A) => h)
             HwfOut HwfΘx Hζb). }
  assert (Heqvbs : a_inc_equiv Θmid ζc (msubst_compose ζb κb) Θ)
    by (eapply a_inc_equiv_strip_var_typ_head; [ exact Heqvb | exact I ]).
  assert (Hwffin : a_wf_aenv (Ξ ++ Θ3))
    by (exact (@a_wf_aenv_strip_tm_mid Ξ x (abind_var_typ A) Θ3
                 (fun h : abind_is_ty (abind_var_typ A) => h) HwfOut)).
  assert (Hlcfin : lc_aenv Θ3)
    by (apply a_wf_aenv_lc_aenv;
        eapply a_wf_aenv_app_r with (Θp := Ξ ++ (x ~ abind_var_typ A));
        simpl_env; exact HwfOut).
  destruct (a_inc_weaken_suffix_target Hincb' Hidb Hlcfin Hsuf)
    as [κb2 [Hidb2 Hincb2]].
  assert (Heqκb2 : κb2 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hincb2 | exact Hincb' | exact Hidb2 | exact Hidb ]).
  subst κb2.
  exists ζb.
  split; [ exact Hζbs | ].
  split.
  { assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζb κc) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θmid) (Θfin := Ξ ++ Θ3) (κ1b := κb) (ζ1 := ζc);
        [ exact Hwf0 | exact Hwfmid | exact Hwffin | exact HwfΘ
        | exact Hidc | exact Hidb
        | intros α Hα;
          pose proof (a_inc_dom_flex Hincc Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hincb2 | exact Hwfmid
            | eapply a_inc_id_flex_preserve;
                [ exact Hincc | exact Hidc | exact Hwf0 | exact Hfα ] ]
        | exact Hincc | exact Hincb2 | exact Hζc | exact Hζbs
        | exact Heqvc | exact Heqvbs ]. }
    rewrite Heqκ. exact Hglue. }
  (* ---- 9. the arrow equivalence ---- *)
  assert (HrigFin : forall α, α `in` ftvar_in_ptyp A ->
             binds α abind_tvar (Ξ ++ Θ3)).
  { intros α Hα. apply binds_app_3.
    eapply a_inc_binds_tvar; [ exact Hincb' | apply HrigMid; exact Hα ]. }
  assert (HmsAζb : msubst_ptyp ζb A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζbs | exact Hwffin | exact HrigFin ]).
  simpl.
  apply a_tyequiv__arrow.
  - rewrite HmsAζb, HB1.
    exact HeqAA'.
  - eapply prop_ctx_mono.a_tyequiv_mono;
      [ exact Heqcb
      | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ A) Θ);
        intros h; exact h ].
Qed.

(* ===================================================================== *)
(*  Strip helpers for the ∀-peeling check rows: the rule DISCARDS the     *)
(*  body run's suffix [Ξ] and its own binder [α], so the optimality       *)
(*  witnesses must lose (a) the [Ξ]-portion of the metasubstitution and   *)
(*  (b) the rigid head — where the Abs/AbsAnno rows only lost a term      *)
(*  entry ([a_inc_strip_tm_head]), which consumes no κ-entry.             *)
(* ===================================================================== *)

(** Strip an all-flexible PREFIX (a pending suffix, declarations AND
    definitions) off an increase's source, keeping the split and its
    domain.  ([a_inc_strip_decls_prefix] is the declarations-only version;
    [a_inc_strengthen_suffix_src] loses the split.) *)
Lemma a_inc_strip_suffix_head : forall (Ξ E : aenv) (κ : metasubst) Θ,
  a_suffix Ξ ->
  κ ∷ (Ξ ++ E) ⊑ Θ ->
  exists κp κt,
    κ = κp ++ κt /\ dom κp [=] dom Ξ /\ κt ∷ E ⊑ Θ.
Proof.
  intros Ξ; induction Ξ as [ | [γ b] Ξ' IH ]; intros E κ Θ Hsuf Hinc.
  - exists nil, κ.
    split; [ reflexivity | split; [ simpl; clear; fsetdec | exact Hinc ] ].
  - inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst.
    inversion Hb; subst; simpl_env in Hinc; inversion Hinc; subst; clear Hinc;
      match goal with
      | Hrest : _ ∷ (_ ++ E) ⊑ _ |- _ =>
          destruct (IH _ _ _ Hsuf' Hrest) as [κp' [κt [-> [Hd Hincr]]]]
      end;
      eexists ((_, _) :: κp'), κt;
      (split; [ reflexivity
              | split; [ simpl; clear - Hd; fsetdec | exact Hincr ] ]).
Qed.

(** The rigid head strips off both ends of an increase: the source's [α]
    row can only be [a_inc__tvar], and a pending target suffix cannot
    supply the target's rigid head (its entries are flexible). *)
Lemma a_inc_strip_tvar_head : forall α Θ0 κ Θ,
  κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ) ->
  κ ∷ Θ0 ⊑ Θ.
Proof.
  intros α Θ0 κ Θ Hinc.
  destruct (a_inc_tvar_inv Hinc) as [Ξ [Θ2 [Heq [Hsuf Hrest]]]].
  destruct Ξ as [ | [γ b] Ξ' ]; simpl_env in Heq.
  - inversion Heq; subst. exact Hrest.
  - inversion Heq; subst.
    inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst.
    inversion Hb.
Qed.

(** …and off a metasubstitution equivalence (mirror of
    [a_inc_equiv_strip_var_typ_head] for the rigid head; the κs pass
    through untouched — [a_inc_equiv__tvar] consumes no entry). *)
Lemma a_inc_equiv_strip_tvar_head : forall α Θ0 κ1 κ2 Θ,
  a_inc_equiv ((α ~ abind_tvar) ++ Θ0) κ1 κ2 ((α ~ abind_tvar) ++ Θ) ->
  a_inc_equiv Θ0 κ1 κ2 Θ.
Proof.
  intros α Θ0 κ1 κ2 Θ Hie.
  inversion Hie; subst.
  match goal with
  | Hsuf : a_suffix ?ΞS, HeqT : ?l = ?r |- _ =>
      first [ constr_eq l ((α ~ abind_tvar) ++ Θ); symmetry in HeqT | idtac ];
      destruct ΞS as [ | [z bz] Ξ' ]; simpl_env in HeqT;
      [ inversion HeqT; subst; assumption
      | inversion HeqT; subst;
        inversion Hsuf as [ | ? ? ? ? Hsb ]; subst;
        inversion Hsb ]
  end.
Qed.

(** Composing with an identity ignores a prefix outside the identity's
    domain — the [Ξ]-portion of the body witness acts on names the
    caller's id never mentions. *)
Lemma msubst_compose_id_prefix_notin : forall (ζp ζt κ1 : metasubst),
  is_id_msubst κ1 ->
  (forall β, β `in` dom κ1 -> β `notin` dom ζp) ->
  msubst_compose (ζp ++ ζt) κ1 = msubst_compose ζt κ1.
Proof.
  intros ζp ζt κ1; induction κ1 as [ | [β τ] κ1' IH ]; intros Hid Hav;
    [ reflexivity | ].
  destruct (is_id_msubst_inv Hid) as [-> Hid'].
  unfold msubst_compose in *. simpl.
  f_equal.
  - f_equal.
    rewrite msubst_lookup_app_notin;
      [ reflexivity | apply Hav; simpl; clear; fsetdec ].
  - apply IH; [ exact Hid' | ].
    intros β' Hβ'. apply Hav. simpl. clear - Hβ'; fsetdec.
Qed.

(** [≡ᵗ] reads Θ only through flexible DEFINITIONS, so a rigid head
    strengthens away outright. *)
Lemma a_tyequiv_strip_tvar_head : forall Θfull A B,
  Θfull ⊢ A ≡ᵗ B ->
  forall α Θ, Θfull = (α ~ abind_tvar) ++ Θ ->
  Θ ⊢ A ≡ᵗ B.
Proof.
  intros Θfull A B H; induction H; intros α0 Θ0 ->.
  - apply a_tyequiv__refl; assumption.
  - apply a_tyequiv__sym; eauto.
  - eapply a_tyequiv__trans; eauto.
  - (* flex_def : the head is rigid, so the definition is in the tail *)
    destruct (binds_cons_1 _ _ _ _ _ _ H) as [[-> Heq] | Hb];
      [ discriminate Heq | ].
    apply a_tyequiv__flex_def. exact Hb.
  - apply a_tyequiv__arrow; eauto.
  - apply a_tyequiv__all with (L := L). intros β Hβ. eapply H0; eauto.
Qed.

(** Refinement's ∀-inh row binds its witness in Δ; the algorithmic side
    puts it in Θ as a rigid entry.  Going Δ → Θ is a weakening (mirror of
    [a_wf_pskl_delta_to_ctx]; [__var] accepts either side, [__hole]'s wf
    weakens, and [__tophole_fill]'s own binder exchanges past the new
    head — [binds] is plain membership). *)
Lemma ad_refine_syn_delta_to_ctx : forall Θ Δ0 Q Q',
  Θ ⨟ Δ0 ⊢ᵣᵃ Q ⊳ Q' ->
  forall α Δ, Δ0 [<=] add α Δ ->
  ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣᵃ Q ⊳ Q'.
Proof.
  intros Θ Δ0 Q Q' H; induction H; intros α0 Δ' Hsub.
  - apply ad_refine_syn__unit.
  - destruct H as [HΔ | Hbt].
    + destruct (α == α0) as [-> | Hne].
      * apply ad_refine_syn__var. right. left.
        unfold binds. simpl. left. reflexivity.
      * apply ad_refine_syn__var. left. clear - HΔ Hsub Hne. fsetdec.
    + apply ad_refine_syn__var. right.
      apply a_binds_tvar_weaken_cons. exact Hbt.
  - apply ad_refine_syn__arrow; auto.
  - apply ad_refine_syn__all with (L := L).
    intros β Hβ.
    apply H0; [ exact Hβ | clear - Hsub; fsetdec ].
  - apply ad_refine_syn__hole.
    eapply a_wf_pskl_delta_to_ctx; [ exact H | clear; fsetdec ].
  - apply ad_refine_syn__tophole_remove; auto.
  - apply ad_refine_syn__tophole_fill with (L := L).
    intros β Hβ.
    eapply ad_refine_syn_weaken;
      [ apply (H0 β Hβ α0 Δ' Hsub) | ].
    intros x b Hb.
    unfold binds in *; simpl in Hb |- *.
    destruct Hb as [Hb | [Hb | Hb]]; auto.
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l;
      [ apply binds_cons_3; exact H | auto ].
  - eapply ad_refine_syn__flex_r;
      [ apply binds_cons_3; exact H | auto ].
Qed.

(* ===================================================================== *)
(*  The two rows, discharging premise (2) with the §6.3#2 scoping         *)
(*  invariant — [a_typing_scope_tvar_nil], the TVAR-marker corollary at   *)
(*  [Ξ0 = nil] (algo/prop_ty_scope.v).                                    *)
(* ===================================================================== *)

(* --- the AbsCheck ∀ row ------------------------------------------------ *)

Lemma a_typing_complete_abs_check_step : forall Θ0 P0 e κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_abs e) ->
  (forall M' Θ0' P0' κ' Θ' B',
     (* ⭐ THE MEASURE GUARD.  These rows recurse on the SAME subject, so
        the glue can only supply an IH at a SMALLER declarative result —
        the lexicographic (size_exp, size_btyp) measure's second
        component.  Without this premise the row is unusable: no
        well-founded measure can hand out an IH at an arbitrary [B']
        beside an unchanged subject. *)
     size_btyp B' < size_btyp (btyp_all_inh B) ->
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp (exp_abs e) ->
     Θ' ⊢ˢᵃ[ M' ] (exp_abs e) ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' (exp_abs e) κ' Θ' B') ->
  Θ ⊢ˢᵃ[ mode_tc ] (exp_abs e) ⦂ (btyp_all_inh B) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_all_inh B)) ->
  typ_complete_concl mode_tc Θ0 P0 (exp_abs e) κ Θ (btyp_all_inh B).
Proof.
  intros Θ0 P0 e κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hskl HsklT
         Hlc IH Hd Href.
  inversion Hd; subst.
  match goal with
  | H : forall α, α `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  (* ---- 1. the TC input is a TYPE; only the ∀ shape survives the        *)
  (*      refinement (the paper's "the only possible shapes") ----        *)
  inversion Hmod; subst.
  match goal with
  | |- typ_complete_concl _ _ (ptyp_to_pskl ?AA) _ _ _ _ => rename AA into Ap
  end.
  rewrite msubst_pskl_embed_ptyp in Href.
  destruct Ap as [ | n | β | Aa Ab | A0 ]; simpl in Href.
  - (* 1 : a guarded painting never refines to an inh-∀ *)
    exfalso.
    eapply ad_refine_syn_f_guarded_src_all_inh_absurd with (Θ := Θ);
      [ exact HwfΘ
      | eapply ad_refine_syn_f_of_plain; exact Href
      | apply guarded_bskl__unit ].
  - (* bvar : not well-formed *)
    simpl in HwfP0. inversion HwfP0.
  - (* flex/rigid var : its κ-image is a MONOTYPE, whose painting is
       guarded *)
    exfalso.
    pose proof (a_inc_lookup_mono β Hinc) as Hm.
    rewrite (mono_inh_eq_syn Hm) in Href.
    eapply ad_refine_syn_f_guarded_src_all_inh_absurd with (Θ := Θ);
      [ exact HwfΘ
      | eapply ad_refine_syn_f_of_plain; exact Href
      | apply mono_bskl_guarded; apply mono_ptyp_to_bskl_syn; exact Hm ].
  - (* arrow : guarded *)
    exfalso.
    simpl in HwfP0. inversion HwfP0; subst.
    match goal with
    | Hw1 : Θ0 ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl Aa),
      Hw2 : Θ0 ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl Ab) |- _ =>
        rename Hw1 into Hwfa; rename Hw2 into Hwfb
    end.
    assert (Hlca : lc_bskl (pskl_to_bskl_inh (ptyp_to_pskl (msubst_ptyp κ Aa)))).
    { apply lc_pskl_to_bskl_inh.
      rewrite <- msubst_pskl_embed_ptyp.
      eapply a_wf_pskl_lc.
      eapply a_wf_pskl_msubst_inc;
        [ exact Hinc | exact Hwf0 | exact Hwfa
        | intros γ Hγ; clear - Hγ; fsetdec ]. }
    assert (Hlcb : lc_bskl (pskl_to_bskl_inh (ptyp_to_pskl (msubst_ptyp κ Ab)))).
    { apply lc_pskl_to_bskl_inh.
      rewrite <- msubst_pskl_embed_ptyp.
      eapply a_wf_pskl_lc.
      eapply a_wf_pskl_msubst_inc;
        [ exact Hinc | exact Hwf0 | exact Hwfb
        | intros γ Hγ; clear - Hγ; fsetdec ]. }
    eapply ad_refine_syn_f_guarded_src_all_inh_absurd with (Θ := Θ);
      [ exact HwfΘ
      | eapply ad_refine_syn_f_of_plain; exact Href
      | apply guarded_bskl__arrow; [ exact Hlca | exact Hlcb ] ].
  - (* ---- 2. the live shape [∀A0] : invert the ∀-inh refinement ---- *)
    inversion Href; subst.
    match goal with
    | H : forall α, α `notin` ?L0 ->
            ad_refine_syn _ _ (open_bskl_wrt_bskl _ _) _ |- _ =>
        rename H into HrefF; rename L0 into L1
    end.
    simpl in HwfP0.
    inversion HwfP0; subst.
    match goal with
    | H : forall α, α `notin` ?L0 -> a_wf_pskl _ _ _ |- _ =>
        rename H into HwfF; rename L0 into L2
    end.
    (* ---- 3. one fresh rigid binder ---- *)
    destruct (atom_fresh (L `union` L1 `union` L2
                `union` dom Θ0 `union` dom Θ `union` ftvar_in_aenv Θ
                `union` dom κ `union` ftvar_in_ptyp A0
                `union` ftvar_in_btyp B `union` ftvar_in_exp e)) as [α Hα].
    assert (Hwf0x : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf0 ]).
    assert (HwfΘx : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    assert (HwfP0x : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))).
    { rewrite ptyp_to_pskl_open.
      eapply a_wf_pskl_delta_to_ctx;
        [ apply (HwfF α ltac:(clear - Hα; fsetdec)) | clear; fsetdec ]. }
    assert (Hincx : κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ))
      by (apply (@a_inc__tvar Θ0 κ Θ nil α);
          [ exact Hinc | apply a_suffix__nil ]).
    assert (Hrigx : forall β, β `in` ftvar_in_exp (exp_abs e) ->
               binds β abind_tvar ((α ~ abind_tvar) ++ Θ0))
      by (intros β Hβ; apply binds_cons_3; apply Hrig; exact Hβ).
    assert (Hsklx : forall y Ps,
               binds y (abind_var_skl Ps) ((α ~ abind_tvar) ++ Θ0) ->
               ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Ps).
    { intros y Ps Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
        [ discriminate Heq | ].
      eapply a_wf_pskl_mono; [ eapply Hskl; exact Hb' | ].
      intros β c _ Hc. apply binds_cons_3. exact Hc. }
    assert (HsklTx : forall y Ps,
               binds y (abind_var_skl Ps) ((α ~ abind_tvar) ++ Θ) ->
               ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛᵃ Ps).
    { intros y Ps Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
        [ discriminate Heq | ].
      eapply a_wf_pskl_mono; [ eapply HsklT; exact Hb' | ].
      intros β c _ Hc. apply binds_cons_3. exact Hc. }
    (* the peeled refinement, moved from the Δ-slot into the context *)
    assert (Hrefx : ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                      (pskl_to_bskl_inh
                         (msubst_pskl κ
                            (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))))
                      ⊳ (btyp_to_bskl (open_btyp_wrt_btyp B (btyp_var_f α)))).
    { rewrite msubst_pskl_embed_ptyp.
      rewrite (@msubst_ptyp_open Θ0 κ Θ A0 α Hinc
                 ltac:(clear - Hα; fsetdec)).
      rewrite ptyp_to_pskl_open.
      rewrite pskl_to_bskl_inh_open.
      rewrite btyp_to_bskl_open. simpl.
      eapply ad_refine_syn_delta_to_ctx;
        [ apply (HrefF α ltac:(clear - Hα; fsetdec)) | clear; fsetdec ]. }
    (* ---- 4. the IH, once, at the peeled problem ---- *)
    destruct (IH mode_tc ((α ~ abind_tvar) ++ Θ0)
                (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
                κ ((α ~ abind_tvar) ++ Θ)
                (open_btyp_wrt_btyp B (btyp_var_f α))
                ltac:(rewrite size_btyp_open_btyp_wrt_btyp_var;
                      simpl; lia)
                Hwf0x HwfΘx HwfP0x (a_ty_mode_compat__tc _) Hincx Hrigx
                Hsklx HsklTx Hlc
                (Hbody α ltac:(clear - Hα; fsetdec)) Hrefx)
      as [A1 [Θrun [HrunB HoptB]]].
    (* ---- 5. the run's identity increase shapes the output ---- *)
    assert (Hexpx : a_wf_exp ((α ~ abind_tvar) ++ Θ0) (exp_abs e)).
    { apply a_wf_exp_of_tvarish; [ exact Hlc | ].
      intros β Hβ. left. apply Hrigx. exact Hβ. }
    destruct (a_typing_sound HrunB Hwf0x Hsklx HwfP0x
                (a_ty_mode_compat__tc _) Hexpx)
      as [HleB [HwfOut [HwfA1out _]]].
    destruct HleB as [[κb [Hidb Hincb]] _].
    destruct (a_inc_tvar_inv Hincb) as [Ξ [Θ2 [-> [Hsuf Hincb']]]].
    (* the §6.3#2 scoping invariant, at the rigid marker *)
    pose proof (@a_typing_scope_tvar_nil _ _ _ _ _ _ _ HrunB Hwf0x Hsklx
                  HwfP0x Hexpx HwfOut Hsuf) as Hscope.
    (* ---- 6. the freshness / disjointness pack ---- *)
    assert (HuOut : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ2))
      by (apply a_wf_aenv_uniq; exact HwfOut).
    assert (HuΞ : uniq Ξ) by (clear - HuOut; solve_uniq).
    assert (HαΞΘ2 : α `notin` dom Ξ `union` dom Θ2)
      by (clear - HuOut; destruct_uniq; unfold disjoint in *;
          simpl_env in *; fsetdec).
    assert (HΞΘ2 : forall γ, γ `in` dom Ξ -> γ `notin` dom Θ2)
      by (clear - HuOut; intros γ Hγ; destruct_uniq;
          unfold disjoint in *; simpl_env in *; fsetdec).
    assert (Hdom02 : dom Θ0 [<=] dom Θ2)
      by (eapply a_inc_id_dom_sub_scope; [ exact Hincb' | exact Hidb ]).
    (* ---- 7. the run : rebuild the peeled ∀ by CLOSING the result ---- *)
    exists (ptyp_all (close_ptyp_wrt_ptyp α A1)), Θ2.
    split.
    { eapply a_typing__abs_check_step with (α := α) (Ξ := Ξ).
      - exact Hsuf.
      - apply uniq_app_of;
          [ exact HuΞ | apply a_wf_aenv_uniq; exact Hwf0 | ].
        intros γ Hγ Hc.
        exact (HΞΘ2 γ Hγ (Hdom02 _ Hc)).
      - (* (2) : THE §6.3#2 discharge — the result avoids the junk *)
        intros γ Hγ.
        rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp.
        pose proof (Hscope γ Hγ) as Hn. clear - Hn; fsetdec.
      - rewrite dom_app.
        rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp.
        simpl. clear - Hα HαΞΘ2. solve_notin.
      - rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp.
        exact HrunB. }
    (* ---- 8. optimality : lift the caller's id across the binder, run  *)
    (*      the body's optimality, then STRIP the junk and the binder    *)
    (*      off its witnesses ----                                       *)
    intros κ1 Hid1 Hinc1.
    assert (Hinc1x : κ1 ∷ ((α ~ abind_tvar) ++ Θ0)
                       ⊑ (Ξ ++ (α ~ abind_tvar) ++ Θ2))
      by (apply (@a_inc__tvar Θ0 κ1 Θ2 Ξ α); [ exact Hinc1 | exact Hsuf ]).
    destruct (HoptB κ1 Hid1 Hinc1x) as [ζb [Hζb [Heqvb Heqcb]]].
    destruct (@a_inc_strip_suffix_head Ξ ((α ~ abind_tvar) ++ Θ2) ζb
                ((α ~ abind_tvar) ++ Θ) Hsuf Hζb)
      as [ζbp [ζbt [-> [Hdomζp Hζbt0]]]].
    pose proof (@a_inc_strip_tvar_head α Θ2 ζbt Θ Hζbt0) as Hstrip.
    pose proof (@a_inc_equiv_strip_tvar_head α Θ0 κ
                  (msubst_compose (ζbp ++ ζbt) κ1) Θ Heqvb) as Heqv0.
    assert (Hnotinζp : forall β, β `in` dom κ1 -> β `notin` dom ζbp).
    { intros β Hβ.
      rewrite Hdomζp.
      intros Hc.
      pose proof (a_inc_dom_sub Hinc1 Hβ) as Hβ0.
      exact (HΞΘ2 β Hc (Hdom02 _ Hβ0)). }
    rewrite (@msubst_compose_id_prefix_notin ζbp ζbt κ1 Hid1 Hnotinζp) in Heqv0.
    exists ζbt.
    split; [ exact Hstrip | ].
    split; [ exact Heqv0 | ].
    (* the ∀-equivalence, from the body's one α-instance *)
    assert (Hagree : msubst_ptyp (ζbp ++ ζbt) A1 = msubst_ptyp ζbt A1).
    { apply msubst_ptyp_agree.
      intros γ Hγ.
      apply msubst_lookup_app_notin.
      rewrite Hdomζp. intros Hc.
      exact (Hscope γ Hc Hγ). }
    rewrite Hagree in Heqcb.
    rewrite btyp_to_ptyp_open in Heqcb.
    assert (Hαζbt : α `notin` dom ζbt).
    { intros Hc.
      pose proof (a_inc_dom_sub Hstrip Hc) as Hc2.
      clear - Hc2 HαΞΘ2; fsetdec. }
    assert (Heq1 : msubst_ptyp ζbt A1
                   = open_ptyp_wrt_ptyp
                       (msubst_ptyp ζbt (close_ptyp_wrt_ptyp α A1))
                       (ptyp_var_f α)).
    { rewrite <- (@msubst_ptyp_open Θ2 ζbt Θ
                    (close_ptyp_wrt_ptyp α A1) α Hstrip Hαζbt).
      rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp. reflexivity. }
    rewrite Heq1 in Heqcb.
    pose proof (a_tyequiv_strip_tvar_head Heqcb eq_refl) as Heqc1.
    simpl.
    set (X := msubst_ptyp ζbt (close_ptyp_wrt_ptyp α A1)) in *.
    assert (HαX : α `notin` ftvar_in_ptyp X).
    { unfold X.
      eapply msubst_ptyp_ftv_notin_inc;
        [ exact Hstrip
        | rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp; clear; fsetdec
        | clear - Hα; fsetdec ]. }
    assert (HαB : α `notin` ftvar_in_ptyp (btyp_to_ptyp B))
      by (rewrite ftvar_in_ptyp_btyp_to_ptyp; clear - Hα; fsetdec).
    apply a_tyequiv__all with
      (L := ftvar_in_ptyp X `union` ftvar_in_ptyp (btyp_to_ptyp B)
              `union` singleton α `union` dom Θ `union` ftvar_in_aenv Θ).
    intros β Hβ.
    pose proof (a_tyequiv_swap α β _ _ _ Heqc1) as Hsw.
    assert (Hfe1 : α `notin` (dom Θ `union` ftvar_in_aenv Θ))
      by (clear - Hα; fsetdec).
    assert (Hfe2 : β `notin` (dom Θ `union` ftvar_in_aenv Θ))
      by (clear - Hβ; fsetdec).
    rewrite (@swap_aenv_fresh_eq α β Θ Hfe1 Hfe2) in Hsw.
    rewrite !swap_ptyp_open in Hsw.
    cbn [swap_ptyp] in Hsw.
    rewrite swap_atom_l in Hsw.
    rewrite (swap_ptyp_fresh_id α β X) in Hsw;
      [ | exact HαX | clear - Hβ; fsetdec ].
    rewrite (swap_ptyp_fresh_id α β (btyp_to_ptyp B)) in Hsw;
      [ | exact HαB | clear - Hβ; fsetdec ].
    exact Hsw.
Qed.

(* --- the AbsAnnoCheck ∀ row ------------------------------------------- *)

Lemma a_typing_complete_abs_anno_check_step : forall Θ0 P0 A e κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_abs_anno A e) ->
  (forall M' Θ0' P0' κ' Θ' B',
     (* ⭐ THE MEASURE GUARD.  These rows recurse on the SAME subject, so
        the glue can only supply an IH at a SMALLER declarative result —
        the lexicographic (size_exp, size_btyp) measure's second
        component.  Without this premise the row is unusable: no
        well-founded measure can hand out an IH at an arbitrary [B']
        beside an unchanged subject. *)
     size_btyp B' < size_btyp (btyp_all_inh B) ->
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) ->
        binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp (exp_abs_anno A e) ->
     Θ' ⊢ˢᵃ[ M' ] (exp_abs_anno A e) ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' (exp_abs_anno A e) κ' Θ' B') ->
  Θ ⊢ˢᵃ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_all_inh B) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_all_inh B)) ->
  typ_complete_concl mode_tc Θ0 P0 (exp_abs_anno A e) κ Θ (btyp_all_inh B).
Proof.
  intros Θ0 P0 A e κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hskl HsklT
         Hlc IH Hd Href.
  inversion Hd; subst.
  match goal with
  | H : forall α, α `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  inversion Hmod; subst.
  match goal with
  | |- typ_complete_concl _ _ (ptyp_to_pskl ?AA) _ _ _ _ => rename AA into Ap
  end.
  rewrite msubst_pskl_embed_ptyp in Href.
  destruct Ap as [ | n | β | Aa Ab | A0 ]; simpl in Href.
  - exfalso.
    eapply ad_refine_syn_f_guarded_src_all_inh_absurd with (Θ := Θ);
      [ exact HwfΘ
      | eapply ad_refine_syn_f_of_plain; exact Href
      | apply guarded_bskl__unit ].
  - simpl in HwfP0. inversion HwfP0.
  - exfalso.
    pose proof (a_inc_lookup_mono β Hinc) as Hm.
    rewrite (mono_inh_eq_syn Hm) in Href.
    eapply ad_refine_syn_f_guarded_src_all_inh_absurd with (Θ := Θ);
      [ exact HwfΘ
      | eapply ad_refine_syn_f_of_plain; exact Href
      | apply mono_bskl_guarded; apply mono_ptyp_to_bskl_syn; exact Hm ].
  - exfalso.
    simpl in HwfP0. inversion HwfP0; subst.
    match goal with
    | Hw1 : Θ0 ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl Aa),
      Hw2 : Θ0 ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl Ab) |- _ =>
        rename Hw1 into Hwfa; rename Hw2 into Hwfb
    end.
    assert (Hlca : lc_bskl (pskl_to_bskl_inh (ptyp_to_pskl (msubst_ptyp κ Aa)))).
    { apply lc_pskl_to_bskl_inh.
      rewrite <- msubst_pskl_embed_ptyp.
      eapply a_wf_pskl_lc.
      eapply a_wf_pskl_msubst_inc;
        [ exact Hinc | exact Hwf0 | exact Hwfa
        | intros γ Hγ; clear - Hγ; fsetdec ]. }
    assert (Hlcb : lc_bskl (pskl_to_bskl_inh (ptyp_to_pskl (msubst_ptyp κ Ab)))).
    { apply lc_pskl_to_bskl_inh.
      rewrite <- msubst_pskl_embed_ptyp.
      eapply a_wf_pskl_lc.
      eapply a_wf_pskl_msubst_inc;
        [ exact Hinc | exact Hwf0 | exact Hwfb
        | intros γ Hγ; clear - Hγ; fsetdec ]. }
    eapply ad_refine_syn_f_guarded_src_all_inh_absurd with (Θ := Θ);
      [ exact HwfΘ
      | eapply ad_refine_syn_f_of_plain; exact Href
      | apply guarded_bskl__arrow; [ exact Hlca | exact Hlcb ] ].
  - inversion Href; subst.
    match goal with
    | H : forall α, α `notin` ?L0 ->
            ad_refine_syn _ _ (open_bskl_wrt_bskl _ _) _ |- _ =>
        rename H into HrefF; rename L0 into L1
    end.
    simpl in HwfP0.
    inversion HwfP0; subst.
    match goal with
    | H : forall α, α `notin` ?L0 -> a_wf_pskl _ _ _ |- _ =>
        rename H into HwfF; rename L0 into L2
    end.
    destruct (atom_fresh (L `union` L1 `union` L2
                `union` dom Θ0 `union` dom Θ `union` ftvar_in_aenv Θ
                `union` dom κ `union` ftvar_in_ptyp A0
                `union` ftvar_in_btyp B
                `union` ftvar_in_ptyp A `union` ftvar_in_exp e)) as [α Hα].
    assert (Hwf0x : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf0 ]).
    assert (HwfΘx : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    assert (HwfP0x : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))).
    { rewrite ptyp_to_pskl_open.
      eapply a_wf_pskl_delta_to_ctx;
        [ apply (HwfF α ltac:(clear - Hα; fsetdec)) | clear; fsetdec ]. }
    assert (Hincx : κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ))
      by (apply (@a_inc__tvar Θ0 κ Θ nil α);
          [ exact Hinc | apply a_suffix__nil ]).
    assert (Hrigx : forall β, β `in` ftvar_in_exp (exp_abs_anno A e) ->
               binds β abind_tvar ((α ~ abind_tvar) ++ Θ0))
      by (intros β Hβ; apply binds_cons_3; apply Hrig; exact Hβ).
    assert (Hsklx : forall y Ps,
               binds y (abind_var_skl Ps) ((α ~ abind_tvar) ++ Θ0) ->
               ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Ps).
    { intros y Ps Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
        [ discriminate Heq | ].
      eapply a_wf_pskl_mono; [ eapply Hskl; exact Hb' | ].
      intros β c _ Hc. apply binds_cons_3. exact Hc. }
    assert (HsklTx : forall y Ps,
               binds y (abind_var_skl Ps) ((α ~ abind_tvar) ++ Θ) ->
               ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛᵃ Ps).
    { intros y Ps Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
        [ discriminate Heq | ].
      eapply a_wf_pskl_mono; [ eapply HsklT; exact Hb' | ].
      intros β c _ Hc. apply binds_cons_3. exact Hc. }
    assert (Hrefx : ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                      (pskl_to_bskl_inh
                         (msubst_pskl κ
                            (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))))
                      ⊳ (btyp_to_bskl (open_btyp_wrt_btyp B (btyp_var_f α)))).
    { rewrite msubst_pskl_embed_ptyp.
      rewrite (@msubst_ptyp_open Θ0 κ Θ A0 α Hinc
                 ltac:(clear - Hα; fsetdec)).
      rewrite ptyp_to_pskl_open.
      rewrite pskl_to_bskl_inh_open.
      rewrite btyp_to_bskl_open. simpl.
      eapply ad_refine_syn_delta_to_ctx;
        [ apply (HrefF α ltac:(clear - Hα; fsetdec)) | clear; fsetdec ]. }
    destruct (IH mode_tc ((α ~ abind_tvar) ++ Θ0)
                (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
                κ ((α ~ abind_tvar) ++ Θ)
                (open_btyp_wrt_btyp B (btyp_var_f α))
                ltac:(rewrite size_btyp_open_btyp_wrt_btyp_var;
                      simpl; lia)
                Hwf0x HwfΘx HwfP0x (a_ty_mode_compat__tc _) Hincx Hrigx
                Hsklx HsklTx Hlc
                (Hbody α ltac:(clear - Hα; fsetdec)) Hrefx)
      as [A1 [Θrun [HrunB HoptB]]].
    assert (Hexpx : a_wf_exp ((α ~ abind_tvar) ++ Θ0) (exp_abs_anno A e)).
    { apply a_wf_exp_of_tvarish; [ exact Hlc | ].
      intros β Hβ. left. apply Hrigx. exact Hβ. }
    destruct (a_typing_sound HrunB Hwf0x Hsklx HwfP0x
                (a_ty_mode_compat__tc _) Hexpx)
      as [HleB [HwfOut [HwfA1out _]]].
    destruct HleB as [[κb [Hidb Hincb]] _].
    destruct (a_inc_tvar_inv Hincb) as [Ξ [Θ2 [-> [Hsuf Hincb']]]].
    pose proof (@a_typing_scope_tvar_nil _ _ _ _ _ _ _ HrunB Hwf0x Hsklx
                  HwfP0x Hexpx HwfOut Hsuf) as Hscope.
    assert (HuOut : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ2))
      by (apply a_wf_aenv_uniq; exact HwfOut).
    assert (HuΞ : uniq Ξ) by (clear - HuOut; solve_uniq).
    assert (HαΞΘ2 : α `notin` dom Ξ `union` dom Θ2)
      by (clear - HuOut; destruct_uniq; unfold disjoint in *;
          simpl_env in *; fsetdec).
    assert (HΞΘ2 : forall γ, γ `in` dom Ξ -> γ `notin` dom Θ2)
      by (clear - HuOut; intros γ Hγ; destruct_uniq;
          unfold disjoint in *; simpl_env in *; fsetdec).
    assert (Hdom02 : dom Θ0 [<=] dom Θ2)
      by (eapply a_inc_id_dom_sub_scope; [ exact Hincb' | exact Hidb ]).
    exists (ptyp_all (close_ptyp_wrt_ptyp α A1)), Θ2.
    split.
    { eapply a_typing__abs_anno_check_step with (α := α) (Ξ := Ξ).
      - exact Hsuf.
      - apply uniq_app_of;
          [ exact HuΞ | apply a_wf_aenv_uniq; exact Hwf0 | ].
        intros γ Hγ Hc.
        exact (HΞΘ2 γ Hγ (Hdom02 _ Hc)).
      - intros γ Hγ.
        rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp.
        pose proof (Hscope γ Hγ) as Hn. clear - Hn; fsetdec.
      - rewrite dom_app.
        rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp.
        simpl. clear - Hα HαΞΘ2. solve_notin.
      - rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp.
        exact HrunB. }
    intros κ1 Hid1 Hinc1.
    assert (Hinc1x : κ1 ∷ ((α ~ abind_tvar) ++ Θ0)
                       ⊑ (Ξ ++ (α ~ abind_tvar) ++ Θ2))
      by (apply (@a_inc__tvar Θ0 κ1 Θ2 Ξ α); [ exact Hinc1 | exact Hsuf ]).
    destruct (HoptB κ1 Hid1 Hinc1x) as [ζb [Hζb [Heqvb Heqcb]]].
    destruct (@a_inc_strip_suffix_head Ξ ((α ~ abind_tvar) ++ Θ2) ζb
                ((α ~ abind_tvar) ++ Θ) Hsuf Hζb)
      as [ζbp [ζbt [-> [Hdomζp Hζbt0]]]].
    pose proof (@a_inc_strip_tvar_head α Θ2 ζbt Θ Hζbt0) as Hstrip.
    pose proof (@a_inc_equiv_strip_tvar_head α Θ0 κ
                  (msubst_compose (ζbp ++ ζbt) κ1) Θ Heqvb) as Heqv0.
    assert (Hnotinζp : forall β, β `in` dom κ1 -> β `notin` dom ζbp).
    { intros β Hβ.
      rewrite Hdomζp.
      intros Hc.
      pose proof (a_inc_dom_sub Hinc1 Hβ) as Hβ0.
      exact (HΞΘ2 β Hc (Hdom02 _ Hβ0)). }
    rewrite (@msubst_compose_id_prefix_notin ζbp ζbt κ1 Hid1 Hnotinζp) in Heqv0.
    exists ζbt.
    split; [ exact Hstrip | ].
    split; [ exact Heqv0 | ].
    assert (Hagree : msubst_ptyp (ζbp ++ ζbt) A1 = msubst_ptyp ζbt A1).
    { apply msubst_ptyp_agree.
      intros γ Hγ.
      apply msubst_lookup_app_notin.
      rewrite Hdomζp. intros Hc.
      exact (Hscope γ Hc Hγ). }
    rewrite Hagree in Heqcb.
    rewrite btyp_to_ptyp_open in Heqcb.
    assert (Hαζbt : α `notin` dom ζbt).
    { intros Hc.
      pose proof (a_inc_dom_sub Hstrip Hc) as Hc2.
      clear - Hc2 HαΞΘ2; fsetdec. }
    assert (Heq1 : msubst_ptyp ζbt A1
                   = open_ptyp_wrt_ptyp
                       (msubst_ptyp ζbt (close_ptyp_wrt_ptyp α A1))
                       (ptyp_var_f α)).
    { rewrite <- (@msubst_ptyp_open Θ2 ζbt Θ
                    (close_ptyp_wrt_ptyp α A1) α Hstrip Hαζbt).
      rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp. reflexivity. }
    rewrite Heq1 in Heqcb.
    pose proof (a_tyequiv_strip_tvar_head Heqcb eq_refl) as Heqc1.
    simpl.
    set (X := msubst_ptyp ζbt (close_ptyp_wrt_ptyp α A1)) in *.
    assert (HαX : α `notin` ftvar_in_ptyp X).
    { unfold X.
      eapply msubst_ptyp_ftv_notin_inc;
        [ exact Hstrip
        | rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp; clear; fsetdec
        | clear - Hα; fsetdec ]. }
    assert (HαB : α `notin` ftvar_in_ptyp (btyp_to_ptyp B))
      by (rewrite ftvar_in_ptyp_btyp_to_ptyp; clear - Hα; fsetdec).
    apply a_tyequiv__all with
      (L := ftvar_in_ptyp X `union` ftvar_in_ptyp (btyp_to_ptyp B)
              `union` singleton α `union` dom Θ `union` ftvar_in_aenv Θ).
    intros β Hβ.
    pose proof (a_tyequiv_swap α β _ _ _ Heqc1) as Hsw.
    assert (Hfe1 : α `notin` (dom Θ `union` ftvar_in_aenv Θ))
      by (clear - Hα; fsetdec).
    assert (Hfe2 : β `notin` (dom Θ `union` ftvar_in_aenv Θ))
      by (clear - Hβ; fsetdec).
    rewrite (@swap_aenv_fresh_eq α β Θ Hfe1 Hfe2) in Hsw.
    rewrite !swap_ptyp_open in Hsw.
    cbn [swap_ptyp] in Hsw.
    rewrite swap_atom_l in Hsw.
    rewrite (swap_ptyp_fresh_id α β X) in Hsw;
      [ | exact HαX | clear - Hβ; fsetdec ].
    rewrite (swap_ptyp_fresh_id α β (btyp_to_ptyp B)) in Hsw;
      [ | exact HαB | clear - Hβ; fsetdec ].
    exact Hsw.
Qed.

