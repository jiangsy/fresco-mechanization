(** COMPLETENESS OF TYPE INFERENCE (section D, thm:complete-type-inference)
    — the landing file for theorem 4 and its kit.  ✅ CLOSED:
    [a_typing_complete] is Qed and axiom-free, [Check]ed in README.v.  Its
    CLOSED-PROGRAM corollaries, which are what README.v shows a reader, live
    next door in [prop_closed.v].

    ⚙ NO TERM-BINDER RENAMING KIT IS NEEDED HERE, and that is the point of the
    EXISTS-FRESH conversion (2026-08-08, `7061d31`).  While [a_typing]'s six
    binder rows were cofinite they shared their outputs across the family, so
    completeness would have had to generate the family from the IH's one fresh
    instance — theorem 4's "K6", the analogue of [a_pat_rename_tm]
    (prop_completeness_pat.v §K6).  Exists-fresh rows are INTRODUCED at a
    chosen witness instead, so every binder row below just applies its rule
    [with (x := x)] and the obligation disappears.  ⚠️ [a_pat] is still
    cofinite, which is exactly why prop_completeness_pat.v still carries K6.

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
    [pat_complete_concl]; the base rows feed [a_sub_complete] at TY,
    with the run's output packaged as a painted [ptyp] by
    [a_sub_ty_ghost_free_output] (typing/prop_rigidity.v) and the optimality
    conclusion converted by [ad_precise_painting_tyequiv]'s idiom (a
    precision between two type paintings IS a type equivalence, via
    [ad_refine_syn_inh_tyequiv]).

    THE NINE ROWS, all closed: Unit/Var (direct), Anno (consumes
    prop_rigidity's [a_typing_tc_rigid_output]), Freeze, Abs / AbsAnno, the four
    check rows [abs{,_anno}_check_{step,base}] — whose [_base] halves needed
    the MISSING prerequisite [a_split_complete_tc], completeness of splitting
    at check mode, i.e. the paper's AbsCheck subcase 2 — and App (invokes
    THEOREM 3).  Glue: lexicographic [(size_exp, size_btyp)] in
    [a_typing_complete_gen].  The suffix-discarding rows' scoping
    premise is discharged from algo/typing/prop_scope.v. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.def_meta.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.algo_decl.def_subtyping.
Require Import src.frost.algo_decl.prop_sub_mirrors.
Require Import src.frost.algo_decl.def_typing.
Require Import src.frost.algo_decl.prop_ctx_mono.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.sub.prop_sub_msubst_equiv.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.sub.prop_completeness_sub_gen.
Require Import src.frost.algo.sub.prop_completeness_sub.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.consis.prop_consis_rename.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.prop_wf_preservation.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Require Import src.frost.algo.sub.prop_soundness_subtag.
Require Import src.frost.algo.pat.prop_soundness_pat.
Require Import src.frost.algo.prop_suffix_erase.
Require Import src.frost.algo.typing.prop_soundness_typing.
Require Import src.frost.algo.prop_precise_sub.
Require Import src.frost.algo.pat.prop_completeness_pat.
Require Import src.frost.algo.typing.prop_rigidity.
Require Import src.frost.algo.typing.prop_shape.
Require Import src.frost.algo.typing.prop_scope.

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
         {{ Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a).

(* ===================================================================== *)
(*  The two tails every base row shares                                   *)
(* ===================================================================== *)

(** The counterpart's wf, read off the fused rule's join: scope from
    [ad_pat_sub_target_wf], ghost-freeness structural (it is a [btyp]'s
    erasure). *)
Lemma typ_counterpart_wf : forall NM M Ψ Θ R (B : btyp),
  {{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ (btyp_to_bskl B) }}ad ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B)) }}a.
Proof.
  intros NM M Ψ Θ R B Hj.
  rewrite bskl_to_pskl_btyp_to_bskl.
  apply a_wf_ptyp_to_wf_pskl.
  eapply a_wf_ptyp_of_scope_pskl;
    [ | rewrite <- bskl_to_pskl_btyp_to_bskl; reflexivity ].
  eapply ad_pat_sub_target_wf. exact Hj.
Qed.

(** The optimality tail every base row shares: a PRECISION between two
    type paintings IS the type equivalence the conclusion carries. *)
Lemma typ_opt_tail : forall Θ ζ A1 (B : btyp),
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ empty ⊢ₚᵣ
    (bskl_to_pskl (msubst_bskl ζ (pskl_to_bskl_syn (ptyp_to_pskl A1))))
    ⊑ (bskl_to_pskl (btyp_to_bskl B)) }}ad ->
  {{ Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros Θ ζ A1 B HwfΘ Hprec.
  rewrite msubst_bskl_syn_erase, msubst_pskl_embed_ptyp, bskl_to_pskl_btyp_to_bskl
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
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⊢ˢᵈ[ M ] exp_unit ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 exp_unit κ Θ B.
Proof.
  intros M Θ0 P0 κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub _ _ _ _ _ _ |- _ =>
      destruct (ad_pat_sub_to_fuel H) as [njoin Hjoin]
  end.
  assert (HwfQ : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B)) }}a)
    by (eapply typ_counterpart_wf;
        exact (ad_pat_sub_of_fuel Hjoin)).
  destruct (@a_sub_complete njoin a_sub_mode_ty M Θ0 P0
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
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⊢ˢᵈ[ M ] (exp_var_f x) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 (exp_var_f x) κ Θ B.
Proof.
  intros M Θ0 P0 x κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub _ _ _ _ _ _ |- _ =>
      destruct (ad_pat_sub_to_fuel H) as [njoin Hjoin]
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
  destruct (@a_sub_complete njoin a_sub_mode_ty M Θ0 P0
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
                    exact (ad_pat_sub_of_fuel Hjoin))
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
(*  then the fused subtyping ([a_sub_complete]).  ⭐ The body run      *)
(*  returns the annotation ITSELF ([a_typing_tc_rigid_output],            *)
(*  typing/prop_rigidity.v) — the fact [AT-Anno]'s premise demands and the        *)
(*  paper's Anno case asserts by metavariable pun.  The optimality glues  *)
(*  the two factorings by [a_inc_equiv_glue]; the dom side condition is   *)
(*  [a_inc_id_flex_preserve] at the body run's own identity increase.     *)
(* ===================================================================== *)

Lemma a_typing_complete_anno : forall M Θ0 P0 e A κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_anno e A) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_anno e A) ->
  (forall M' Θ0' P0' κ' Θ' B',
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0') ->
     lc_exp e ->
     {{ Θ' ⊢ˢᵈ[ M' ] e ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' e κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ M ] (exp_anno e A) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 (exp_anno e A) κ Θ B.
Proof.
  intros M Θ0 P0 e A κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hlc
         IH Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub _ _ _ _ _ _ |- _ =>
      destruct (ad_pat_sub_to_fuel H) as [njoin Hjoin]
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
  assert (HwfpA0 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfA0).
  (* ---- 1. the BODY stage, by the IH at (TC, ⌈A⌉) ---- *)
  destruct (IH mode_tc Θ0 (ptyp_to_pskl A) κ Θ (ptyp_to_btyp_inh A)
              Hwf0 HwfΘ HwfpA0
              (a_ty_mode_compat__tc A)
              Hinc Hrige Hlce Hde
              ltac:(rewrite msubst_pskl_embed_ptyp, HmsA,
                      <- (pskl_to_bskl_inh_ptyp A);
                    apply ad_refine_syn_refl_inh;
                    apply a_wf_ptyp_to_wf_pskl; exact HwfAΘ))
    as [A1' [Θmid [HrunB HoptB]]].
  (* ⭐ the run returned the ANNOTATION ITSELF (typing/prop_rigidity.v) *)
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
  assert (Hexpe : {{ Θ0 ⊢ᵉ e }}a)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlce | intros α Hα; left; apply Hrige; exact Hα ]).
  destruct (a_typing_sound HrunB Hwf0 HwfpA0
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
  assert (HwfP0mid : {{ Θmid ⨟ empty ⊢ₚₛ P0 }}a).
  { pose proof (a_wf_pskl_msubst_inc Hincb Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)) as Hw.
    rewrite (msubst_pskl_id P0 Hidb) in Hw. exact Hw. }
  (* ---- 2. transport the refinement to ζb ---- *)
  assert (Hσ : msubst_compose ζb κb ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hincb | exact Hwf0 | exact Hwfmid | exact Hζb ]).
  assert (HwfQ : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B)) }}a)
    by (eapply typ_counterpart_wf;
        exact (ad_pat_sub_of_fuel Hjoin)).
  assert (Hpp : {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl (msubst_compose ζb κb) P0)
                  ⊑ (msubst_pskl κ P0) }}ad).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
      | exact Heqvb | clear; fsetdec ]. }
  assert (HrefT : {{ Θ ⨟ empty ⊢ᵣ
                    (pskl_to_bskl_inh (msubst_pskl (msubst_compose ζb κb) P0))
                    ⊳ (btyp_to_bskl B) }}ad).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact Href | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQ ]. }
  assert (Hms : msubst_pskl (msubst_compose ζb κb) P0 = msubst_pskl ζb P0).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwfmid | exact Hidb | exact Hincb | exact Hζb
      | exact (a_scope_pskl_of_wf HwfP0) ]. }
  rewrite Hms in HrefT.
  (* ---- 3. the SUB stage ---- *)
  destruct (@a_sub_complete njoin a_sub_mode_ty M Θmid P0
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
                    apply ptyp_to_pskl_lc; exact HlcA)
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

(** Well-formedness transports along [≡ᵗ], both ways (the flex-def row
    swaps a variable for its definition, both wf in a wf context).  Stated
    over any binds-including context so the ∀ row's extension composes. *)
Lemma a_tyequiv_wf_iff : forall Θ A B,
  {{ Θ ⊢ A ≡ᵗ B }}a ->
  forall Θ',
  (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
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
        (assert (Hwfx : {{ ⊢ ((α ~ abind_tvar) ++ Θ') }}a)
          by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]));
        (assert (Hinclx : forall x (b : abind),
                   binds x b Θ -> binds x b ((α ~ abind_tvar) ++ Θ'))
          by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb));
        first
          [ eapply (proj1 (H0 α ltac:(clear - Hα; solve_notin_auto) _ Hinclx Hwfx));
            apply Hfam; clear - Hα; fsetdec
          | eapply (proj2 (H0 α ltac:(clear - Hα; solve_notin_auto) _ Hinclx Hwfx));
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
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  {{ ⊢ Θ }}a ->
  a_wf_ptyp Θ (btyp_to_ptyp B).
Proof.
  intros M Θ e B H; induction H; intros Hwf;
    try match goal with
        | Hj : ad_pat_sub _ _ _ _ _ _ |- _ =>
            eapply a_wf_ptyp_of_scope_pskl;
              [ | rewrite <- bskl_to_pskl_btyp_to_bskl; reflexivity ];
            eapply ad_pat_sub_target_wf; exact Hj
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
    rewrite <- btyp_to_ptyp_open_var.
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
    rewrite <- btyp_to_ptyp_open_var.
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
(*  the consistency stage ([a_consis_complete]) with the subject      *)
(*  transported along [≡ˢ] to the declarative types.  The conclusion's    *)
(*  [≡ᵗ] comes from the consis run's own subject-≡-input                  *)
(*  ([a_consis_chk_tyequiv]) pushed through the witnesses.                *)
(* ===================================================================== *)

Lemma a_typing_complete_freeze : forall Θ0 P0 e κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_freeze e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_freeze e) ->
  (forall M' Θ0' P0' κ' Θ' B',
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0') ->
     lc_exp e ->
     {{ Θ' ⊢ˢᵈ[ M' ] e ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' e κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_freeze e) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 (exp_freeze e) κ Θ B.
Proof.
  intros Θ0 P0 e κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hlc
         IH Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_sd_typing mode_ti Θ e (ptyp_to_btyp_syn ?BB) |- _ =>
      rename H into Hde; rename BB into B0
  end.
  match goal with
  | H : {{ Θ ⊢ B0 ≡ᵗ ?AA }}a |- _ => rename H into Heq0; rename AA into A
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
              Hrig Hlce Hde
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    rewrite <- pskl_to_bskl_syn_ptyp;
                    apply ad_refine_syn__hole;
                    apply a_wf_ptyp_to_wf_pskl; exact HwfB0))
    as [B' [Θmid [HrunB HoptB]]].
  assert (Hexpe : {{ Θ0 ⊢ᵉ e }}a)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlce | intros α Hα; left; apply Hrig; exact Hα ]).
  destruct (a_typing_sound HrunB Hwf0 (a_wf_pskl__hole _ _)
              a_ty_mode_compat__ti Hexpe)
    as [HleB [Hwfmid [HwfB'mid _]]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (HoptB κb Hidb Hincb) as [ζb [Hζb [Heqvb HeqB']]].
  rewrite btyp_to_ptyp_ptyp_to_btyp_syn in HeqB'.
  assert (HeqAll : {{ Θ ⊢ (msubst_ptyp ζb B') ≡ᵗ A }}a)
    by (eapply a_tyequiv__trans; [ exact HeqB' | exact Heq0 ]).
  assert (HwfApmid : {{ Θmid ⨟ empty ⊢ₚₛ (ptyp_to_pskl Ap) }}a).
  { pose proof (a_wf_pskl_msubst_inc Hincb Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)) as Hw.
    rewrite (msubst_pskl_id _ Hidb) in Hw. exact Hw. }
  (* ---- 2. the transports for the consistency stage ---- *)
  assert (Hσ : msubst_compose ζb κb ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hincb | exact Hwf0 | exact Hwfmid | exact Hζb ]).
  set (Qb := btyp_to_bskl (ptyp_to_btyp_inh A)) in *.
  assert (HwfQb : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Qb) }}a).
  { unfold Qb. rewrite bskl_to_pskl_btyp_to_bskl, btyp_to_ptyp_ptyp_to_btyp_inh.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA. }
  assert (Hpp : {{ Θ ⨟ empty ⊢ₚᵣ
                  (msubst_pskl (msubst_compose ζb κb) (ptyp_to_pskl Ap))
                  ⊑ (msubst_pskl κ (ptyp_to_pskl Ap)) }}ad).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
      | exact Heqvb | clear; fsetdec ]. }
  assert (HrefT : {{ Θ ⨟ empty ⊢ᵣ
                    (pskl_to_bskl_inh
                       (msubst_pskl (msubst_compose ζb κb) (ptyp_to_pskl Ap)))
                    ⊳ Qb }}ad).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact Href | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQb ]. }
  assert (Hms : msubst_pskl (msubst_compose ζb κb) (ptyp_to_pskl Ap)
                = msubst_pskl ζb (ptyp_to_pskl Ap)).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwfmid | exact Hidb | exact Hincb | exact Hζb
      | exact (a_scope_pskl_of_wf HwfP0) ]. }
  rewrite Hms in HrefT.
  assert (Heqs : {{ Θ ⊢ (ptyp_to_pskl (msubst_ptyp ζb B')) ≡ˢ (ptyp_to_pskl A) }}a)
    by (apply a_tyequiv_pskl; exact HeqAll).
  assert (Hjoin : {{ empty ⨟ Θ ⊢ˢ
                    (pskl_to_uskl (msubst_pskl ζb (ptyp_to_pskl B'))) ∼ Qb }}ad).
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
    unfold Qb. rewrite bskl_to_pskl_btyp_to_bskl, btyp_to_ptyp_ptyp_to_btyp_inh.
    apply ad_refine_pskl_f_of_plain.
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA. }
  (* ---- 3. the consistency stage ---- *)
  destruct (a_consis_complete Hwfmid HwfApmid
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
    exact (a_scope_pskl_of_wf HwfApmid). }
  assert (HeqIO : {{ Θ2 ⊢ B' ≡ᵗ Ap }}a)
    by (eapply a_consis_chk_tyequiv;
        [ exists Qc; exact HcRun | exact Hwfmid | exact HwfApP
        | exact HwfB'mid ]).
  assert (HeqIOΘ : {{ Θ ⊢ (msubst_ptyp ζs B') ≡ᵗ (msubst_ptyp ζs Ap) }}a)
    by (eapply a_tyequiv_msubst; [ exact HeqIO | exact Hwf2 | exact Hζs ]).
  assert (HmsB' : msubst_ptyp (msubst_compose ζs κs) B' = msubst_ptyp ζs B')
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwfmid | exact Hwf2 | exact Hids | exact Hincs | exact Hζs
        | exact HwfB'mid ]).
  assert (HeqW : {{ Θ ⊢ (msubst_ptyp ζb B') ≡ᵗ (msubst_ptyp ζs B') }}a).
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
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_app e1 e2) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_app e1 e2) ->
  (* the e1 IH *)
  (forall M' Θ0' P0' κ' Θ' B',
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ0') ->
     lc_exp e1 ->
     {{ Θ' ⊢ˢᵈ[ M' ] e1 ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' e1 κ' Θ' B') ->
  (* the e2 IH *)
  (forall M' Θ0' P0' κ' Θ' B',
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ0') ->
     lc_exp e2 ->
     {{ Θ' ⊢ˢᵈ[ M' ] e2 ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' e2 κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ M ] (exp_app e1 e2) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 (exp_app e1 e2) κ Θ B.
Proof.
  intros M Θ0 P0 e1 e2 κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
         Hlc IH1 IH2 Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat mode_tc Θ e2 (pskl_to_bskl_syn ?PP) |- _ =>
      rename H into Hd2s; rename PP into P
  end.
  match goal with
  | H : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl ?BB) }}ad |- _ =>
      rename H into HrefP; rename BB into B1
  end.
  match goal with
  | H : ad_sd_typing (mode_fn M) Θ e1 (btyp_arrow B1 ?BB) |- _ =>
      rename H into Hd1; rename BB into B2
  end.
  match goal with
  | H : {{ Θ ⊢ (btyp_to_ptyp B1) ≡ᵗ ?AA }}a |- _ =>
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
  assert (Hexp2 : {{ Θ0 ⊢ᵉ e2 }}a)
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
  assert (HwfP : {{ Θ ⨟ empty ⊢ₚₛ P }}a).
  { pose proof (ad_pat_target_wf Hd2s HwfΘ) as Hw.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw. exact Hw. }
  (* ---- 1. the SKELETON stage : THEOREM 3 at (TC, ◇) ---- *)
  destruct (@a_pat_complete e2 mode_tc Θ0 pskl_hole κ Θ (pskl_to_bskl_syn P)
              Hwf0 HwfΘ (a_wf_pskl__hole _ _) a_sk_mode_compat__tc Hinc
              Hrig2 Hlc2 Hd2s
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    apply ad_refine_syn__hole; exact HwfP))
    as [P' [Θ1' [Hrun1 Hopt1]]].
  destruct (a_pat_sound Hrun1 Hwf0 (a_wf_pskl__hole _ _)
              a_sk_mode_compat__tc Hexp2)
    as [Hle1 [Hwf1 _]].
  destruct Hle1 as [[κ1b [Hid1b Hinc1b]] _].
  destruct (Hopt1 κ1b Hid1b Hinc1b) as [ζ1 [Hζ1 [Heqv1 Hprec1]]].
  rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec1.
  (* ---- 2. the FUNCTION stage : IH1 at (fn M, P' → P0) ---- *)
  assert (HwfP' : {{ Θ1' ⨟ empty ⊢ₚₛ P' }}a)
    by (eapply a_pat_output_wf;
        [ exact Hrun1 | exact Hwf0
        | apply a_wf_pskl__hole | apply a_sk_mode_compat__tc | exact Hexp2 ]).
  assert (HwfP0m : {{ Θ1' ⨟ empty ⊢ₚₛ P0 }}a).
  { pose proof (a_wf_pskl_msubst_inc Hinc1b Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)) as Hw.
    rewrite (msubst_pskl_id P0 Hid1b) in Hw. exact Hw. }
  assert (Hrig1m : forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ1')
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hinc1b | apply Hrig1; exact Hα ]).
  (* the codomain refinement, transported to ζ1 (the Anno idiom) *)
  assert (Hσ1 : msubst_compose ζ1 κ1b ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hinc1b | exact Hwf0 | exact Hwf1 | exact Hζ1 ]).
  assert (HwfQ2 : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B2)) }}a).
  { rewrite bskl_to_pskl_btyp_to_bskl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfB2. }
  assert (Hpp1 : {{ Θ ⨟ empty ⊢ₚᵣ
                   (msubst_pskl (msubst_compose ζ1 κ1b) P0)
                   ⊑ (msubst_pskl κ P0) }}ad).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ1
      | exact Heqv1 | clear; fsetdec ]. }
  assert (Hcod : {{ Θ ⨟ empty ⊢ᵣ
                   (pskl_to_bskl_inh (msubst_pskl (msubst_compose ζ1 κ1b) P0))
                   ⊳ (btyp_to_bskl B2) }}ad).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp1 | exact Href | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQ2 ]. }
  assert (Hms1 : msubst_pskl (msubst_compose ζ1 κ1b) P0 = msubst_pskl ζ1 P0).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwf1 | exact Hid1b | exact Hinc1b | exact Hζ1
      | exact (a_scope_pskl_of_wf HwfP0) ]. }
  rewrite Hms1 in Hcod.
  (* the domain refinement : precision preserves the rule's own (paper's
     lemma:precision-preserves-refinement, verbatim) *)
  assert (HwfB1e : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B1)) }}a).
  { rewrite bskl_to_pskl_btyp_to_bskl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfB1. }
  assert (Hdom : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl ζ1 P'))
                   ⊳ (btyp_to_bskl B1) }}ad).
  { eapply ad_precise_preserves_refine;
      [ exact Hprec1 | exact HrefP | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfB1e ]. }
  destruct (IH1 (mode_fn M) Θ1' (pskl_arrow P' P0) ζ1 Θ (btyp_arrow B1 B2)
              Hwf1 HwfΘ
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP' | exact HwfP0m ])
              ltac:(apply a_ty_mode_compat__fn; exact Hmod)
              Hζ1 Hrig1m Hlc1 Hd1
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
  assert (Hexp1 : {{ Θ1' ⊢ᵉ e1 }}a)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc1 | intros α Hα; left; apply Hrig1m; exact Hα ]).
  destruct (a_typing_sound Hrun2 Hwf1
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
  assert (Hexp2m : {{ Θ2' ⊢ᵉ e2 }}a)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc2 | intros α Hα; left; apply Hrig2m; exact Hα ]).
  assert (HeqChain : {{ Θ ⊢ (msubst_ptyp ζ2 Af) ≡ᵗ A2 }}a)
    by (eapply a_tyequiv__trans; [ exact HeqDom | exact HeqA2 ]).
  assert (Heqs : {{ Θ ⊢ (ptyp_to_pskl (msubst_ptyp ζ2 Af)) ≡ˢ (ptyp_to_pskl A2) }}a)
    by (apply a_tyequiv_pskl; exact HeqChain).
  assert (Href3 : {{ Θ ⨟ empty ⊢ᵣ
                    (pskl_to_bskl_inh (msubst_pskl ζ2 (ptyp_to_pskl Af)))
                    ⊳ (btyp_to_bskl (ptyp_to_btyp_inh A2)) }}ad).
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
              Hζ2 Hrig2m Hlc2 Hd2 Href3)
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
  destruct (a_typing_sound Hrun3 Hwf2
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
  assert (HeqW : {{ Θ ⊢ (msubst_ptyp ζ2 Bf) ≡ᵗ (msubst_ptyp ζ3 Bf) }}a).
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
Lemma a_guess_mono_ghost_free_id : forall Θg P Ξg A',
  a_guess_mono Θg P Ξg A' ->
  pskl_ghost_free P ->
  Ξg = nil /\ ptyp_to_pskl A' = P.
Proof.
  intros Θg P Ξg A' H; induction H; intros Hg; simpl in Hg;
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

(** Ghost-freeness is decidable. *)
Lemma pskl_ghost_free_dec : forall P,
  sumbool (pskl_ghost_free P) (~ pskl_ghost_free P).
Proof.
  induction P; simpl; auto.
  destruct IHP1; destruct IHP2; [ left; split; assumption | | | ];
    right; intros [H1 H2]; contradiction.
Qed.

(** Looking up past a block the atom avoids. *)
(** ⭐ The GHOST-FREE shortcut: a ghost-free subtree guesses to itself, and
    a refinement between two ghost-free paintings IS the equivalence. *)
Lemma a_guess_mono_complete_ghost_free : forall Θ Δ κ P (Bt : btyp) Θg Ξg A',
  pskl_ghost_free P ->
  ad_refine_syn Θ Δ (pskl_to_bskl_inh (msubst_pskl κ P)) (btyp_to_bskl Bt) ->
  {{ ⊢ Θ }}a ->
  a_guess_mono Θg P Ξg A' ->
  Ξg = nil /\ {{ Θ ⊢ (msubst_ptyp κ A') ≡ᵗ (btyp_to_ptyp Bt) }}a.
Proof.
  intros Θ Δ κ P Bt Θg Ξg A' Hgf Href HwfΘ Hg.
  destruct (a_guess_mono_ghost_free_id Hg Hgf) as [-> HPA].
  split; [ reflexivity | ].
  rewrite <- HPA in Href.
  rewrite msubst_pskl_embed_ptyp in Href.
  exact (ad_refine_syn_inh_tyequiv Href HwfΘ
           (msubst_ptyp κ A') Bt eq_refl eq_refl).
Qed.

(** Stacking a block of guessed flexibles onto an increase. *)
Lemma a_inc_extend_flex_block : forall (Ξg : aenv) (ζg κ : metasubst) Θ1 Θ,
  κ ∷ Θ1 ⊑ Θ ->
  List.map fst ζg = List.map fst Ξg ->
  a_decls Ξg ->
  (forall α τ, In (α, τ) ζg -> mono_ptyp τ /\ a_wf_ptyp Θ τ) ->
  (ζg ++ κ) ∷ (Ξg ++ Θ1) ⊑ Θ.
Proof.
  intros Ξg; induction Ξg as [ | [α b] Ξg' IH ];
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
Lemma guess_complete_var_image : forall Θ Δ κ β (Bt : btyp) Θg Ξg A',
  ad_refine_syn Θ Δ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β)))
    (btyp_to_bskl Bt) ->
  {{ ⊢ Θ }}a ->
  a_guess_mono Θg (pskl_var_f β) Ξg A' ->
  Ξg = nil /\ {{ Θ ⊢ (msubst_ptyp κ A') ≡ᵗ (btyp_to_ptyp Bt) }}a.
Proof.
  intros Θ Δ κ β Bt Θg Ξg A' Href HwfΘ Hg.
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

Lemma map_fst_eq_dom : forall (ζ : metasubst) (Ξg : aenv),
  List.map fst ζ = List.map fst Ξg ->
  dom ζ [=] dom Ξg.
Proof.
  intros ζ; induction ζ as [ | [α τ] ζ' IH ]; intros Ξg Hmap;
    destruct Ξg as [ | [β b] Ξg' ]; simpl in Hmap; try discriminate.
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
  forall P0 (Bt : btyp) Θg Ξg A' κ Θ1,
  {{ ⊢ Θ }}a ->
  Qs = pskl_to_bskl_inh (msubst_pskl κ P0) ->
  Qt = btyp_to_bskl Bt ->
  is_ityp Bt ->
  a_guess_mono Θg P0 Ξg A' ->
  κ ∷ Θ1 ⊑ Θ ->
  uniq Ξg ->
  (forall α, α `in` dom Ξg ->
     α `notin` ftvar_in_pskl P0 `union` dom κ
       `union` dom Θ `union` ftvar_in_aenv Θ) ->
  exists ζg,
    List.map fst ζg = List.map fst Ξg /\
    (forall α τ, In (α, τ) ζg -> mono_ptyp τ /\ a_wf_ptyp Θ τ) /\
    {{ Θ ⊢ (msubst_ptyp (ζg ++ κ) A') ≡ᵗ (btyp_to_ptyp Bt) }}a.
Proof.
  intros Θ Δ Qs Qt Href.
  (* the two head-generic moves, packaged: *)
  (* [var_image_case] — the input head is a flexible/rigid VARIABLE; its
     κ-image is what the row sees, and the guess is the identity there *)
  (* [mono_clash] — a variable input's image is a MONOTYPE, whose painting
     never matches a ghost/quantifier subject *)
  induction Href;
    intros P0 Bt Θg Ξg A' κ Θ1 HwfΘ HeqS HeqT Hit Hg Hinc Huq Hav.
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
      destruct (@guess_complete_var_image Θ Δ κ βv Bt Θg Ξg A' Href' HwfΘ Hg) as [-> Heqc].
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
    destruct (@guess_complete_var_image Θ Δ κ βv Bt Θg Ξg A' Href' HwfΘ Hg) as [-> Heqc].
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
      destruct (@guess_complete_var_image Θ Δ κ βv Bt Θg Ξg A' Href' HwfΘ Hg) as [-> Heqc].
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
                                                clear - Hα; solve_notin_auto)) as Hn;
                        clear - Hn; fsetdec))
        as [ζg1 [Hmap1 [Hent1 Heqc1]]].
      destruct (IHHref2 Pb B2 Θg Ξ2 A2 κ Θ1 HwfΘ eq_refl eq_refl
                  ltac:(assumption) Hg2 Hinc Hu2
                  ltac:(intros α Hα; simpl in Hav;
                        pose proof (Hav α ltac:(rewrite dom_app;
                                                clear - Hα; solve_notin_auto)) as Hn;
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
        pose proof (Hav α ltac:(rewrite dom_app; clear - Hc; solve_notin_auto)) as Hn.
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
        pose proof (Hav α ltac:(rewrite dom_app; clear - Hc; solve_notin_auto)) as Hn.
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
      destruct (atom_fresh (L `union` L2 `union` dom Ξg
                  `union` ftvar_in_pskl Pw `union` ftvar_in_aenv Θg
                  `union` dom κ `union` dom Θ `union` ftvar_in_aenv Θ
                  `union` ftvar_in_ptyp (close_ptyp_wrt_ptyp β A0)
                  `union` ftvar_in_btyp B0 `union` singleton β)) as [α0 Hα0].
      assert (Hgα0 : a_guess_mono ((α0 ~ abind_tvar) ++ Θg)
                       (open_pskl_wrt_pskl Pw (pskl_var_f α0)) Ξg
                       (open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp β A0)
                          (ptyp_var_f α0))).
      { apply a_guess_mono_open_at;
          [ apply a_guess_mono__forall with (β := β);
              [ exact Hfrβ | exact Hg0 ]
          | clear - Hα0; fsetdec ]. }
      destruct (H0 α0 ltac:(clear - Hα0; solve_notin_auto)
                  (open_pskl_wrt_pskl Pw (pskl_var_f α0))
                  (open_btyp_wrt_btyp B0 (btyp_var_f α0))
                  ((α0 ~ abind_tvar) ++ Θg) Ξg
                  (open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp β A0)
                     (ptyp_var_f α0))
                  κ Θ1 HwfΘ
                  ltac:(assert (Hfr0 : α0 `notin` dom κ)
                          by (clear - Hα0; solve_notin_auto);
                        rewrite (@msubst_pskl_open Θ1 κ Θ Pw α0 Hinc Hfr0);
                        rewrite pskl_to_bskl_inh_open; reflexivity)
                  ltac:(rewrite btyp_to_bskl_open; reflexivity)
                  (Hit1 α0 ltac:(clear - Hα0; solve_notin_auto))
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
      assert (Hincg : (ζg ++ κ) ∷ (Ξg ++ Θ1) ⊑ Θ)
        by (apply a_inc_extend_flex_block;
            [ exact Hinc | exact Hmap
            | eapply a_guess_mono_decls; exact Hg0 | exact Hent ]).
      pose proof (map_fst_eq_dom _ _ Hmap) as Hdζ.
      assert (Hfrg : α0 `notin` dom (ζg ++ κ))
        by (rewrite dom_app; rewrite Hdζ; clear - Hα0; fsetdec).
      rewrite (@msubst_ptyp_open (Ξg ++ Θ1) (ζg ++ κ) Θ
                 (close_ptyp_wrt_ptyp β A0) α0 Hincg Hfrg)
        in Heqc0.
      rewrite btyp_to_ptyp_open_var in Heqc0.
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
      2:{ rewrite ftvar_btyp_to_ptyp. clear - Hα0; fsetdec. }
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
      destruct (IHHref Pt Bt Θg Ξg A' κ Θ1 HwfΘ eq_refl eq_refl Hit Hg0
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
    destruct (@guess_complete_var_image Θ Δ κ βv Bt Θg Ξg A' Href' HwfΘ Hg) as [-> Heqc].
    exists nil; split;
      [ reflexivity
      | split; [ intros α2 τ2 Hin; inversion Hin | exact Heqc ] ].
  - (* flex_r : unfold the target's definition and recurse (any input) *)
    destruct Bt as [ | n | γ | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate HeqT.
    inversion HeqT; subst γ.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    destruct (IHHref P0 (ptyp_to_btyp_syn τ) Θg Ξg A' κ Θ1 HwfΘ HeqS
                ltac:(rewrite <- pskl_to_bskl_syn_ptyp,
                        <- ptyp_to_bskl_syn_via_pskl; reflexivity)
                (mono_ptyp_to_btyp_syn_is_ityp Hmτ)
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

(** Strip a block of flexible DECLARATIONS off an increase's source. *)
Lemma a_inc_strip_decls_head : forall (Ξg : aenv) (κ : metasubst) Θ0 Θ,
  a_decls Ξg ->
  κ ∷ (Ξg ++ Θ0) ⊑ Θ ->
  exists κp κ0,
    κ = κp ++ κ0 /\ length κp = length Ξg /\ κ0 ∷ Θ0 ⊑ Θ.
Proof.
  intros Ξg; induction Ξg as [ | [α b] Ξg' IH ]; intros κ Θ0 Θ Hd Hinc.
  - exists nil, κ.
    split; [ reflexivity | split; [ reflexivity | exact Hinc ] ].
  - inversion Hd; subst.
    simpl_env in Hinc.
    pose proof (@a_inc_strip_flex_mid nil α (Ξg' ++ Θ0) κ Θ
                  a_decls__nil Hinc) as Hstrip.
    destruct Hstrip
      as [κ1 [τ [κ2 [Heqκ [Hlen1 [_ [_ [Hwfτ [Hmτ Hinc2]]]]]]]]].
    destruct κ1 as [ | p κ1' ]; [ | simpl in Hlen1; discriminate Hlen1 ].
    simpl in Heqκ. subst κ.
    match goal with
    | Hd' : a_decls Ξg' |- _ =>
        destruct (IH _ _ _ Hd' Hinc2) as [κp [κ0 [-> [Hlen Hinc0]]]]
    end.
    exists ((α, τ) :: κp), κ0.
    split; [ reflexivity | ].
    split; [ simpl; rewrite Hlen; reflexivity | exact Hinc0 ].
Qed.

(** …and off a metasubstitution equivalence's source. *)
Lemma a_inc_equiv_strip_decls_head : forall (Ξg : aenv) Θ0 κ1 κ2 Θ,
  a_decls Ξg ->
  a_inc_equiv (Ξg ++ Θ0) κ1 κ2 Θ ->
  exists κ1p κ1t κ2p κ2t,
    κ1 = κ1p ++ κ1t /\ κ2 = κ2p ++ κ2t /\
    length κ1p = length Ξg /\ length κ2p = length Ξg /\
    a_inc_equiv Θ0 κ1t κ2t Θ.
Proof.
  intros Ξg; induction Ξg as [ | [α b] Ξg' IH ]; intros Θ0 κ1 κ2 Θ Hd Heqv.
  - exists nil, κ1, nil, κ2.
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ reflexivity | ]. split; [ reflexivity | exact Heqv ].
  - inversion Hd; subst.
    simpl_env in Heqv.
    inversion Heqv; subst.
    match goal with
    | Hd' : a_decls Ξg' |- _ =>
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
    rewrite <- ptyp_to_btyp_inh_open_var.
    auto.
Qed.

(** A declarations block's member is its flexible entry. *)
Lemma a_decls_in_dom_binds : forall (Ξg : aenv) α,
  a_decls Ξg -> α `in` dom Ξg -> binds α abind_flex_mono Ξg.
Proof.
  intros Ξg α Hd; induction Hd; intros Hin; simpl in Hin;
    [ exfalso; clear - Hin; fsetdec | ].
  destruct (α == α1) as [-> | Hne];
    [ apply binds_app_2; unfold binds; simpl; auto
    | apply binds_app_3; apply IHHd; clear - Hin Hne; fsetdec ].
Qed.

(** A fresh declarations block extends a wf context. *)
Lemma a_wf_aenv_decls_app_disjoint : forall (Ξg : aenv) Θ0,
  a_decls Ξg ->
  uniq Ξg ->
  (forall α, α `in` dom Ξg -> α `notin` dom Θ0) ->
  {{ ⊢ Θ0 }}a ->
  {{ ⊢ (Ξg ++ Θ0) }}a.
Proof.
  intros Ξg Θ0 Hd; induction Hd; intros Huq Hfr Hwf;
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
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  M <> mode_tc ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs e) ->
  (forall x M' Θ0' P0' κ' Θ' B',
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
        binds α abind_tvar Θ0') ->
     lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     {{ Θ' ⊢ˢᵈ[ M' ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' (open_exp_wrt_exp e (exp_var_f x))
       κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ M ] (exp_abs e) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 (exp_abs e) κ Θ B.
Proof.
  intros M Θ0 P0 e κ Θ B Hwf0 HwfΘ HwfP0 Hmod HMne Hinc Hrig
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
      {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ0 }}a /\
      a_ty_mode_compat (decr_mode M) Q /\
      ({{ Θ0 ⨟ empty ⊢ₚₛ P }}a) /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Q }}a) /\
      ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P))
         ⊳ (btyp_to_bskl (ptyp_to_btyp_inh A)) }}ad) /\
      ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ Q))
         ⊳ (btyp_to_bskl Bc) }}ad)).
  { inversion Hmod; subst.
    - (* TI : ◇ splits into ◇ → ◇ *)
      exists pskl_hole, pskl_hole.
      cbn [msubst_pskl pskl_to_bskl_inh] in Href |- *.
      inversion Href; subst.
      match goal with
      | Hp : pskl_to_bskl_syn ?PF = _, Hw : {{ _ ⨟ empty ⊢ₚₛ ?PF }}a |- _ =>
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
    as [Ξg [A' [Hguess [Hdecls [Huqb Havb]]]]].
  (* ---- 3. the fills : the paper's "sketchy" ⑯⑰ ---- *)
  destruct (@a_guess_mono_complete Θ empty _ _ HrefD
              P (ptyp_to_btyp_inh A) Θ0 Ξg A' κ Θ0 HwfΘ eq_refl eq_refl
              (ptyp_to_btyp_inh_ityp (a_wf_ptyp_lc HwfA))
              Hguess Hinc Huqb
              ltac:(intros α Hα;
                    pose proof (Havb α Hα) as Hn; clear - Hn; solve_notin_auto))
    as [ζg [Hmap [Hents HeqA']]].
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh in HeqA'.
  set (κg := ζg ++ κ) in *.
  assert (Hincg : κg ∷ (Ξg ++ Θ0) ⊑ Θ)
    by (apply a_inc_extend_flex_block;
        [ exact Hinc | exact Hmap | exact Hdecls | exact Hents ]).
  pose proof (map_fst_eq_dom _ _ Hmap) as Hdζ.
  (* ⑱ : the codomain refinement is untouched by the fills *)
  assert (HrefCg : {{ Θ ⨟ empty ⊢ᵣ
                     (pskl_to_bskl_inh (msubst_pskl κg Q))
                     ⊳ (btyp_to_bskl Bc) }}ad).
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
                          `union` dom Ξg
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A `union` ftvar_in_ptyp A'
                          `union` ftvar_in_pskl P `union` ftvar_in_pskl Q))
    as [x Hx].
  assert (HwfΞg : {{ ⊢ (Ξg ++ Θ0) }}a).
  { apply a_wf_aenv_decls_app_disjoint; [ exact Hdecls | exact Huqb | | exact Hwf0 ].
    intros α Hα. pose proof (Havb α Hα) as Hn. clear - Hn; fsetdec. }
  assert (HwfA' : a_wf_ptyp (Ξg ++ Θ0) A').
  { apply a_wf_ptyp_of_lc_tvarish;
      [ eapply a_guess_mono_lc; exact Hguess | ].
    intros α Hα.
    pose proof (a_guess_mono_ftv Hguess) as Hsub.
    destruct (AtomSetProperties.In_dec α (dom Ξg)) as [Hin | Hni].
    - right; left. apply binds_app_2.
      apply a_decls_in_dom_binds; [ exact Hdecls | exact Hin ].
    - assert (HαP : α `in` ftvar_in_pskl P) by (clear - Hα Hsub Hni; fsetdec).
      destruct (a_wf_pskl_ftv_tvarish HwfP HαP) as [Hc | Ht];
        [ exfalso; clear - Hc; fsetdec | ].
      destruct Ht as [Hr | [Hm | [τ Hdf]]];
        [ left; apply binds_app_3; exact Hr
        | right; left; apply binds_app_3; exact Hm
        | right; right; exists τ; apply binds_app_3; exact Hdf ]. }
  assert (Hwf0x : {{ ⊢ ((x ~ abind_var_typ A') ++ Ξg ++ Θ0) }}a)
    by (apply a_wf_aenv__var_typ;
        [ rewrite dom_app; clear - Hx; fsetdec | exact HwfA' | exact HwfΞg ]).
  assert (HwfΘx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (Hincx : κg ∷ ((x ~ abind_var_typ A') ++ Ξg ++ Θ0)
                    ⊑ ((x ~ abind_var_typ A) ++ Θ)).
  { apply (@a_inc__var (Ξg ++ Θ0) κg Θ nil x A' A);
      [ exact Hincg
      | apply a_tyequiv__sym; exact HeqA'
      | apply a_suffix__nil ]. }
  (* the side data for the IH *)
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (apply Hlce).
  assert (Hrigx : forall α,
             α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
             binds α abind_tvar ((x ~ abind_var_typ A') ++ Ξg ++ Θ0)).
  { intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup.
    apply binds_cons_3. apply binds_app_3. apply Hrig.
    clear - Hα Hup; fsetdec. }
  assert (HwfQx : {{ ((x ~ abind_var_typ A') ++ Ξg ++ Θ0) ⨟ empty ⊢ₚₛ Q }}a)
    by (eapply a_wf_pskl_mono;
        [ exact HwfQ
        | intros α c _ Hc; apply binds_cons_3; apply binds_app_3; exact Hc ]).
  (* ---- 5. the IH, once ---- *)
  destruct (IH x (decr_mode M) ((x ~ abind_var_typ A') ++ Ξg ++ Θ0) Q κg
              ((x ~ abind_var_typ A) ++ Θ) Bc
              Hwf0x HwfΘx HwfQx HmodQ Hincx Hrigx Hlcbody
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact HrefCg
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [B' [Θout [HrunB HoptB]]].
  (* ---- 6. the body run's identity increase shapes the output ---- *)
  assert (Hexpx : {{ ((x ~ abind_var_typ A') ++ Ξg ++ Θ0) ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a).
  { apply a_wf_exp_of_tvarish; [ exact Hlcbody | ].
    intros α Hα. left. apply Hrigx. exact Hα. }
  destruct (a_typing_sound HrunB Hwf0x HwfQx HmodQ Hexpx)
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
  assert (HftvΞg : ftvar_in_aenv Ξg [<=] dom Ξg)
    by (clear - Hdecls; induction Hdecls; simpl; fsetdec).
  (* ---- 8. the run ---- *)
  exists (ptyp_arrow A' B'), (Ξ ++ Θ2).
  split.
  { eapply a_typing__abs with (x := x) (Ξ := Ξ) (Θ2 := Θ2)
      (P := P) (Q := Q) (αs := Ξg) (Θ1 := Θ0).
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
  assert (Hinc1b : κb ∷ ((x ~ abind_var_typ A') ++ Ξg ++ Θ0)
                     ⊑ (Ξ ++ (x ~ abind_var_typ A') ++ Θ2)).
  { apply (@a_inc__var (Ξg ++ Θ0) κb Θ2 Ξ x A' A');
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
  assert (Heqvbs : a_inc_equiv (Ξg ++ Θ0) κg (msubst_compose ζb κb) Θ)
    by (eapply a_inc_equiv_strip_var_typ_head; [ exact Heqvb | exact I ]).
  (* split the body id and the equivalence along the block *)
  destruct (@a_inc_strip_decls_head Ξg κb Θ0 Θ2 Hdecls Hincb')
    as [κbp [κbt [Heqκb [Hlenb Hincbt]]]].
  destruct (@a_inc_equiv_strip_decls_head Ξg Θ0 κg (msubst_compose ζb κb) Θ Hdecls Heqvbs)
    as [κ1p [κ1t [κ2p [κ2t [Hspl1 [Hspl2 [Hl1 [Hl2 Heqv0]]]]]]]].
  (* the equivalence's left tail is the caller's κ *)
  assert (Hlenζg : length ζg = length Ξg).
  { pose proof (f_equal (@length atom) Hmap) as Hl.
    rewrite !List.length_map in Hl. exact Hl. }
  (* identify the tails *)
  destruct (app_split_by_head_length _ _ _ _ Hspl1
              ltac:(rewrite Hl1; exact Hlenζg))
    as [Heqp1 Heqt1].
  assert (Hκ1t : κ1t = κ) by (clear - Heqt1; congruence).
  subst κ1t.
  (* the right side splits along the compose of the body id's split *)
  rewrite Heqκb in Hspl2.
  unfold msubst_compose in Hspl2.
  rewrite List.map_app in Hspl2.
  destruct (app_split_by_head_length _ _ _ _ Hspl2
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
  assert (Hwffin : {{ ⊢ (Ξ ++ Θ2) }}a)
    by (exact (@a_wf_aenv_strip_tm_mid Ξ x (abind_var_typ A') Θ2
                 (fun h : abind_is_ty (abind_var_typ A') => h) HwfOut)).
  assert (HwfA'x : a_wf_ptyp ((x ~ abind_var_typ A') ++ Ξg ++ Θ0) A')
    by (eapply a_wf_ptyp_weaken;
        [ intros y c Hc; apply binds_cons_3; exact Hc | exact HwfA' ]).
  assert (Hpush : {{ Θ ⊢ (msubst_ptyp κg A') ≡ᵗ
                    (msubst_ptyp (msubst_compose ζb κb) A') }}a).
  { apply (@a_inc_equiv_msubst_ptyp A' (Ξg ++ Θ0) κg
             (msubst_compose ζb κb) Θ HwfA' Heqvbs HwfΞg
             ltac:(eapply a_inc_msubst_lc; exact Hincg)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζbs
                   | exact (is_id_msubst_values_lc Hidb) ])). }
  assert (Hlcfin2 : lc_aenv Θ2)
    by (apply a_wf_aenv_lc_aenv;
        eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (x ~ abind_var_typ A'));
        simpl_env; exact HwfOut).
  destruct (a_inc_weaken_suffix_target Hincb' Hidb Hlcfin2 Hsuf)
    as [κb2 [Hidb2 Hincb2]].
  assert (Heqκb2 : κb2 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hincb2 | exact Hincb' | exact Hidb2 | exact Hidb ]).
  subst κb2.
  assert (Hcid : msubst_ptyp (msubst_compose ζb κb) A' = msubst_ptyp ζb A')
    by (eapply msubst_compose_id_ptyp;
        [ exact HwfΞg | exact Hwffin | exact Hidb | exact Hincb2
        | exact Hζbs | exact HwfA' ]).
  rewrite Hcid in Hpush.
  simpl.
  apply a_tyequiv__arrow.
  - rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
    eapply a_tyequiv__trans;
      [ apply a_tyequiv__sym; exact Hpush | exact HeqA' ].
  - eapply a_tyequiv_ctx_mono;
      [ exact Heqcb
      | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ A) Θ);
        intros h; exact h ].
Qed.

(* --- the AbsAnno row -------------------------------------------------- *)

Lemma a_typing_complete_abs_anno : forall M Θ0 P0 A e κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  M <> mode_tc ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs_anno A e) ->
  (forall x M' Θ0' P0' κ' Θ' B',
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
        binds α abind_tvar Θ0') ->
     lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     {{ Θ' ⊢ˢᵈ[ M' ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' (open_exp_wrt_exp e (exp_var_f x))
       κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ M ] (exp_abs_anno A e) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 (exp_abs_anno A e) κ Θ B.
Proof.
  intros M Θ0 P0 A e κ Θ B Hwf0 HwfΘ HwfP0 Hmod HMne Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst; [ exfalso; auto | exfalso; auto | ].
  match goal with
  | H : forall x, x `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  (* ⚙ [subst] consumed the rule's [btyp_to_ptyp B1 = A'] equation and
     [A'] with it — the ≡ᵗ premise now reads [{{ Θ ⊢ A ≡ᵗ ⌊B1⌋ }}a]. *)
  match goal with
  | H : {{ Θ ⊢ A ≡ᵗ (btyp_to_ptyp ?BB) }}a |- _ =>
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
      {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ0 }}a /\
      a_ty_mode_compat (decr_mode M) Q /\
      ({{ Θ0 ⨟ empty ⊢ₚₛ P }}a) /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Q }}a) /\
      ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P))
         ⊳ (btyp_to_bskl B1) }}ad) /\
      ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ Q))
         ⊳ (btyp_to_bskl B2) }}ad)).
  { inversion Hmod; subst.
    - exists pskl_hole, pskl_hole.
      cbn [msubst_pskl pskl_to_bskl_inh] in Href |- *.
      inversion Href; subst.
      match goal with
      | Hp : pskl_to_bskl_syn ?PF = _, Hw : {{ _ ⨟ empty ⊢ₚₛ ?PF }}a |- _ =>
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
  assert (HwfpA0 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfA0).
  assert (Heqs : {{ Θ ⊢ (ptyp_to_pskl A) ≡ˢ (ptyp_to_pskl A') }}a)
    by (apply a_tyequiv_pskl; exact HeqAA').
  assert (Hjoin : {{ empty ⨟ Θ ⊢ˢ
                    (pskl_to_uskl (msubst_pskl κ (ptyp_to_pskl A)))
                    ∼ (btyp_to_bskl B1) }}ad).
  { rewrite msubst_pskl_embed_ptyp, HmsA.
    eapply (proj2 (skl_tyequiv_consis_transport Heqs HwfΘ
                     (fun x b h => h))).
    rewrite pskl_to_uskl_ptyp.
    apply (ad_pat_consis_syn_bid HwfA' B1 HB1). }
  assert (Hrp : ad_refine_pskl_f empty Θ empty
                  (msubst_pskl κ (ptyp_to_pskl A))
                  (bskl_to_pskl (btyp_to_bskl B1))).
  { rewrite msubst_pskl_embed_ptyp, HmsA.
    rewrite bskl_to_pskl_btyp_to_bskl, HB1.
    eapply (proj2 (skl_tyequiv_refine_pskl_f_transport Heqs HwfΘ
                     (fun x b h => h))).
    apply ad_refine_pskl_f_of_plain.
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA'. }
  destruct (a_consis_complete Hwf0 HwfP HwfpA0 Hinc HwfΘ Hjoin
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
  assert (Hwf0x : {{ ⊢ ((x ~ abind_var_typ A) ++ Θmid) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAmid | exact Hwfmid ]).
  assert (HwfΘx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a)
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
  assert (HwfQB2 : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B2)) }}a).
  { pose proof (ad_sd_typing_target_wf Hd HwfΘ) as Hw.
    simpl in Hw. inversion Hw; subst.
    rewrite bskl_to_pskl_btyp_to_bskl.
    apply a_wf_ptyp_to_wf_pskl. assumption. }
  assert (Hpp : {{ Θ ⨟ empty ⊢ₚᵣ
                  (msubst_pskl (msubst_compose ζc κc) Q)
                  ⊑ (msubst_pskl κ Q) }}ad).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfQ | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
      | exact Heqvc | clear; fsetdec ]. }
  assert (HrefCζ : {{ Θ ⨟ empty ⊢ᵣ
                     (pskl_to_bskl_inh
                        (msubst_pskl (msubst_compose ζc κc) Q))
                     ⊳ (btyp_to_bskl B2) }}ad).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact HrefC | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQB2 ]. }
  assert (HmsQ : msubst_pskl (msubst_compose ζc κc) Q = msubst_pskl ζc Q).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwfmid | exact Hidc | exact Hincc | exact Hζc
      | exact (a_scope_pskl_of_wf HwfQ) ]. }
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
  assert (HwfQmid : {{ Θmid ⨟ empty ⊢ₚₛ Q }}a).
  { pose proof (a_wf_pskl_msubst_inc Hincc Hwf0 HwfQ
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)) as Hw.
    rewrite (msubst_pskl_id Q Hidc) in Hw. exact Hw. }
  (* ---- 4. the IH, once ---- *)
  destruct (IH x (decr_mode M) ((x ~ abind_var_typ A) ++ Θmid) Q ζc
              ((x ~ abind_var_typ A) ++ Θ) B2
              Hwf0x HwfΘx
              ltac:(eapply a_wf_pskl_mono;
                    [ exact HwfQmid
                    | intros α c _ Hc; apply binds_cons_3; exact Hc ])
              HmodQ Hincx Hrigx (Hlce x)
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact HrefCζ
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [B' [Θout [HrunB HoptB]]].
  (* ---- 5. the body run's identity increase shapes the output ---- *)
  assert (Hexpx : {{ ((x ~ abind_var_typ A) ++ Θmid) ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a).
  { apply a_wf_exp_of_tvarish; [ exact (Hlce x) | ].
    intros α Hα. left. apply Hrigx. exact Hα. }
  assert (HwfQx : {{ ((x ~ abind_var_typ A) ++ Θmid) ⨟ empty ⊢ₚₛ Q }}a)
    by (eapply a_wf_pskl_mono;
        [ exact HwfQmid
        | intros α c _ Hc; apply binds_cons_3; exact Hc ]).
  destruct (a_typing_sound HrunB Hwf0x HwfQx HmodQ Hexpx)
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
  assert (Hwffin : {{ ⊢ (Ξ ++ Θ3) }}a)
    by (exact (@a_wf_aenv_strip_tm_mid Ξ x (abind_var_typ A) Θ3
                 (fun h : abind_is_ty (abind_var_typ A) => h) HwfOut)).
  assert (Hlcfin : lc_aenv Θ3)
    by (apply a_wf_aenv_lc_aenv;
        eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (x ~ abind_var_typ A));
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
  - eapply a_tyequiv_ctx_mono;
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

(** Refinement's ∀-inh row binds its witness in Δ; the algorithmic side
    puts it in Θ as a rigid entry.  Going Δ → Θ is a weakening (mirror of
    [a_wf_pskl_delta_to_tvar]; [__var] accepts either side, [__hole]'s wf
    weakens, and [__tophole_fill]'s own binder exchanges past the new
    head — [binds] is plain membership). *)
Lemma ad_refine_syn_delta_to_ctx : forall Θ Δ0 Q Q',
  {{ Θ ⨟ Δ0 ⊢ᵣ Q ⊳ Q' }}ad ->
  forall α Δ, Δ0 [<=] add α Δ ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
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
    eapply a_wf_pskl_delta_to_tvar; [ exact H | clear; fsetdec ].
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
(*  [Ξ0 = nil] (algo/typing/prop_scope.v).                                    *)
(* ===================================================================== *)

(* --- the AbsCheck ∀ row ------------------------------------------------ *)

Lemma a_typing_complete_abs_check_step : forall Θ0 P0 e κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs e) ->
  (forall M' Θ0' P0' κ' Θ' B',
     (* ⭐ THE MEASURE GUARD.  These rows recurse on the SAME subject, so
        the glue can only supply an IH at a SMALLER declarative result —
        the lexicographic (size_exp, size_btyp) measure's second
        component.  Without this premise the row is unusable: no
        well-founded measure can hand out an IH at an arbitrary [B']
        beside an unchanged subject. *)
     size_btyp B' < size_btyp (btyp_all_inh B) ->
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0') ->
     lc_exp (exp_abs e) ->
     {{ Θ' ⊢ˢᵈ[ M' ] (exp_abs e) ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' (exp_abs e) κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_all_inh B) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_all_inh B)) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 (exp_abs e) κ Θ (btyp_all_inh B).
Proof.
  intros Θ0 P0 e κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
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
    | Hw1 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Aa) }}a,
      Hw2 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Ab) }}a |- _ =>
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
    assert (Hwf0x : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf0 ]).
    assert (HwfΘx : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    assert (HwfP0x : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) }}a).
    { rewrite ptyp_to_pskl_open.
      eapply a_wf_pskl_delta_to_tvar;
        [ apply (HwfF α ltac:(clear - Hα; solve_notin_auto)) | clear; fsetdec ]. }
    assert (Hincx : κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ))
      by (apply (@a_inc__tvar Θ0 κ Θ nil α);
          [ exact Hinc | apply a_suffix__nil ]).
    assert (Hrigx : forall β, β `in` ftvar_in_exp (exp_abs e) ->
               binds β abind_tvar ((α ~ abind_tvar) ++ Θ0))
      by (intros β Hβ; apply binds_cons_3; apply Hrig; exact Hβ).
    (* the peeled refinement, moved from the Δ-slot into the context *)
    assert (Hrefx : {{ ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                      (pskl_to_bskl_inh
                         (msubst_pskl κ
                            (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))))
                      ⊳ (btyp_to_bskl (open_btyp_wrt_btyp B (btyp_var_f α))) }}ad).
    { rewrite msubst_pskl_embed_ptyp.
      rewrite (@msubst_ptyp_open Θ0 κ Θ A0 α Hinc
                 ltac:(clear - Hα; solve_notin_auto)).
      rewrite ptyp_to_pskl_open.
      rewrite pskl_to_bskl_inh_open.
      rewrite btyp_to_bskl_open. simpl.
      eapply ad_refine_syn_delta_to_ctx;
        [ apply (HrefF α ltac:(clear - Hα; solve_notin_auto)) | clear; fsetdec ]. }
    (* ---- 4. the IH, once, at the peeled problem ---- *)
    destruct (IH mode_tc ((α ~ abind_tvar) ++ Θ0)
                (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
                κ ((α ~ abind_tvar) ++ Θ)
                (open_btyp_wrt_btyp B (btyp_var_f α))
                ltac:(rewrite size_btyp_open_btyp_wrt_btyp_var;
                      simpl; lia)
                Hwf0x HwfΘx HwfP0x (a_ty_mode_compat__tc _) Hincx Hrigx
                Hlc
                (Hbody α ltac:(clear - Hα; solve_notin_auto)) Hrefx)
      as [A1 [Θrun [HrunB HoptB]]].
    (* ---- 5. the run's identity increase shapes the output ---- *)
    assert (Hexpx : {{ ((α ~ abind_tvar) ++ Θ0) ⊢ᵉ (exp_abs e) }}a).
    { apply a_wf_exp_of_tvarish; [ exact Hlc | ].
      intros β Hβ. left. apply Hrigx. exact Hβ. }
    destruct (a_typing_sound HrunB Hwf0x HwfP0x
                (a_ty_mode_compat__tc _) Hexpx)
      as [HleB [HwfOut [HwfA1out _]]].
    destruct HleB as [[κb [Hidb Hincb]] _].
    destruct (a_inc_tvar_inv Hincb) as [Ξ [Θ2 [-> [Hsuf Hincb']]]].
    (* the §6.3#2 scoping invariant, at the rigid marker *)
    pose proof (@a_typing_scope_tvar_nil _ _ _ _ _ _ _ HrunB Hwf0x
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
    rewrite btyp_to_ptyp_open_var in Heqcb.
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
    pose proof (a_tyequiv_strengthen_tvar_cons Heqcb eq_refl) as Heqc1.
    simpl.
    set (X := msubst_ptyp ζbt (close_ptyp_wrt_ptyp α A1)) in *.
    assert (HαX : α `notin` ftvar_in_ptyp X).
    { unfold X.
      eapply msubst_ptyp_ftv_notin_inc;
        [ exact Hstrip
        | rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp; clear; fsetdec
        | clear - Hα; fsetdec ]. }
    assert (HαB : α `notin` ftvar_in_ptyp (btyp_to_ptyp B))
      by (rewrite ftvar_btyp_to_ptyp; clear - Hα; fsetdec).
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
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs_anno A e) ->
  (forall M' Θ0' P0' κ' Θ' B',
     (* ⭐ THE MEASURE GUARD.  These rows recurse on the SAME subject, so
        the glue can only supply an IH at a SMALLER declarative result —
        the lexicographic (size_exp, size_btyp) measure's second
        component.  Without this premise the row is unusable: no
        well-founded measure can hand out an IH at an arbitrary [B']
        beside an unchanged subject. *)
     size_btyp B' < size_btyp (btyp_all_inh B) ->
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) ->
        binds α abind_tvar Θ0') ->
     lc_exp (exp_abs_anno A e) ->
     {{ Θ' ⊢ˢᵈ[ M' ] (exp_abs_anno A e) ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' (exp_abs_anno A e) κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_all_inh B) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_all_inh B)) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 (exp_abs_anno A e) κ Θ (btyp_all_inh B).
Proof.
  intros Θ0 P0 A e κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
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
    | Hw1 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Aa) }}a,
      Hw2 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Ab) }}a |- _ =>
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
    assert (Hwf0x : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf0 ]).
    assert (HwfΘx : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    assert (HwfP0x : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) }}a).
    { rewrite ptyp_to_pskl_open.
      eapply a_wf_pskl_delta_to_tvar;
        [ apply (HwfF α ltac:(clear - Hα; solve_notin_auto)) | clear; fsetdec ]. }
    assert (Hincx : κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ))
      by (apply (@a_inc__tvar Θ0 κ Θ nil α);
          [ exact Hinc | apply a_suffix__nil ]).
    assert (Hrigx : forall β, β `in` ftvar_in_exp (exp_abs_anno A e) ->
               binds β abind_tvar ((α ~ abind_tvar) ++ Θ0))
      by (intros β Hβ; apply binds_cons_3; apply Hrig; exact Hβ).
    assert (Hrefx : {{ ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                      (pskl_to_bskl_inh
                         (msubst_pskl κ
                            (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))))
                      ⊳ (btyp_to_bskl (open_btyp_wrt_btyp B (btyp_var_f α))) }}ad).
    { rewrite msubst_pskl_embed_ptyp.
      rewrite (@msubst_ptyp_open Θ0 κ Θ A0 α Hinc
                 ltac:(clear - Hα; solve_notin_auto)).
      rewrite ptyp_to_pskl_open.
      rewrite pskl_to_bskl_inh_open.
      rewrite btyp_to_bskl_open. simpl.
      eapply ad_refine_syn_delta_to_ctx;
        [ apply (HrefF α ltac:(clear - Hα; solve_notin_auto)) | clear; fsetdec ]. }
    destruct (IH mode_tc ((α ~ abind_tvar) ++ Θ0)
                (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
                κ ((α ~ abind_tvar) ++ Θ)
                (open_btyp_wrt_btyp B (btyp_var_f α))
                ltac:(rewrite size_btyp_open_btyp_wrt_btyp_var;
                      simpl; lia)
                Hwf0x HwfΘx HwfP0x (a_ty_mode_compat__tc _) Hincx Hrigx
                Hlc
                (Hbody α ltac:(clear - Hα; solve_notin_auto)) Hrefx)
      as [A1 [Θrun [HrunB HoptB]]].
    assert (Hexpx : {{ ((α ~ abind_tvar) ++ Θ0) ⊢ᵉ (exp_abs_anno A e) }}a).
    { apply a_wf_exp_of_tvarish; [ exact Hlc | ].
      intros β Hβ. left. apply Hrigx. exact Hβ. }
    destruct (a_typing_sound HrunB Hwf0x HwfP0x
                (a_ty_mode_compat__tc _) Hexpx)
      as [HleB [HwfOut [HwfA1out _]]].
    destruct HleB as [[κb [Hidb Hincb]] _].
    destruct (a_inc_tvar_inv Hincb) as [Ξ [Θ2 [-> [Hsuf Hincb']]]].
    pose proof (@a_typing_scope_tvar_nil _ _ _ _ _ _ _ HrunB Hwf0x
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
    rewrite btyp_to_ptyp_open_var in Heqcb.
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
    pose proof (a_tyequiv_strengthen_tvar_cons Heqcb eq_refl) as Heqc1.
    simpl.
    set (X := msubst_ptyp ζbt (close_ptyp_wrt_ptyp α A1)) in *.
    assert (HαX : α `notin` ftvar_in_ptyp X).
    { unfold X.
      eapply msubst_ptyp_ftv_notin_inc;
        [ exact Hstrip
        | rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp; clear; fsetdec
        | clear - Hα; fsetdec ]. }
    assert (HαB : α `notin` ftvar_in_ptyp (btyp_to_ptyp B))
      by (rewrite ftvar_btyp_to_ptyp; clear - Hα; fsetdec).
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

(* ===================================================================== *)
(*  STEP A.1 — composing an increment with the SOURCE'S OWN identity is    *)
(*  the increment itself.                                                 *)
(*                                                                        *)
(*  Both metasubstitutions enumerate [Θ0]'s flexible entries in the same   *)
(*  order (that is what [a_inc]'s two flexible rows do), so the pointwise  *)
(*  composition is literally [κ].  Needed by the split's ARROW row, whose  *)
(*  "stage" leaves the context alone: its optimality obligation is         *)
(*  [a_inc_equiv Θ0 κ (ζ ∘ κ1) Θ] at [ζ := κ].                             *)
(* ===================================================================== *)

Lemma msubst_compose_cons : forall ζ α τ κ,
  msubst_compose ζ ((α, τ) :: κ) = (α, msubst_ptyp ζ τ) :: msubst_compose ζ κ.
Proof. reflexivity. Qed.

Lemma msubst_compose_inc_id_r : forall Θ0 κ Θ κ1 Θ',
  κ ∷ Θ0 ⊑ Θ ->
  κ1 ∷ Θ0 ⊑ Θ' ->
  is_id_msubst κ1 ->
  {{ ⊢ Θ0 }}a ->
  msubst_compose κ κ1 = κ.
Proof.
  intros Θ0 κ Θ κ1 Θ' Hinc; revert κ1 Θ'.
  induction Hinc; intros κ1 Θ'' Hinc1 Hid1 Hwf0.
  - (* empty *)
    inversion Hinc1; subst. reflexivity.
  - (* flex α *)
    inversion Hinc1 as [ | Θa κa Θb αa τa Hrest Hwfa Hma Heqκ1 HeqΘ0 HeqΘ''
                       | | | | ]; subst.
    destruct (is_id_msubst_inv Hid1) as [Heqe Hid1'].
    simpl in Heqe. subst.
    inversion Hwf0 as [ | αh Θh Hnd Hwa | | | | ]; subst.
    assert (Hnd1 : α `notin` dom κa)
      by (pose proof (a_inc_dom_sub Hrest) as Hs; clear - Hs Hnd; fsetdec).
    assert (Hcut : msubst_compose ((α, τ) :: κ) κa = msubst_compose κ κa)
      by (exact (@msubst_compose_id_app_agree κa [(α, τ)] κ Hid1'
                   ltac:(intros y Hy Hc; simpl in Hc;
                         assert (Hya : y = α) by (clear - Hc; solve_notin_auto);
                         subst; clear - Hnd1 Hy; solve_notin_auto))).
    rewrite msubst_compose_cons, Hcut.
    cbn [msubst_ptyp msubst_lookup].
    destruct (α == α) as [_ | Hc]; [ | exfalso; apply Hc; reflexivity ].
    f_equal.
    eapply IHHinc; [ exact Hrest | exact Hid1' | exact Hwa ].
  - (* flex_def α := τ *)
    inversion Hinc1 as [ | | Θa κa Θb αa τa τa' Hrest Hwfa Hma Heqa
                             Heqκ1 HeqΘ0 HeqΘ'' | | | ]; subst.
    destruct (is_id_msubst_inv Hid1) as [Heqe Hid1'].
    simpl in Heqe. subst.
    inversion Hwf0 as [ | | αh τh Θh Hnd Hwp Hm Hwa | | | ]; subst.
    assert (Hnd1 : α `notin` dom κa)
      by (pose proof (a_inc_dom_sub Hrest) as Hs; clear - Hs Hnd; fsetdec).
    assert (Hcut : msubst_compose ((α, τ') :: κ) κa = msubst_compose κ κa)
      by (exact (@msubst_compose_id_app_agree κa [(α, τ')] κ Hid1'
                   ltac:(intros y Hy Hc; simpl in Hc;
                         assert (Hya : y = α) by (clear - Hc; solve_notin_auto);
                         subst; clear - Hnd1 Hy; solve_notin_auto))).
    rewrite msubst_compose_cons, Hcut.
    cbn [msubst_ptyp msubst_lookup].
    destruct (α == α) as [_ | Hc]; [ | exfalso; apply Hc; reflexivity ].
    f_equal.
    eapply IHHinc; [ exact Hrest | exact Hid1' | exact Hwa ].
  - (* var_typ x : neither side consumes an entry *)
    destruct (a_inc_var_inv Hinc1) as [Ξ1 [A1 [T1 [_ [_ [_ Hrest]]]]]].
    inversion Hwf0; subst.
    eapply IHHinc; [ exact Hrest | exact Hid1 | eassumption ].
  - (* var_skl x *)
    destruct (a_inc_var_skl_inv Hinc1) as [Ξ1 [P1 [T1 [_ [_ [_ Hrest]]]]]].
    inversion Hwf0; subst.
    eapply IHHinc; [ exact Hrest | exact Hid1 | eassumption ].
  - (* tvar α *)
    destruct (a_inc_tvar_inv Hinc1) as [Ξ1 [T1 [_ [_ Hrest]]]].
    inversion Hwf0; subst.
    eapply IHHinc; [ exact Hrest | exact Hid1 | eassumption ].
Qed.

(** Lookup in a cons cell — stated at [atom] so [rewrite] fires no matter
    which variable ALIAS ([ptypvar], [usklvar], …) the occurrence carries.
    ⚙ [destruct (β == α)] does NOT reduce the [if] when the two sides were
    elaborated at different aliases. *)
(* ===================================================================== *)
(*  STEP A.2 — a MONOTYPE painting that refines to an arrow IS an arrow,   *)
(*  up to [≡ᵗ].                                                           *)
(*                                                                        *)
(*  The split's flexible row has to invent the two halves [β̂1]/[α̂1] and    *)
(*  SOLVE them, so completeness must first name the monotypes they stand   *)
(*  for.  The only rows a monotype painting can take are [unit], [var],    *)
(*  [arrow] and the two flexible lookups; against an ARROW target only     *)
(*  [arrow] and [flex_l] survive, and [flex_l] recurses at the (shorter)   *)
(*  definition — so the induction is on the REFINEMENT, exactly as in      *)
(*  [ad_pat_consis_mono_to_refine].                                       *)
(* ===================================================================== *)

Lemma mono_refine_arrow_inv : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  forall τ0 R1 R2,
  {{ ⊢ Θ }}a ->
  a_wf_ptyp Θ τ0 ->
  mono_ptyp τ0 ->
  Qs = ptyp_to_bskl_syn τ0 ->
  Qt = bskl_arrow R1 R2 ->
  exists τ1 τ2,
    mono_ptyp τ1 /\ mono_ptyp τ2 /\
    a_wf_ptyp Θ τ1 /\ a_wf_ptyp Θ τ2 /\
    {{ Θ ⊢ τ0 ≡ᵗ (ptyp_arrow τ1 τ2) }}a /\
    ({{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn τ1) ⊳ R1 }}ad) /\
    ({{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn τ2) ⊳ R2 }}ad).
Proof.
  intros Θ Δ Qs Qt H; induction H;
    intros τ0 R1 R2 Hwf Hwfτ Hm HeqS HeqT;
    unfold ptyp_to_bskl_syn in *;
    try solve [ destruct τ0; simpl in HeqS; discriminate
              | discriminate HeqT ].
  - (* arrow : the painting IS an arrow *)
    destruct τ0 as [ | n | α | τa τb | τc ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst. inversion HeqT; subst.
    inversion Hm; subst. inversion Hwfτ; subst.
    exists τa, τb.
    repeat split; try assumption.
    apply a_tyequiv__refl. apply mono_ptyp_lc. exact Hm.
  - (* flex_l : unfold the definition and recurse *)
    destruct τ0 as [ | n | α0 | τa τb | τc ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    assert (Hwfτ' : a_wf_ptyp Θ τ)
      by (eapply prop_basic.a_wf_aenv_binds_def_wf; [ exact Hwf | exact H ]).
    destruct (IHad_refine_syn τ R1 R2 Hwf Hwfτ' Hmτ eq_refl eq_refl)
      as [τ1 [τ2 [Hm1 [Hm2 [Hw1 [Hw2 [Heqv [Hr1 Hr2]]]]]]]].
    exists τ1, τ2.
    repeat split; try assumption.
    eapply a_tyequiv__trans; [ apply a_tyequiv__flex_def; exact H | exact Heqv ].
Qed.

(** A variable painting that refines to an ARROW must be a DEFINED
    flexible: [__var] and [__flex_r] both conclude at a variable target,
    so only [__flex_l] can fire.  This is what kills the split's RIGID
    sub-case ([a_split_rigid_var_absurd] is its algorithmic mirror). *)
Lemma refine_var_arrow_flex_def : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  forall β R1 R2, Qs = bskl_var_f β -> Qt = bskl_arrow R1 R2 ->
  exists τ, binds β (abind_flex_mono_def τ) Θ.
Proof.
  intros Θ Δ Qs Qt H; induction H; intros β0 R1 R2 HeqS HeqT;
    try solve [ discriminate HeqS | discriminate HeqT ].
  inversion HeqS; subst. exists τ. assumption.
Qed.

(* ===================================================================== *)
(*  STEP A.3 — COMPLETENESS OF SPLITTING AT CHECK MODE.                   *)
(*                                                                        *)
(*  [a_split_complete] (prop_completeness_pat.v:932) is stated for        *)
(*  [M <> mode_tc] and returns the IDENTITY split — at TC the input is a   *)
(*  TYPE painting [⌈A0⌉], so [a_split__flex] IS reachable                  *)
(*  ([a_split_ty_shape]'s "whole asymmetry") and the row has to be built.  *)
(*  This is the paper's AbsCheck subcase 2.                                *)
(*                                                                        *)
(*  The declarative side hands us a refinement of [κ⌈A0⌉] to an ARROW, and *)
(*  only two shapes of [A0] survive it: a syntactic arrow (⟹ the identity  *)
(*  split) and a FLEXIBLE (⟹ invent [β̂1]/[α̂1] and solve them by a full     *)
(*  consistency run, which [a_consis_complete] supplies at the         *)
(*  monotypes [τ1]/[τ2] the flexible's own image decomposes into).         *)
(*  [unit] / [∀] / a RIGID variable all die on the refinement.             *)
(*                                                                        *)
(*  The conclusion is the standard stage package: the run, its own         *)
(*  identity increase, and a factoring witness [ζ] at which BOTH the       *)
(*  binder's [≡ᵗ] (what [a_inc__var] consumes) and the codomain's          *)
(*  refinement (what the body's IH consumes) hold.                         *)
(* ===================================================================== *)

Lemma a_split_complete_tc : forall Θ0 A0 κ Θ A (B1 : btyp),
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl A0) }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ (ptyp_to_pskl A0)))
    ⊳ (btyp_to_bskl (btyp_arrow (ptyp_to_btyp_inh A) B1)) }}ad ->
  exists Ad Bc Θ1 κs ζ,
    ({{ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl Ad) ⇢ (ptyp_to_pskl Bc) ⊣ Θ1 }}a) /\
    {{ ⊢ Θ1 }}a /\
    a_wf_ptyp Θ1 Ad /\ a_wf_ptyp Θ1 Bc /\
    is_id_msubst κs /\ κs ∷ Θ0 ⊑ Θ1 /\
    ζ ∷ Θ1 ⊑ Θ /\
    a_inc_equiv Θ0 κ (msubst_compose ζ κs) Θ /\
    {{ Θ ⊢ (msubst_ptyp ζ Ad) ≡ᵗ A }}a /\
    ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl ζ (ptyp_to_pskl Bc)))
       ⊳ (btyp_to_bskl B1) }}ad).
Proof.
  intros Θ0 A0 κ Θ A B1 Hwf0 HwfΘ HwfP0 Hinc Href.
  cbn [btyp_to_bskl] in Href.
  (* the split, its own identity increase and the factoring witness, built
     per shape; everything downstream is uniform *)
  assert (Hbuilt : exists Ad Bc Θ1 ζ,
             ({{ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl Ad)
                 ⇢ (ptyp_to_pskl Bc) ⊣ Θ1 }}a) /\
             ζ ∷ Θ1 ⊑ Θ /\
             (forall κs, is_id_msubst κs -> κs ∷ Θ0 ⊑ Θ1 ->
                a_inc_equiv Θ0 κ (msubst_compose ζ κs) Θ) /\
             {{ Θ ⊢ (msubst_ptyp ζ Ad) ≡ᵗ A }}a /\
             ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl ζ (ptyp_to_pskl Bc)))
                ⊳ (btyp_to_bskl B1) }}ad)).
  { destruct A0 as [ | n | β | Aa Ab | Ac ];
      rewrite msubst_pskl_embed_ptyp in Href.
    - (* unit : [bskl_unit] refines only to [bskl_unit] *)
      exfalso. cbn in Href. inversion Href.
    - (* a bound variable is not well formed *)
      exfalso. cbn in HwfP0. inversion HwfP0.
    - (* a VARIABLE : rigid dies, flexible is the paper's subcase 2 *)
      cbn [ptyp_to_pskl] in HwfP0.
      assert (Hbt : a_binds_tvar β Θ0)
        by (inversion HwfP0 as [ | ? ? ? Hb | | | | ]; subst;
            destruct Hb as [Hc | Hb];
            [ exfalso; clear - Hc; fsetdec | exact Hb ]).
      pose proof (a_inc_lookup_mono β Hinc) as Hmτ.
      pose proof (@a_inc_lookup_wf Θ0 κ Θ β Hinc Hwf0 Hbt) as Hwfτ.
      cbn [ptyp_to_pskl msubst_ptyp] in Href.
      rewrite (mono_inh_eq_syn Hmτ) in Href.
      destruct Hbt as [Hrig | Hflex].
      { (* RIGID : the image is [β] itself, which refines only to itself *)
        exfalso.
        assert (Hid : msubst_lookup κ β = ptyp_var_f β).
        { change (msubst_lookup κ β) with (msubst_ptyp κ (ptyp_var_f β)).
          eapply msubst_ptyp_rigid_id;
            [ exact Hinc | exact Hwf0
            | intros γ Hγ; cbn in Hγ;
              assert (Hγβ : γ = β) by (clear - Hγ; fsetdec); subst;
              exact Hrig ]. }
        rewrite Hid in Href.
        unfold ptyp_to_bskl_syn in Href.
        cbn [ptyp_to_pskl pskl_to_bskl_syn] in Href.
        destruct (refine_var_arrow_flex_def Href eq_refl eq_refl) as [τx Hb].
        assert (Hrt : binds β abind_tvar Θ)
          by (eapply a_inc_binds_tvar; [ exact Hinc | exact Hrig ]).
        pose proof (binds_unique _ _ _ _ _ Hb Hrt (a_wf_aenv_uniq HwfΘ)) as Hc.
        discriminate Hc. }
      (* FLEXIBLE — name the two monotypes the image decomposes into *)
      destruct (mono_refine_arrow_inv Href HwfΘ Hwfτ Hmτ eq_refl eq_refl)
        as [τ1 [τ2 [Hm1 [Hm2 [Hw1 [Hw2 [Heqτ [Hr1 Hr2]]]]]]]].
      (* two fresh flexibles for the split's halves *)
      destruct (atom_fresh (ftvar_in_aenv Θ0 `union` dom Θ0 `union` dom κ
                              `union` dom Θ `union` ftvar_in_aenv Θ))
        as [β1 Hβ1].
      destruct (atom_fresh (add β1 (ftvar_in_aenv Θ0) `union` dom Θ0
                              `union` dom κ `union` dom Θ
                              `union` ftvar_in_aenv Θ)) as [α1 Hα1].
      assert (Hne : α1 <> β1) by (clear - Hα1; fsetdec).
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      assert (Hfrβ1 : β1 `notin` dom Θ0) by (clear - Hβ1; fsetdec).
      assert (Hfrα1 : α1 `notin` dom Θ0) by (clear - Hα1; fsetdec).
      assert (Hwf0' : {{ ⊢ ((α1 ~ abind_flex_mono)
                                  ++ (β1 ~ abind_flex_mono) ++ Θ0) }}a).
      { apply a_wf_aenv__flex;
          [ simpl_env; repeat rewrite dom_app; simpl;
            clear - Hfrα1 Hne; fsetdec | ].
        apply a_wf_aenv__flex; [ clear - Hfrβ1; fsetdec | exact Hwf0 ]. }
      assert (Hinc' : ((α1, τ2) :: (β1, τ1) :: κ)
                        ∷ ((α1 ~ abind_flex_mono)
                             ++ (β1 ~ abind_flex_mono) ++ Θ0) ⊑ Θ).
      { apply a_inc__flex; [ | exact Hw2 | exact Hm2 ].
        apply a_inc__flex; [ exact Hinc | exact Hw1 | exact Hm1 ]. }
      assert (Hne1 : β1 <> α1) by (intros Hc; apply Hne; symmetry; exact Hc).
      assert (Hlkβ1 : msubst_lookup ((α1, τ2) :: (β1, τ1) :: κ) β1 = τ1)
        by (rewrite (@msubst_lookup_cons_neq β1 α1 τ2 ((β1, τ1) :: κ) Hne1);
            apply msubst_lookup_cons_eq).
      assert (Hlkα1 : msubst_lookup ((α1, τ2) :: (β1, τ1) :: κ) α1 = τ2)
        by (apply msubst_lookup_cons_eq).
      assert (Hβdom : β `in` dom Θ0)
        by (destruct Hflex as [Hb | [τx Hb]]; eapply binds_In; eassumption).
      assert (Hβα1 : β <> α1)
        by (intros Hc; rewrite Hc in Hβdom; clear - Hfrα1 Hβdom; fsetdec).
      assert (Hββ1 : β <> β1)
        by (intros Hc; rewrite Hc in Hβdom; clear - Hfrβ1 Hβdom; fsetdec).
      assert (Hlkβ : msubst_lookup ((α1, τ2) :: (β1, τ1) :: κ) β
                     = msubst_lookup κ β)
        by (rewrite (@msubst_lookup_cons_neq β α1 τ2 ((β1, τ1) :: κ) Hβα1),
                    (@msubst_lookup_cons_neq β β1 τ1 κ Hββ1); reflexivity).
      assert (HwfA12 : a_wf_ptyp Θ (ptyp_arrow τ1 τ2))
        by (apply a_wf_ptyp__arrow; assumption).
      assert (Hm12 : mono_ptyp (ptyp_arrow τ1 τ2))
        by (apply mono_ptyp__arrow; assumption).
      assert (Heqs : {{ Θ ⊢ (ptyp_to_pskl (msubst_lookup κ β))
                       ≡ˢ (ptyp_to_pskl (ptyp_arrow τ1 τ2)) }}a)
        by (apply a_tyequiv_pskl; exact Heqτ).
      (* the JOIN, built reflexively at [τ1 → τ2] and subject-transported *)
      assert (Hjoin : {{ empty ⨟ Θ ⊢ˢ
                        (pskl_to_uskl (msubst_pskl ((α1, τ2) :: (β1, τ1) :: κ)
                                         (pskl_var_f β)))
                        ∼ (ptyp_to_bskl_syn (ptyp_arrow τ1 τ2)) }}ad).
      { cbn [msubst_pskl]. rewrite Hlkβ.
        eapply (proj2 (skl_tyequiv_consis_transport Heqs HwfΘ
                         (fun x b (h : binds x b Θ) => h))).
        rewrite pskl_to_uskl_ptyp.
        pose proof (ad_pat_consis_syn_bid HwfA12
                      (ptyp_to_btyp_syn (ptyp_arrow τ1 τ2))
                      (btyp_to_ptyp_ptyp_to_btyp_syn _)) as Hc.
        rewrite btyp_to_bskl_ptyp_to_btyp_syn in Hc.
        exact Hc. }
      (* the two refinements the consistency completeness theorem wants *)
      assert (Hrs : ad_refine_syn_f empty Θ empty
                      (pskl_to_bskl_inh
                         (msubst_pskl ((α1, τ2) :: (β1, τ1) :: κ)
                            (pskl_arrow (pskl_var_f β1) (pskl_var_f α1))))
                      (ptyp_to_bskl_syn (ptyp_arrow τ1 τ2))).
      { cbn [msubst_pskl]. rewrite Hlkβ1, Hlkα1.
        change (pskl_arrow (ptyp_to_pskl τ1) (ptyp_to_pskl τ2))
          with (ptyp_to_pskl (ptyp_arrow τ1 τ2)).
        rewrite <- (mono_inh_eq_syn Hm12).
        apply ad_refine_syn_f_of_plain.
        apply ad_refine_syn_refl_inh.
        apply a_wf_ptyp_to_wf_pskl; exact HwfA12. }
      assert (Hrp : ad_refine_pskl_f empty Θ empty
                      (msubst_pskl ((α1, τ2) :: (β1, τ1) :: κ) (pskl_var_f β))
                      (bskl_to_pskl (ptyp_to_bskl_syn (ptyp_arrow τ1 τ2)))).
      { cbn [msubst_pskl]. rewrite Hlkβ.
        unfold ptyp_to_bskl_syn.
        rewrite bskl_to_pskl_pskl_to_bskl_syn.
        eapply (proj2 (skl_tyequiv_refine_pskl_f_transport Heqs HwfΘ
                         (fun x b (h : binds x b Θ) => h))).
        apply ad_refine_pskl_f_refl.
        apply a_wf_ptyp_to_wf_pskl; exact HwfA12. }
      (* THE CONSISTENCY RUN *)
      destruct (a_consis_complete Hwf0'
                  ltac:(apply a_wf_pskl__arrow; apply a_wf_pskl__var;
                        right; right; left;
                        [ unfold binds; simpl; right; left; reflexivity
                        | unfold binds; simpl; left; reflexivity ])
                  ltac:(apply a_wf_pskl__var; right;
                        destruct Hflex as [Hb | [τx Hb]];
                        [ right; left | right; right; exists τx ];
                        repeat apply binds_cons_3; exact Hb)
                  Hinc' HwfΘ Hjoin Hrs Hrp)
        as [P1 [Θ1 [Hcons Hopt]]].
      (* the SPLIT *)
      assert (Hsplit : {{ Θ0 ⊲ (pskl_var_f β) ▹ (pskl_var_f β1)
                          ⇢ (pskl_var_f α1) ⊣ Θ1 }}a)
        by (apply a_split__flex with (Q := P1);
            [ clear - Hβ1; fsetdec | clear - Hα1; fsetdec | exact Hcons ]).
      (* its own identity increase, extended over the two invented atoms *)
      destruct (a_split_wf Hsplit Hwf0 HwfP0)
        as [Hle01 [Hwf1 [HwfAd HwfBc]]].
      destruct Hle01 as [[κs [Hids Hincs]] _].
      assert (Hincs' : ((α1, ptyp_var_f α1) :: (β1, ptyp_var_f β1) :: κs)
                         ∷ ((α1 ~ abind_flex_mono)
                              ++ (β1 ~ abind_flex_mono) ++ Θ0) ⊑ Θ1).
      { apply a_inc__flex;
          [ | apply a_wf_ptyp__var;
              inversion HwfBc as [ | ? ? ? Hb | | | | ]; subst;
              destruct Hb as [Hc | Hb];
              [ exfalso; clear - Hc; fsetdec | exact Hb ]
            | apply mono_ptyp__var ].
        apply a_inc__flex;
          [ exact Hincs
          | apply a_wf_ptyp__var;
            inversion HwfAd as [ | ? ? ? Hb | | | | ]; subst;
            destruct Hb as [Hc | Hb];
            [ exfalso; clear - Hc; fsetdec | exact Hb ]
          | apply mono_ptyp__var ]. }
      assert (Hids' : is_id_msubst
                        ((α1, ptyp_var_f α1) :: (β1, ptyp_var_f β1) :: κs))
        by (repeat (apply Forall_cons; [ reflexivity | ]); exact Hids).
      destruct (Hopt _ Hids' Hincs') as [ζ [Hζ [Heqv Hprec]]].
      (* peel the two invented atoms off the equivalence *)
      rewrite !msubst_compose_cons in Heqv.
      cbn [msubst_ptyp] in Heqv.
      inversion Heqv as [ | Θx κx1 κx2 Θy αx σ1 σ2 Heqv1 Hteq1
                            Heqa Heqb Heqc Heqd | | | | ]; subst.
      inversion Heqv1 as [ | Θx' κx1' κx2' Θy' αx' σ1' σ2' Heqv0 Hteq0
                             Heqa' Heqb' Heqc' Heqd' | | | | ]; subst.
      exists (ptyp_var_f β1), (ptyp_var_f α1), Θ1, ζ.
      split; [ exact Hsplit | ].
      split; [ exact Hζ | ].
      split.
      { (* the caller's identity IS [κs] *)
        intros κs0 Hid0 Hinc0.
        assert (Heqκ : κs0 = κs)
          by (eapply a_inc_id_msubst_unique;
              [ exact Hinc0 | exact Hincs | exact Hid0 | exact Hids ]).
        subst κs0. exact Heqv0. }
      split.
      { (* the binder's [≡ᵗ] *)
        cbn [msubst_ptyp].
        eapply a_tyequiv__trans;
          [ apply a_tyequiv__sym; exact Hteq0 | ].
        rewrite <- (btyp_to_ptyp_ptyp_to_btyp_inh A).
        eapply ad_refine_syn_inh_tyequiv;
          [ exact Hr1 | exact HwfΘ
          | rewrite <- (mono_inh_eq_syn Hm1); reflexivity
          | reflexivity ]. }
      { (* the codomain's refinement, subject-transported to [ζ α̂1] *)
        cbn [msubst_pskl ptyp_to_pskl].
        eapply ad_refine_syn_f_forget.
        eapply (proj1 (skl_tyequiv_refine_syn_f_transport
                         (a_tyequiv_pskl Hteq1) HwfΘ
                         (fun x b (h : binds x b Θ) => h))).
        rewrite (mono_inh_eq_syn Hm2).
        apply ad_refine_syn_f_of_plain.
        exact Hr2. }
    - (* an ARROW : the IDENTITY split *)
      exists Aa, Ab, Θ0, κ.
      cbn [ptyp_to_pskl msubst_ptyp pskl_to_bskl_inh] in Href.
      destruct (ad_refine_syn_arrow_inv Href) as [HrD HrC].
      split; [ apply a_split__arrow | ].
      split; [ exact Hinc | ].
      split.
      { intros κs Hids Hincs.
        rewrite (msubst_compose_inc_id_r Hinc Hincs Hids Hwf0).
        apply a_inc_equiv_refl; exact Hinc. }
      split.
      { rewrite <- (btyp_to_ptyp_ptyp_to_btyp_inh A).
        eapply ad_refine_syn_inh_tyequiv;
          [ exact HrD | exact HwfΘ | reflexivity | reflexivity ]. }
      { rewrite msubst_pskl_embed_ptyp. exact HrC. }
    - (* a ∀ : an inherited quantifier never refines to an arrow *)
      exfalso. cbn in Href. inversion Href. }
  (* ---- uniform tail : the split's wf and its own identity increase ---- *)
  destruct Hbuilt as [Ad [Bc [Θ1 [ζ [Hsplit [Hζ [Heqv [Heqd Hrefc]]]]]]]].
  destruct (a_split_wf Hsplit Hwf0 HwfP0) as [Hle01 [Hwf1 [HwfAd HwfBc]]].
  destruct Hle01 as [[κs [Hids Hincs]] _].
  exists Ad, Bc, Θ1, κs, ζ.
  repeat split; try assumption.
  - eapply a_wf_ptyp_of_scope_pskl;
      [ exact (a_scope_pskl_of_wf HwfAd)
      | reflexivity ].
  - eapply a_wf_ptyp_of_scope_pskl;
      [ exact (a_scope_pskl_of_wf HwfBc)
      | reflexivity ].
  - apply Heqv; assumption.
Qed.

(* ===================================================================== *)
(*  STEP B — the two [_base] check rows.                                  *)
(*                                                                        *)
(*  Template: [a_typing_complete_abs] MINUS the guess^TY block (the        *)
(*  domain now comes from the SPLIT, not from [a_guess_mono]) PLUS the     *)
(*  suffix discard — whose two obligations are premise (1) [uniq (Ξ++Θ1)]  *)
(*  and premise (2), the latter discharged by the §6.3#2 scoping           *)
(*  invariant at the TERM marker ([a_typing_scope_tm_nil]).               *)
(*  The IH is at a strictly SMALLER SUBJECT (the opened body), so these    *)
(*  rows need no measure guard.                                           *)
(* ===================================================================== *)

Lemma a_typing_complete_abs_check_base : forall Θ0 P0 e κ Θ Ba (B1 : btyp),
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs e) ->
  (forall x M' Θ0' P0' κ' Θ' B',
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
        binds α abind_tvar Θ0') ->
     lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     {{ Θ' ⊢ˢᵈ[ M' ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' (open_exp_wrt_exp e (exp_var_f x))
       κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_arrow Ba B1) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_arrow Ba B1)) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 (exp_abs e) κ Θ (btyp_arrow Ba B1).
Proof.
  intros Θ0 P0 e κ Θ Ba B1 Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst; [ | exfalso; auto ].
  match goal with
  | H : forall x, x `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : a_wf_ptyp Θ ?AA |- _ => rename H into HwfA; rename AA into A
  end.
  inversion Hmod; subst.
  match goal with
  | |- typ_complete_concl _ _ (ptyp_to_pskl ?AA) _ _ _ _ => rename AA into Ain
  end.
  simpl in Hrig.
  assert (Hlce : forall x, lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (intros x; inversion Hlc; auto).
  assert (Hexp0 : {{ Θ0 ⊢ᵉ (exp_abs e) }}a)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc | intros α Hα; left; apply Hrig; exact Hα ]).
  (* ---- 1. THE SPLIT (step A) ---- *)
  destruct (@a_split_complete_tc Θ0 Ain κ Θ A B1 Hwf0 HwfΘ HwfP0 Hinc Href)
    as [Ad [Bc [Θ1 [κs [ζ [Hsplit [Hwf1 [HwfAd [HwfBc
       [Hids [Hincs [Hζ [Heqvs [Heqd Hrefc]]]]]]]]]]]]]].
  destruct (a_split_wf Hsplit Hwf0 HwfP0) as [Hles _].
  (* the skeleton-entry discipline crosses the split *)
  (* ---- 2. one fresh binder ---- *)
  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ1 `union` ftvar_in_aenv Θ1
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A `union` ftvar_in_ptyp Ad
                          `union` ftvar_in_ptyp Bc)) as [x Hx].
  assert (Hwf0x : {{ ⊢ ((x ~ abind_var_typ Ad) ++ Θ1) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAd | exact Hwf1 ]).
  assert (HwfΘx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (Hincx : ζ ∷ ((x ~ abind_var_typ Ad) ++ Θ1)
                    ⊑ ((x ~ abind_var_typ A) ++ Θ)).
  { apply (@a_inc__var Θ1 ζ Θ nil x Ad A);
      [ exact Hζ | apply a_tyequiv__sym; exact Heqd | apply a_suffix__nil ]. }
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x))) by (apply Hlce).
  assert (Hrigx : forall α,
             α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
             binds α abind_tvar ((x ~ abind_var_typ Ad) ++ Θ1)).
  { intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup.
    apply binds_cons_3.
    eapply a_inc_binds_tvar;
      [ exact Hincs | apply Hrig; clear - Hα Hup; fsetdec ]. }
  assert (HwfBcx : {{ ((x ~ abind_var_typ Ad) ++ Θ1) ⨟ empty ⊢ₚₛ
                     (ptyp_to_pskl Bc) }}a)
    by (apply a_wf_pskl_weaken_cons; apply a_wf_ptyp_to_wf_pskl; exact HwfBc).
  (* ---- 3. the IH, once ---- *)
  destruct (IH x mode_tc ((x ~ abind_var_typ Ad) ++ Θ1) (ptyp_to_pskl Bc) ζ
              ((x ~ abind_var_typ A) ++ Θ) B1
              Hwf0x HwfΘx HwfBcx (a_ty_mode_compat__tc _) Hincx Hrigx
              Hlcbody
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact Hrefc
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [B1' [Θout [HrunB HoptB]]].
  (* ---- 4. the body run's identity increase shapes the output ---- *)
  assert (Hexpx : {{ ((x ~ abind_var_typ Ad) ++ Θ1) ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a).
  { apply a_wf_exp_of_tvarish; [ exact Hlcbody | ].
    intros α Hα. left. apply Hrigx. exact Hα. }
  destruct (a_typing_sound HrunB Hwf0x HwfBcx
              (a_ty_mode_compat__tc _) Hexpx)
    as [HleB [HwfOut [HwfB1out _]]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (a_inc_var_inv Hincb) as [Ξ [Ad' [Θ2 [-> [_ [Hsuf Hincb']]]]]].
  assert (HuOut : uniq (Ξ ++ (x ~ abind_var_typ Ad') ++ Θ2))
    by (apply a_wf_aenv_uniq; exact HwfOut).
  assert (Hbx1 : binds x (abind_var_typ Ad)
                   (Ξ ++ (x ~ abind_var_typ Ad') ++ Θ2))
    by (eapply a_typing_tm_le;
        [ exact HrunB | exact I | unfold binds; simpl; auto ]).
  assert (HAd' : abind_var_typ Ad = abind_var_typ Ad')
    by (eapply binds_mid_eq; [ exact Hbx1 | exact HuOut ]).
  inversion HAd'; subst Ad'.
  (* the §6.3#2 scoping invariant, at the TERM marker *)
  pose proof (@a_typing_scope_tm_nil x Ad Θ1 Bc
                (open_exp_wrt_exp e (exp_var_f x)) B1' Ξ Θ2
                HrunB Hwf0x HwfBcx Hexpx HwfOut Hsuf) as Hscope.
  (* ---- 5. the freshness / disjointness pack ---- *)
  assert (HuΞ : uniq Ξ) by (clear - HuOut; solve_uniq).
  assert (HxΞ : x `notin` (dom Ξ `union` ftvar_in_aenv Ξ))
    by (eapply a_wf_aenv_notin_ftv_tm_prefix;
        [ exact Hsuf | exact HwfOut | exact I ]).
  assert (HxΘ2 : x `notin` (dom Θ2 `union` ftvar_in_aenv Θ2))
    by (eapply a_wf_aenv_notin_ftv_tm_below; exact HwfOut).
  assert (HΞΘ2 : forall γ, γ `in` dom Ξ -> γ `notin` dom Θ2)
    by (clear - HuOut; intros γ Hγ; destruct_uniq;
        unfold disjoint in *; simpl_env in *; fsetdec).
  assert (Hdom12 : dom Θ1 [<=] dom Θ2)
    by (eapply a_inc_id_dom_sub_scope; [ exact Hincb' | exact Hidb ]).
  assert (Hwf2 : {{ ⊢ Θ2 }}a)
    by (eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (x ~ abind_var_typ Ad));
        simpl_env; exact HwfOut).
  (* ---- 6. the run ---- *)
  exists (ptyp_arrow Ad B1'), Θ2.
  split.
  { eapply a_typing__abs_check_base with (x := x) (Ξ := Ξ) (Θ1 := Θ1).
    - exact Hsplit.
    - exact Hsuf.
    - apply uniq_app_of;
        [ exact HuΞ | apply a_wf_aenv_uniq; exact Hwf1
        | intros γ Hγ Hc; exact (HΞΘ2 γ Hγ (Hdom12 _ Hc)) ].
    - exact Hscope.
    - rewrite !dom_app. clear - Hx HxΞ HxΘ2. solve_notin.
    - exact HrunB. }
  (* ---- 7. optimality : glue the split and the body ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κs)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincs | exact Hid1 | exact Hids ]).
  assert (Hinc1b : κb ∷ ((x ~ abind_var_typ Ad) ++ Θ1)
                     ⊑ (Ξ ++ (x ~ abind_var_typ Ad) ++ Θ2)).
  { apply (@a_inc__var Θ1 κb Θ2 Ξ x Ad Ad);
      [ exact Hincb'
      | rewrite (msubst_ptyp_id Ad Hidb);
        apply a_tyequiv__refl; eapply a_wf_ptyp_lc; exact HwfAd
      | exact Hsuf ]. }
  destruct (HoptB κb Hidb Hinc1b) as [ζb [Hζb [Heqvb Heqcb]]].
  (* strip the term binder, then the discarded suffix *)
  assert (Hζbm : ζb ∷ (Ξ ++ Θ2) ⊑ Θ)
    by (exact (@a_inc_strip_tm_head Ξ x (abind_var_typ Ad) (abind_var_typ A)
                 Θ2 ζb Θ Hsuf
                 (fun h : abind_is_ty (abind_var_typ Ad) => h)
                 (fun h : abind_is_ty (abind_var_typ A) => h)
                 HwfOut HwfΘx Hζb)).
  destruct (@a_inc_strip_suffix_head Ξ Θ2 ζb Θ Hsuf Hζbm)
    as [ζbp [ζbt [Heqζb [Hdomζp Hζbt]]]].
  assert (Heqvbs : a_inc_equiv Θ1 ζ (msubst_compose ζb κb) Θ)
    by (eapply a_inc_equiv_strip_var_typ_head; [ exact Heqvb | exact I ]).
  assert (Hnotinζp : forall β, β `in` dom κb -> β `notin` dom ζbp).
  { intros β Hβ.
    rewrite Hdomζp.
    intros Hc.
    pose proof (a_inc_dom_sub Hincb' Hβ) as Hβ1.
    exact (HΞΘ2 β Hc (Hdom12 _ Hβ1)). }
  assert (Hcz : msubst_compose ζb κb = msubst_compose ζbt κb)
    by (rewrite Heqζb;
        apply (@msubst_compose_id_prefix_notin ζbp ζbt κb Hidb Hnotinζp)).
  rewrite Hcz in Heqvbs.
  exists ζbt.
  split; [ exact Hζbt | ].
  split.
  { rewrite Heqκ.
    eapply a_inc_equiv_glue with
      (Θmid := Θ1) (Θfin := Θ2) (κ1b := κb) (ζ1 := ζ);
      [ exact Hwf0 | exact Hwf1 | exact Hwf2 | exact HwfΘ
      | exact Hids | exact Hidb
      | intros α Hα;
        pose proof (a_inc_dom_flex Hincs Hα) as Hfα;
        eapply a_inc_flex_dom;
          [ exact Hincb' | exact Hwf1
          | eapply a_inc_id_flex_preserve;
              [ exact Hincs | exact Hids | exact Hwf0 | exact Hfα ] ]
      | exact Hincs | exact Hincb' | exact Hζ | exact Hζbt
      | exact Heqvs | exact Heqvbs ]. }
  (* the arrow equivalence *)
  assert (Hagree : msubst_ptyp ζb B1' = msubst_ptyp ζbt B1').
  { rewrite Heqζb.
    apply msubst_ptyp_agree.
    intros γ Hγ.
    apply msubst_lookup_app_notin.
    rewrite Hdomζp. intros Hc.
    exact (Hscope γ Hc Hγ). }
  assert (Hpush : {{ Θ ⊢ (msubst_ptyp ζ Ad)
                    ≡ᵗ (msubst_ptyp (msubst_compose ζbt κb) Ad) }}a).
  { apply (@a_inc_equiv_msubst_ptyp Ad Θ1 ζ (msubst_compose ζbt κb) Θ
             HwfAd Heqvbs Hwf1
             ltac:(eapply a_inc_msubst_lc; exact Hζ)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζbt
                   | exact (is_id_msubst_values_lc Hidb) ])). }
  assert (Hcid : msubst_ptyp (msubst_compose ζbt κb) Ad = msubst_ptyp ζbt Ad)
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwf1 | exact Hwf2 | exact Hidb | exact Hincb'
        | exact Hζbt | exact HwfAd ]).
  rewrite Hcid in Hpush.
  simpl.
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
  apply a_tyequiv__arrow.
  - eapply a_tyequiv__trans; [ apply a_tyequiv__sym; exact Hpush | exact Heqd ].
  - rewrite <- Hagree.
    eapply a_tyequiv_ctx_mono;
      [ exact Heqcb
      | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ A) Θ);
        intros h; exact h ].
Qed.

(* --- the AbsAnnoCheck (→) row ----------------------------------------- *)

(** THREE stages — the split, the annotation's consistency, the body —
    so the optimality glue is the App row's TRIPLE glue, and the suffix
    discard is the AbsCheck [_base] row's.  ⭐ The consistency is oriented
    SUBJECT = the split's domain, INPUT = the written annotation (the
    reverse of AT-AbsAnno's; docs/PAPER-GAPS.md), and the conclusion's
    domain is the split's [A'] — which is exactly what the appendix's
    [{{ Θ ⊢ A ≡ᵗ A' }}a] premise on sd-AbsAnnoCheck is for. *)
Lemma a_typing_complete_abs_anno_check_base :
  forall Θ0 P0 Aan e κ Θ Ba (B1 : btyp),
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno Aan e) ->
     binds α abind_tvar Θ0) ->
  lc_exp (exp_abs_anno Aan e) ->
  (forall x M' Θ0' P0' κ' Θ' B',
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
        binds α abind_tvar Θ0') ->
     lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     {{ Θ' ⊢ˢᵈ[ M' ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' (open_exp_wrt_exp e (exp_var_f x))
       κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno Aan e) ⦂ (btyp_arrow Ba B1) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_arrow Ba B1)) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 (exp_abs_anno Aan e) κ Θ (btyp_arrow Ba B1).
Proof.
  intros Θ0 P0 Aan e κ Θ Ba B1 Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst; [ | exfalso; auto ].
  match goal with
  | H : forall x, x `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : {{ Θ ⊢ Aan ≡ᵗ ?AA }}a |- _ => rename H into HeqAA'; rename AA into Adec
  end.
  match goal with
  | H : a_wf_ptyp Θ Aan |- _ => rename H into HwfAanΘ
  end.
  inversion Hmod; subst.
  match goal with
  | |- typ_complete_concl _ _ (ptyp_to_pskl ?AA) _ _ _ _ => rename AA into Ain
  end.
  simpl in Hrig.
  assert (HrigA : forall α, α `in` ftvar_in_ptyp Aan ->
             binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlce : forall x, lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (intros x; inversion Hlc; auto).
  assert (HlcA : lc_ptyp Aan) by (inversion Hlc; assumption).
  (* ---- 1. THE SPLIT (step A) ---- *)
  destruct (@a_split_complete_tc Θ0 Ain κ Θ Adec B1 Hwf0 HwfΘ HwfP0 Hinc Href)
    as [Ad [Bc [Θ1 [κs [ζ [Hsplit [Hwf1 [HwfAd [HwfBc
       [Hids [Hincs [Hζ [Heqvs [Heqd Hrefc]]]]]]]]]]]]]].
  destruct (a_split_wf Hsplit Hwf0 HwfP0) as [Hles _].
  assert (HrigA1 : forall α, α `in` ftvar_in_ptyp Aan ->
             binds α abind_tvar Θ1)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincs | apply HrigA; exact Hα ]).
  assert (HwfAan1 : a_wf_ptyp Θ1 Aan)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA1; exact Hα ]).
  assert (HmsAζ : msubst_ptyp ζ Aan = Aan)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζ | exact Hwf1 | exact HrigA1 ]).
  (* ---- 2. the annotation's CONSISTENCY stage ---- *)
  assert (HeqdA : {{ Θ ⊢ (msubst_ptyp ζ Ad) ≡ᵗ Aan }}a)
    by (eapply a_tyequiv__trans;
        [ exact Heqd | apply a_tyequiv__sym; exact HeqAA' ]).
  assert (Heqs : {{ Θ ⊢ (ptyp_to_pskl (msubst_ptyp ζ Ad))
                   ≡ˢ (ptyp_to_pskl Aan) }}a)
    by (apply a_tyequiv_pskl; exact HeqdA).
  assert (Hjoin : {{ empty ⨟ Θ ⊢ˢ
                    (pskl_to_uskl (msubst_pskl ζ (ptyp_to_pskl Ad)))
                    ∼ (btyp_to_bskl (ptyp_to_btyp_inh Aan)) }}ad).
  { rewrite msubst_pskl_embed_ptyp.
    eapply (proj2 (skl_tyequiv_consis_transport Heqs HwfΘ
                     (fun x b (h : binds x b Θ) => h))).
    rewrite pskl_to_uskl_ptyp.
    apply (ad_pat_consis_syn_bid HwfAanΘ (ptyp_to_btyp_inh Aan)
             (btyp_to_ptyp_ptyp_to_btyp_inh Aan)). }
  assert (Hrs : ad_refine_syn_f empty Θ empty
                  (pskl_to_bskl_inh (msubst_pskl ζ (ptyp_to_pskl Aan)))
                  (btyp_to_bskl (ptyp_to_btyp_inh Aan))).
  { rewrite msubst_pskl_embed_ptyp, HmsAζ.
    rewrite <- (pskl_to_bskl_inh_ptyp Aan).
    apply ad_refine_syn_f_of_plain.
    apply ad_refine_syn_refl_inh.
    apply a_wf_ptyp_to_wf_pskl; exact HwfAanΘ. }
  assert (Hrp : ad_refine_pskl_f empty Θ empty
                  (msubst_pskl ζ (ptyp_to_pskl Ad))
                  (bskl_to_pskl (btyp_to_bskl (ptyp_to_btyp_inh Aan)))).
  { rewrite msubst_pskl_embed_ptyp.
    rewrite bskl_to_pskl_btyp_to_bskl, btyp_to_ptyp_ptyp_to_btyp_inh.
    eapply (proj2 (skl_tyequiv_refine_pskl_f_transport Heqs HwfΘ
                     (fun x b (h : binds x b Θ) => h))).
    apply ad_refine_pskl_f_of_plain.
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl; exact HwfAanΘ. }
  assert (HwfAanP1 : {{ Θ1 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Aan) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfAan1).
  assert (HwfAdP1 : {{ Θ1 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Ad) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfAd).
  assert (HwfBcP1 : {{ Θ1 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Bc) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfBc).
  destruct (a_consis_complete Hwf1 HwfAanP1 HwfAdP1 Hζ HwfΘ Hjoin Hrs Hrp)
    as [Qc [Θ2 [HcRun HoptC]]].
  destruct (a_consis_isub_wf_nil HcRun Hwf1 HwfAanP1 HwfAdP1) as [HleC Hwf2].
  destruct HleC as [[κc [Hidc Hincc]] _].
  destruct (HoptC κc Hidc Hincc) as [ζc [Hζc [Heqvc _]]].
  (* ---- 3. the binder and its side data ---- *)
  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ1 `union` ftvar_in_aenv Θ1
                          `union` dom Θ2 `union` ftvar_in_aenv Θ2
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp Aan `union` ftvar_in_ptyp Ad
                          `union` ftvar_in_ptyp Bc)) as [x Hx].
  assert (HrigA2 : forall α, α `in` ftvar_in_ptyp Aan ->
             binds α abind_tvar Θ2)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincc | apply HrigA1; exact Hα ]).
  assert (HwfAan2 : a_wf_ptyp Θ2 Aan)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA2; exact Hα ]).
  assert (Hwf0x : {{ ⊢ ((x ~ abind_var_typ Aan) ++ Θ2) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAan2 | exact Hwf2 ]).
  assert (HwfΘx : {{ ⊢ ((x ~ abind_var_typ Aan) ++ Θ) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAanΘ | exact HwfΘ ]).
  assert (HmsAζc : msubst_ptyp ζc Aan = Aan)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζc | exact Hwf2 | exact HrigA2 ]).
  assert (Hincx : ζc ∷ ((x ~ abind_var_typ Aan) ++ Θ2)
                    ⊑ ((x ~ abind_var_typ Aan) ++ Θ)).
  { apply (@a_inc__var Θ2 ζc Θ nil x Aan Aan);
      [ exact Hζc
      | rewrite HmsAζc; apply a_tyequiv__refl; exact HlcA
      | apply a_suffix__nil ]. }
  (* the codomain refinement, pushed from ζ to ζc (the Anno idiom) *)
  assert (Hσ : msubst_compose ζc κc ∷ Θ1 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hincc | exact Hwf1 | exact Hwf2 | exact Hζc ]).
  assert (HwfQB1 : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B1)) }}a).
  { pose proof (ad_sd_typing_target_wf Hd HwfΘ) as Hw.
    simpl in Hw. inversion Hw; subst.
    rewrite bskl_to_pskl_btyp_to_bskl.
    apply a_wf_ptyp_to_wf_pskl. assumption. }
  assert (Hpp : {{ Θ ⨟ empty ⊢ₚᵣ
                  (msubst_pskl (msubst_compose ζc κc) (ptyp_to_pskl Bc))
                  ⊑ (msubst_pskl ζ (ptyp_to_pskl Bc)) }}ad).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ1) (Δ0 := empty);
      [ exact HwfBcP1 | exact Hwf1 | exact HwfΘ | exact Hζ | exact Hσ
      | exact Heqvc | clear; fsetdec ]. }
  assert (HrefCζ : {{ Θ ⨟ empty ⊢ᵣ
                     (pskl_to_bskl_inh
                        (msubst_pskl (msubst_compose ζc κc) (ptyp_to_pskl Bc)))
                     ⊳ (btyp_to_bskl B1) }}ad).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact Hrefc | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQB1 ]. }
  assert (HmsQ : msubst_pskl (msubst_compose ζc κc) (ptyp_to_pskl Bc)
                 = msubst_pskl ζc (ptyp_to_pskl Bc)).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf1 | exact Hwf2 | exact Hidc | exact Hincc | exact Hζc
      | exact (a_scope_pskl_of_wf HwfBcP1) ]. }
  rewrite HmsQ in HrefCζ.
  (* the remaining IH side data *)
  assert (Hrigx : forall α,
             α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
             binds α abind_tvar ((x ~ abind_var_typ Aan) ++ Θ2)).
  { intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup.
    apply binds_cons_3. eapply a_inc_binds_tvar;
      [ exact Hincc | eapply a_inc_binds_tvar;
        [ exact Hincs | apply Hrig; clear - Hα Hup; fsetdec ] ]. }
  assert (HwfBc2 : {{ Θ2 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Bc) }}a).
  { pose proof (a_wf_pskl_msubst_inc Hincc Hwf1 HwfBcP1
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)) as Hw.
    rewrite (msubst_pskl_id (ptyp_to_pskl Bc) Hidc) in Hw. exact Hw. }
  assert (HwfBcx : {{ ((x ~ abind_var_typ Aan) ++ Θ2) ⨟ empty ⊢ₚₛ
                     (ptyp_to_pskl Bc) }}a)
    by (apply a_wf_pskl_weaken_cons; exact HwfBc2).
  (* ---- 4. the IH, once ---- *)
  destruct (IH x mode_tc ((x ~ abind_var_typ Aan) ++ Θ2) (ptyp_to_pskl Bc) ζc
              ((x ~ abind_var_typ Aan) ++ Θ) B1
              Hwf0x HwfΘx HwfBcx (a_ty_mode_compat__tc _) Hincx Hrigx
              (Hlce x)
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact HrefCζ
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [B1' [Θout [HrunB HoptB]]].
  (* ---- 5. the body run's identity increase shapes the output ---- *)
  assert (Hexpx : {{ ((x ~ abind_var_typ Aan) ++ Θ2) ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a).
  { apply a_wf_exp_of_tvarish; [ exact (Hlce x) | ].
    intros α Hα. left. apply Hrigx. exact Hα. }
  destruct (a_typing_sound HrunB Hwf0x HwfBcx
              (a_ty_mode_compat__tc _) Hexpx)
    as [HleB [HwfOut [HwfB1out _]]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (a_inc_var_inv Hincb) as [Ξ [Aan' [Θ3 [-> [_ [Hsuf Hincb']]]]]].
  assert (HuOut : uniq (Ξ ++ (x ~ abind_var_typ Aan') ++ Θ3))
    by (apply a_wf_aenv_uniq; exact HwfOut).
  assert (Hbx1 : binds x (abind_var_typ Aan)
                   (Ξ ++ (x ~ abind_var_typ Aan') ++ Θ3))
    by (eapply a_typing_tm_le;
        [ exact HrunB | exact I | unfold binds; simpl; auto ]).
  assert (HAan' : abind_var_typ Aan = abind_var_typ Aan')
    by (eapply binds_mid_eq; [ exact Hbx1 | exact HuOut ]).
  inversion HAan'; subst Aan'.
  pose proof (@a_typing_scope_tm_nil x Aan Θ2 Bc
                (open_exp_wrt_exp e (exp_var_f x)) B1' Ξ Θ3
                HrunB Hwf0x HwfBcx Hexpx HwfOut Hsuf) as Hscope.
  (* ---- 6. the freshness / disjointness pack ---- *)
  assert (HuΞ : uniq Ξ) by (clear - HuOut; solve_uniq).
  assert (HxΞ : x `notin` (dom Ξ `union` ftvar_in_aenv Ξ))
    by (eapply a_wf_aenv_notin_ftv_tm_prefix;
        [ exact Hsuf | exact HwfOut | exact I ]).
  assert (HxΘ3 : x `notin` (dom Θ3 `union` ftvar_in_aenv Θ3))
    by (eapply a_wf_aenv_notin_ftv_tm_below; exact HwfOut).
  assert (HΞΘ3 : forall γ, γ `in` dom Ξ -> γ `notin` dom Θ3)
    by (clear - HuOut; intros γ Hγ; destruct_uniq;
        unfold disjoint in *; simpl_env in *; fsetdec).
  assert (Hdom23 : dom Θ2 [<=] dom Θ3)
    by (eapply a_inc_id_dom_sub_scope; [ exact Hincb' | exact Hidb ]).
  assert (Hwf3 : {{ ⊢ Θ3 }}a)
    by (eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (x ~ abind_var_typ Aan));
        simpl_env; exact HwfOut).
  (* ---- 7. the run ---- *)
  exists (ptyp_arrow Ad B1'), Θ3.
  split.
  { eapply a_typing__abs_anno_check_base with (x := x) (Ξ := Ξ)
      (Θ1 := Θ1) (Θ2 := Θ2).
    - exact Hsplit.
    - exists Qc; exact HcRun.
    - exact Hsuf.
    - apply uniq_app_of;
        [ exact HuΞ | apply a_wf_aenv_uniq; exact Hwf2
        | intros γ Hγ Hc; exact (HΞΘ3 γ Hγ (Hdom23 _ Hc)) ].
    - exact Hscope.
    - rewrite !dom_app. clear - Hx HxΞ HxΘ3. solve_notin.
    - exact HrunB. }
  (* ---- 8. optimality : the TRIPLE glue + the suffix strip ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κs)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincs | exact Hid1 | exact Hids ]).
  assert (Hinc1b : κb ∷ ((x ~ abind_var_typ Aan) ++ Θ2)
                     ⊑ (Ξ ++ (x ~ abind_var_typ Aan) ++ Θ3)).
  { apply (@a_inc__var Θ2 κb Θ3 Ξ x Aan Aan);
      [ exact Hincb'
      | rewrite (msubst_ptyp_id Aan Hidb);
        apply a_tyequiv__refl; exact HlcA
      | exact Hsuf ]. }
  destruct (HoptB κb Hidb Hinc1b) as [ζb [Hζb [Heqvb Heqcb]]].
  assert (Hζbm : ζb ∷ (Ξ ++ Θ3) ⊑ Θ)
    by (exact (@a_inc_strip_tm_head Ξ x (abind_var_typ Aan)
                 (abind_var_typ Aan) Θ3 ζb Θ Hsuf
                 (fun h : abind_is_ty (abind_var_typ Aan) => h)
                 (fun h : abind_is_ty (abind_var_typ Aan) => h)
                 HwfOut HwfΘx Hζb)).
  destruct (@a_inc_strip_suffix_head Ξ Θ3 ζb Θ Hsuf Hζbm)
    as [ζbp [ζbt [Heqζb [Hdomζp Hζbt]]]].
  assert (Heqvbs : a_inc_equiv Θ2 ζc (msubst_compose ζb κb) Θ)
    by (eapply a_inc_equiv_strip_var_typ_head; [ exact Heqvb | exact I ]).
  assert (Hnotinζp : forall β, β `in` dom κb -> β `notin` dom ζbp).
  { intros β Hβ.
    rewrite Hdomζp.
    intros Hc.
    pose proof (a_inc_dom_sub Hincb' Hβ) as Hβ2.
    exact (HΞΘ3 β Hc (Hdom23 _ Hβ2)). }
  assert (Hcz : msubst_compose ζb κb = msubst_compose ζbt κb)
    by (rewrite Heqζb;
        apply (@msubst_compose_id_prefix_notin ζbp ζbt κb Hidb Hnotinζp)).
  rewrite Hcz in Heqvbs.
  (* the inner glue : stages 2 + 3 *)
  assert (Hglue23 : a_inc_equiv Θ1 ζ (msubst_compose ζbt κc) Θ).
  { eapply a_inc_equiv_glue with
      (Θmid := Θ2) (Θfin := Θ3) (κ1b := κb) (ζ1 := ζc);
      [ exact Hwf1 | exact Hwf2 | exact Hwf3 | exact HwfΘ
      | exact Hidc | exact Hidb
      | intros α Hα;
        pose proof (a_inc_dom_flex Hincc Hα) as Hfα;
        eapply a_inc_flex_dom;
          [ exact Hincb' | exact Hwf2
          | eapply a_inc_id_flex_preserve;
              [ exact Hincc | exact Hidc | exact Hwf1 | exact Hfα ] ]
      | exact Hincc | exact Hincb' | exact Hζc | exact Hζbt
      | exact Heqvc | exact Heqvbs ]. }
  assert (Hinc23 : msubst_compose κb κc ∷ Θ1 ⊑ Θ3)
    by (eapply a_inc_compose;
        [ exact Hincc | exact Hwf1 | exact Hwf2 | exact Hincb' ]).
  rewrite (msubst_compose_id_id Hidc Hidb) in Hinc23.
  exists ζbt.
  split; [ exact Hζbt | ].
  split.
  { rewrite Heqκ.
    eapply a_inc_equiv_glue with
      (Θmid := Θ1) (Θfin := Θ3) (κ1b := κc) (ζ1 := ζ);
      [ exact Hwf0 | exact Hwf1 | exact Hwf3 | exact HwfΘ
      | exact Hids | exact Hidc
      | intros α Hα;
        pose proof (a_inc_dom_flex Hincs Hα) as Hfα;
        eapply a_inc_flex_dom;
          [ exact Hinc23 | exact Hwf1
          | eapply a_inc_id_flex_preserve;
              [ exact Hincs | exact Hids | exact Hwf0 | exact Hfα ] ]
      | exact Hincs | exact Hinc23 | exact Hζ | exact Hζbt
      | exact Heqvs | exact Hglue23 ]. }
  (* ---- 9. the arrow equivalence ---- *)
  assert (Hagree : msubst_ptyp ζb B1' = msubst_ptyp ζbt B1').
  { rewrite Heqζb.
    apply msubst_ptyp_agree.
    intros γ Hγ.
    apply msubst_lookup_app_notin.
    rewrite Hdomζp. intros Hc.
    exact (Hscope γ Hc Hγ). }
  assert (Hpush : {{ Θ ⊢ (msubst_ptyp ζ Ad)
                    ≡ᵗ (msubst_ptyp (msubst_compose ζbt κc) Ad) }}a).
  { apply (@a_inc_equiv_msubst_ptyp Ad Θ1 ζ (msubst_compose ζbt κc) Θ
             HwfAd Hglue23 Hwf1
             ltac:(eapply a_inc_msubst_lc; exact Hζ)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζbt
                   | exact (is_id_msubst_values_lc Hidc) ])). }
  assert (Hcid : msubst_ptyp (msubst_compose ζbt κc) Ad = msubst_ptyp ζbt Ad)
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwf1 | exact Hwf3 | exact Hidc | exact Hinc23
        | exact Hζbt | exact HwfAd ]).
  rewrite Hcid in Hpush.
  simpl.
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
  apply a_tyequiv__arrow.
  - eapply a_tyequiv__trans; [ apply a_tyequiv__sym; exact Hpush | exact Heqd ].
  - rewrite <- Hagree.
    eapply a_tyequiv_ctx_mono;
      [ exact Heqcb
      | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ Aan) Θ);
        intros h; exact h ].
Qed.

(* ===================================================================== *)
(*  THEOREM 4 — thm:complete-type-inference.  The induction is pure glue   *)
(*  over the twelve step lemmas, on the LEXICOGRAPHIC measure              *)
(*  [(size_exp e, size_btyp B)]: ten rows recurse at a strictly smaller    *)
(*  SUBJECT (any second component is then allowed), and only the two       *)
(*  [_step] check rows recurse at the SAME subject — they peel one ∀ off   *)
(*  the declarative result, so the second component drops.                 *)
(* ===================================================================== *)

Lemma a_typing_complete_gen : forall n m e M Θ0 P0 κ Θ B,
  size_exp e < n -> size_btyp B < m ->
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
  lc_exp e ->
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 e κ Θ B.
Proof.
  induction n as [ | n IHn ];
    [ intros m e M Θ0 P0 κ Θ B Hszn; exfalso; clear - Hszn; lia | ].
  induction m as [ | m IHm ];
    intros e M Θ0 P0 κ Θ B Hszn Hszm Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
           Hlc Hd Href;
    [ exfalso; clear - Hszm; lia | ].
  destruct e as [ | i | x | e0 | Aan e0 | e1 e2 | e0 Aan | e0 ];
    simpl in Hszn.
  - (* unit *) apply a_typing_complete_unit; assumption.
  - (* a bound variable has no rule *) inversion Hd.
  - (* var *) apply a_typing_complete_var; assumption.
  - (* abs : the mode, then (at TC) the declarative result's shape *)
    destruct M as [ | | M' ].
    + (* TI *)
      apply a_typing_complete_abs; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                  | clear; lia ].
    + (* TC : ∀ ⟹ [_step], arrow ⟹ [_base], everything else has no rule *)
      destruct B as [ | i2 | γ | Bd Bc | B' | B' ];
        try solve [ inversion Hd ]; simpl in Hszm.
      * (* arrow : the [_base] row *)
        apply a_typing_complete_abs_check_base; try assumption.
        intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
        apply IHn with (m := S (size_btyp B2)); try assumption;
          try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                    | clear; lia ].
      * (* ∀ (inherited) : the [_step] row — the SAME subject, smaller B *)
        apply a_typing_complete_abs_check_step; try assumption.
        intros M2 Θ02 P02 κ2 Θ2 B2 HszB2; intros.
        apply IHm; try assumption;
          try solve [ simpl; clear - Hszn; lia
                    | clear - Hszm HszB2; simpl in HszB2; lia ].
    + (* FN *)
      apply a_typing_complete_abs; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                  | clear; lia ].
  - (* abs_anno : the same dispatch *)
    destruct M as [ | | M' ].
    + apply a_typing_complete_abs_anno; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                  | clear; lia ].
    + destruct B as [ | i2 | γ | Bd Bc | B' | B' ];
        try solve [ inversion Hd ]; simpl in Hszm.
      * apply a_typing_complete_abs_anno_check_base; try assumption.
        intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
        apply IHn with (m := S (size_btyp B2)); try assumption;
          try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                    | clear; lia ].
      * apply a_typing_complete_abs_anno_check_step; try assumption.
        intros M2 Θ02 P02 κ2 Θ2 B2 HszB2; intros.
        apply IHm; try assumption;
          try solve [ simpl; clear - Hszn; lia
                    | clear - Hszm HszB2; simpl in HszB2; lia ].
    + apply a_typing_complete_abs_anno; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                  | clear; lia ].
  - (* app *)
    pose proof (size_exp_min e1) as Hm1.
    pose proof (size_exp_min e2) as Hm2.
    apply a_typing_complete_app; try assumption.
    + intros M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ clear - Hszn Hm2; lia | clear; lia ].
    + intros M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ clear - Hszn Hm1; lia | clear; lia ].
  - (* anno *)
    apply a_typing_complete_anno; try assumption.
    intros M2 Θ02 P02 κ2 Θ2 B2; intros.
    apply IHn with (m := S (size_btyp B2)); try assumption;
      try solve [ clear - Hszn; lia | clear; lia ].
  - (* freeze : the rule pins the mode *)
    destruct M as [ | | M' ]; [ inversion Hd | | inversion Hd ].
    inversion Hmod; subst.
    apply a_typing_complete_freeze; try assumption.
    intros M2 Θ02 P02 κ2 Θ2 B2; intros.
    apply IHn with (m := S (size_btyp B2)); try assumption;
      try solve [ clear - Hszn; lia | clear; lia ].
Qed.

(** ⭐ THEOREM 4 (thm:complete-type-inference).  Whenever the DECLARATIVE
    system types [e] at [B] under any solution [κ] of the question
    [(Θ0; M; P0)], the ALGORITHM's run succeeds, and for every identity
    increase out of the question context the run's answer factors through
    the solution: a composing witness [ζ] whose composite is equivalent to
    [κ] and whose image of the run's result is Θ-EQUIVALENT to the
    declarative type.

    Hypotheses beyond the paper's statement are the same
    WF-SIDE-CONDITIONS.md externals theorem 3 carries: well-formedness of
    the two contexts and the input skeleton, mode compatibility, and the term
    side condition — an annotation is SOURCE syntax, so its type variables are
    RIGID.  ⚙ NOT [lc_exp e]: unlike theorem 3, this one has an [ad_sd_typing]
    premise, and that judgement exhibits its own subject as well formed.  The
    [a_pat] analogue does NOT hold — [ad_pat__anno] has no premise about its
    subterm at all — so [a_pat_complete] keeps its [lc]. *)
Theorem a_typing_complete : forall e M Θ0 P0 κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  exists A1 Θ1,
    a_typing M Θ0 P0 e A1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         {{ Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a).
Proof.
  intros e M Θ0 P0 κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Had Href.
  (* [lc_exp e] is NOT a hypothesis: a derivation exhibits its own subject as a
     well-formed term ([ad_sd_typing_wf_exp], prop_soundness_typing.v §12h), and
     a well-formed term is locally closed. *)
  pose proof (a_wf_exp_lc (ad_sd_typing_wf_exp Had)) as Hlc.
  eapply a_typing_complete_gen
    with (n := S (size_exp e)) (m := S (size_btyp B));
    try eassumption;
    clear; lia.
Qed.
