(** Splitting: lifting from [a_*] to supply-threaded [e_*] derivations. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.ltac_utils.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.prop_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.prop_solve.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.subtyping.prop_solve_rel.
Require Import src.fresco.ext_algo.lifting.prop_lift_context.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.consistency.prop_consis_rename.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.consistency.prop_consis.
Require Import src.fresco.ext_algo.subtyping.def_sub.
Require Import src.fresco.ext_algo.subtyping.prop_sub.
Require Import src.fresco.ext_algo.subtyping.prop_extract.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_wf_preservation.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.ext_algo.typing.def_pat.
Require Import src.fresco.ext_algo.typing.prop_pat.
Require Import src.fresco.algo.basic.prop_mod_compat.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.typing.prop_completeness_pat.
Require Import src.fresco.algo.typing.prop_soundness_typing.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.ext_algo.typing.def_typing.
Require Import src.fresco.ext_algo.typing.prop_typing.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

Require Export src.fresco.ext_algo.lifting.prop_lift_solve.
Require Export src.fresco.ext_algo.lifting.prop_lift_consis.
Require Export src.fresco.ext_algo.lifting.prop_lift_sub.


(* ===================================================================== *)
(*  §11  ⭐⭐ THE a_split RUNG — [a_split] lifts to [e_split], all 3 rows    *)
(*  (2026-08-21)                                                          *)
(*                                                                        *)
(*  Two of the three rows invent nothing and move nothing.  The third,     *)
(*  [Split-Flex], is [W-Solve]'s shape at a smaller scale: it invents TWO  *)
(*  flexibles and calls CONSISTENCY at Δ = ∅, so [lift_consis_nil] is the  *)
(*  whole of its content.  ⭐ NO restriction is needed — the two invented   *)
(*  atoms SURVIVE into the output ([auc_dom_mono_consis]), so the motive's  *)
(*  own block premise already puts them off ρ's left column.               *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  THE MOTIVE — the §8c.32 discipline, at [a_split]'s shape              *)
(*                                                                        *)
(*  [a_split] has ONE input skeleton and TWO outputs, and its only         *)
(*  generative row calls CONSISTENCY at Δ = ∅ — so [lift_consis_nil] is    *)
(*  the whole of its content, exactly as it was for [S-Check]/[S-Arrow].   *)
(* ===================================================================== *)

Definition lift_split_post (Θ0 : aenv) (P Q : pskl) (Θ1 : aenv)
    (S0 : atoms) (Θ0' : aenv) (P0' : pskl)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' P' Q',
    {{ S0 ↝ S1 ⊨ Θ0' ⊲ P0' ▹ P' ⇢ Q' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_pskl (ρe ++ ρ) V P P'
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_split_concl (Θ0 : aenv) (P0 P Q : pskl) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' P0' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    lift_split_post Θ0 P Q Θ1 S0 Θ0' P0' ρ V.

Theorem a_split_rel_e : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a ->
  lift_split_concl Θ0 P0 P Q Θ1.
Proof.
  intros Θ0 P0 P Q Θ1 HD.
  destruct HD as [ Θa Pa Qa | Θa | Θa Θb α β α1 Qc Hβf Hα1f Hc ];
    intros S0 Θ0' P0' ρ V HrΘ HrP0 Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0.
  - (* Split-Arrow : nothing is invented, nothing moves *)
    inversion HrP0 as [ | | | A1 A2 Pa2 Qa2 HrPa HrQa | | | ]; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', Pa2, Qa2.
    split; [ apply e_split__arrow | ]. simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ exact HrPa | ].
    split; [ exact HrQa | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* Split-Hole *)
    inversion HrP0; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', pskl_ghost, pskl_ghost.
    split; [ apply e_split__ghost | ]. simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ apply rel_pskl__ghost | ].
    split; [ apply rel_pskl__ghost | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* ⭐⭐ Split-Flex — the generative row.  Same shape as [W-Solve]: the two
       invented atoms SURVIVE into the output, so the motive's own block
       premise puts them off ρ's left column and NO restriction is needed. *)
    inversion HrP0 as [ | | ax α2 Hat | | | | ]; subst.
    destruct (atom_fresh S0) as [b2 Hb2].
    destruct (atom_fresh (add b2 S0)) as [a2 Ha2].
    assert (Hsc : ftvar_in_aenv Θa [<=] dom Θa)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    pose proof (dom_subset_ftvar_in_aenv Θa) as Hds.
    assert (Hβnd : β `notin` dom Θa) by (clear - Hβf Hds; fsetdec).
    assert (Hα1nd : α1 `notin` dom Θa) by (clear - Hα1f Hds; fsetdec).
    assert (Hα1β : α1 <> β) by (intros Ex; rewrite Ex in Hα1f;
                                clear - Hα1f; fsetdec).
    (* the two invented atoms reach the output *)
    assert (Hdm : dom ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θa)
                  [<=] dom Θb)
      by (exact (auc_dom_mono_consis Hc)).
    assert (HβΘ1 : β `in` dom Θb)
      by (clear - Hdm; simpl in Hdm; fsetdec).
    assert (Hα1Θ1 : α1 `in` dom Θb)
      by (clear - Hdm; simpl in Hdm; fsetdec).
    assert (Hβcl : β `notin` cols_l ρ)
      by (apply Hblk; [ exact HβΘ1 | exact Hβnd ]).
    assert (Hα1cl : α1 `notin` cols_l ρ)
      by (apply Hblk; [ exact Hα1Θ1 | exact Hα1nd ]).
    assert (HβV : β `notin` V) by (clear - Hβf Hscp; fsetdec).
    assert (Hα1V : α1 `notin` V) by (clear - Hα1f Hscp; fsetdec).
    assert (Hb2V : b2 `notin` V) by (clear - Hb2 Hcov; fsetdec).
    assert (Ha2V : a2 `notin` V) by (clear - Ha2 Hcov; fsetdec).
    assert (Hb2cr : b2 `notin` cols_r ρ) by (clear - Hb2 Hcov; fsetdec).
    assert (Ha2cr : a2 `notin` cols_r ρ) by (clear - Ha2 Hcov; fsetdec).
    assert (Ha2b2 : a2 <> b2) by (clear - Ha2; fsetdec).
    assert (Hb2d : b2 `notin` dom Θ0') by (clear - Hb2 HdΘ; fsetdec).
    assert (Ha2d : a2 `notin` dom Θ0') by (clear - Ha2 HdΘ; fsetdec).
    remember ((α1, a2) :: (β, b2) :: ρ) as ρ1 eqn:Eρ1.
    assert (Hρ1incl : forall a b, In (a, b) ρ -> In (a, b) ρ1)
      by (subst ρ1; intros a b Hin; right; right; exact Hin).
    (* ---- the extended contexts and the extended relation ---- *)
    assert (HrΘ1 : rel_aenv ρ1 V
              ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θa)
              ((a2 ~ abind_flex_mono) ++ (b2 ~ abind_flex_mono) ++ Θ0')).
    { apply rel_aenv__cons;
        [ apply rel_atom__pair; subst ρ1; left; reflexivity
        | constructor | ].
      apply rel_aenv__cons;
        [ apply rel_atom__pair; subst ρ1; right; left; reflexivity
        | constructor | ].
      eapply rel_aenv_mono;
        [ exact HrΘ | exact Hρ1incl | intros x Hx; exact Hx ]. }
    assert (Hagr1 : flex_agree_rel ρ1 V
              ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θa)
              ((a2 ~ abind_flex_mono) ++ (b2 ~ abind_flex_mono) ++ Θ0')).
    { split.
      - intros x HxV.
        assert (Hxα1 : x <> α1) by (intros ->; contradiction).
        assert (Hxβ : x <> β) by (intros ->; contradiction).
        assert (Hxa2 : x <> a2) by (intros ->; contradiction).
        assert (Hxb2 : x <> b2) by (intros ->; contradiction).
        rewrite ! a_flex_tvar_cons_other by assumption.
        exact (proj1 Hagr x HxV).
      - intros x0 y0 Hin. subst ρ1.
        destruct Hin as [E1 | [E2 | Hin]].
        + injection E1 as -> ->. split; intros _; left; unfold binds;
            simpl; left; reflexivity.
        + injection E2 as -> ->. split; intros _; left; unfold binds;
            simpl; right; left; reflexivity.
        + assert (Hxα1 : x0 <> α1)
            by (intros ->; apply Hα1cl; eapply cols_l_in; exact Hin).
          assert (Hxβ : x0 <> β)
            by (intros ->; apply Hβcl; eapply cols_l_in; exact Hin).
          assert (Hya2 : y0 <> a2)
            by (intros ->; apply Ha2cr; eapply cols_r_in; exact Hin).
          assert (Hyb2 : y0 <> b2)
            by (intros ->; apply Hb2cr; eapply cols_r_in; exact Hin).
          rewrite ! a_flex_tvar_cons_other by assumption.
          exact (proj2 Hagr x0 y0 Hin). }
    assert (Hinj1 : rel_inj ρ1 V).
    { subst ρ1. apply rel_inj_push;
        [ apply rel_inj_push; [ exact Hinj | exact Hb2V | exact Hb2cr ]
        | exact Ha2V | simpl; clear - Ha2cr Ha2b2; fsetdec ]. }
    assert (Hfun1 : rel_fun ρ1 V
              (dom ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θa))).
    { subst ρ1. eapply rel_fun_weaken;
        [ apply rel_fun_push;
            [ apply rel_fun_push; [ exact Hfun | exact HβV | exact Hβcl ]
            | exact Hα1V | simpl; clear - Hα1cl Hα1β; fsetdec ]
        | intros u v Hu; exact Hu
        | simpl; clear; fsetdec ]. }
    (* ---- the premise's packages ---- *)
    assert (Hwf1 : {{ ⊢ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono)
                          ++ Θa) }}a).
    { apply a_wf_aenv__flex; [ simpl; clear - Hα1f Hds Hα1β; fsetdec | ].
      apply a_wf_aenv__flex; [ exact Hβnd | exact Hwf ]. }
    assert (Huq2' : uniq ((a2 ~ abind_flex_mono) ++ (b2 ~ abind_flex_mono)
                           ++ Θ0'))
      by (clear - Huq2p Ha2d Hb2d Ha2b2; solve_uniq).
    assert (Hftv2' : ftvar_in_aenv ((a2 ~ abind_flex_mono)
                       ++ (b2 ~ abind_flex_mono) ++ Θ0')
                     [<=] add a2 (add b2 S0))
      by (simpl; clear - Hftv2; fsetdec).
    assert (Hscp1 : V [<=] ftvar_in_aenv ((α1 ~ abind_flex_mono)
                      ++ (β ~ abind_flex_mono) ++ Θa))
      by (simpl; clear - Hscp; fsetdec).
    assert (Hblk1 : forall a, a `in` dom Θb ->
              a `notin` dom ((α1 ~ abind_flex_mono)
                             ++ (β ~ abind_flex_mono) ++ Θa) ->
              a `notin` cols_l ρ1).
    { intros a Ha Hn. simpl in Hn. subst ρ1. simpl.
      assert (Hn0 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn; fsetdec ]).
      clear - Hn Hn0. fsetdec. }
    assert (HdΘ1 : dom ((a2 ~ abind_flex_mono) ++ (b2 ~ abind_flex_mono)
                         ++ Θ0') [<=] add a2 (add b2 S0))
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hcov1 : V ∪ cols_r ρ1 [<=] add a2 (add b2 S0))
      by (subst ρ1; simpl; clear - Hcov; fsetdec).
    assert (Hα2S : α2 `in` S0).
    { inversion Hat as [ u v Hin | u Hin ]; subst;
        [ assert (Hyr : α2 `in` cols_r ρ) by (eapply cols_r_in; exact Hin);
          clear - Hyr Hcov; fsetdec
        | clear - Hin Hcov; fsetdec ]. }
    assert (HcovP1 : ftvar_in_pskl (pskl_arrow (pskl_var_f b2)
                                      (pskl_var_f a2))
                     ∪ ftvar_in_pskl (pskl_var_f α2)
                     [<=] add a2 (add b2 S0))
      by (simpl; clear - Hα2S; fsetdec).
    assert (Hwfp1 : {{ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono)
                        ++ Θa) ⨟ empty ⊢ₚₛ
                       (pskl_arrow (pskl_var_f β) (pskl_var_f α1)) }}a).
    { apply a_wf_pskl__arrow;
        apply a_wf_pskl__var; right; left; unfold binds; simpl;
        solve [ left; reflexivity | right; left; reflexivity ]. }
    assert (Hwfp1s : {{ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono)
                         ++ Θa) ⨟ empty ⊢ₚₛ (pskl_var_f α) }}a)
      by (eapply a_wf_pskl_weaken;
          [ intros z bd Hb; apply binds_app_3; apply binds_app_3; exact Hb
          | exact Hwfp0 ]).
    assert (HrP1 : rel_pskl ρ1 V (pskl_arrow (pskl_var_f β) (pskl_var_f α1))
                     (pskl_arrow (pskl_var_f b2) (pskl_var_f a2))).
    { subst ρ1. constructor; apply rel_pskl__var_f; apply rel_atom__pair;
        [ right; left; reflexivity | left; reflexivity ]. }
    assert (HrPs : rel_pskl ρ1 V (pskl_var_f α) (pskl_var_f α2))
      by (apply rel_pskl__var_f; eapply rel_atom_incl;
          [ exact Hat | exact Hρ1incl ]).
    destruct (lift_consis_nil Hc HrΘ1 HrP1 HrPs Hagr1 Hinj1 Hfun1 Hwf1
                Huq2' Hftv2' Hscp1 Hblk1 HdΘ1 Hcov1 HcovP1 Hwfp1 Hwfp1s)
      as (S1 & ρe & Θ1' & Qc' & De & HrΘo & Hagro & HrQo & Hexto & Hdomo).
    exists S1, (ρe ++ (α1, a2) :: (β, b2) :: nil), Θ1',
      (pskl_var_f b2), (pskl_var_f a2).
    split.
    { apply e_split__flex with (Q := Qc');
        [ exact Hb2 | clear - Ha2; fsetdec | subst ρ1; exact De ]. }
    subst ρ1.
    assert (Erw : (ρe ++ (α1, a2) :: (β, b2) :: nil) ++ ρ
                  = ρe ++ (α1, a2) :: (β, b2) :: ρ)
      by (rewrite app_assoc; reflexivity).
    rewrite Erw.
    split; [ exact HrΘo | ].
    split; [ exact Hagro | ].
    split.
    { apply rel_pskl__var_f. apply rel_atom__pair.
      apply in_or_app. right. right. left. reflexivity. }
    split.
    { apply rel_pskl__var_f. apply rel_atom__pair.
      apply in_or_app. right. left. reflexivity. }
    split.
    { eapply rel_ext_app;
        [ | exact Hexto | | | ].
      - (* the two-pair rel_ext *)
        unfold rel_ext. split; [ | split ].
        + intros a b Hin. destruct Hin as [E | [E | []]];
            injection E as -> ->;
            [ split; [ clear - Hα1f; fsetdec | clear - Ha2; fsetdec ]
            | split; [ clear - Hβf; fsetdec | clear - Hb2; fsetdec ] ].
        + intros a1 a3 b Hin1 Hin2.
          destruct Hin1 as [E1 | [E1 | []]]; destruct Hin2 as [E2 | [E2 | []]];
            inversion E1; inversion E2; subst;
            solve [ reflexivity | exfalso; congruence ].
        + intros a b1 b3 Hin1 Hin2.
          destruct Hin1 as [E1 | [E1 | []]]; destruct Hin2 as [E2 | [E2 | []]];
            inversion E1; inversion E2; subst;
            solve [ reflexivity | exfalso; congruence ].
      - simpl. clear; fsetdec.
      - clear; fsetdec.
      - intros a b Hin. destruct Hin as [E | [E | []]];
          injection E as -> ->;
          [ split; [ simpl; clear; fsetdec | clear; fsetdec ]
          | split; [ simpl; clear; fsetdec | clear; fsetdec ] ]. }
    (* the two SIDE-2 atoms reach the output too, by the same route the
       [S-Arrow] row uses: soundness, then consistency's own dom-mono *)
    assert (HcovE : ftvar_in_aenv ((a2 ~ abind_flex_mono)
                      ++ (b2 ~ abind_flex_mono) ++ Θ0')
                    ∪ ftvar_in_pskl (pskl_arrow (pskl_var_f b2)
                                       (pskl_var_f a2))
                    ∪ ftvar_in_pskl (pskl_var_f α2) ∪ empty ∪ empty
                    [<=] add a2 (add b2 S0))
      by (clear - Hftv2' HcovP1; simpl in *; fsetdec).
    assert (Hdm2 : dom ((a2 ~ abind_flex_mono) ++ (b2 ~ abind_flex_mono)
                        ++ Θ0') [<=] dom Θ1').
    { pose proof (e_consis_sound De Huq2' HcovE) as Ha2s.
      exact (auc_dom_mono_consis Ha2s). }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hdomo _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + destruct Hin as [E | [E | []]]; injection E as -> ->;
        [ split; [ exact Hα1Θ1 | clear - Hdm2; simpl in Hdm2; fsetdec ]
        | split; [ exact HβΘ1 | clear - Hdm2; simpl in Hdm2; fsetdec ] ].
Qed.
