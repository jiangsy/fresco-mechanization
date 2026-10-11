(** Skeleton inference: lifting from [a_*] to supply-threaded [e_*] derivations. *)

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
Require Export src.fresco.ext_algo.lifting.prop_lift_split.


(* ===================================================================== *)
(*  §12  ⭐⭐⭐ THE a_pat RUNG — [a_pat] lifts to [e_pat], all 10 rows        *)
(*  (2026-08-22, §8c.44–§8c.45)                                            *)
(*                                                                        *)
(*  ⭐ The motive relates EXPRESSIONS ([rel_exp], §13d of prop_lift_context): *)
(*  the abs rows open the body at a term variable fresh only for the       *)
(*  CONTEXT while [e_pat]'s draw theirs from the SUPPLY, and that premise  *)
(*  is part of the induction, so the renaming route is closed (§8c.33).    *)
(*  ⚙ [a_wf_exp] and [a_sk_mode_compat] ride along as side-1 premises —    *)
(*  the first is what puts an annotation's type variables in the context,  *)
(*  the second is what makes the SK split CONTEXT-IDENTITY                 *)
(*  ([a_split_sk_shape]) at the abs rows.                                  *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  THE MOTIVE — the §8c.32 discipline, plus the EXPRESSION               *)
(*                                                                        *)
(*  ⭐ Side 2's expression is RELATED, not equal: the abs rows open at a    *)
(*  term variable the two sides choose differently (side 1 fresh for the   *)
(*  CONTEXT, side 2 fresh for the SUPPLY).  ⚙ [a_wf_exp] is what puts the  *)
(*  annotations' type variables in the context, which is what the four     *)
(*  [a_sub]-calling rows need to satisfy [lift_sub_concl]'s subject-wf.    *)
(* ===================================================================== *)

Definition lift_pat_post (Θ0 : aenv) (Q : pskl) (Θ1 : aenv)
    (S0 : atoms) (m : mode) (Θ0' : aenv) (P0' : pskl) (e' : exp)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' Q',
    {{ S0 ↝ S1 ⊨ Θ0' ⊢ˢ[ m ; P0' ] e' ⦂ Q' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_pat_concl (m : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (Q : pskl) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' P0' e' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    rel_exp ρ V e e' ->
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
    ftvar_in_pskl P0' ∪ ftvar_in_exp e' ∪ fvar_in_exp e' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⊢ᵉ e }}a ->
    a_sk_mode_compat m P0 ->
    lift_pat_post Θ0 Q Θ1 S0 m Θ0' P0' e' ρ V.

(** ⚙ The four [a_sub]-calling rows, factored: they differ only in the
    SUBJECT skeleton and in the [e_pat] constructor they finish with. *)
Lemma lift_pat_sub : forall m Θ0 Θ1 P0 Ps Q,
  {{ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] Ps ⩽ Q ⊣ Θ1 }}a ->
  forall S0 Θ0' P0' Ps' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    rel_pskl ρ V Ps Ps' ->
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
    ftvar_in_pskl P0' ∪ ftvar_in_pskl Ps' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ Ps }}a ->
    lift_sub_post Θ0 Q Θ1 S0 a_sub_mode_sk m Θ0' P0' Ps' ρ V.
Proof.
  intros m Θ0 Θ1 P0 Ps Q HD.
  exact ((proj1 a_sub_sub_flex_rel_e) _ _ _ _ _ _ _ HD).
Qed.

(* ===================================================================== *)
(*  ⭐⭐ THE SHARED ABS CORE — restrict at the TERM variable, push the      *)
(*  pair, run the body, then PEEL the term entry from both outputs.        *)
(*                                                                        *)
(*  The four abs rows differ only in their PRELUDE (split / consis-chk /   *)
(*  nothing) and in the [e_pat] constructor they finish with; the          *)
(*  restrict-push-run-peel is one lemma, exactly as [lift_sub_flex_peel]   *)
(*  was for the walk.  ⚙ The term variable does NOT reach the output       *)
(*  (§8c.40's discriminator), hence [restrict_pairs]; the junk suffix [Ξ]  *)
(*  DOES survive into the output, hence NO [restrict_l].                   *)
(* ===================================================================== *)

Lemma lift_pat_abs_core : forall m' Θb Q0 e Q Ξ Θc x bd,
  {{ ((x ~ bd) ++ Θb) ⊢ˢ[ m' ; Q0 ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q
     ⊣ (Ξ ++ (x ~ bd) ++ Θc) }}a ->
  lift_pat_concl m' ((x ~ bd) ++ Θb) Q0 (open_exp_wrt_exp e (exp_var_f x)) Q
    (Ξ ++ (x ~ bd) ++ Θc) ->
  a_suffix Ξ ->
  x `notin` dom (Ξ ++ Θb) ∪ dom Θc ∪ fvar_in_exp e ->
  x `notin` ftvar_in_exp e ->
  abind_is_tm bd ->
  ftvar_in_abind bd [<=] dom Θb ->
  a_sk_mode_compat m' Q0 ->
  forall S0 Θb' Q0' e' bd' ρ V,
  rel_aenv ρ V Θb Θb' ->
  rel_pskl ρ V Q0 Q0' ->
  rel_exp ρ V e e' ->
  rel_abind ρ V bd bd' ->
  abind_is_tm bd' ->
  ftvar_in_abind bd' [<=] S0 ->
  flex_agree_rel ρ V Θb Θb' ->
  rel_inj ρ V ->
  rel_fun ρ V (dom Θb) ->
  {{ ⊢ ((x ~ bd) ++ Θb) }}a ->
  {{ Θb ⨟ empty ⊢ₚₛ Q0 }}a ->
  {{ ((x ~ bd) ++ Θb) ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a ->
  uniq Θb' ->
  ftvar_in_aenv Θb' [<=] S0 ->
  V [<=] ftvar_in_aenv Θb ->
  (forall a, a `in` dom (Ξ ++ Θc) -> a `notin` dom Θb -> a `notin` cols_l ρ) ->
  dom Θb' [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl Q0' ∪ ftvar_in_exp e' ∪ fvar_in_exp e' [<=] S0 ->
  exists S1 x2 ρe Ξ2 Θc2' Q',
    x2 `notin` S0
    /\ {{ (add x2 S0) ↝ S1 ⊨ ((x2 ~ bd') ++ Θb') ⊢ˢ[ m' ; Q0' ]
          (open_exp_wrt_exp e' (exp_var_f x2)) ⦂ Q'
          ⊣ (Ξ2 ++ (x2 ~ bd') ++ Θc2') }}e
    /\ a_suffix Ξ2
    /\ rel_aenv (ρe ++ ρ) V (Ξ ++ Θc) (Ξ2 ++ Θc2')
    /\ flex_agree_rel (ρe ++ ρ) V (Ξ ++ Θc) (Ξ2 ++ Θc2')
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv Θb) S0
    /\ (forall a b, In (a, b) ρe ->
          a `in` dom (Ξ ++ Θc) /\ b `in` dom (Ξ2 ++ Θc2'))
    /\ dom Θb' [<=] dom (Ξ2 ++ Θc2').
Proof.
  intros m' Θb Q0 e Q Ξ Θc x bd Hbody IH Hsuf Hxf Hxe Htm Hbdf Hmod'.
  intros S0 Θb' Q0' e' bd' ρ V HrΘ HrQ0 HrE Hrbd Htm' Hbd'f Hagr Hinj Hfun
    HwfX HwfQ0 Hwfeo Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP.
  destruct (atom_fresh S0) as [x2 Hx2].
  simpl_env in Hxf.
  assert (HxΞ : x `notin` dom Ξ) by (clear - Hxf; fsetdec).
  assert (HxΘb : x `notin` dom Θb) by (clear - Hxf; fsetdec).
  assert (HxΘc : x `notin` dom Θc) by (clear - Hxf; fsetdec).
  assert (Hxfv : x `notin` fvar_in_exp e) by (clear - Hxf; fsetdec).
  assert (HwfΘb : {{ ⊢ Θb }}a)
    by (eapply a_wf_aenv_strip_prefix with (Ξ := x ~ bd); simpl_env;
        exact HwfX).
  assert (Hsc0 : ftvar_in_aenv Θb [<=] dom Θb)
    by (apply a_wf_aenv_ftv_dom; exact HwfΘb).
  assert (HxftvΘb : x `notin` ftvar_in_aenv Θb)
    by (clear - HxΘb Hsc0; fsetdec).
  assert (HxV : x `notin` V) by (clear - Hscp HxftvΘb; fsetdec).
  assert (Hxbd : x `notin` ftvar_in_abind bd) by (clear - Hbdf HxΘb; fsetdec).
  assert (HxQ0 : x `notin` ftvar_in_pskl Q0).
  { intros Hin. pose proof (a_wf_pskl_ftv_binds HwfQ0 Hin) as Htv;
    apply HxΘb; apply a_binds_tvar_in_dom; exact Htv. }
  assert (Hx2V : x2 `notin` V) by (clear - Hx2 Hcov; fsetdec).
  assert (Hx2Θb' : x2 `notin` dom Θb') by (clear - Hx2 HdΘ; fsetdec).
  assert (Hx2ftv : x2 `notin` ftvar_in_aenv Θb') by (clear - Hx2 Hftv2; fsetdec).
  assert (Hx2bd' : x2 `notin` ftvar_in_abind bd')
    by (clear - Hx2 Hbd'f; fsetdec).
  (* ---- the restriction, and the push ---- *)
  assert (Hρrincl : forall a b, In (a, b) (restrict_pairs x x2 ρ) ->
            In (a, b) ρ)
    by (intros a b Hin; eapply restrict_pairs_incl; exact Hin).
  assert (Hclr : cols_l (restrict_pairs x x2 ρ) [<=] cols_l ρ)
    by apply cols_l_restrict_pairs.
  assert (Hcrr : cols_r (restrict_pairs x x2 ρ) [<=] cols_r ρ)
    by apply cols_r_restrict_pairs.
  assert (Hxl : x `notin` cols_l (restrict_pairs x x2 ρ))
    by apply restrict_pairs_notin_l.
  assert (Hx2r : x2 `notin` cols_r (restrict_pairs x x2 ρ))
    by apply restrict_pairs_notin_r.
  assert (Hρ1incl : forall a b, In (a, b) (restrict_pairs x x2 ρ) ->
            In (a, b) ((x, x2) :: restrict_pairs x x2 ρ))
    by (intros a b Hin; right; exact Hin).
  assert (HrΘ1 : rel_aenv ((x, x2) :: restrict_pairs x x2 ρ) V
                   ((x ~ bd) ++ Θb) ((x2 ~ bd') ++ Θb')).
  { apply rel_aenv__cons;
      [ apply rel_atom__pair; left; reflexivity | | ].
    - eapply rel_abind_mono;
        [ eapply rel_abind_restrict; [ exact Hrbd | exact Hxbd | exact Hx2bd' ]
        | exact Hρ1incl | intros z Hz; exact Hz ].
    - eapply rel_aenv_mono;
        [ eapply rel_aenv_restrict; [ exact HrΘ | exact HxftvΘb | exact Hx2ftv ]
        | exact Hρ1incl | intros z Hz; exact Hz ]. }
  assert (Hx2Q0' : x2 `notin` ftvar_in_pskl Q0')
    by (clear - Hx2 HcovP; fsetdec).
  assert (HrQ01 : rel_pskl ((x, x2) :: restrict_pairs x x2 ρ) V Q0 Q0')
    by (eapply rel_pskl_mono;
        [ eapply rel_pskl_restrict;
            [ exact HrQ0 | exact HxQ0 | exact Hx2Q0' ]
        | exact Hρ1incl | intros z Hz; exact Hz ]).
  assert (HrEo : rel_exp ((x, x2) :: restrict_pairs x x2 ρ) V
                   (open_exp_wrt_exp e (exp_var_f x))
                   (open_exp_wrt_exp e' (exp_var_f x2))).
  { apply rel_exp_open_pair. apply rel_exp_restrict;
      [ exact HrE | clear - Hxfv Hxe; fsetdec
      | clear - Hx2 HcovP; fsetdec ]. }
  assert (Hagr1 : flex_agree_rel ((x, x2) :: restrict_pairs x x2 ρ) V
                    ((x ~ bd) ++ Θb) ((x2 ~ bd') ++ Θb')).
  { apply flex_agree_rel_push_tm;
      [ eapply flex_agree_rel_weaken;
          [ exact Hagr | exact Hρrincl | intros z Hz; exact Hz ]
      | apply abind_is_tm_nonflex; exact Htm
      | apply abind_is_tm_nonflex; exact Htm'
      | exact HxΘb | exact Hx2Θb' ]. }
  assert (Hinj1 : rel_inj ((x, x2) :: restrict_pairs x x2 ρ) V)
    by (apply rel_inj_push;
        [ eapply rel_inj_sub; [ exact Hinj | exact Hρrincl ]
        | exact Hx2V | exact Hx2r ]).
  assert (Hfun1 : rel_fun ((x, x2) :: restrict_pairs x x2 ρ) V
                    (dom ((x ~ bd) ++ Θb))).
  { simpl. apply rel_fun_push;
      [ eapply rel_fun_weaken;
          [ exact Hfun | exact Hρrincl | intros z Hz; exact Hz ]
      | exact HxV | exact Hxl ]. }
  assert (Huq2X : uniq ((x2 ~ bd') ++ Θb'))
    by (clear - Huq2p Hx2Θb'; solve_uniq).
  assert (Hftv2X : ftvar_in_aenv ((x2 ~ bd') ++ Θb') [<=] add x2 S0)
    by (simpl; clear - Hftv2 Hbd'f; fsetdec).
  assert (HscpX : V [<=] ftvar_in_aenv ((x ~ bd) ++ Θb))
    by (simpl; clear - Hscp; fsetdec).
  assert (HblkX : forall a, a `in` dom (Ξ ++ (x ~ bd) ++ Θc) ->
            a `notin` dom ((x ~ bd) ++ Θb) ->
            a `notin` cols_l ((x, x2) :: restrict_pairs x x2 ρ)).
  { intros a Ha Hn. simpl_env in Ha. simpl_env in Hn. simpl.
    assert (Hne : a <> x) by (clear - Hn; fsetdec).
    assert (Ha' : a `in` dom (Ξ ++ Θc))
      by (simpl_env; clear - Ha Hne; fsetdec).
    assert (Hc : a `notin` cols_l ρ)
      by (apply Hblk; [ exact Ha' | clear - Hn; fsetdec ]).
    clear - Hne Hc Hclr. fsetdec. }
  assert (HdΘX : dom ((x2 ~ bd') ++ Θb') [<=] add x2 S0)
    by (simpl; clear - HdΘ; fsetdec).
  assert (HcovX : V ∪ cols_r ((x, x2) :: restrict_pairs x x2 ρ)
                  [<=] add x2 S0)
    by (simpl; clear - Hcov Hcrr; fsetdec).
  assert (HcovPX : ftvar_in_pskl Q0'
                   ∪ ftvar_in_exp (open_exp_wrt_exp e' (exp_var_f x2))
                   ∪ fvar_in_exp (open_exp_wrt_exp e' (exp_var_f x2))
                   [<=] add x2 S0).
  { pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e' (exp_var_f x2)) as Hu1.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper e' (exp_var_f x2)) as Hu2.
    simpl in Hu1, Hu2. clear - HcovP Hu1 Hu2. fsetdec. }
  assert (HwfQ0X : {{ ((x ~ bd) ++ Θb) ⨟ empty ⊢ₚₛ Q0 }}a)
    by (eapply a_wf_pskl_weaken;
        [ intros z b0 Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
  destruct (IH (add x2 S0) ((x2 ~ bd') ++ Θb') Q0'
              (open_exp_wrt_exp e' (exp_var_f x2))
              ((x, x2) :: restrict_pairs x x2 ρ) V
              HrΘ1 HrQ01 HrEo Hagr1 Hinj1 Hfun1 HwfX Huq2X Hftv2X HscpX
              HblkX HdΘX HcovX HcovPX HwfQ0X Hwfeo Hmod')
    as (S1 & ρe & Θout' & Q' & De & HrΘo & Hagro & HrQo & Hexto & Hdomo).
  (* ---- side 1's output wf, and the body's dom-mono ---- *)
  destruct (a_pat_sound Hbody HwfX HwfQ0X Hmod' Hwfeo) as [Hle [HwfOut _]].
  assert (HuqOut : uniq (Ξ ++ (x ~ bd) ++ Θc))
    by (apply a_wf_aenv_uniq; exact HwfOut).
  assert (HwfΞΘc : {{ ⊢ (Ξ ++ Θc) }}a)
    by (eapply a_wf_aenv_strip_tm_mid;
        [ | exact HwfOut ];
        destruct bd; simpl in Htm |- *; intuition).
  assert (HftvΞΘc : ftvar_in_aenv (Ξ ++ Θc) [<=] dom (Ξ ++ Θc))
    by (apply a_wf_aenv_ftv_dom; exact HwfΞΘc).
  assert (HxftvOut : x `notin` ftvar_in_aenv (Ξ ++ Θc))
    by (simpl_env in HftvΞΘc; clear - HftvΞΘc HxΞ HxΘc; fsetdec).
  (* ---- side 2's packages at the body ---- *)
  pose proof (e_pat_supply_grows De) as Hgr.
  assert (HcovEX : ftvar_in_aenv ((x2 ~ bd') ++ Θb') ∪ ftvar_in_pskl Q0'
                   ∪ fvar_in_exp (open_exp_wrt_exp e' (exp_var_f x2))
                   ∪ ftvar_in_exp (open_exp_wrt_exp e' (exp_var_f x2))
                   [<=] add x2 S0)
    by (clear - Hftv2X HcovPX; fsetdec).
  destruct (e_pat_sound De Huq2X HcovEX) as (HaDe & HuqOut2 & HftvOut2 & HftQ').
  (* ---- the full pair list's injectivity, and the two exclusions ---- *)
  assert (Hinjout : rel_inj (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V)
    by (eapply rel_inj_app; [ exact Hinj1 | exact Hexto | exact HcovX ]).
  assert (Hxρe : forall b, ~ In (x, b) ρe).
  { intros b Hin. destruct Hexto as [Hxfr _].
    destruct (Hxfr _ _ Hin) as [Hna _].
    apply Hna. simpl. clear; fsetdec. }
  assert (Hx2ρe : forall a, ~ In (a, x2) ρe).
  { intros a Hin. destruct Hexto as [Hxfr _].
    destruct (Hxfr _ _ Hin) as [_ Hnb].
    apply Hnb. clear; fsetdec. }
  assert (Hxonly : forall y,
            rel_atom (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V x y ->
            y = x2).
  { intros y Hat. inversion Hat as [ a0 b0 Hin | a0 HinV ]; subst.
    - apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
      + exfalso. exact (Hxρe _ Hin).
      + inversion Ehd; reflexivity.
      + exfalso. apply Hxl. eapply cols_l_in; exact Hin.
    - exfalso. exact (HxV HinV). }
  (* ---- SPLIT the output at the junk suffix, then at the term entry ---- *)
  destruct (@rel_aenv_app_inv_l Ξ
              (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V
              ((x ~ bd) ++ Θc) Θout' HrΘo)
    as (Ξ2 & Θrest & Eout & HrΞ2 & HrTail).
  subst Θout'.
  destruct (rel_aenv_cons_inv_l HrTail)
    as (b & bd2' & Θc2' & E2 & Hab2 & Hbd2 & HrΘc2).
  subst Θrest.
  assert (Eb : b = x2) by (apply Hxonly; exact Hab2).
  subst b.
  (* ---- the term entry is PRESERVED, so side 2's mid binding is [bd'] ---- *)
  assert (Hb'out : binds x2 bd' (Ξ2 ++ (x2 ~ bd2') ++ Θc2')).
  { apply (a_pat_tm_le HaDe);
      [ exact Htm' | unfold binds; simpl; left; reflexivity ]. }
  assert (Ebd : bd2' = bd').
  { assert (Hbmid : binds x2 bd2' (Ξ2 ++ (x2 ~ bd2') ++ Θc2'))
      by (unfold binds; apply in_or_app; right; left; reflexivity).
    eapply binds_unique; [ exact Hbmid | exact Hb'out | exact HuqOut2 ]. }
  subst bd2'.
  (* ---- side 2's junk, and the term atom, off the stripped output ---- *)
  assert (Hx2ftvOut : x2 `notin` ftvar_in_aenv (Ξ2 ++ Θc2')).
  { intros Hin.
    assert (HrOut : rel_aenv (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V
                      (Ξ ++ Θc) (Ξ2 ++ Θc2'))
      by (apply rel_aenv_app; [ exact HrΞ2 | exact HrΘc2 ]).
    destruct (rel_aenv_ftv_corr_r HrOut Hin) as (a & Ha & Hat).
    assert (Ea : a = x).
    { apply (Hinjout a x x2 Hat). apply rel_atom__pair.
      apply in_or_app. right. left. reflexivity. }
    subst a. exact (HxftvOut Ha). }
  (* ---- the answer's pieces ---- *)
  assert (HrOut : rel_aenv (ρe ++ (x, x2) :: restrict_pairs x x2 ρ) V
                    (Ξ ++ Θc) (Ξ2 ++ Θc2'))
    by (apply rel_aenv_app; [ exact HrΞ2 | exact HrΘc2 ]).
  assert (Hincl : forall a b0,
            In (a, b0) (restrict_pairs x x2
                          (ρe ++ (x, x2) :: restrict_pairs x x2 ρ)) ->
            In (a, b0) (ρe ++ ρ)).
  { intros a b0 Hin.
    assert (Hane : a <> x).
    { intros ->.
      apply (@restrict_pairs_notin_l x x2
               (ρe ++ (x, x2) :: restrict_pairs x x2 ρ)).
      eapply cols_l_in; exact Hin. }
    apply restrict_pairs_incl in Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
    - apply in_or_app; left; exact Hin.
    - exfalso. injection Ehd as E1 E2x. apply Hane. symmetry. exact E1.
    - apply in_or_app; right. apply Hρrincl. exact Hin. }
  assert (HrFinal : rel_aenv (ρe ++ ρ) V (Ξ ++ Θc) (Ξ2 ++ Θc2')).
  { eapply rel_aenv_mono;
      [ eapply rel_aenv_restrict;
          [ exact HrOut | exact HxftvOut | exact Hx2ftvOut ]
      | exact Hincl | intros z Hz; exact Hz ]. }
  (* ---- the yield: drop the pair via ftvar-correspondence ---- *)
  assert (HwfQout : {{ (Ξ ++ (x ~ bd) ++ Θc) ⨟ empty ⊢ₚₛ Q }}a)
    by (eapply a_pat_output_wf;
        [ exact Hbody | exact HwfX | exact HwfQ0X | exact Hmod'
        | exact Hwfeo ]).
  assert (HxQ : x `notin` ftvar_in_pskl Q).
  { intros Hin. pose proof (a_wf_pskl_ftv_binds HwfQout Hin) as Htv.
    assert (Hbx : binds x bd (Ξ ++ (x ~ bd) ++ Θc))
      by (unfold binds; apply in_or_app; right; left; reflexivity).
    destruct Htv as [Hb | [Hb | [τ Hb]]];
      pose proof (binds_unique _ _ _ _ _ Hb Hbx HuqOut) as E;
      subst bd; simpl in Htm; contradiction. }
  assert (Hx2Q' : x2 `notin` ftvar_in_pskl Q').
  { intros Hin.
    destruct (rel_pskl_ftv_corr_r HrQo Hin) as (a & Ha & Hat).
    assert (Ea : a = x).
    { apply (Hinjout a x x2 Hat). apply rel_atom__pair.
      apply in_or_app. right. left. reflexivity. }
    subst a. exact (HxQ Ha). }
  assert (HrQfin : rel_pskl (ρe ++ ρ) V Q Q').
  { eapply rel_pskl_mono;
      [ eapply rel_pskl_restrict; [ exact HrQo | exact HxQ | exact Hx2Q' ]
      | exact Hincl | intros z Hz; exact Hz ]. }
  assert (Hextfin : rel_ext ρe (ftvar_in_aenv Θb) S0).
  { destruct Hexto as [Hxfr [Hri Hlf]]. unfold rel_ext.
    split; [ | split ].
    - intros a b0 Hin. destruct (Hxfr _ _ Hin) as [Hna Hnb].
      simpl in Hna.
      split; [ clear - Hna; fsetdec | clear - Hnb; fsetdec ].
    - exact Hri.
    - exact Hlf. }
  assert (Hagrfin : flex_agree_rel (ρe ++ ρ) V (Ξ ++ Θc) (Ξ2 ++ Θc2')).
  { eapply rel_aenv_flex_agree_ext;
      [ exact HrFinal | exact Hinj | exact Hfun | exact Hextfin
      | apply dom_subset_ftvar_in_aenv
      | clear - Hscp Hsc0; fsetdec | exact Hcov | exact Hblk ]. }

  (* ---- assemble ---- *)
  exists S1, x2, ρe, Ξ2, Θc2', Q'.
  split; [ exact Hx2 | ].
  split; [ exact De | ].
  split; [ eapply rel_aenv_suffix; [ exact HrΞ2 | exact Hsuf ] | ].
  split; [ exact HrFinal | ].
  split; [ exact Hagrfin | ].
  split; [ exact HrQfin | ].
  split; [ exact Hextfin | ].
  split.
  { intros a b0 Hin.
    destruct (Hdomo _ _ Hin) as [Hd1 Hd2].
    assert (Hane : a <> x) by (intros ->; exact (Hxρe _ Hin)).
    assert (Hbne : b0 <> x2) by (intros ->; exact (Hx2ρe _ Hin)).
    simpl_env in Hd1. simpl_env in Hd2. simpl_env.
    split; [ clear - Hd1 Hane; fsetdec | clear - Hd2 Hbne; fsetdec ]. }
  (* ---- side 2's dom-mono, term entry stripped from both sides ---- *)
  pose proof (a_pat_dom_mono HaDe) as Hdm2.
  intros a Ha.
  assert (Hane : a <> x2) by (intros ->; exact (Hx2Θb' Ha)).
  assert (Ha1 : a `in` dom ((x2 ~ bd') ++ Θb'))
    by (simpl_env; clear - Ha; fsetdec).
  apply Hdm2 in Ha1. simpl_env in Ha1. simpl_env.
  clear - Ha1 Hane. fsetdec.
Qed.

Theorem a_pat_rel_e : forall m Θ0 P0 e Q Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}a ->
  lift_pat_concl m Θ0 P0 e Q Θ1.
Proof.
  intros m Θ0 P0 e Q Θ1 HD.
  induction HD as
    [ m0 Θa Θb P0a Pa Hsub
    | m0 Θa Θb P0a x A Qa Hb Hsub
    | m0 Θa Θb P0a x Ps Qa Hb Hsub
    | m0 Θa Θb P0a ea A Qa Hsub
    | Θa ea Qa Θb Hp IHp
    | x m0 Θa Θb Θc P0a Pa Q0 ea Qa Ξ Hne Hsp Hsuf Hxf Hp IHp
    | x m0 Θa Θb Θc Θd P0a Pa Q0 A ea Qa Ξ Hne Hsp Hchk Hsuf Hxf Hp IHp
    | x Θa Θb ea Qa Ξ Hsuf Hxf Hp IHp
    | x Θa Θb A ea Qa Ξ Hsuf Hxf Hp IHp
    | m0 Θa Θb Θc P0a Q0 Pa Qa e1 e2 Hp2 IHp2 Hp1 IHp1 ];
    intros S0 Θ0' P0' e' ρ V HrΘ HrP0 HrE Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfe Hmod.
  - (* AP-Unit *)
    inversion HrE; subst.
    assert (HcovS : ftvar_in_pskl P0' ∪ ftvar_in_pskl pskl_unit [<=] S0)
      by (simpl; clear - HcovP; simpl in HcovP; fsetdec).
    destruct (lift_pat_sub Hsub HrΘ HrP0 (rel_pskl__unit ρ V) Hagr Hinj Hfun
                Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovS Hwfp0
                (a_wf_pskl__unit Θa empty))
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_pat__unit; exact De | ].
    split; [ exact HrΘ1 | ]. split; [ exact Hagr1 | ].
    split; [ exact HrQ | ]. split; [ exact Hext | ]. exact Hdom1.
  - (* AP-Var, type-bound *)
    inversion HrE as [ | | x1 x2 Hax | | | | | ]; subst.
    destruct (@rel_aenv_binds_pin ρ V Θa Θ0' x x2 (abind_var_typ A)
                HrΘ Hfun Hb Hax) as (bd2 & Habd & Hb2).
    inversion Habd as [ | | | A1 A2 HrA | ]; subst.
    assert (HcovS : ftvar_in_pskl P0' ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] S0).
    { pose proof (@rel_pskl_ftv_r ρ V (ptyp_to_pskl A) (ptyp_to_pskl A2) HrA)
        as HA2.
      clear - HcovP HA2 Hcov. simpl in HcovP. fsetdec. }
    assert (HwfA : {{ Θa ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl;
          eapply a_wf_aenv_binds_var_typ_wf; [ exact Hwf | exact Hb ]).
    destruct (lift_pat_sub Hsub HrΘ HrP0 HrA Hagr Hinj Hfun
                Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovS Hwfp0 HwfA)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ eapply e_pat__var; [ exact Hb2 | exact De ] | ].
    split; [ exact HrΘ1 | ]. split; [ exact Hagr1 | ].
    split; [ exact HrQ | ]. split; [ exact Hext | ]. exact Hdom1.
  - (* AP-Var, skeleton-bound *)
    inversion HrE as [ | | x1 x2 Hax | | | | | ]; subst.
    destruct (@rel_aenv_binds_pin ρ V Θa Θ0' x x2 (abind_var_skl Ps)
                HrΘ Hfun Hb Hax) as (bd2 & Habd & Hb2).
    inversion Habd as [ | | | | Ps1 Ps2 HrPs ]; subst.
    assert (HcovS : ftvar_in_pskl P0' ∪ ftvar_in_pskl Ps2 [<=] S0).
    { pose proof (@rel_pskl_ftv_r ρ V Ps Ps2 HrPs) as HP2.
      clear - HcovP HP2 Hcov. simpl in HcovP. fsetdec. }
    assert (HwfP : {{ Θa ⨟ empty ⊢ₚₛ Ps }}a)
      by (eapply a_wf_aenv_binds_var_skl_wf; [ exact Hwf | exact Hb ]).
    destruct (lift_pat_sub Hsub HrΘ HrP0 HrPs Hagr Hinj Hfun
                Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovS Hwfp0 HwfP)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ eapply e_pat__var_skl; [ exact Hb2 | exact De ] | ].
    split; [ exact HrΘ1 | ]. split; [ exact Hagr1 | ].
    split; [ exact HrQ | ]. split; [ exact Hext | ]. exact Hdom1.
  - (* AP-Anno *)
    inversion HrE as [ | | | | | | eb1 eb2 A1 A2 HrEb HrA | ]; subst.
    inversion Hwfe as [ | | Θq eq Aq HwfAq Hwfeq | | | | ]; subst.
    assert (HcovS : ftvar_in_pskl P0' ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] S0)
      by (simpl in HcovP; rewrite ftvar_ptyp_to_pskl;
          clear - HcovP; fsetdec).
    assert (HwfA : {{ Θa ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfAq).
    destruct (lift_pat_sub Hsub HrΘ HrP0 HrA Hagr Hinj Hfun
                Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovS Hwfp0 HwfA)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_pat__anno; exact De | ].
    split; [ exact HrΘ1 | ]. split; [ exact Hagr1 | ].
    split; [ exact HrQ | ]. split; [ exact Hext | ]. exact Hdom1.
  - (* AP-Freeze *)
    inversion HrE as [ | | | | | | | eb1 eb2 HrEb ]; subst.
    inversion HrP0; subst.
    inversion Hwfe as [ | | | Θq eq Hwfeq | | | ]; subst.
    assert (HcovE : ftvar_in_pskl pskl_ghost ∪ ftvar_in_exp eb2
                    ∪ fvar_in_exp eb2 [<=] S0)
      by (simpl in HcovP |- *; clear - HcovP; fsetdec).
    destruct (IHp S0 Θ0' pskl_ghost eb2 ρ V HrΘ (rel_pskl__ghost ρ V) HrEb
                Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovE
                (a_wf_pskl__ghost Θa empty) Hwfeq a_sk_mode_compat__ti)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_pat__freeze; exact De | ].
    split; [ exact HrΘ1 | ]. split; [ exact Hagr1 | ].
    split; [ exact HrQ | ]. split; [ exact Hext | ]. exact Hdom1.
  - (* ⭐⭐ AP-Abs — the SK split is CONTEXT-IDENTITY ([a_split_sk_shape]),
       so the row is one CORE call per shape. *)
    destruct (a_split_sk_shape Hsp Hmod) as [HeqΘ Hshape]. subst Θb.
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb
                     | A1 A2 eb1 eb2 HrA HrEb
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb HrA | eb1 eb2 HrEb ]; subst.
    assert (Hfe : ftvar_in_exp ea [<=] dom Θa)
      by (pose proof (a_wf_exp_ftv_dom Hwfe) as Hd; simpl in Hd; exact Hd).
    pose proof Hxf as Hxf2. simpl_env in Hxf2.
    assert (HxΘa : x `notin` dom Θa) by (clear - Hxf2; fsetdec).
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfe HxΘa; fsetdec).
    assert (Hwfeo : {{ ((x ~ abind_var_skl Pa) ++ Θa) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a)
      by (apply a_wf_exp_weaken_cons; eapply a_wf_exp_abs_pick; exact Hwfe).
    destruct Hshape as [[EP0 [EP EQ0]] | EP0].
    + (* the ◇ shape: P0 = P = Q0 = ◇ *)
      subst P0a Pa Q0.
      inversion HrP0; subst.
      assert (Hmodc : a_sk_mode_compat (decr_mode m0) pskl_ghost).
      { destruct (a_sk_mode_compat_ghost_inv Hmod) as [-> | ->];
          [ apply a_sk_mode_compat__ti | congruence ]. }
      assert (HwfXc : {{ ⊢ ((x ~ abind_var_skl pskl_ghost) ++ Θa) }}a)
        by (apply a_wf_aenv__var;
            [ exact HxΘa | apply a_wf_pskl__ghost | exact Hwf ]).
      assert (HcovPc : ftvar_in_pskl pskl_ghost ∪ ftvar_in_exp eb2
                       ∪ fvar_in_exp eb2 [<=] S0)
        by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
      assert (Hbdf0 : ftvar_in_abind (abind_var_skl pskl_ghost) [<=] dom Θa)
        by (simpl; clear; fsetdec).
      assert (Hbdf0' : ftvar_in_abind (abind_var_skl pskl_ghost) [<=] S0)
        by (simpl; clear; fsetdec).
      destruct (@lift_pat_abs_core (decr_mode m0) Θa pskl_ghost ea Qa Ξ Θc x
                  (abind_var_skl pskl_ghost)
                  Hp IHp Hsuf Hxf Hxe I Hbdf0 Hmodc
                  S0 Θ0' pskl_ghost eb2 (abind_var_skl pskl_ghost) ρ V
                  HrΘ (rel_pskl__ghost ρ V) HrEb
                  (rel_abind__var_skl (rel_pskl__ghost ρ V)) I Hbdf0'
                  Hagr Hinj Hfun HwfXc
                  (a_wf_pskl__ghost Θa empty) Hwfeo Huq2p Hftv2 Hscp Hblk
                  HdΘ Hcov HcovPc)
        as (S1 & x2 & ρe & Ξ2 & Θc2' & Q' & Hx2S0 & De & HsufΞ2 & HrF
            & HagrF & HrQ' & HextF & HdomF & Hdm2).
      exists S1, ρe, (Ξ2 ++ Θc2'), (pskl_arrow pskl_ghost Q').
      split.
      { eapply e_pat__abs;
          [ exact Hne | apply e_split__ghost | exact HsufΞ2
          | exact Hx2S0 | exact De ]. }
      split; [ exact HrF | ].
      split; [ exact HagrF | ].
      split; [ constructor; [ apply rel_pskl__ghost | exact HrQ' ] | ].
      split; [ exact HextF | ]. exact HdomF.
    + (* the ARROW shape: P0 = P → Q0 *)
      subst P0a.
      inversion HrP0 as [ | n0 | u0 v0 Hu0 | B1 B2 Pa' Q0c' HrPa HrQ0c
                        | B3 B4 Hu1 | | B5 B6 Hu2 ]; subst.
      inversion Hwfp0 as [ Θx Δx | Θx Δx αx Hbx | Θx Δx Xa Xb HwfPa HwfQ0a
                         | Lx Θx Δx Xp Hallx | Θx Δx
                         | Θx Δx Xp Hgx Hwix ]; subst.
      destruct (a_sk_mode_compat_arrow_inv Hmod) as (m'' & Em & Hmodc0).
      subst m0.
      assert (Hmodc : a_sk_mode_compat (decr_mode (mode_fn m'')) Q0)
        by (simpl; exact Hmodc0).
      assert (HbdfPa : ftvar_in_abind (abind_var_skl Pa) [<=] dom Θa).
      { simpl. intros z Hz.
        apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds HwfPa Hz). }
      assert (HwfXc : {{ ⊢ ((x ~ abind_var_skl Pa) ++ Θa) }}a)
        by (apply a_wf_aenv__var; [ exact HxΘa | exact HwfPa | exact Hwf ]).
      assert (Hbd'f : ftvar_in_abind (abind_var_skl Pa') [<=] S0)
        by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
      assert (HcovPc : ftvar_in_pskl Q0c' ∪ ftvar_in_exp eb2
                       ∪ fvar_in_exp eb2 [<=] S0)
        by (simpl in HcovP; clear - HcovP; fsetdec).
      destruct (@lift_pat_abs_core (decr_mode (mode_fn m'')) Θa Q0 ea Qa Ξ Θc
                  x (abind_var_skl Pa)
                  Hp IHp Hsuf Hxf Hxe I HbdfPa Hmodc
                  S0 Θ0' Q0c' eb2 (abind_var_skl Pa') ρ V
                  HrΘ HrQ0c HrEb
                  (rel_abind__var_skl HrPa) I Hbd'f
                  Hagr Hinj Hfun HwfXc HwfQ0a Hwfeo Huq2p Hftv2 Hscp Hblk
                  HdΘ Hcov HcovPc)
        as (S1 & x2 & ρe & Ξ2 & Θc2' & Q' & Hx2S0 & De & HsufΞ2 & HrF
            & HagrF & HrQ' & HextF & HdomF & Hdm2).
      exists S1, ρe, (Ξ2 ++ Θc2'), (pskl_arrow Pa' Q').
      split.
      { eapply e_pat__abs;
          [ exact Hne | apply e_split__arrow | exact HsufΞ2
          | exact Hx2S0 | exact De ]. }
      split; [ exact HrF | ].
      split; [ exact HagrF | ].
      split.
      { constructor; [ | exact HrQ' ].
        eapply rel_pskl_mono;
          [ exact HrPa | intros u v Hu; apply in_or_app; right; exact Hu
          | intros u Hu; exact Hu ]. }
      split; [ exact HextF | ]. exact HdomF.
  - (* ⭐⭐ AP-AbsAnno — the consis-chk between the (identity) split and the
       body: [lift_consis_nil], widen, the CORE, then [rel_ext_app] — the
       AP-App composition one binder in. *)
    destruct (a_split_sk_shape Hsp Hmod) as [HeqΘ Hshape]. subst Θb.
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb
                     | A1 A2 eb1 eb2 HrA HrEb
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb HrA | eb1 eb2 HrEb ]; subst.
    inversion Hwfe as [ | | | | | Lw Θw Aw ew HwfA Hwfb | ]; subst.
    destruct Hchk as [Qc Hcc].
    (* ---- the shapes' shared data ---- *)
    assert (Hfe : ftvar_in_exp ea ∪ ftvar_in_ptyp A [<=] dom Θa)
      by (pose proof (a_wf_exp_ftv_dom Hwfe) as Hd; simpl in Hd;
          clear - Hd; fsetdec).
    assert (HwfcA : {{ Θa ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfA).
    assert (HrAp : rel_pskl ρ V (ptyp_to_pskl A) (ptyp_to_pskl A2))
      by (exact HrA).
    assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hdmc : dom Θa [<=] dom Θc) by (exact (auc_dom_mono_consis Hcc)).
    pose proof (a_pat_dom_mono Hp) as Hdmb.
    pose proof Hxf as Hxf2. simpl_env in Hxf2.
    assert (HxΘc : x `notin` dom Θc) by (clear - Hxf2; fsetdec).
    assert (HxΘa : x `notin` dom Θa) by (clear - HxΘc Hdmc; fsetdec).
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfe HxΘa; fsetdec).
    (* the CHK output reaches the conclusion's output: the body's dom-mono
       with the term entry stripped *)
    assert (Hdmout : dom Θc [<=] dom (Ξ ++ Θd)).
    { intros a Ha.
      assert (Hax : a <> x) by (intros ->; exact (HxΘc Ha)).
      assert (Ha1 : a `in` dom ((x ~ abind_var_typ A) ++ Θc))
        by (simpl_env; clear - Ha; fsetdec).
      apply Hdmb in Ha1. simpl_env in Ha1. simpl_env.
      clear - Ha1 Hax. fsetdec. }
    (* ---- shape data: the split's two outputs ---- *)
    assert (Hpieces :
      {{ Θa ⨟ empty ⊢ₚₛ Pa }}a /\ {{ Θa ⨟ empty ⊢ₚₛ Q0 }}a /\
      a_sk_mode_compat (decr_mode m0) Q0 /\
      exists Pa' Q0',
        rel_pskl ρ V Pa Pa' /\ rel_pskl ρ V Q0 Q0' /\
        ftvar_in_pskl Pa' ∪ ftvar_in_pskl Q0' [<=] S0 /\
        {{ S0 ↝ S0 ⊨ Θ0' ⊲ P0' ▹ Pa' ⇢ Q0' ⊣ Θ0' }}e).
    { destruct Hshape as [[EP0 [EP EQ0]] | EP0].
      - subst P0a Pa Q0. inversion HrP0; subst.
        split; [ apply a_wf_pskl__ghost | ].
        split; [ apply a_wf_pskl__ghost | ].
        split.
        { destruct (a_sk_mode_compat_ghost_inv Hmod) as [-> | ->];
            [ apply a_sk_mode_compat__ti | congruence ]. }
        exists pskl_ghost, pskl_ghost.
        split; [ apply rel_pskl__ghost | ].
        split; [ apply rel_pskl__ghost | ].
        split; [ simpl; clear; fsetdec | ].
        apply e_split__ghost.
      - subst P0a.
        inversion HrP0 as [ | n0 | u0 v0 Hu0 | B1 B2 Pa' Q0c' HrPa HrQ0c
                          | B3 B4 Hu1 | | B5 B6 Hu2 ]; subst.
        inversion Hwfp0 as [ Θx Δx | Θx Δx αx Hbx | Θx Δx Xa Xb HwfPaa HwfQ0a
                           | Lx Θx Δx Xp Hallx | Θx Δx
                           | Θx Δx Xp Hgx Hwix ]; subst.
        destruct (a_sk_mode_compat_arrow_inv Hmod) as (m'' & Em & Hmodc0).
        subst m0.
        split; [ exact HwfPaa | ].
        split; [ exact HwfQ0a | ].
        split; [ simpl; exact Hmodc0 | ].
        exists Pa', Q0c'.
        split; [ exact HrPa | ].
        split; [ exact HrQ0c | ].
        split; [ simpl in HcovP; clear - HcovP; fsetdec | ].
        apply e_split__arrow. }
    destruct Hpieces as (HwfPa & HwfQ0a & Hmodc
                         & Pa' & Q0' & HrPa & HrQ0c & HftPQ & Dsp).
    (* ---- the chk lift ---- *)
    assert (Hblk1 : forall a, a `in` dom Θc -> a `notin` dom Θa ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk;
          [ apply Hdmout; exact Ha | exact Hn ]).
    assert (HcovC : ftvar_in_pskl Pa' ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] S0).
    { simpl in HcovP. rewrite ftvar_ptyp_to_pskl.
      clear - HcovP HftPQ. fsetdec. }
    destruct (lift_consis_nil Hcc HrΘ HrPa HrAp Hagr Hinj Hfun Hwf Huq2p
                Hftv2 Hscp Hblk1 HdΘ Hcov HcovC HwfPa HwfcA)
      as (S1c & ρe1 & Θc' & Qc' & Dchk & HrΘc & Hagrc & HrQcU & Hext1
          & Hdom1).
    pose proof (e_consis_supply_grows Dchk) as Hgr1.
    (* ---- side 2's package at the chk's output ---- *)
    assert (HdΘ1 : dom Θc' [<=] S1c).
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ _ _ _ Dchk) as Hup.
      clear - Hup HdΘ Hgr1. fsetdec. }
    assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl Pa'
                    ∪ ftvar_in_pskl (ptyp_to_pskl A2) [<=] S0)
      by (clear - Hftv2 HcovC; fsetdec).
    assert (Hftv1 : ftvar_in_aenv Θc' [<=] S1c)
      by (eapply (proj2 (proj2 e_assign_unify_consis_ctx_ftvar));
          [ exact Dchk | exact HcovE ]).
    assert (HcovE2 : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl Pa'
                     ∪ ftvar_in_pskl (ptyp_to_pskl A2) ∪ empty ∪ empty
                     [<=] S0)
      by (clear - HcovE; fsetdec).
    assert (Huq1' : uniq Θc').
    { pose proof (e_consis_sound Dchk Huq2p HcovE2) as Ha1.
      exact ((proj2 (proj2 a_assign_unify_consis_uniq)) _ _ _ _ _ _ _ Ha1
               Huq2p). }
    (* ---- side 1's package at the chk's output ---- *)
    destruct (a_consis_isub_wf_nil Hcc Hwf HwfPa HwfcA) as [Hle01 HwfΘc].
    assert (Hd1s : dom Θc [<=] ftvar_in_aenv Θc)
      by (apply dom_subset_ftvar_in_aenv).
    assert (Hscp1 : V [<=] ftvar_in_aenv Θc)
      by (clear - Hscp Hsc0 Hdmc Hd1s; fsetdec).
    assert (HwfAc : a_wf_ptyp Θc A)
      by (eapply a_wf_ptyp_isub; [ exact HwfA | exact Hle01 ]).
    assert (HwfXc : {{ ⊢ ((x ~ abind_var_typ A) ++ Θc) }}a)
      by (apply a_wf_aenv__var_typ; [ exact HxΘc | exact HwfAc | exact HwfΘc ]).
    assert (HbdfA : ftvar_in_abind (abind_var_typ A) [<=] dom Θc)
      by (simpl; pose proof (a_wf_ptyp_ftv_dom HwfAc) as Hd; exact Hd).
    assert (HwfQ0c : {{ Θc ⨟ empty ⊢ₚₛ Q0 }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact HwfQ0a ]).
    assert (Hwfeo : {{ ((x ~ abind_var_typ A) ++ Θc) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a)
      by (apply a_wf_exp_weaken_cons; eapply a_wf_exp_abs_anno_pick;
          eapply a_wf_exp_isub; [ exact Hwfe | exact Hle01 ]).
    (* ---- the relation, widened by the chk's pairs ---- *)
    assert (Hinj1 : rel_inj (ρe1 ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (HVdom0 : V [<=] dom Θa) by (clear - Hscp Hsc0; fsetdec).
    assert (Hfun1 : rel_fun (ρe1 ++ ρ) V (dom Θc)).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hext1 | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; exact (Hblk1 a Ha Hn)
        | intros a Ha Hn; clear - HVdom0 Hn; fsetdec ]. }
    assert (HrEb' : rel_exp (ρe1 ++ ρ) V ea eb2)
      by (eapply rel_exp_mono;
          [ exact HrEb | intros u v Hu; apply in_or_app; right; exact Hu
          | intros u Hu; exact Hu ]).
    assert (HrA' : rel_pskl (ρe1 ++ ρ) V (ptyp_to_pskl A) (ptyp_to_pskl A2))
      by (apply rel_pskl_widen; exact HrAp).
    assert (HrQ0w : rel_pskl (ρe1 ++ ρ) V Q0 Q0')
      by (apply rel_pskl_widen; exact HrQ0c).
    assert (Hc1r : cols_r ρe1 [<=] S1c).
    { intros y Hy. destruct (cols_r_in_inv _ _ Hy) as (a & Hin).
      destruct (Hdom1 _ _ Hin) as [_ Hd2]. clear - Hd2 HdΘ1. fsetdec. }
    assert (Hcov1 : V ∪ cols_r (ρe1 ++ ρ) [<=] S1c)
      by (rewrite cols_r_app; clear - Hcov Hc1r Hgr1; fsetdec).
    assert (Hblk2 : forall a, a `in` dom (Ξ ++ Θd) -> a `notin` dom Θc ->
                    a `notin` cols_l (ρe1 ++ ρ)).
    { intros a Ha Hn. rewrite cols_l_app.
      assert (Hc1 : a `notin` cols_l ρe1).
      { intros Hy. destruct (cols_l_in_inv _ _ Hy) as (y & Hin).
        destruct (Hdom1 _ _ Hin) as [Hd1 _]. contradiction. }
      assert (Hc2 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn Hdmc; fsetdec ]).
      clear - Hc1 Hc2. fsetdec. }
    assert (Hbd'fc : ftvar_in_abind (abind_var_typ A2) [<=] S1c).
    { simpl. rewrite ftvar_ptyp_to_pskl in HcovC.
      clear - HcovC Hgr1. fsetdec. }
    assert (HcovPc : ftvar_in_pskl Q0' ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S1c)
      by (simpl in HcovP; clear - HcovP HftPQ Hgr1; fsetdec).
    (* ---- the CORE ---- *)
    destruct (@lift_pat_abs_core (decr_mode m0) Θc Q0 ea Qa Ξ Θd x
                (abind_var_typ A)
                Hp IHp Hsuf Hxf Hxe I HbdfA Hmodc
                S1c Θc' Q0' eb2 (abind_var_typ A2) (ρe1 ++ ρ) V
                HrΘc HrQ0w HrEb'
                (rel_abind__var_typ HrA') I Hbd'fc
                Hagrc Hinj1 Hfun1 HwfXc HwfQ0c Hwfeo Huq1' Hftv1 Hscp1
                Hblk2 HdΘ1 Hcov1 HcovPc)
      as (S1 & x2 & ρe2 & Ξ2 & Θc2' & Q' & Hx2S1c & De & HsufΞ2 & HrF
          & HagrF & HrQ' & HextF & HdomF & Hdm2).
    (* ---- the answer ---- *)
    exists S1, (ρe2 ++ ρe1), (Ξ2 ++ Θc2'),
      (pskl_arrow (ptyp_to_pskl A2) Q').
    split.
    { eapply e_pat__abs_anno;
        [ exact Hne | exact Dsp | exists Qc'; exact Dchk | exact HsufΞ2
        | exact Hx2S1c | exact De ]. }
    rewrite app_assoc.
    split; [ exact HrF | ].
    split; [ exact HagrF | ].
    split.
    { constructor; [ | exact HrQ' ].
      eapply rel_pskl_mono;
        [ exact HrA' | intros u v Hu; apply in_or_app; right; exact Hu
        | intros u Hu; exact Hu ]. }
    split.
    { eapply rel_ext_app;
        [ exact Hext1 | exact HextF
        | clear - Hsc0 Hdmc Hd1s; fsetdec
        | exact Hgr1
        | intros a b Hin; destruct (Hdom1 _ _ Hin) as [Hd1 Hd2];
          split; [ clear - Hd1 Hd1s; fsetdec | clear - Hd2 HdΘ1; fsetdec ] ]. }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (HdomF _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; [ apply Hdmout; exact Hd1 | apply Hdm2; exact Hd2 ].
  - (* ⭐ AP-AbsCheck — no prelude at all: ONE core call *)
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb
                     | A1 A2 eb1 eb2 HrA HrEb
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb HrA | eb1 eb2 HrEb ]; subst.
    inversion HrP0; subst.
    assert (Hfe : ftvar_in_exp ea [<=] dom Θa)
      by (pose proof (a_wf_exp_ftv_dom Hwfe) as Hd; simpl in Hd; exact Hd).
    pose proof Hxf as Hxf2. simpl_env in Hxf2.
    assert (HxΘa : x `notin` dom Θa) by (clear - Hxf2; fsetdec).
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfe HxΘa; fsetdec).
    assert (Hwfeo : {{ ((x ~ abind_var_skl pskl_ghost) ++ Θa) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a)
      by (apply a_wf_exp_weaken_cons; eapply a_wf_exp_abs_pick; exact Hwfe).
    assert (HwfXc : {{ ⊢ ((x ~ abind_var_skl pskl_ghost) ++ Θa) }}a)
      by (apply a_wf_aenv__var;
          [ exact HxΘa | apply a_wf_pskl__ghost | exact Hwf ]).
    assert (HcovPc : ftvar_in_pskl pskl_ghost ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S0)
      by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hbdf0 : ftvar_in_abind (abind_var_skl pskl_ghost) [<=] dom Θa)
      by (simpl; clear; fsetdec).
    assert (Hbdf0' : ftvar_in_abind (abind_var_skl pskl_ghost) [<=] S0)
      by (simpl; clear; fsetdec).
    destruct (@lift_pat_abs_core mode_tc Θa pskl_ghost ea Qa Ξ Θb x
                (abind_var_skl pskl_ghost)
                Hp IHp Hsuf Hxf Hxe I Hbdf0 a_sk_mode_compat__tc
                S0 Θ0' pskl_ghost eb2 (abind_var_skl pskl_ghost) ρ V
                HrΘ (rel_pskl__ghost ρ V) HrEb
                (rel_abind__var_skl (rel_pskl__ghost ρ V)) I Hbdf0'
                Hagr Hinj Hfun HwfXc
                (a_wf_pskl__ghost Θa empty) Hwfeo Huq2p Hftv2 Hscp Hblk
                HdΘ Hcov HcovPc)
      as (S1 & x2 & ρe & Ξ2 & Θc2' & Q' & Hx2S0 & De & HsufΞ2 & HrF
          & HagrF & HrQ' & HextF & HdomF & Hdm2).
    exists S1, ρe, (Ξ2 ++ Θc2'),
      (pskl_univ_ghost (pskl_arrow pskl_ghost Q')).
    split.
    { eapply e_pat__abs_check;
        [ exact HsufΞ2 | exact Hx2S0 | exact De ]. }
    split; [ exact HrF | ].
    split; [ exact HagrF | ].
    split.
    { constructor. constructor; [ apply rel_pskl__ghost | exact HrQ' ]. }
    split; [ exact HextF | ]. exact HdomF.
  - (* ⭐ AP-AbsAnnoCheck — the annotated twin, same shape *)
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb
                     | A1 A2 eb1 eb2 HrA HrEb
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb HrA | eb1 eb2 HrEb ]; subst.
    inversion HrP0; subst.
    inversion Hwfe as [ | | | | | Lw Θw Aw ew HwfA Hwfb | ]; subst.
    assert (Hfe : ftvar_in_exp ea [<=] dom Θa)
      by (pose proof (a_wf_exp_ftv_dom Hwfe) as Hd; simpl in Hd;
          clear - Hd; fsetdec).
    pose proof Hxf as Hxf2. simpl_env in Hxf2.
    assert (HxΘa : x `notin` dom Θa) by (clear - Hxf2; fsetdec).
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfe HxΘa; fsetdec).
    assert (Hwfeo : {{ ((x ~ abind_var_typ A) ++ Θa) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a)
      by (apply a_wf_exp_weaken_cons; eapply a_wf_exp_abs_anno_pick;
          exact Hwfe).
    assert (HwfXc : {{ ⊢ ((x ~ abind_var_typ A) ++ Θa) }}a)
      by (apply a_wf_aenv__var_typ; [ exact HxΘa | exact HwfA | exact Hwf ]).
    assert (HbdfA : ftvar_in_abind (abind_var_typ A) [<=] dom Θa)
      by (simpl; apply a_wf_ptyp_ftv_dom; exact HwfA).
    assert (Hbd'f : ftvar_in_abind (abind_var_typ A2) [<=] S0).
    { simpl. simpl in HcovP.
      pose proof (@rel_pskl_ftv_r ρ V (ptyp_to_pskl A) (ptyp_to_pskl A2) HrA)
        as Hfr.
      rewrite ftvar_ptyp_to_pskl in Hfr. clear - Hfr Hcov. fsetdec. }
    assert (HcovPc : ftvar_in_pskl pskl_ghost ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S0)
      by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
    destruct (@lift_pat_abs_core mode_tc Θa pskl_ghost ea Qa Ξ Θb x
                (abind_var_typ A)
                Hp IHp Hsuf Hxf Hxe I HbdfA a_sk_mode_compat__tc
                S0 Θ0' pskl_ghost eb2 (abind_var_typ A2) ρ V
                HrΘ (rel_pskl__ghost ρ V) HrEb
                (rel_abind__var_typ HrA) I Hbd'f
                Hagr Hinj Hfun HwfXc
                (a_wf_pskl__ghost Θa empty) Hwfeo Huq2p Hftv2 Hscp Hblk
                HdΘ Hcov HcovPc)
      as (S1 & x2 & ρe & Ξ2 & Θc2' & Q' & Hx2S0 & De & HsufΞ2 & HrF
          & HagrF & HrQ' & HextF & HdomF & Hdm2).
    exists S1, ρe, (Ξ2 ++ Θc2'),
      (pskl_univ_ghost (pskl_arrow (ptyp_to_pskl A2) Q')).
    split.
    { eapply e_pat__abs_anno_check;
        [ exact HsufΞ2 | exact Hx2S0 | exact De ]. }
    split; [ exact HrF | ].
    split; [ exact HagrF | ].
    split.
    { constructor. constructor; [ | exact HrQ' ].
      eapply rel_pskl_mono;
        [ exact HrA | intros u v Hu; apply in_or_app; right; exact Hu
        | intros u Hu; exact Hu ]. }
    split; [ exact HextF | ]. exact HdomF.
  - (* ⭐ AP-App — the S-Arrow template one judgement up: the argument at
       (TC, ◇), then the function at ITS output, [rel_ext_app] composing
       the two extensions. *)
    inversion HrE as [ | | x1 y1 Hat | e1a e2a HrEa
                     | A1 A2 e1a e2a HrA HrEa
                     | a1 a2 b1 b2 HrE1 HrE2
                     | e1a e2a A1 A2 HrEa HrA | e1a e2a HrEa ]; subst.
    destruct (a_wf_exp_app_inv Hwfe) as [Hwfe1 Hwfe2].
    assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hdm0 : dom Θa [<=] dom Θb) by (exact (a_pat_dom_mono Hp2)).
    assert (Hdm1 : dom Θb [<=] dom Θc) by (exact (a_pat_dom_mono Hp1)).
    assert (Hblk1 : forall a, a `in` dom Θb -> a `notin` dom Θa ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk; [ clear - Ha Hdm1; fsetdec | exact Hn ]).
    assert (HcovP1 : ftvar_in_pskl pskl_ghost ∪ ftvar_in_exp b2
                     ∪ fvar_in_exp b2 [<=] S0)
      by (simpl in HcovP |- *; clear - HcovP; fsetdec).
    destruct (IHp2 S0 Θ0' pskl_ghost b2 ρ V HrΘ (rel_pskl__ghost ρ V) HrE2
                Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk1 HdΘ Hcov HcovP1
                (a_wf_pskl__ghost Θa empty) Hwfe2 a_sk_mode_compat__tc)
      as (S1 & ρe1 & Θb' & P0c' & D2e & HrΘ1 & Hagr1 & HrP0c & Hext1 & Hdom1).
    pose proof (e_pat_supply_grows D2e) as Hgr1.
    (* ---- side 2's package at the first call's output ---- *)
    assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl pskl_ghost
                    ∪ fvar_in_exp b2 ∪ ftvar_in_exp b2 [<=] S0)
      by (simpl; simpl in HcovP; clear - Hftv2 HcovP; fsetdec).
    destruct (e_pat_sound D2e Huq2p HcovE) as (Ha2p & Huq1' & Hftv1 & HftQ1).
    assert (HdΘ1 : dom Θb' [<=] S1)
      by (pose proof (dom_subset_ftvar_in_aenv Θb') as Hd;
          clear - Hd Hftv1; fsetdec).
    (* ---- side 1's package at the first call's output ---- *)
    destruct (a_pat_sound Hp2 Hwf (a_wf_pskl__ghost Θa empty)
                a_sk_mode_compat__tc Hwfe2) as [Hle01 [HwfΘb _]].
    assert (Hd1s : dom Θb [<=] ftvar_in_aenv Θb)
      by (apply dom_subset_ftvar_in_aenv).
    assert (Hscp1 : V [<=] ftvar_in_aenv Θb)
      by (clear - Hscp Hsc0 Hdm0 Hd1s; fsetdec).
    assert (HwfP0a : {{ Θb ⨟ empty ⊢ₚₛ P0a }}a)
      by (eapply a_pat_output_wf;
          [ exact Hp2 | exact Hwf | apply a_wf_pskl__ghost
          | exact a_sk_mode_compat__tc | exact Hwfe2 ]).
    assert (HwfQ0b : {{ Θb ⨟ empty ⊢ₚₛ Q0 }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hwfp0 ]).
    assert (Hwfarr : {{ Θb ⨟ empty ⊢ₚₛ (pskl_arrow P0a Q0) }}a)
      by (apply a_wf_pskl__arrow; [ exact HwfP0a | exact HwfQ0b ]).
    assert (Hwfe1b : {{ Θb ⊢ᵉ e1 }}a)
      by (eapply a_wf_exp_isub; [ exact Hwfe1 | exact Hle01 ]).
    (* ---- the relation, widened by the first call's new pairs ---- *)
    assert (Hinj1 : rel_inj (ρe1 ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (HVdom0 : V [<=] dom Θa) by (clear - Hscp Hsc0; fsetdec).
    assert (Hfun1 : rel_fun (ρe1 ++ ρ) V (dom Θb)).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hext1 | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; exact (Hblk1 a Ha Hn)
        | intros a Ha Hn; clear - HVdom0 Hn; fsetdec ]. }
    assert (HrQ0' : rel_pskl (ρe1 ++ ρ) V Q0 P0')
      by (apply rel_pskl_widen; exact HrP0).
    assert (Hrarr : rel_pskl (ρe1 ++ ρ) V (pskl_arrow P0a Q0)
                      (pskl_arrow P0c' P0'))
      by (constructor; [ exact HrP0c | exact HrQ0' ]).
    assert (HrE1' : rel_exp (ρe1 ++ ρ) V e1 b1)
      by (eapply rel_exp_mono;
          [ exact HrE1 | intros u v Hu; apply in_or_app; right; exact Hu
          | intros u Hu; exact Hu ]).
    assert (Hc1r : cols_r ρe1 [<=] S1).
    { intros y Hy. destruct (cols_r_in_inv _ _ Hy) as (a & Hin).
      destruct (Hdom1 _ _ Hin) as [_ Hd2]. clear - Hd2 HdΘ1. fsetdec. }
    assert (Hcov1 : V ∪ cols_r (ρe1 ++ ρ) [<=] S1)
      by (rewrite cols_r_app; clear - Hcov Hc1r Hgr1; fsetdec).
    assert (Hblk2 : forall a, a `in` dom Θc -> a `notin` dom Θb ->
                    a `notin` cols_l (ρe1 ++ ρ)).
    { intros a Ha Hn. rewrite cols_l_app.
      assert (Hc1 : a `notin` cols_l ρe1).
      { intros Hy. destruct (cols_l_in_inv _ _ Hy) as (y & Hin).
        destruct (Hdom1 _ _ Hin) as [Hd1 _]. contradiction. }
      assert (Hc2 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn Hdm0; fsetdec ]).
      clear - Hc1 Hc2. fsetdec. }
    assert (HcovP2 : ftvar_in_pskl (pskl_arrow P0c' P0')
                     ∪ ftvar_in_exp b1 ∪ fvar_in_exp b1 [<=] S1).
    { pose proof (@rel_pskl_ftv_r (ρe1 ++ ρ) V P0a P0c' HrP0c) as HfQ.
      rewrite cols_r_app in HfQ.
      simpl. simpl in HcovP.
      clear - HfQ HcovP Hcov Hc1r Hgr1. fsetdec. }
    destruct (IHp1 S1 Θb' (pskl_arrow P0c' P0') b1 (ρe1 ++ ρ) V
                HrΘ1 Hrarr HrE1' Hagr1 Hinj1 Hfun1 HwfΘb Huq1' Hftv1
                Hscp1 Hblk2 HdΘ1 Hcov1 HcovP2 Hwfarr Hwfe1b
                (a_sk_mode_compat__fn P0a Hmod))
      as (S2 & ρe2 & Θc' & Qc' & D1e & HrΘ2 & Hagr2 & HrQ2 & Hext2 & Hdom2).
    inversion HrQ2 as [ | | u5 v5 Hu5 | C1 C2 Pa' Qa' HrPa' HrQa'
                      | C3 C4 Hu6 | | C5 C6 Hu7 ]; subst.
    (* ---- side 2's dom mono across the second call ---- *)
    assert (HcovE3 : ftvar_in_aenv Θb' ∪ ftvar_in_pskl (pskl_arrow P0c' P0')
                     ∪ fvar_in_exp b1 ∪ ftvar_in_exp b1 [<=] S1)
      by (clear - Hftv1 HcovP2; fsetdec).
    assert (Hdm2' : dom Θb' [<=] dom Θc').
    { destruct (e_pat_sound D1e Huq1' HcovE3) as (Ha1p & _).
      exact (a_pat_dom_mono Ha1p). }
    (* ---- the answer ---- *)
    exists S2, (ρe2 ++ ρe1), Θc', Qa'.
    split; [ eapply e_pat__app; [ exact D2e | exact D1e ] | ].
    rewrite app_assoc.
    split; [ exact HrΘ2 | ].
    split; [ exact Hagr2 | ].
    split; [ exact HrQa' | ].
    split.
    { eapply rel_ext_app;
        [ exact Hext1 | exact Hext2
        | clear - Hsc0 Hdm0 Hd1s; fsetdec
        | exact Hgr1
        | intros a b Hin; destruct (Hdom1 _ _ Hin) as [Hd1 Hd2];
          split; [ clear - Hd1 Hd1s; fsetdec | clear - Hd2 HdΘ1; fsetdec ] ]. }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hdom2 _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; [ clear - Hd1 Hdm1; fsetdec | clear - Hd2 Hdm2'; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §13 — THE a_typing RUNG — LIVES IN [prop_lift_typing.v]               *)
(*                                                                        *)
(*  Split out 2026-08-22: it is 3.7k of this file's 12.8k lines, it is a  *)
(*  clean PREFIX boundary (nothing above depends on it), and keeping it   *)
(*  here made every edit to the typing rung re-check the nine rungs below *)
(*  (docs/REPORT-interface-proofpath-audit.md §B4).                       *)
(* ===================================================================== *)
