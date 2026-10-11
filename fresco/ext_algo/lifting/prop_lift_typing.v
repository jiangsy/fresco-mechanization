(** ext_algo — ⭐⭐⭐ THE LIFT'S LAST RUNG: [a_typing] ⟹ [e_typing].

    §13 of what used to be one 12.8k-line [prop_lift.v], split out
    2026-08-22 so that editing the TYPING rung does not re-check the nine
    rungs below it (docs/REPORT-interface-proofpath-audit.md §B4).  The
    boundary is a clean prefix: everything here depends on [prop_lift.v],
    nothing there depends on anything here, and [a_typing_rel_e] is the
    only name this file exports to a consumer (prop_run_corollaries.v).

    ⭐ WHAT IT CLOSES.  With this rung the whole ladder reads guess ✅ look
    ✅ solve ✅ cstr ✅ extract ✅ consis ✅ sub ✅ split ✅ pat ✅ typing ✅,
    so every judgement of [fresco/algo] transports onto the supply-threaded
    runner's rails — and the decidability corollary's NEGATIVE branch
    reaches the PAPER's own judgement (prop_run_corollaries.v §5–§7).
    The design record is hand-off §8c.46 (the plan) and §8c.47 (the
    closure); read [prop_lift.v]'s header first for the technique. *)

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
Require Import src.fresco.ext_algo.lifting.prop_lift.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §13  ⭐⭐⭐ THE a_typing RUNG — [a_typing] lifts to [e_typing], all 11   *)
(*  rows.  THE LAST RUNG OF THE LIFT: with it, every judgement of the     *)
(*  first encoding transports onto the supply-threaded runner's rails.    *)
(*                                                                        *)
(*  The motive is [lift_pat_concl] with a TYPE result and                 *)
(*  [a_ty_mode_compat] in place of the SK compat.  The six binder-free    *)
(*  rows go through [lift_typing_sub] (the TY-sorted [a_sub] wrapper) +   *)
(*  the COERCION IMAGE; [AT-Anno] pins its result by FUNCTIONALITY of     *)
(*  the relation ([rel_pskl_fun_dom]), not determinism of the runner.     *)
(*  The abs rows share ONE core ([lift_typing_abs_core], the [a_pat]      *)
(*  core one judgement over); the four suffix-DISCARDING [_check] rows    *)
(*  are the landed S-ForallR row (§10) line for line — restrict at the    *)
(*  junk suffix's domain, push the opener pair, run, peel — plus the one  *)
(*  step S-ForallR did not have: the RESULT CLOSE                         *)
(*  ([A' := close α2 B''], cancellation premise-free), whose ∀-rel is     *)
(*  exactly [rel_pskl_close_pair_restrict].                               *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  ⭐ THE COERCION IMAGE — a skeleton related to an EMBEDDED TYPE is       *)
(*  itself an embedded type, and the underlying types are related.         *)
(*  [a_typing]'s rows pin their yields to [⌈·⌉]-images, and the e-rules    *)
(*  do the same, so every row needs this to READ its premise's yield.      *)
(* ===================================================================== *)

Lemma rel_pskl_ptyp_image_r : forall ρ V A1 Q',
  rel_pskl ρ V (ptyp_to_pskl A1) Q' ->
  exists A', Q' = ptyp_to_pskl A' /\ rel_ptyp ρ V A1 A'.
Proof.
  intros ρ V A1; induction A1; intros Q' Hr; simpl in Hr;
    inversion Hr; subst.
  - exists ptyp_unit. split; [ reflexivity | constructor ].
  - match goal with
    | H : rel_pskl _ _ (pskl_var_b _) _ |- _ => idtac
    end.
    exists (ptyp_var_b n). split; [ reflexivity | ].
    unfold rel_ptyp. simpl. constructor.
  - match goal with
    | Ha : rel_atom _ _ _ ?y |- _ =>
        exists (ptyp_var_f y); split;
          [ reflexivity
          | unfold rel_ptyp; simpl; apply rel_pskl__var_f; exact Ha ]
    end.
  - match goal with
    | H1 : rel_pskl _ _ (ptyp_to_pskl A1_1) ?q1,
      H2 : rel_pskl _ _ (ptyp_to_pskl A1_2) ?q2 |- _ =>
        destruct (IHA1_1 _ H1) as (B1 & -> & Hb1);
        destruct (IHA1_2 _ H2) as (B2 & -> & Hb2);
        exists (ptyp_arrow B1 B2); split;
          [ reflexivity
          | unfold rel_ptyp; simpl; constructor; assumption ]
    end.
  - match goal with
    | H1 : rel_pskl _ _ (ptyp_to_pskl A1) ?q1 |- _ =>
        destruct (IHA1 _ H1) as (B1 & -> & Hb1);
        exists (ptyp_all B1); split;
          [ reflexivity
          | unfold rel_ptyp; simpl; constructor; exact Hb1 ]
    end.
Qed.

(* ===================================================================== *)
(*  THE MOTIVE — [lift_pat_concl] with a TYPE result                       *)
(* ===================================================================== *)

Definition lift_typing_post (Θ0 : aenv) (B : ptyp) (Θ1 : aenv)
    (S0 : atoms) (m : mode) (Θ0' : aenv) (P0' : pskl) (e' : exp)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' B',
    {{ S0 ↝ S1 ⊨ Θ0' ⊢[ m ; P0' ] e' ⦂ B' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_ptyp (ρe ++ ρ) V B B'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_typing_concl (m : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (B : ptyp) (Θ1 : aenv) : Prop :=
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
    a_ty_mode_compat m P0 ->
    lift_typing_post Θ0 B Θ1 S0 m Θ0' P0' e' ρ V.

(** ⚙ The TY-sorted [a_sub] wrapper, [lift_pat_sub]'s twin. *)
Lemma lift_typing_sub : forall m Θ0 Θ1 P0 Ps Q,
  {{ Θ0 ⊢[ a_sub_mode_ty | m | P0 ] Ps ⩽ Q ⊣ Θ1 }}a ->
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
    lift_sub_post Θ0 Q Θ1 S0 a_sub_mode_ty m Θ0' P0' Ps' ρ V.
Proof.
  intros m Θ0 Θ1 P0 Ps Q HD.
  exact ((proj1 a_sub_sub_flex_rel_e) _ _ _ _ _ _ _ HD).
Qed.

(** ⭐⭐ RIGHT-FUNCTIONALITY OF [rel_pskl], on a domain that covers the
    subject's free variables.  ⛔ FORCED by [AT-Anno]: its premise PINS the
    result to the annotation on BOTH sides, but the IH returns only a
    RELATED result — and a "result = check-against at TC" pin is FALSE on
    both sides ([abs_check_base] at a flex check-against splits [α̂] into
    [β̂→α̂₁]).  Functionality of the RELATION is what actually holds. *)
Lemma rel_pskl_fun_dom : forall ρ V P Q1 Q2 D,
  rel_pskl ρ V P Q1 -> rel_pskl ρ V P Q2 ->
  rel_fun ρ V D -> ftvar_in_pskl P [<=] D -> Q1 = Q2.
Proof.
  intros ρ V P Q1 Q2 D H1; revert Q2;
    induction H1; intros Qx H2 Hfun Hd; inversion H2; subst;
    simpl in Hd; try reflexivity.
  - (* var_f *)
    f_equal.
    match goal with
    | Ha : rel_atom _ _ α ?b1, Hb : rel_atom _ _ α ?b2 |- ?b1 = ?b2 =>
        apply (Hfun α b1 b2); [ clear - Hd; fsetdec | exact Ha | exact Hb ]
    end.
  - (* arrow *)
    f_equal;
      [ apply IHrel_pskl1 | apply IHrel_pskl2 ];
      try assumption; clear - Hd; fsetdec.
  - (* all_syn *)
    f_equal. apply IHrel_pskl; assumption.
  - (* univ_ghost *)
    f_equal. apply IHrel_pskl; assumption.
Qed.

(** The ARROW inversion of [rel_ptyp], for [AT-App]'s middle premise —
    the e-rule pins that result to an arrow. *)
Lemma rel_ptyp_arrow_inv : forall ρ V A B T,
  rel_ptyp ρ V (ptyp_arrow A B) T ->
  exists TA TB, T = ptyp_arrow TA TB /\ rel_ptyp ρ V A TA /\ rel_ptyp ρ V B TB.
Proof.
  intros ρ V A B T Hr. unfold rel_ptyp in Hr. simpl in Hr.
  destruct T; simpl in Hr; inversion Hr; subst.
  exists T1, T2. split; [ reflexivity | split; assumption ].
Qed.

(** The ∀ inversion, for the [_check_step] rows — the check-against is
    [⌈∀A0⌉] and its image must be a [∀] again. *)
Lemma rel_ptyp_all_inv : forall ρ V A T,
  rel_ptyp ρ V (ptyp_all A) T ->
  exists TA, T = ptyp_all TA /\ rel_ptyp ρ V A TA.
Proof.
  intros ρ V A T Hr. unfold rel_ptyp in Hr. simpl in Hr.
  destruct T; simpl in Hr; inversion Hr; subst.
  exists T. split; [ reflexivity | assumption ].
Qed.

Lemma lift_typing_abs_core : forall m' Θb Q0 e (Bt : ptyp) Ξ Θc x bd,
  {{ ((x ~ bd) ++ Θb) ⊢[ m' ; Q0 ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Bt
     ⊣ (Ξ ++ (x ~ bd) ++ Θc) }}a ->
  lift_typing_concl m' ((x ~ bd) ++ Θb) Q0 (open_exp_wrt_exp e (exp_var_f x)) Bt
    (Ξ ++ (x ~ bd) ++ Θc) ->
  a_suffix Ξ ->
  x `notin` dom (Ξ ++ Θb) ∪ dom Θc ∪ fvar_in_exp e ->
  x `notin` ftvar_in_exp e ->
  abind_is_tm bd ->
  ftvar_in_abind bd [<=] dom Θb ->
  a_ty_mode_compat m' Q0 ->
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
  exists S1 x2 ρe Ξ2 Θc2' Bt',
    x2 `notin` S0
    /\ {{ (add x2 S0) ↝ S1 ⊨ ((x2 ~ bd') ++ Θb') ⊢[ m' ; Q0' ]
          (open_exp_wrt_exp e' (exp_var_f x2)) ⦂ Bt'
          ⊣ (Ξ2 ++ (x2 ~ bd') ++ Θc2') }}e
    /\ a_suffix Ξ2
    /\ rel_aenv (ρe ++ ρ) V (Ξ ++ Θc) (Ξ2 ++ Θc2')
    (* the SPLIT halves too — the [_check] rows discard [Ξ], and their
       junk-strip needs the correspondence AT the suffix alone *)
    /\ rel_aenv (ρe ++ ρ) V Ξ Ξ2
    /\ rel_aenv (ρe ++ ρ) V Θc Θc2'
    /\ flex_agree_rel (ρe ++ ρ) V (Ξ ++ Θc) (Ξ2 ++ Θc2')
    /\ rel_ptyp (ρe ++ ρ) V Bt Bt'
    /\ rel_ext ρe (ftvar_in_aenv Θb) S0
    /\ (forall a b, In (a, b) ρe ->
          a `in` dom (Ξ ++ Θc) /\ b `in` dom (Ξ2 ++ Θc2'))
    /\ dom Θb' [<=] dom (Ξ2 ++ Θc2').
Proof.
  intros m' Θb Q0 e Bt Ξ Θc x bd Hbody IH Hsuf Hxf Hxe Htm Hbdf Hmod'.
  intros S0 Θb' Q0' e' bd' ρ V HrΘ HrQ0 HrE Hrbd Htm' Hbd'f Hagr Hinj Hfun
    HwfX HwfQ0 Hwfeo Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP.
  destruct (atom_fresh S0) as [x2 Hx2].
  destruct (lift_abs_push Hx2 Hxf Hxe Htm Htm' Hbdf Hbd'f HrΘ HrQ0 HrE Hrbd
              Hagr Hinj Hfun HwfX HwfQ0 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP)
    as (HrΘ1 & HrQ01 & HrEo & Hagr1 & Hinj1 & Hfun1 & Huq2X & Hftv2X & HscpX
        & HblkX & HdΘX & HcovX & HcovPX & HwfQ0X).
  destruct (IH (add x2 S0) ((x2 ~ bd') ++ Θb') Q0'
              (open_exp_wrt_exp e' (exp_var_f x2))
              ((x, x2) :: restrict_pairs x x2 ρ) V
              HrΘ1 HrQ01 HrEo Hagr1 Hinj1 Hfun1 HwfX Huq2X Hftv2X HscpX
              HblkX HdΘX HcovX HcovPX HwfQ0X Hwfeo Hmod')
    as (S1 & ρe & Θout' & Bt' & De & HrΘo & _ & HrQo & Hexto & Hdomo).
  (* ---- side 1's output wf; side 2's run read back on side 1 ---- *)
  destruct (a_typing_sound Hbody HwfX HwfQ0X Hmod' Hwfeo)
    as [_ [HwfOut [HwfQout _]]].
  assert (HxQ : x `notin` ftvar_in_pskl (ptyp_to_pskl Bt))
    by (eapply a_wf_pskl_tm_entry_fresh with (Δ := empty);
        [ exact HwfOut | exact Htm | apply a_wf_ptyp_to_wf_pskl; exact HwfQout ]).
  assert (HcovEX : ftvar_in_aenv ((x2 ~ bd') ++ Θb') ∪ ftvar_in_pskl Q0'
                   ∪ fvar_in_exp (open_exp_wrt_exp e' (exp_var_f x2))
                   ∪ ftvar_in_exp (open_exp_wrt_exp e' (exp_var_f x2))
                   [<=] add x2 S0)
    by (clear - Hftv2X HcovPX; fsetdec).
  destruct (e_typing_sound De Huq2X HcovEX) as (HaDe & HuqOut2 & _).
  assert (Hb'out : binds x2 bd' Θout')
    by (apply (a_typing_tm_le HaDe);
        [ exact Htm' | unfold binds; simpl; left; reflexivity ]).
  assert (Hx2Θb' : x2 `notin` dom Θb') by (clear - Hx2 HdΘ; fsetdec).
  destruct (lift_abs_peel HrΘo HrQo Hexto Hdomo HwfX HwfOut Htm HxQ Hb'out
              HuqOut2 Hsuf Hinj Hfun Hscp Hcov Hblk Hx2Θb'
              (a_typing_dom_mono HaDe))
    as (Ξ2 & Θc2' & -> & HsufΞ2 & HrF & HrFΞ & HrFΘ & HagrF & HrQF & HextF
        & HdomF & Hdm).
  exists S1, x2, ρe, Ξ2, Θc2', Bt'.
  exact (conj Hx2 (conj De (conj HsufΞ2 (conj HrF (conj HrFΞ (conj HrFΘ
          (conj HagrF (conj HrQF (conj HextF (conj HdomF Hdm)))))))))).
Qed.

(* ===================================================================== *)
(*  The AbsCheckStep / AbsAnnoCheckStep rows, generic in the subject.      *)
(*                                                                         *)
(*  Both algorithmic rules, both e-rules, and both proofs are the same up  *)
(*  to the subject: the subject does NOT open, the TYPE opens at a rigid   *)
(*  pair, and the junk suffix [Ξ] is DISCARDED — the landed S-ForallR row  *)
(*  (prop_lift.v §10) at the typing level: restrict-push-run-peel, plus    *)
(*  the one step S-ForallR did not have — the RESULT CLOSE: the e-rule     *)
(*  pins its body result to [open A' α2], so take [A' := close α2 B'']     *)
(*  (cancellation is premise-free).  The e-rule comes in as [Hrule], the   *)
(*  related subjects as [t] / [t'].                                        *)
(* ===================================================================== *)

Lemma lift_typing_check_step_of_rule :
  forall t t' α Θa Θb A0 A Ξ S0 Θ0' P0' ρ V,
  (forall α S0 S1 Θ0 Θ1 A0 A Ξ,
     a_suffix Ξ ->
     uniq (Ξ ++ Θ0) ->
     (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
     α `notin` ftvar_in_ptyp A ->
     α `notin` S0 ->
     {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
        ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
        t' ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
        ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}e ->
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ]
        t' ⦂ (ptyp_all A) ⊣ Θ1 }}e) ->
  a_suffix Ξ ->
  uniq (Ξ ++ Θa) ->
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
  α `notin` dom (Ξ ++ Θa) `union` dom Θb `union`
    ftvar_in_ptyp A0 `union` ftvar_in_ptyp A `union` ftvar_in_exp t ->
  {{ ((α ~ abind_tvar) ++ Θa)
    ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
    t ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
    ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θb) }}a ->
  lift_typing_concl mode_tc ((α ~ abind_tvar) ++ Θa)
    (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) t
    (open_ptyp_wrt_ptyp A (ptyp_var_f α)) (Ξ ++ (α ~ abind_tvar) ++ Θb) ->
  rel_aenv ρ V Θa Θ0' ->
  rel_pskl ρ V (ptyp_to_pskl (ptyp_all A0)) P0' ->
  rel_exp ρ V t t' ->
  flex_agree_rel ρ V Θa Θ0' ->
  rel_inj ρ V ->
  rel_fun ρ V (dom Θa) ->
  {{ ⊢ Θa }}a ->
  uniq Θ0' ->
  ftvar_in_aenv Θ0' [<=] S0 ->
  V [<=] ftvar_in_aenv Θa ->
  (forall a, a `in` dom Θb -> a `notin` dom Θa -> a `notin` cols_l ρ) ->
  dom Θ0' [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  ftvar_in_pskl P0' ∪ ftvar_in_exp t' ∪ fvar_in_exp t' [<=] S0 ->
  {{ Θa ⨟ empty ⊢ₚₛ (ptyp_to_pskl (ptyp_all A0)) }}a ->
  {{ Θa ⊢ᵉ t }}a ->
  lift_typing_post Θa (ptyp_all A) Θb S0 mode_tc Θ0' P0' t' ρ V.
Proof.
  intros t t' α Θa Θb A0 A Ξ S0 Θ0' P0' ρ V Hrule Hsuf Huq Hgam Hαf Ht IHt
    HrΘ HrP0 HrE Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP
    Hwfp0 Hwfe.
  destruct (@rel_pskl_ptyp_image_r ρ V (ptyp_all A0) P0' HrP0)
    as (T0 & -> & HrAll0).
  destruct (rel_ptyp_all_inv HrAll0) as (A0' & -> & HrA0).
  destruct (atom_fresh S0) as [α2 Hα2].
  rewrite dom_app in Hαf.
  assert (Hαd : α `notin` dom Θa) by (clear - Hαf; fsetdec).
  assert (HαΞ : α `notin` dom Ξ) by (clear - Hαf; fsetdec).
  assert (HfrA0 : α `notin` ftvar_in_ptyp A0) by (clear - Hαf; fsetdec).
  assert (HfrA : α `notin` ftvar_in_ptyp A) by (clear - Hαf; fsetdec).
  assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HfrΘ : α `notin` ftvar_in_aenv Θa) by (clear - Hαd Hsc0; fsetdec).
  assert (HαV : α `notin` V)
    by (intros Hin; apply HfrΘ; apply Hscp; exact Hin).
  assert (Hα2d : α2 `notin` dom Θ0') by (clear - Hα2 HdΘ; fsetdec).
  assert (Hα2V : α2 `notin` V) by (clear - Hα2 Hcov; fsetdec).
  assert (Hα2f : α2 `notin` ftvar_in_aenv Θ0')
    by (clear - Hα2 Hftv2; fsetdec).
  (* ---- the SUBJECT's atoms live in Θa — the PAID restriction:
     [a_typing_fvar_binds] for the term variables (the opener's entry
     strips by KIND), the wf for the type variables ---- *)
  assert (Hfve : fvar_in_exp t [<=] dom Θa).
  { intros z Hz.
    destruct (a_typing_fvar_binds Ht Hz) as (bd & Hb & Htm).
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[E Ebd] | Hb0];
      [ exfalso; subst bd; simpl in Htm; exact Htm
      | eapply binds_In; exact Hb0 ]. }
  assert (Hfte : ftvar_in_exp t [<=] dom Θa)
    by (apply a_wf_exp_ftv_dom; exact Hwfe).
  assert (Hαe : α `notin` fvar_in_exp t
                  ∪ ftvar_in_exp t)
    by (clear - Hαf Hfve Hαd; fsetdec).
  assert (Hα2e : α2 `notin` fvar_in_exp t'
                   ∪ ftvar_in_exp t')
    by (clear - Hα2 HcovP; fsetdec).
  (* ⭐ FIRST restrict at the JUNK SUFFIX's domain (§8c.39): the rule
     freshens Ξ only against the CONTEXT, so its names can collide with
     ρ's left column — and then the block premise is underivable. *)
  assert (HdisjΞ : disjoint Ξ Θa) by (clear - Huq; solve_uniq).
  unfold disjoint in HdisjΞ.
  assert (HΞΘa : dom Ξ ∩ ftvar_in_aenv Θa [=] empty)
    by (clear - HdisjΞ Hsc0; fsetdec).
  assert (HΞP0 : dom Ξ ∩ ftvar_in_pskl (ptyp_to_pskl (ptyp_all A0))
                 [=] empty).
  { assert (Hsub : ftvar_in_pskl (ptyp_to_pskl (ptyp_all A0)) [<=] dom Θa).
    { intros z Hz. apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds Hwfp0 Hz). }
    clear - HdisjΞ Hsub. fsetdec. }
  assert (HΞe : dom Ξ ∩ (fvar_in_exp t
                         ∪ ftvar_in_exp t) [=] empty)
    by (clear - HdisjΞ Hfve Hfte; fsetdec).
  destruct (lift_restrict_junk HΞΘa HrΘ Hagr Hinj Hfun Hcov)
    as (Hρ0incl & Hρ0in & Hcl00 & Hcr00 & HΞcols & HrΘ0 & Hagr0 & Hinj0
        & Hfun0 & Hcov0).
  assert (HrA00 : rel_pskl (restrict_l (dom Ξ) ρ) V (ptyp_to_pskl A0) (ptyp_to_pskl A0')).
  { apply rel_pskl_restrict_l; [ exact HrA0 | ].
    simpl in HΞP0. clear - HΞP0. fsetdec. }
  assert (HrE0 : rel_exp (restrict_l (dom Ξ) ρ) V t t')
    by (apply rel_exp_restrict_l; [ exact HrE | exact HΞe ]).
  set (ρ0 := restrict_l (dom Ξ) ρ) in *. clearbody ρ0.
  (* ---- the pair restriction and the PUSH ---- *)
  assert (Hcl0 : cols_l (restrict_pairs α α2 ρ0) [<=] cols_l ρ0)
    by apply cols_l_restrict_pairs.
  destruct (lift_consis_open_pair HrΘ0 Hagr0 Hinj0 Hfun0 HfrΘ Hα2f HαV Hα2V)
    as (HrΘ' & Hagr' & Hinj' & Hfun').
  assert (Hblk0 : forall a, a `in` dom Θb -> a `notin` dom Θa ->
                  a `notin` cols_l ρ0)
    by (intros a Ha Hn; pose proof (Hblk a Ha Hn) as Hc;
        clear - Hc Hcl00; fsetdec).
  destruct (lift_consis_open_scope Hwf Huq2p Hftv2 Hscp Hblk0 HdΘ Hcov0 Hαd
              Hα2d)
    as (Hwf' & Huq2' & Hftv2' & Hscp' & _ & HdΘ' & Hcov').
  assert (Hα2A0' : α2 `notin` ftvar_in_pskl (ptyp_to_pskl A0'))
    by (simpl in HcovP; clear - Hα2 HcovP; fsetdec).
  assert (HαA0 : α `notin` ftvar_in_pskl (ptyp_to_pskl A0)).
  { pose proof (ftvar_ptyp_to_pskl A0) as He. clear - He HfrA0. fsetdec. }
  assert (HrA0r : rel_pskl (restrict_pairs α α2 ρ0) V
                    (ptyp_to_pskl A0) (ptyp_to_pskl A0'))
    by (apply rel_pskl_restrict;
        [ exact HrA00 | exact HαA0 | exact Hα2A0' ]).
  assert (HrP0' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ0) V
                    (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
                    (ptyp_to_pskl (open_ptyp_wrt_ptyp A0' (ptyp_var_f α2)))).
  { rewrite !ptyp_to_pskl_open. apply rel_pskl_open_pair. exact HrA0r. }
  assert (HrE' : rel_exp ((α, α2) :: restrict_pairs α α2 ρ0) V
                   t t').
  { eapply rel_exp_mono;
      [ apply rel_exp_restrict; [ exact HrE0 | exact Hαe | exact Hα2e ]
      | intros z y Hz; right; exact Hz | intros z Hz; exact Hz ]. }
  assert (HcovP' : ftvar_in_pskl
                     (ptyp_to_pskl (open_ptyp_wrt_ptyp A0' (ptyp_var_f α2)))
                   ∪ ftvar_in_exp t'
                   ∪ fvar_in_exp t' [<=] add α2 S0).
  { rewrite ptyp_to_pskl_open.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                  (ptyp_to_pskl A0') (pskl_var_f α2)) as Hu1.
    simpl in Hu1, HcovP. clear - Hu1 HcovP. fsetdec. }
  assert (Hwfp0' : {{ ((α ~ abind_tvar) ++ Θa) ⨟ empty ⊢ₚₛ
                     (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) }}a).
  { rewrite ptyp_to_pskl_open.
    apply a_wf_pskl_all_syn_open_tvar; [ exact Hwfp0 | ].
    clear - Hαd HαA0. fsetdec. }
  assert (Hwfe' : {{ ((α ~ abind_tvar) ++ Θa) ⊢ᵉ t }}a)
    by (apply a_wf_exp_weaken_cons; exact Hwfe).
  assert (Hblk' : forall a, a `in` dom (Ξ ++ (α ~ abind_tvar) ++ Θb) ->
            a `notin` dom ((α ~ abind_tvar) ++ Θa) ->
            a `notin` cols_l ((α, α2) :: restrict_pairs α α2 ρ0)).
  { intros a Ha Hn. simpl in Ha, Hn |- *.
    assert (Hne : a <> α) by (clear - Hn; fsetdec).
    repeat rewrite dom_app in Ha. simpl dom in Ha.
    assert (Hc : a `notin` cols_l ρ0).
    { destruct (AtomSetProperties.In_dec a (dom Ξ)) as [HaΞ | HaΞ].
      - exact (HΞcols a HaΞ).
      - assert (HaΘb : a `in` dom Θb) by (clear - Ha HaΞ Hne; fsetdec).
        assert (Hc0 : a `notin` cols_l ρ)
          by (apply Hblk; [ exact HaΘb | clear - Hn; fsetdec ]).
        clear - Hc0 Hcl00. fsetdec. }
    clear - Hne Hc Hcl0. fsetdec. }
  destruct (IHt (add α2 S0) ((α2 ~ abind_tvar) ++ Θ0')
              (ptyp_to_pskl (open_ptyp_wrt_ptyp A0' (ptyp_var_f α2)))
              t'
              ((α, α2) :: restrict_pairs α α2 ρ0) V
              HrΘ' HrP0' HrE' Hagr' Hinj' Hfun' Hwf' Huq2' Hftv2' Hscp'
              Hblk' HdΘ' Hcov' HcovP' Hwfp0' Hwfe'
              (a_ty_mode_compat__tc (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))))
    as (S1 & ρe & Θ1out & B'' & De & HrΘout & Hagrout & HrB'' & Hext
        & Hdomout).
  (* ---- side 1's output, via [a_typing]'s own soundness ---- *)
  destruct (a_typing_sound Ht Hwf' Hwfp0'
              (a_ty_mode_compat__tc (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
              Hwfe') as [Hle [HwfOut _]].
  assert (HcovS : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0')
                  ∪ ftvar_in_pskl
                      (ptyp_to_pskl (open_ptyp_wrt_ptyp A0' (ptyp_var_f α2)))
                  ∪ fvar_in_exp t'
                  ∪ ftvar_in_exp t' [<=] add α2 S0)
    by (clear - Hftv2' HcovP'; fsetdec).
  destruct (e_typing_sound De Huq2' HcovS) as (_ & HuqOut2 & _).
  (* ---- split the output at the junk and the opener, and hand it back at
     the CALLER's pair list ---- *)
  destruct (lift_opener_strip Hρ0incl HΞcols Hinj Hfun Hcov Hwf Hscp Hblk
              Huq Huq2p HdΘ HαV HαΞ Hinj' Hcov' HwfOut HrΘout Hext Hdomout
              HuqOut2)
    as (Ξ2 & Θ1' & -> & HrΞ2 & Huq2Ξ & Hinjout & Hαρe & Hα2ρe & HrΘfin
        & Hagrfin & Hextfin & Hdomeo).
  (* ⭐ THE RESULT CLOSE and side 2's own rule premises *)
  assert (Hα2B'' : α2 `notin` ftvar_in_ptyp (close_ptyp_wrt_ptyp α2 B''))
    by (rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp; clear; fsetdec).
  assert (Hγ2 : forall γ, γ `in` dom Ξ2 ->
            γ `notin` ftvar_in_ptyp (close_ptyp_wrt_ptyp α2 B'')).
  { intros γ Hγ Hc.
    rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp in Hc.
    assert (HγB : γ `in` ftvar_in_ptyp B'') by (clear - Hc; fsetdec).
    assert (HγB2 : γ `in` ftvar_in_pskl (ptyp_to_pskl B'')).
    { pose proof (ftvar_ptyp_to_pskl B'') as He. clear - He HγB. fsetdec. }
    destruct (rel_pskl_ftv_corr_r HrB'' HγB2) as (a & Ha & Hat).
    destruct (rel_aenv_dom_r_inv HrΞ2 Hγ) as (a' & Ha' & Hat').
    assert (Ea : a' = a) by (exact (Hinjout a' a γ Hat' Hat)).
    subst a'.
    assert (HaA : a `in` ftvar_in_ptyp
                          (open_ptyp_wrt_ptyp A (ptyp_var_f α))).
    { pose proof (ftvar_ptyp_to_pskl
                    (open_ptyp_wrt_ptyp A (ptyp_var_f α))) as He.
      clear - He Ha. fsetdec. }
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A (ptyp_var_f α))
      as Hup. simpl in Hup.
    assert (Hne : a <> α) by (intros ->; clear - Ha' HαΞ; fsetdec).
    assert (HaftA : a `in` ftvar_in_ptyp A)
      by (clear - HaA Hup Hne; fsetdec).
    exact (Hgam a Ha' HaftA). }
  assert (Dc : {{ S0 ↝ S1 ⊨ Θ0' ⊢[ mode_tc ;
                  (ptyp_to_pskl (ptyp_all A0')) ] t'
                  ⦂ (ptyp_all (close_ptyp_wrt_ptyp α2 B'')) ⊣ Θ1' }}e).
  { apply Hrule with (α := α2) (Ξ := Ξ2);
      [ eapply rel_aenv_suffix; [ exact HrΞ2 | exact Hsuf ]
      | exact Huq2Ξ
      | exact Hγ2
      | exact Hα2B''
      | exact Hα2
      | rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp; exact De ]. }
  (* ---- the ∀-REL: close both bodies, land on the caller's list ---- *)
  assert (HαclρE : α `notin` cols_l ρe).
  { intros Hc. destruct (cols_l_in_inv _ _ Hc) as (b0 & Hin).
    exact (Hαρe _ Hin). }
  assert (Hα2crρE : α2 `notin` cols_r ρe).
  { intros Hc. destruct (cols_r_in_inv _ _ Hc) as (a0 & Hin).
    exact (Hα2ρe _ Hin). }
  assert (HrClose : rel_pskl (ρe ++ ρ0) V
                      (ptyp_to_pskl (close_ptyp_wrt_ptyp α
                         (open_ptyp_wrt_ptyp A (ptyp_var_f α))))
                      (ptyp_to_pskl (close_ptyp_wrt_ptyp α2 B''))).
  { rewrite !ptyp_to_pskl_close.
    apply rel_pskl_close_pair_restrict with (ρa := ρe) (ρ := ρ0);
      [ exact HrB'' | exact HαV | exact HαclρE | exact Hα2V
      | exact Hα2crρE
      | intros a b0 Hin; apply in_or_app; left; exact Hin
      | intros a b0 Hin; apply in_or_app; right; exact Hin ]. }
  rewrite (close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp A α HfrA) in HrClose.
  assert (HΞftA : dom Ξ ∩ ftvar_in_pskl (ptyp_to_pskl A) [=] empty).
  { pose proof (ftvar_ptyp_to_pskl A) as He.
    intros z. split; intros Hz; [ exfalso | exfalso; clear - Hz; fsetdec ].
    assert (Hz1 : z `in` dom Ξ) by (clear - Hz; fsetdec).
    assert (Hz2 : z `in` ftvar_in_pskl (ptyp_to_pskl A))
      by (clear - Hz; fsetdec).
    assert (Hz3 : z `in` ftvar_in_ptyp A) by (clear - He Hz2; fsetdec).
    exact (Hgam z Hz1 Hz3). }
  assert (HinclA : forall a b0,
            In (a, b0) (restrict_l (dom Ξ) (ρe ++ ρ0)) ->
            In (a, b0) ((restrict_l (dom Ξ) ρe) ++ ρ)).
  { intros a b0 Hin.
    assert (HaΞ : a `notin` dom Ξ).
    { intros Ha. apply (restrict_l_notin (ρe ++ ρ0) Ha).
      eapply cols_l_in; exact Hin. }
    apply restrict_l_incl in Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - apply in_or_app; left. apply restrict_l_in; assumption.
    - apply in_or_app; right. apply Hρ0incl. exact Hin. }
  assert (HrCloseR : rel_pskl (restrict_l (dom Ξ) (ρe ++ ρ0)) V
                       (ptyp_to_pskl A)
                       (ptyp_to_pskl (close_ptyp_wrt_ptyp α2 B'')))
    by (apply rel_pskl_restrict_l; [ exact HrClose | exact HΞftA ]).
  assert (HrQfin : rel_ptyp ((restrict_l (dom Ξ) ρe) ++ ρ) V (ptyp_all A)
                     (ptyp_all (close_ptyp_wrt_ptyp α2 B''))).
  { unfold rel_ptyp. simpl. apply rel_pskl__all_syn.
    eapply rel_pskl_mono;
      [ exact HrCloseR | exact HinclA | intros z Hz; exact Hz ]. }
  exists S1, (restrict_l (dom Ξ) ρe), Θ1', (ptyp_all (close_ptyp_wrt_ptyp α2 B'')).
  exact (conj Dc (conj HrΘfin (conj Hagrfin (conj HrQfin (conj Hextfin
    Hdomeo))))).
Qed.

(* ===================================================================== *)
(*  ⭐ THE [_check_base] ROWS' JUNK STRIP, shared by AT-AbsCheckBase and    *)
(*  AT-AbsAnnoCheckBase.  Both run a middle stage (the split, plus the     *)
(*  consis-chk for the annotated row) at pairs [ρm] over the caller's      *)
(*  list restricted at the junk suffix ([ρ0 = restrict_l (dom Ξ) ρ]),      *)
(*  then the body through [lift_typing_abs_core], which KEEPS [Ξ]; these   *)
(*  rows DROP it.  What is left after the core is the same for both: side  *)
(*  2's junk is apart from the middle output (the e-rule's [uniq] and      *)
(*  γ-filter premises), and the outputs are handed back at the CALLER's   *)
(*  pair list with the junk's pairs cut off.                              *)
(* ===================================================================== *)

Lemma lift_check_base_strip :
  forall {ρ ρ0 ρm ρe2 V Ξ Ξ2 Θa Θm Θm' Θout Θout' S0 Sm S2 x x2 A A2 Ad Ad'
          B0' B1 B1' eb2},
  (forall a b, In (a, b) ρ0 -> In (a, b) ρ) ->
  (forall a, a `in` dom Ξ -> a `notin` cols_l ρ0) ->
  rel_inj ρ V ->
  rel_fun ρ V (dom Θa) ->
  V ∪ cols_r ρ [<=] S0 ->
  {{ ⊢ Θa }}a ->
  V [<=] ftvar_in_aenv Θa ->
  (forall a, a `in` dom Θout -> a `notin` dom Θa -> a `notin` cols_l ρ) ->
  rel_ext ρm (ftvar_in_aenv Θa) S0 ->
  (forall a b, In (a, b) ρm -> a `in` dom Θm /\ b `in` dom Θm') ->
  S0 [<=] Sm ->
  dom Θm' [<=] Sm ->
  uniq Θm' ->
  ftvar_in_aenv Θm' [<=] Sm ->
  dom Θa [<=] dom Θm ->
  dom Θm [<=] dom Θout ->
  uniq (Ξ ++ Θm) ->
  rel_inj (ρm ++ ρ0) V ->
  V ∪ cols_r (ρm ++ ρ0) [<=] Sm ->
  {{ ⊢ (Ξ ++ (x ~ abind_var_typ A) ++ Θout) }}a ->
  x2 `notin` Sm ->
  ftvar_in_ptyp A2 ∪ ftvar_in_pskl (ptyp_to_pskl B0') ∪ ftvar_in_exp eb2
    ∪ fvar_in_exp eb2 [<=] Sm ->
  {{ (add x2 Sm) ↝ S2 ⊨ ((x2 ~ abind_var_typ A2) ++ Θm')
     ⊢[ mode_tc ; (ptyp_to_pskl B0') ] (open_exp_wrt_exp eb2 (exp_var_f x2))
     ⦂ B1' ⊣ (Ξ2 ++ (x2 ~ abind_var_typ A2) ++ Θout') }}e ->
  rel_aenv (ρe2 ++ ρm ++ ρ0) V Ξ Ξ2 ->
  rel_aenv (ρe2 ++ ρm ++ ρ0) V Θout Θout' ->
  rel_ptyp (ρe2 ++ ρm ++ ρ0) V B1 B1' ->
  rel_ext ρe2 (ftvar_in_aenv Θm) Sm ->
  (forall a b, In (a, b) ρe2 ->
     a `in` dom (Ξ ++ Θout) /\ b `in` dom (Ξ2 ++ Θout')) ->
  dom Θm' [<=] dom (Ξ2 ++ Θout') ->
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1) ->
  rel_ptyp (ρm ++ ρ0) V Ad Ad' ->
  ftvar_in_ptyp Ad [<=] dom Θm ->
  uniq (Ξ2 ++ Θm')
  /\ (forall γ, γ `in` dom Ξ2 -> γ `notin` ftvar_in_ptyp B1')
  /\ rel_aenv (restrict_l (dom Ξ) (ρe2 ++ ρm) ++ ρ) V Θout Θout'
  /\ flex_agree_rel (restrict_l (dom Ξ) (ρe2 ++ ρm) ++ ρ) V Θout Θout'
  /\ rel_ptyp (restrict_l (dom Ξ) (ρe2 ++ ρm) ++ ρ) V
       (ptyp_arrow Ad B1) (ptyp_arrow Ad' B1')
  /\ rel_ext (restrict_l (dom Ξ) (ρe2 ++ ρm)) (ftvar_in_aenv Θa) S0
  /\ (forall a b, In (a, b) (restrict_l (dom Ξ) (ρe2 ++ ρm)) ->
        a `in` dom Θout /\ b `in` dom Θout').
Proof.
  intros ρ ρ0 ρm ρe2 V Ξ Ξ2 Θa Θm Θm' Θout Θout' S0 Sm S2 x x2 A A2 Ad Ad'
    B0' B1 B1' eb2 Hρ0incl HΞcols Hinj Hfun Hcov Hwf Hscp Hblk Hextm Hdomm
    Hgrm HdΘm' HuqΘm' HftvΘm' Hdm0 Hdmout Huq Hinj1 HcovX HwfOutB Hx2S HcovPX
    De HrFΞ HrFΘ HrB1' HextF HdomF Hdm2 Hgam HrAs HftAd.
  assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HdisjΞ : disjoint Ξ Θm) by (clear - Huq; solve_uniq).
  unfold disjoint in HdisjΞ.
  (* ---- side 2's package at the body's output ---- *)
  assert (Hx2Θm' : x2 `notin` dom Θm') by (clear - Hx2S HdΘm'; fsetdec).
  assert (Huq2X : uniq ((x2 ~ abind_var_typ A2) ++ Θm'))
    by (clear - HuqΘm' Hx2Θm'; solve_uniq).
  assert (HcovDe : ftvar_in_aenv ((x2 ~ abind_var_typ A2) ++ Θm')
                   ∪ ftvar_in_pskl (ptyp_to_pskl B0')
                   ∪ fvar_in_exp (open_exp_wrt_exp eb2 (exp_var_f x2))
                   ∪ ftvar_in_exp (open_exp_wrt_exp eb2 (exp_var_f x2))
                   [<=] add x2 Sm).
  { pose proof (ftvar_in_exp_open_exp_wrt_exp_upper eb2 (exp_var_f x2))
      as Hu1.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper eb2 (exp_var_f x2))
      as Hu2.
    simpl in Hu1, Hu2. simpl.
    clear - Hu1 Hu2 HftvΘm' HcovPX. fsetdec. }
  destruct (e_typing_sound De Huq2X HcovDe) as (_ & HuqOutDe & _).
  assert (Hinjcore : rel_inj (ρe2 ++ ρm ++ ρ0) V)
    by (eapply rel_inj_app; [ exact Hinj1 | exact HextF | exact HcovX ]).
  split.
  (* ---- side 2's junk is apart from the middle output ---- *)
  { apply uniq_app_4.
    - clear - HuqOutDe. solve_uniq.
    - exact HuqΘm'.
    - apply disjoint_from_pointwise. intros b0 Hb0.
      destruct (rel_aenv_dom_r_inv HrFΞ Hb0) as (a' & Ha' & Hat').
      inversion Hat' as [ z0 y0 Hin | z0 HinV ]; subst.
      + apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        * destruct HextF as [Hxfr _]. destruct (Hxfr _ _ Hin) as [_ Hnb].
          clear - Hnb HdΘm'. fsetdec.
        * apply in_app_or in Hin. destruct Hin as [Hin | Hin].
          -- exfalso. destruct (Hdomm _ _ Hin) as [Hd1 _].
             clear - HdisjΞ Ha' Hd1. fsetdec.
          -- exfalso. apply (HΞcols a' Ha'). eapply cols_l_in. exact Hin.
      + exfalso.
        assert (Had : b0 `in` dom Θa)
          by (apply Hscp in HinV; clear - HinV Hsc0; fsetdec).
        clear - HdisjΞ Ha' Had Hdm0. fsetdec. }
  split.
  (* ---- the γ-filter on the RESULT, via the correspondence ---- *)
  { intros γ Hγ Hc.
    assert (HγB2 : γ `in` ftvar_in_pskl (ptyp_to_pskl B1')).
    { pose proof (ftvar_ptyp_to_pskl B1') as He. clear - He Hc. fsetdec. }
    destruct (rel_pskl_ftv_corr_r HrB1' HγB2) as (a & Ha & Hat).
    destruct (rel_aenv_dom_r_inv HrFΞ Hγ) as (a' & Ha' & Hat').
    assert (Ea : a' = a) by (exact (Hinjcore a' a γ Hat' Hat)).
    subst a'.
    assert (HaB1 : a `in` ftvar_in_ptyp B1).
    { pose proof (ftvar_ptyp_to_pskl B1) as He. clear - He Ha. fsetdec. }
    exact (Hgam a Ha' HaB1). }
  (* ---- THE JUNK STRIP: hand back at the CALLER's pair list ---- *)
  set (ρef := restrict_l (dom Ξ) (ρe2 ++ ρm)).
  assert (Hinclr : forall a b,
    In (a, b) (restrict_l (dom Ξ) (ρe2 ++ ρm ++ ρ0)) -> In (a, b) (ρef ++ ρ)).
  { unfold ρef. intros a b Hin. eapply restrict_l_app_restore;
      [ exact Hρ0incl | rewrite !app_assoc; exact Hin ]. }
  (* dom Ξ is apart from Θout (side 1's own output uniq) *)
  assert (HuqOutB : uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θout))
    by (apply a_wf_aenv_uniq; exact HwfOutB).
  assert (HΞΘout : dom Ξ ∩ dom Θout [=] empty).
  { assert (Hd : disjoint Ξ ((x ~ abind_var_typ A) ++ Θout))
      by (clear - HuqOutB; solve_uniq).
    unfold disjoint in Hd. simpl in Hd. clear - Hd. fsetdec. }
  assert (HwfΘout : {{ ⊢ Θout }}a).
  { eapply a_wf_aenv_strip_prefix.
    eapply a_wf_aenv_strip_prefix with (Ξ := Ξ). simpl_env. exact HwfOutB. }
  assert (HftvΘout : ftvar_in_aenv Θout [<=] dom Θout)
    by (apply a_wf_aenv_ftv_dom; exact HwfΘout).
  assert (HΞfΘout : dom Ξ ∩ ftvar_in_aenv Θout [=] empty)
    by (clear - HΞΘout HftvΘout; fsetdec).
  assert (HrΘfin : rel_aenv (ρef ++ ρ) V Θout Θout').
  { eapply rel_aenv_mono;
      [ exact (rel_aenv_restrict_l HrFΘ HΞfΘout)
      | exact Hinclr | intros z Hz; exact Hz ]. }
  assert (Hextfin : rel_ext ρef (ftvar_in_aenv Θa) S0).
  { assert (Hd1s : dom Θm [<=] ftvar_in_aenv Θm)
      by (apply dom_subset_ftvar_in_aenv).
    assert (Hcomb : rel_ext (ρe2 ++ ρm) (ftvar_in_aenv Θa) S0).
    { eapply rel_ext_app;
        [ exact Hextm | exact HextF
        | clear - Hsc0 Hdm0 Hd1s; fsetdec
        | exact Hgrm
        | intros a b0 Hin; destruct (Hdomm _ _ Hin) as [Hd1 Hd2];
          split; [ clear - Hd1 Hd1s; fsetdec
                 | clear - Hd2 HdΘm'; fsetdec ] ]. }
    unfold ρef. apply rel_ext_restrict_l; exact Hcomb. }
  split; [ exact HrΘfin | ].
  split.
  { eapply rel_aenv_flex_agree_ext;
      [ exact HrΘfin | exact Hinj | exact Hfun | exact Hextfin
      | apply dom_subset_ftvar_in_aenv
      | clear - Hscp Hsc0; fsetdec | exact Hcov | exact Hblk ]. }
  split.
  (* ---- the RESULT's relation, restricted off the junk ---- *)
  { assert (HΞftAd : dom Ξ ∩ ftvar_in_pskl (ptyp_to_pskl Ad) [=] empty).
    { pose proof (ftvar_ptyp_to_pskl Ad) as He.
      clear - He HftAd HdisjΞ. fsetdec. }
    assert (HΞftB1 : dom Ξ ∩ ftvar_in_pskl (ptyp_to_pskl B1) [=] empty).
    { pose proof (ftvar_ptyp_to_pskl B1) as He.
      intros z. split; intros Hz; [ exfalso | exfalso; clear - Hz; fsetdec ].
      assert (Hz1 : z `in` dom Ξ) by (clear - Hz; fsetdec).
      assert (Hz3 : z `in` ftvar_in_ptyp B1) by (clear - He Hz; fsetdec).
      exact (Hgam z Hz1 Hz3). }
    assert (HrAs2 : rel_pskl (ρe2 ++ ρm ++ ρ0) V (ptyp_to_pskl Ad)
                      (ptyp_to_pskl Ad'))
      by (eapply rel_pskl_mono;
          [ exact HrAs
          | intros u v Hu; apply in_or_app; right; exact Hu
          | intros u Hu; exact Hu ]).
    unfold rel_ptyp. simpl. constructor.
    - eapply rel_pskl_mono;
        [ apply rel_pskl_restrict_l; [ exact HrAs2 | exact HΞftAd ]
        | exact Hinclr | intros z Hz; exact Hz ].
    - eapply rel_pskl_mono;
        [ apply rel_pskl_restrict_l; [ exact HrB1' | exact HΞftB1 ]
        | exact Hinclr | intros z Hz; exact Hz ]. }
  split; [ exact Hextfin | ].
  unfold ρef. eapply rel_aenv_restrict_l_dom;
    [ exact HrFΞ | exact Hinjcore
    | intros a b Hin; repeat rewrite <- app_assoc in Hin;
      repeat rewrite <- app_assoc;
      apply in_or_app; auto | ].
  intros a b Hin. apply in_app_or in Hin; destruct Hin as [Hin | Hin].
  - exact (HdomF _ _ Hin).
  - destruct (Hdomm _ _ Hin) as [Ha Hb].
    split; [ rewrite dom_app; apply AtomSetImpl.union_3; apply Hdmout; exact Ha
           | apply Hdm2; exact Hb ].
Qed.

Theorem a_typing_rel_e : forall m Θ0 P0 e B Θ1,
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}a ->
  lift_typing_concl m Θ0 P0 e B Θ1.
Proof.
  intros m Θ0 P0 e B Θ1 H; induction H as
    [ m0 Θa P0a A Θb Hsub
    | m0 Θa P0a x A B0 Θb Hb Hsub
    | m0 Θa P0a ea A B0 Θb Θc Ht IHt Hsub
    | Θa ea A B0 Θb Θc Ht IHt Hchk
    | x m0 Θa Θb Θc P0a Pa Q0 αs A ea B0 Ξ Hne Hsp Hgm Huq Hsuf Hxf Ht IHt
    | x m0 Θa Θb Θc Θd P0a Pa Q0 A ea B0 Ξ Hne Hsp Hchk Hsuf Hxf Ht IHt
    | α Θa Θb A0 ea A Ξ Hsuf Huq Hgam Hαf Ht IHt
    | x Θa Θb Θc A0 A B0 B1 ea Ξ Hsp Hsuf Huq Hgam Hxf Ht IHt
    | α Θa Θb A0 Aan ea A Ξ Hsuf Huq Hgam Hαf Ht IHt
    | x Θa Θb Θc Θd A0 A' A B0 B1 ea Ξ Hsp Hchk Hsuf Huq Hgam Hxf Ht IHt
    | m0 Θa Θb Θc Θd Pa Q0 A A' B0 e1 e2 Hp2 Ht1 IHt1 Ht2 IHt2 ];
    intros S0 Θ0' P0' e' ρ V HrΘ HrP0 HrE Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfe Hmod.
  - (* AT-Unit *)
    inversion HrE; subst.
    assert (HcovS : ftvar_in_pskl P0' ∪ ftvar_in_pskl pskl_unit [<=] S0)
      by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
    destruct (lift_typing_sub Hsub HrΘ HrP0 (rel_pskl__unit ρ V) Hagr Hinj
                Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovS Hwfp0
                (a_wf_pskl__unit Θa empty))
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    destruct (@rel_pskl_ptyp_image_r (ρe ++ ρ) V A Q' HrQ)
      as (A' & -> & HrA').
    exists S1, ρe, Θ1', A'.
    split; [ apply e_typing__unit; exact De | ].
    exact (conj HrΘ1 (conj Hagr1 (conj HrA' (conj Hext Hdom1)))).
  - (* AT-Var *)
    inversion HrE as [ | | x1 x2 Hat | | | | | ]; subst.
    destruct (@rel_aenv_binds_pin ρ V Θa Θ0' x x2 (abind_var_typ A)
                HrΘ Hfun Hb Hat) as (bd2 & Habd & Hb2).
    inversion Habd as [ | | | A1 A2 HrA | ]; subst.
    assert (HcovS : ftvar_in_pskl P0' ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] S0).
    { pose proof (@rel_pskl_ftv_r ρ V (ptyp_to_pskl A) (ptyp_to_pskl A2)
                    HrA) as HA2.
      clear - HcovP HA2 Hcov. simpl in HcovP. fsetdec. }
    assert (HwfA : {{ Θa ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl;
          eapply a_wf_aenv_binds_var_typ_wf; [ exact Hwf | exact Hb ]).
    destruct (lift_typing_sub Hsub HrΘ HrP0 HrA Hagr Hinj Hfun Hwf Huq2p
                Hftv2 Hscp Hblk HdΘ Hcov HcovS Hwfp0 HwfA)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    destruct (@rel_pskl_ptyp_image_r (ρe ++ ρ) V B0 Q' HrQ)
      as (B' & -> & HrB').
    exists S1, ρe, Θ1', B'.
    split; [ eapply e_typing__var; [ exact Hb2 | exact De ] | ].
    exact (conj HrΘ1 (conj Hagr1 (conj HrB' (conj Hext Hdom1)))).
  - (* ⭐ AT-Anno — the recursive call at (TC, ⌈A⌉), whose RESULT the rule
       PINS to the annotation.  The IH gives only a RELATED result, and the
       pin is recovered by [rel_pskl_fun_dom] — functionality of the
       relation at [dom Θ0], where wf puts [⌈A⌉]'s atoms. *)
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb0
                     | A1 A2 eb1 eb2 HrA0 HrEb0
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb HrA | eb1 eb2 HrEb0 ]; subst.
    inversion Hwfe as [ | | Θw ew Aw HwfA Hwfeb | | | | ]; subst.
    assert (Hdm0 : dom Θa [<=] dom Θb) by (exact (a_typing_dom_mono Ht)).
    assert (Hdm1 : dom Θb [<=] dom Θc)
      by (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hsub)).
    assert (Hblk1 : forall a, a `in` dom Θb -> a `notin` dom Θa ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk; [ clear - Ha Hdm1; fsetdec | exact Hn ]).
    assert (HwfcA : {{ Θa ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfA).
    assert (HcovP1 : ftvar_in_pskl (ptyp_to_pskl A2) ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S0)
      by (rewrite ftvar_ptyp_to_pskl; simpl in HcovP; clear - HcovP; fsetdec).
    destruct (IHt S0 Θ0' (ptyp_to_pskl A2) eb2 ρ V HrΘ HrA HrEb
                Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk1 HdΘ Hcov HcovP1
                HwfcA Hwfeb (a_ty_mode_compat__tc A))
      as (S1 & ρe1 & Θb' & B'' & D1e & HrΘ1 & Hagr1 & HrB'' & Hext1 & Hdom1).
    pose proof (e_typing_supply_grows D1e) as Hgr1.
    (* ---- side 2's package at the first call's output ---- *)
    assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                    ∪ fvar_in_exp eb2 ∪ ftvar_in_exp eb2 [<=] S0)
      by (clear - Hftv2 HcovP1; fsetdec).
    destruct (e_typing_sound D1e Huq2p HcovE)
      as (Ha1p & Huq1' & Hftv1 & HftB'').
    assert (HdΘ1 : dom Θb' [<=] S1)
      by (pose proof (dom_subset_ftvar_in_aenv Θb') as Hd;
          clear - Hd Hftv1; fsetdec).
    (* ---- the widened relation, and the PIN ---- *)
    destruct (lift_seq_widen Hinj Hfun Hext1 Hdom1 Hwf Hscp Hcov Hblk Hdm0
                Hdm1 Hgr1 HdΘ1)
      as (Hinj1 & Hfun1 & Hscp1 & Hcov1 & Hblk2).
    assert (HrA1 : rel_pskl (ρe1 ++ ρ) V (ptyp_to_pskl A) (ptyp_to_pskl A2))
      by (apply rel_pskl_widen; exact HrA).
    assert (HftA : ftvar_in_pskl (ptyp_to_pskl A) [<=] dom Θb).
    { rewrite ftvar_ptyp_to_pskl.
      pose proof (a_wf_ptyp_ftv_dom HwfA) as Hd.
      clear - Hd Hdm0. fsetdec. }
    assert (EB : B'' = A2).
    { apply (@ptyp_to_pskl_inj B'' A2).
      eapply rel_pskl_fun_dom;
        [ exact HrB'' | exact HrA1 | exact Hfun1 | exact HftA ]. }
    subst B''.
    (* ---- side 1's package at the first call's output ---- *)
    destruct (a_typing_sound Ht Hwf HwfcA (a_ty_mode_compat__tc A)
                Hwfeb) as [Hle01 [HwfΘb [HwfAb _]]].
    assert (HwfcAb : {{ Θb ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfAb).
    assert (Hwfp0b : {{ Θb ⨟ empty ⊢ₚₛ P0a }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hwfp0 ]).
    assert (HrP0w : rel_pskl (ρe1 ++ ρ) V P0a P0')
      by (apply rel_pskl_widen; exact HrP0).
    assert (HcovP2 : ftvar_in_pskl P0'
                     ∪ ftvar_in_pskl (ptyp_to_pskl A2) [<=] S1)
      by (simpl in HcovP; rewrite ftvar_ptyp_to_pskl;
          clear - HcovP Hgr1; fsetdec).
    destruct (lift_typing_sub Hsub HrΘ1 HrP0w HrA1 Hagr1 Hinj1 Hfun1
                HwfΘb Huq1' Hftv1 Hscp1 Hblk2 HdΘ1 Hcov1 HcovP2
                Hwfp0b HwfcAb)
      as (S2 & ρe2 & Θc' & Q' & D2e & HrΘ2 & Hagr2 & HrQ2 & Hext2 & Hdom2).
    destruct (@rel_pskl_ptyp_image_r (ρe2 ++ ρe1 ++ ρ) V B0 Q' HrQ2)
      as (B' & -> & HrB').
    (* ---- side 2's dom mono across the sub ---- *)
    assert (HcovE3 : ftvar_in_aenv Θb' ∪ ftvar_in_pskl P0'
                     ∪ ftvar_in_pskl (ptyp_to_pskl A2) [<=] S1)
      by (clear - Hftv1 HcovP2; fsetdec).
    assert (Hdm2' : dom Θb' [<=] dom Θc').
    { pose proof (e_sub_sound D2e Huq1' HcovE3) as Ha2.
      exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Ha2). }
    (* ---- the answer ---- *)
    exists S2, (ρe2 ++ ρe1), Θc', B'.
    split; [ eapply e_typing__anno; [ exact D1e | exact D2e ] | ].
    rewrite app_assoc.
    split; [ exact HrΘ2 | ].
    split; [ exact Hagr2 | ].
    split; [ exact HrB' | ].
    exact (lift_seq_ext Hext1 Hext2 Hdom1 Hdom2 Hwf Hdm0 Hdm1 Hgr1 HdΘ1
             Hdm2').
  - (* ⭐ AT-Freeze — the TI run, then the consis-chk at its output *)
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb0
                     | A1 A2 eb1 eb2 HrA0 HrEb0
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb0 HrA0 | eb1 eb2 HrEb ]; subst.
    inversion Hwfe as [ | | | Θw ew Hwfeb | | | ]; subst.
    destruct (@rel_pskl_ptyp_image_r ρ V A P0' HrP0) as (A2 & -> & HrA2).
    destruct Hchk as [Qc Hcc].
    assert (Hdm0 : dom Θa [<=] dom Θb) by (exact (a_typing_dom_mono Ht)).
    assert (Hdm1 : dom Θb [<=] dom Θc)
      by (exact (a_consis_chk_dom_mono (ex_intro _ Qc Hcc))).
    assert (Hblk1 : forall a, a `in` dom Θb -> a `notin` dom Θa ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk; [ clear - Ha Hdm1; fsetdec | exact Hn ]).
    assert (HcovP1 : ftvar_in_pskl pskl_ghost ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S0)
      by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
    destruct (IHt S0 Θ0' pskl_ghost eb2 ρ V HrΘ (rel_pskl__ghost ρ V) HrEb
                Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk1 HdΘ Hcov HcovP1
                (a_wf_pskl__ghost Θa empty) Hwfeb a_ty_mode_compat__ti)
      as (S1 & ρe1 & Θb' & B'' & D1e & HrΘ1 & Hagr1 & HrB'' & Hext1 & Hdom1).
    pose proof (e_typing_supply_grows D1e) as Hgr1.
    (* ---- side 2's package at the run's output ---- *)
    assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl pskl_ghost
                    ∪ fvar_in_exp eb2 ∪ ftvar_in_exp eb2 [<=] S0)
      by (simpl; simpl in HcovP; clear - Hftv2 HcovP; fsetdec).
    destruct (e_typing_sound D1e Huq2p HcovE)
      as (Ha1p & Huq1' & Hftv1 & HftB'').
    assert (HdΘ1 : dom Θb' [<=] S1)
      by (pose proof (dom_subset_ftvar_in_aenv Θb') as Hd;
          clear - Hd Hftv1; fsetdec).
    (* ---- side 1's package ---- *)
    destruct (a_typing_sound Ht Hwf (a_wf_pskl__ghost Θa empty)
                a_ty_mode_compat__ti Hwfeb) as [Hle01 [HwfΘb [HwfBb _]]].
    assert (HwfcB : {{ Θb ⨟ empty ⊢ₚₛ (ptyp_to_pskl B0) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfBb).
    assert (HwfcAb : {{ Θb ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hwfp0 ]).
    (* ---- the widened relation ---- *)
    destruct (lift_seq_widen Hinj Hfun Hext1 Hdom1 Hwf Hscp Hcov Hblk Hdm0
                Hdm1 Hgr1 HdΘ1)
      as (Hinj1 & Hfun1 & Hscp1 & Hcov1 & Hblk2).
    assert (HrA1 : rel_pskl (ρe1 ++ ρ) V (ptyp_to_pskl A) (ptyp_to_pskl A2))
      by (apply rel_pskl_widen; exact HrA2).
    (* the subject's side-2 coverage comes from the RUN's own output bound *)
    assert (HcovC : ftvar_in_pskl (ptyp_to_pskl A2)
                    ∪ ftvar_in_pskl (ptyp_to_pskl B'') [<=] S1).
    { rewrite ! ftvar_ptyp_to_pskl.
      assert (HA2 : ftvar_in_ptyp A2 [<=] S0)
        by (rewrite ftvar_ptyp_to_pskl in HcovP; clear - HcovP; fsetdec).
      clear - HftB'' HA2 Hgr1. fsetdec. }
    destruct (lift_consis_nil Hcc HrΘ1 HrA1 HrB'' Hagr1 Hinj1 Hfun1
                HwfΘb Huq1' Hftv1 Hscp1 Hblk2 HdΘ1 Hcov1 HcovC
                HwfcAb HwfcB)
      as (S2 & ρe2 & Θc' & Qc' & Dchk & HrΘ2 & Hagr2 & HrQc & Hext2 & Hdom2).
    (* ---- side 2's dom mono across the chk ---- *)
    pose proof (e_consis_supply_grows Dchk) as Hgr2.
    assert (HcovE2 : ftvar_in_aenv Θb'
                     ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                     ∪ ftvar_in_pskl (ptyp_to_pskl B'')
                     ∪ empty ∪ empty [<=] S1)
      by (clear - Hftv1 HcovC; fsetdec).
    assert (Hdm2' : dom Θb' [<=] dom Θc').
    { pose proof (e_consis_sound Dchk Huq1' HcovE2) as Ha2.
      exact (auc_dom_mono_consis Ha2). }
    (* ---- the answer ---- *)
    exists S2, (ρe2 ++ ρe1), Θc', A2.
    split.
    { eapply e_typing__freeze;
        [ exact D1e | exists Qc'; exact Dchk ]. }
    rewrite app_assoc.
    split; [ exact HrΘ2 | ].
    split; [ exact Hagr2 | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrA1
        | intros u v Hu; apply in_or_app; right; exact Hu
        | intros u Hu; exact Hu ]. }
    exact (lift_seq_ext Hext1 Hext2 Hdom1 Hdom2 Hwf Hdm0 Hdm1 Hgr1 HdΘ1
             Hdm2').
  - (* ⭐⭐ AT-Abs — the GUESS-MONO row.  The split is CONTEXT-IDENTITY
       ([a_split_ty_shape], m ≠ TC), the guess contributes a PAIRED BLOCK
       ([a_guess_mono_rel_e]) that SURVIVES into the output (W-Solve's
       discriminator: no restriction), and the CORE does the binder. *)
    destruct (a_split_ty_shape Hsp Hmod Hne) as [HeqΘ Hshape]. subst Θb.
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb
                     | Aan1 Aan2 eb1 eb2 HrA0 HrEb0
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2c HrEb0 HrA0 | eb1 eb2 HrEb0 ]; subst.
    assert (Hfe : ftvar_in_exp ea [<=] dom Θa)
      by (pose proof (a_wf_exp_ftv_dom Hwfe) as Hd; simpl in Hd; exact Hd).
    pose proof Hxf as Hxf2. simpl_env in Hxf2.
    assert (HxΘa : x `notin` dom Θa) by (clear - Hxf2; fsetdec).
    assert (Hxαs : x `notin` dom αs) by (clear - Hxf2; fsetdec).
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfe HxΘa; fsetdec).
    assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    pose proof (a_typing_dom_mono Ht) as Hdmb.
    (* every αs atom REACHES the conclusion's output *)
    assert (Hαout : dom αs [<=] dom (Ξ ++ Θc)).
    { intros a Ha.
      assert (Hax : a <> x) by (intros ->; exact (Hxαs Ha)).
      assert (Ha1 : a `in` dom ((x ~ abind_var_typ A) ++ αs ++ Θa))
        by (simpl_env; clear - Ha; fsetdec).
      apply Hdmb in Ha1. simpl_env in Ha1. simpl_env.
      clear - Ha1 Hax. fsetdec. }
    assert (Hαscl : dom αs ∩ cols_l ρ [=] empty).
    { intros z. split; intros Hz; [ exfalso | clear - Hz; fsetdec ].
      assert (Hz1 : z `in` dom αs) by (clear - Hz; fsetdec).
      assert (Hz2 : z `in` cols_l ρ) by (clear - Hz; fsetdec).
      assert (HzΘa : z `notin` dom Θa)
        by (assert (Hd : disjoint αs Θa) by (clear - Huq; solve_uniq);
            unfold disjoint in Hd; clear - Hd Hz1; fsetdec).
      apply (Hblk z); [ apply Hαout; exact Hz1 | exact HzΘa | exact Hz2 ]. }
    (* ---- shape data ---- *)
    assert (HcovP0 : ftvar_in_pskl P0' [<=] S0) by (clear - HcovP; fsetdec).
    destruct (lift_split_identity Θ0' Hshape HrP0 Hwfp0 HcovP0)
      as (HwfPa & HwfQ0a & Pa' & Q0' & HrPa & HrQ0c & HftPQ & Dsp).
    pose proof (a_ty_mode_compat_split_decr Hmod Hne Hshape) as Hmodc.
    (* ---- the GUESS lift ---- *)
    assert (Hscpg0 : V [<=] ftvar_in_aenv Θa ∪ ftvar_in_pskl Pa)
      by (clear - Hscp; fsetdec).
    assert (Hcovg0 : V ∪ ftvar_in_pskl Pa' [<=] S0)
      by (clear - Hcov HftPQ; fsetdec).
    destruct (a_guess_mono_rel_e Hgm HrPa Hscpg0 Hcovg0)
      as (S1g & ρn & αs2 & A2 & Hgm2 & Eαs1 & Eαs2 & HrA2c).
    pose proof (e_guess_mono_supply_grows Hgm2) as Hgrg.
    pose proof (e_guess_mono_generated_in_supply Hgm2) as Hing.
    pose proof (e_guess_mono_uniq Hgm2) as Huqαs2.
    assert (Hdfl : dom αs [=] cols_l ρn)
      by (rewrite Eαs1; apply dom_flex_pairs_l).
    assert (Hdfr : dom αs2 [=] cols_r ρn)
      by (rewrite Eαs2; apply dom_flex_pairs_r).
    assert (Hfrg : dom αs2 ∩ S0 [=] empty).
    { intros z. split; intros Hz; [ exfalso | clear - Hz; fsetdec ].
      assert (Hz1 : z `in` dom αs2) by (clear - Hz; fsetdec).
      pose proof (e_guess_mono_generated_fresh Hgm2 Hz1) as Hn.
      clear - Hn Hz. fsetdec. }
    assert (HαsV : dom αs ∩ V [=] empty).
    { assert (Hd : disjoint αs Θa) by (clear - Huq; solve_uniq).
      unfold disjoint in Hd. clear - Hd Hscp Hsc0. fsetdec. }
    assert (Hnl : cols_l ρn ∩ (V ∪ cols_l ρ) [=] empty)
      by (clear - Hdfl HαsV Hαscl; fsetdec).
    assert (Hnr : cols_r ρn ∩ (V ∪ cols_r ρ) [=] empty)
      by (clear - Hdfr Hfrg Hcov; fsetdec).
    assert (Hρnincl : forall a b, In (a, b) ρ -> In (a, b) (ρn ++ ρ))
      by (intros a b Hin; apply in_or_app; right; exact Hin).
    assert (HrΘg : rel_aenv (ρn ++ ρ) V (αs ++ Θa) (αs2 ++ Θ0')).
    { apply rel_aenv_app.
      - rewrite Eαs1, Eαs2. apply rel_aenv_flex_pairs.
      - eapply rel_aenv_mono;
          [ exact HrΘ | exact Hρnincl | intros z Hz; exact Hz ]. }
    assert (Hagrg : flex_agree_rel (ρn ++ ρ) V (αs ++ Θa) (αs2 ++ Θ0')).
    { rewrite Eαs1, Eαs2. apply flex_agree_rel_push_pairs;
        [ exact Hagr | exact Hnl | exact Hnr ]. }
    assert (HαsftvΘa : cols_l ρn ∩ ftvar_in_aenv Θa [=] empty).
    { assert (Hd : disjoint αs Θa) by (clear - Huq; solve_uniq).
      unfold disjoint in Hd. clear - Hd Hsc0 Hdfl. fsetdec. }
    assert (Hextg : rel_ext ρn (ftvar_in_aenv Θa) S0).
    { apply rel_ext_flex_pairs;
        [ rewrite <- Eαs1; clear - Huq; solve_uniq
        | rewrite <- Eαs2; exact Huqαs2
        | exact HαsftvΘa
        | clear - Hdfr Hfrg; fsetdec ]. }
    assert (Hinjg : rel_inj (ρn ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hextg | exact Hcov ]).
    assert (Hfung : rel_fun (ρn ++ ρ) V (dom (αs ++ Θa))).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hextg | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; rewrite dom_app in Ha;
          assert (Haαs : a `in` dom αs) by (clear - Ha Hn; fsetdec);
          clear - Haαs Hαscl; fsetdec
        | intros a Ha Hn; rewrite dom_app in Ha;
          assert (Haαs : a `in` dom αs) by (clear - Ha Hn; fsetdec);
          clear - Haαs HαsV; fsetdec ]. }
    (* ---- side 1's wf at the block ---- *)
    assert (Hdecls : a_decls αs) by (eapply a_guess_mono_decls; exact Hgm).
    assert (Hwfαs : {{ ⊢ (αs ++ Θa) }}a)
      by (apply a_wf_aenv_decls_app; assumption).
    assert (HΞtv : forall α1, binds α1 abind_flex_mono αs ->
                     a_binds_tvar α1 (αs ++ Θa)).
    { intros α1 Hb. right; left.
      unfold binds; apply in_or_app; left; exact Hb. }
    assert (HPtv : forall α1, α1 `in` ftvar_in_pskl Pa ->
                     a_binds_tvar α1 (αs ++ Θa)).
    { intros α1 Hα1.
      pose proof (a_wf_pskl_ftv_binds HwfPa Hα1) as Htv0;
        apply a_binds_tvar_weaken_cons; exact Htv0. }
    assert (HwfAg : a_wf_ptyp (αs ++ Θa) A)
      by (eapply a_guess_mono_wf; [ exact Hgm | exact HPtv | exact HΞtv ]).
    assert (HwfXg : {{ ⊢ ((x ~ abind_var_typ A) ++ αs ++ Θa) }}a).
    { apply a_wf_aenv__var_typ;
        [ rewrite dom_app; clear - HxΘa Hxαs; fsetdec
        | exact HwfAg | exact Hwfαs ]. }
    assert (HwfQ0g : {{ (αs ++ Θa) ⨟ empty ⊢ₚₛ Q0 }}a)
      by (eapply a_wf_pskl_weaken;
          [ intros z c Hbz; apply binds_app_3; exact Hbz | exact HwfQ0a ]).
    assert (Hwfeog : {{ ((x ~ abind_var_typ A) ++ αs ++ Θa) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a).
    { apply a_wf_exp_weaken_cons.
      eapply a_wf_exp_mono;
        [ eapply a_wf_exp_abs_pick; exact Hwfe
        | apply aenv_tbinds_le_of_binds_le; apply aenv_binds_le_weaken_l ]. }
    (* ---- side 2's package at the block ---- *)
    assert (Huq2g : uniq (αs2 ++ Θ0')).
    { apply uniq_app_4;
        [ exact Huqαs2 | exact Huq2p
        | intros z Hz;
          assert (Hz1 : z `in` dom αs2) by (clear - Hz; fsetdec);
          assert (Hz2 : z `in` dom Θ0') by (clear - Hz; fsetdec);
          clear - Hz1 Hz2 Hfrg HdΘ; fsetdec ]. }
    assert (Hftv2g : ftvar_in_aenv (αs2 ++ Θ0') [<=] S1g).
    { rewrite ftvar_in_aenv_app.
      assert (H1 : ftvar_in_aenv αs2 [<=] S1g).
      { rewrite Eαs2. pose proof (ftvar_in_aenv_flex_pairs_r ρn) as He.
        rewrite He. clear - Hdfr Hing. fsetdec. }
      clear - H1 Hftv2 Hgrg. fsetdec. }
    assert (Hscpg : V [<=] ftvar_in_aenv (αs ++ Θa))
      by (rewrite ftvar_in_aenv_app; clear - Hscp; fsetdec).
    assert (Hblkg : forall a, a `in` dom (Ξ ++ Θc) ->
              a `notin` dom (αs ++ Θa) -> a `notin` cols_l (ρn ++ ρ)).
    { intros a Ha Hn. rewrite dom_app in Hn. rewrite cols_l_app.
      assert (H1 : a `notin` cols_l ρn) by (clear - Hn Hdfl; fsetdec).
      assert (H2 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn; fsetdec ]).
      clear - H1 H2. fsetdec. }
    assert (HdΘg : dom (αs2 ++ Θ0') [<=] S1g)
      by (rewrite dom_app; clear - Hing HdΘ Hgrg; fsetdec).
    assert (Hcovg : V ∪ cols_r (ρn ++ ρ) [<=] S1g)
      by (rewrite cols_r_app; clear - Hcov Hdfr Hing Hgrg; fsetdec).
    assert (HrQ0g : rel_pskl (ρn ++ ρ) V Q0 Q0')
      by (eapply rel_pskl_mono;
          [ exact HrQ0c | exact Hρnincl | intros z Hz; exact Hz ]).
    assert (HrEbg : rel_exp (ρn ++ ρ) V ea eb2)
      by (eapply rel_exp_mono;
          [ exact HrEb | exact Hρnincl | intros z Hz; exact Hz ]).
    assert (HbdfAg : ftvar_in_abind (abind_var_typ A) [<=] dom (αs ++ Θa))
      by (simpl; apply a_wf_ptyp_ftv_dom; exact HwfAg).
    assert (Hbd'fg : ftvar_in_abind (abind_var_typ A2) [<=] S1g).
    { simpl.
      pose proof (@rel_pskl_ftv_r (ρn ++ ρ) V (ptyp_to_pskl A)
                    (ptyp_to_pskl A2) HrA2c) as Hf.
      rewrite ftvar_ptyp_to_pskl in Hf.
      clear - Hf Hcovg. fsetdec. }
    assert (HcovPg : ftvar_in_pskl Q0' ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S1g)
      by (simpl in HcovP; clear - HcovP HftPQ Hgrg; fsetdec).
    (* ---- the CORE at base [αs ++ Θa] ---- *)
    destruct (@lift_typing_abs_core (decr_mode m0) (αs ++ Θa) Q0 ea B0 Ξ Θc
                x (abind_var_typ A)
                Ht IHt Hsuf Hxf Hxe I HbdfAg Hmodc
                S1g (αs2 ++ Θ0') Q0' eb2 (abind_var_typ A2) (ρn ++ ρ) V
                HrΘg HrQ0g HrEbg
                (rel_abind__var_typ HrA2c) I Hbd'fg
                Hagrg Hinjg Hfung HwfXg HwfQ0g Hwfeog Huq2g Hftv2g Hscpg
                Hblkg HdΘg Hcovg HcovPg)
      as (S3 & x2 & ρe2 & Ξ2 & Θd2' & B' & Hx2S & De & HsufΞ2 & HrF
          & HrFΞ & HrFΘ & HagrF & HrB' & HextF & HdomF & Hdm2).
    (* ---- the answer ---- *)
    exists S3, (ρe2 ++ ρn), (Ξ2 ++ Θd2'), (ptyp_arrow A2 B').
    split.
    { eapply e_typing__abs;
        [ exact Hne | exact Dsp | exact Hgm2 | exact HsufΞ2
        | exact Hx2S | exact De ]. }
    rewrite app_assoc.
    split; [ exact HrF | ].
    split; [ exact HagrF | ].
    split.
    { unfold rel_ptyp. simpl. constructor; [ | exact HrB' ].
      eapply rel_pskl_mono;
        [ exact HrA2c
        | intros u v Hu; apply in_or_app; right; exact Hu
        | intros u Hu; exact Hu ]. }
    split.
    { eapply rel_ext_app;
        [ exact Hextg | exact HextF
        | rewrite ftvar_in_aenv_app; clear; fsetdec
        | exact Hgrg
        | intros a b Hin;
          assert (Hal : a `in` cols_l ρn) by (eapply cols_l_in; exact Hin);
          assert (Har : b `in` cols_r ρn) by (eapply cols_r_in; exact Hin);
          split;
            [ rewrite ftvar_in_aenv_app;
              pose proof (dom_subset_ftvar_in_aenv αs) as Hds;
              clear - Hal Hdfl Hds; fsetdec
            | clear - Har Hdfr Hing; fsetdec ] ]. }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (HdomF _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + assert (Hal : a `in` cols_l ρn) by (eapply cols_l_in; exact Hin).
      assert (Har : b `in` cols_r ρn) by (eapply cols_r_in; exact Hin).
      split.
      * apply Hαout. clear - Hal Hdfl. fsetdec.
      * apply Hdm2. rewrite dom_app. clear - Har Hdfr. fsetdec.
  - (* ⭐⭐ AT-AbsAnno — the consis-chk between the (identity) split and the
       body: [lift_consis_nil], widen, the CORE, then [rel_ext_app] — the
       AP-App composition one binder in. *)
    destruct (a_split_ty_shape Hsp Hmod Hne) as [HeqΘ Hshape]. subst Θb.
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
    pose proof (a_typing_dom_mono Ht) as Hdmb.
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
    assert (HcovP0 : ftvar_in_pskl P0' [<=] S0) by (clear - HcovP; fsetdec).
    destruct (lift_split_identity Θ0' Hshape HrP0 Hwfp0 HcovP0)
      as (HwfPa & HwfQ0a & Pa' & Q0' & HrPa & HrQ0c & HftPQ & Dsp).
    pose proof (a_ty_mode_compat_split_decr Hmod Hne Hshape) as Hmodc.
    (* ---- the chk lift, and the relation widened by its pairs ---- *)
    assert (Hblk1 : forall a, a `in` dom Θc -> a `notin` dom Θa ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk;
          [ apply Hdmout; exact Ha | exact Hn ]).
    assert (HcovC : ftvar_in_pskl Pa' ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] S0).
    { simpl in HcovP. rewrite ftvar_ptyp_to_pskl.
      clear - HcovP HftPQ. fsetdec. }
    destruct (lift_consis_nil_out Hcc HrΘ HrPa HrAp Hagr Hinj Hfun Hwf Huq2p
                Hftv2 Hscp Hblk1 HdΘ Hcov HcovC HwfPa HwfcA)
      as (S1c & ρe1 & Θc' & Qc' & Dchk & HrΘc & Hagrc & HrQcU & Hext1
          & Hdom1 & Hgr1 & HdΘ1 & Hftv1 & Huq1' & Hle01 & HwfΘc).
    destruct (lift_seq_widen Hinj Hfun Hext1 Hdom1 Hwf Hscp Hcov Hblk Hdmc
                Hdmout Hgr1 HdΘ1)
      as (Hinj1 & Hfun1 & Hscp1 & Hcov1 & Hblk2).
    (* ---- side 1's package at the chk's output ---- *)
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
    assert (HrEb' : rel_exp (ρe1 ++ ρ) V ea eb2)
      by (eapply rel_exp_mono;
          [ exact HrEb | intros u v Hu; apply in_or_app; right; exact Hu
          | intros u Hu; exact Hu ]).
    assert (HrA' : rel_pskl (ρe1 ++ ρ) V (ptyp_to_pskl A) (ptyp_to_pskl A2))
      by (apply rel_pskl_widen; exact HrAp).
    assert (HrQ0w : rel_pskl (ρe1 ++ ρ) V Q0 Q0')
      by (apply rel_pskl_widen; exact HrQ0c).
    assert (Hbd'fc : ftvar_in_abind (abind_var_typ A2) [<=] S1c).
    { simpl. rewrite ftvar_ptyp_to_pskl in HcovC.
      clear - HcovC Hgr1. fsetdec. }
    assert (HcovPc : ftvar_in_pskl Q0' ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S1c)
      by (simpl in HcovP; clear - HcovP HftPQ Hgr1; fsetdec).
    (* ---- the CORE ---- *)
    destruct (@lift_typing_abs_core (decr_mode m0) Θc Q0 ea B0 Ξ Θd x
                (abind_var_typ A)
                Ht IHt Hsuf Hxf Hxe I HbdfA Hmodc
                S1c Θc' Q0' eb2 (abind_var_typ A2) (ρe1 ++ ρ) V
                HrΘc HrQ0w HrEb'
                (rel_abind__var_typ HrA') I Hbd'fc
                Hagrc Hinj1 Hfun1 HwfXc HwfQ0c Hwfeo Huq1' Hftv1 Hscp1
                Hblk2 HdΘ1 Hcov1 HcovPc)
      as (S1 & x2 & ρe2 & Ξ2 & Θc2' & Q' & Hx2S1c & De & HsufΞ2 & HrF
          & HrFΞ & HrFΘ & HagrF & HrQ' & HextF & HdomF & Hdm2).
    (* ---- the answer ---- *)
    exists S1, (ρe2 ++ ρe1), (Ξ2 ++ Θc2'), (ptyp_arrow A2 Q').
    split.
    { eapply e_typing__abs_anno;
        [ exact Hne | exact Dsp | exists Qc'; exact Dchk | exact HsufΞ2
        | exact Hx2S1c | exact De ]. }
    rewrite app_assoc.
    split; [ exact HrF | ].
    split; [ exact HagrF | ].
    split.
    { unfold rel_ptyp. simpl. constructor; [ | exact HrQ' ].
      eapply rel_pskl_mono;
        [ exact HrA' | intros u v Hu; apply in_or_app; right; exact Hu
        | intros u Hu; exact Hu ]. }
    exact (lift_seq_ext Hext1 HextF Hdom1 HdomF Hwf Hdmc Hdmout Hgr1 HdΘ1
             Hdm2).
  - (* ⭐⭐ AT-AbsCheckStep — the landed S-ForallR row (prop_lift.v §10) at
       the typing level: [lift_typing_check_step_of_rule]. *)
    inversion HrE; subst.
    eapply (@lift_typing_check_step_of_rule (exp_abs ea)); try eassumption.
    intros; eapply e_typing__abs_check_step; eassumption.
  - (* ⭐⭐ AT-AbsCheckBase — mode TC, so the split's FLEX row CAN run: a
       REAL [a_split_rel_e] call, then the term push through
       [lift_typing_abs_core], then the JUNK STRIP (the core KEEPS [Ξ];
       this row DROPS it) — the S-ForallR closing half, inlined. *)
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb
                     | A1 A2 eb1 eb2 HrA0x HrEb0
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb0 HrA0x | eb1 eb2 HrEb0 ]; subst.
    destruct (@rel_pskl_ptyp_image_r ρ V A0 P0' HrP0) as (A0' & -> & HrA0).
    (* ---- side 1's packages at the split ---- *)
    destruct (a_split_wf Hsp Hwf Hwfp0) as [Hle0 [HwfΘb [HwfPs HwfQs]]].
    assert (HwfA : a_wf_ptyp Θb A)
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfPs).
    assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hdm0 : dom Θa [<=] dom Θb) by (exact (a_split_dom_mono Hsp)).
    pose proof (a_typing_dom_mono Ht) as Hdmb.
    pose proof Hxf as Hxf2. rewrite dom_app in Hxf2.
    assert (HxΘb : x `notin` dom Θb) by (clear - Hxf2; fsetdec).
    assert (HxΘc : x `notin` dom Θc) by (clear - Hxf2; fsetdec).
    assert (HxΘa : x `notin` dom Θa) by (clear - HxΘb Hdm0; fsetdec).
    assert (Hxfv : x `notin` fvar_in_exp ea) by (clear - Hxf2; fsetdec).
    assert (Hfte : ftvar_in_exp ea [<=] dom Θa).
    { pose proof (a_wf_exp_ftv_dom Hwfe) as Hd. simpl in Hd. exact Hd. }
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfte HxΘa; fsetdec).
    (* the subject's TERM variables are Θb-bound — [a_typing_fvar_binds]
       on the body, the binder's own entry stripped by name *)
    assert (Hfvb : fvar_in_exp ea [<=] dom Θb).
    { intros z Hz.
      assert (Hz' : z `in` fvar_in_exp (open_exp_wrt_exp ea (exp_var_f x))).
      { pose proof (fvar_in_exp_open_exp_wrt_exp_lower ea (exp_var_f x))
          as Hl. clear - Hz Hl. fsetdec. }
      destruct (a_typing_fvar_binds Ht Hz') as (bd & Hb & Htm).
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[E Ebd] | Hb0];
        [ exfalso; subst z; exact (Hxfv Hz) | eapply binds_In; exact Hb0 ]. }
    (* the run reaches the conclusion's output *)
    assert (HdisjΞ : disjoint Ξ Θb) by (clear - Huq; solve_uniq).
    unfold disjoint in HdisjΞ.
    assert (Hdmout : dom Θb [<=] dom Θc).
    { intros a Ha.
      assert (Hax : a <> x) by (intros ->; exact (HxΘb Ha)).
      assert (Ha1 : a `in` dom ((x ~ abind_var_typ A) ++ Θb))
        by (simpl_env; clear - Ha; fsetdec).
      apply Hdmb in Ha1. simpl_env in Ha1.
      assert (HaΞ : a `notin` dom Ξ)
        by (clear - HdisjΞ Ha; fsetdec).
      clear - Ha1 Hax HaΞ. fsetdec. }
    (* ⭐ FIRST restrict at the JUNK SUFFIX's domain (§8c.39) *)
    assert (HΞΘa : dom Ξ ∩ ftvar_in_aenv Θa [=] empty)
      by (clear - HdisjΞ Hsc0 Hdm0; fsetdec).
    assert (HΞP0 : dom Ξ ∩ ftvar_in_pskl (ptyp_to_pskl A0) [=] empty).
    { assert (Hsub : ftvar_in_pskl (ptyp_to_pskl A0) [<=] dom Θa).
      { intros z Hz. apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds Hwfp0 Hz). }
      clear - HdisjΞ Hsub Hdm0. fsetdec. }
    assert (HΞeb : dom Ξ ∩ (fvar_in_exp ea ∪ ftvar_in_exp ea) [=] empty)
      by (clear - HdisjΞ Hfvb Hfte Hdm0; fsetdec).
    destruct (lift_restrict_junk HΞΘa HrΘ Hagr Hinj Hfun Hcov)
      as (Hρ0incl & Hρ0in & Hcl00 & Hcr00 & HΞcols & HrΘ0 & Hagr0 & Hinj0
          & Hfun0 & Hcov0).
    assert (HrA00 : rel_pskl (restrict_l (dom Ξ) ρ) V (ptyp_to_pskl A0) (ptyp_to_pskl A0'))
      by (apply rel_pskl_restrict_l; [ exact HrA0 | exact HΞP0 ]).
    assert (HrEb0 : rel_exp (restrict_l (dom Ξ) ρ) V ea eb2)
      by (apply rel_exp_restrict_l; [ exact HrEb | exact HΞeb ]).
    set (ρ0 := restrict_l (dom Ξ) ρ) in *. clearbody ρ0.
    assert (Hblk0X : forall a, a `in` dom (Ξ ++ Θc) -> a `notin` dom Θa ->
                     a `notin` cols_l ρ0).
    { intros a Ha Hn. rewrite dom_app in Ha.
      destruct (AtomSetProperties.In_dec a (dom Ξ)) as [HaΞ | HaΞ];
        [ exact (HΞcols a HaΞ) | ].
      assert (Hc : a `notin` cols_l ρ)
        by (apply Hblk; [ clear - Ha HaΞ; fsetdec | exact Hn ]).
      clear - Hc Hcl00. fsetdec. }
    assert (HdmbX : dom Θb [<=] dom (Ξ ++ Θc))
      by (rewrite dom_app; clear - Hdm0 Hdmout; fsetdec).
    assert (Hblksp0 : forall a, a `in` dom Θb -> a `notin` dom Θa ->
                      a `notin` cols_l ρ0)
      by (intros a Ha Hn; apply Hblk0X; [ apply HdmbX; exact Ha | exact Hn ]).
    (* ---- the SPLIT lift ---- *)
    assert (HcovP0 : ftvar_in_pskl (ptyp_to_pskl A0') [<=] S0)
      by (clear - HcovP; fsetdec).
    pose proof (a_split_rel_e Hsp) as Hsplift.
    unfold lift_split_concl in Hsplift.
    destruct (Hsplift S0 Θ0' (ptyp_to_pskl A0') ρ0 V HrΘ0 HrA00 Hagr0 Hinj0
                Hfun0 Hwf Huq2p Hftv2 Hscp Hblksp0 HdΘ Hcov0 HcovP0 Hwfp0)
      as (S1s & ρs & Θb' & P' & Q' & Dsp & HrΘb & Hagrs & HrPs & HrQs
          & Hexts & Hdoms).
    destruct (@rel_pskl_ptyp_image_r (ρs ++ ρ0) V A P' HrPs)
      as (A' & -> & HrAs).
    destruct (@rel_pskl_ptyp_image_r (ρs ++ ρ0) V B0 Q' HrQs)
      as (B0' & -> & HrB0s).
    (* ---- side 2's package after the split ---- *)
    pose proof (e_split_supply_grows Dsp) as Hgrs.
    assert (HcovSp : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl (ptyp_to_pskl A0')
                     [<=] S0)
      by (clear - Hftv2 HcovP0; fsetdec).
    destruct (e_split_sound Dsp Huq2p HcovSp)
      as (HaSp & HuqΘb' & HftvΘb' & HftPQ').
    assert (HdΘb' : dom Θb' [<=] S1s).
    { pose proof (e_split_dom_upper Dsp) as Hup.
      clear - Hup HdΘ Hgrs. fsetdec. }
    (* ---- side 1's packages at Θb ---- *)
    assert (HwfXb : {{ ⊢ ((x ~ abind_var_typ A) ++ Θb) }}a)
      by (apply a_wf_aenv__var_typ; [ exact HxΘb | exact HwfA | exact HwfΘb ]).
    assert (HbdfA : ftvar_in_abind (abind_var_typ A) [<=] dom Θb)
      by (simpl; apply a_wf_ptyp_ftv_dom; exact HwfA).
    assert (Hwfeo : {{ ((x ~ abind_var_typ A) ++ Θb) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a)
      by (apply a_wf_exp_weaken_cons; eapply a_wf_exp_abs_pick;
          eapply a_wf_exp_isub; [ exact Hwfe | exact Hle0 ]).
    (* ---- the relation, widened by the split's pairs ---- *)
    destruct (lift_seq_widen Hinj0 Hfun0 Hexts Hdoms Hwf Hscp Hcov0 Hblk0X Hdm0
                HdmbX Hgrs HdΘb')
      as (Hinj1 & Hfun1 & Hscp1 & HcovX & HblkX).
    assert (HrEb1 : rel_exp (ρs ++ ρ0) V ea eb2)
      by (eapply rel_exp_mono;
          [ exact HrEb0 | intros u v Hu; apply in_or_app; right; exact Hu
          | intros u Hu; exact Hu ]).
    assert (HftA' : ftvar_in_ptyp A' [<=] S1s)
      by (pose proof (ftvar_ptyp_to_pskl A') as He;
          clear - HftPQ' He; fsetdec).
    assert (Hbd'f : ftvar_in_abind (abind_var_typ A') [<=] S1s)
      by (simpl; exact HftA').
    assert (HcovPX : ftvar_in_pskl (ptyp_to_pskl B0') ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S1s)
      by (simpl in HcovP; clear - HcovP HftPQ' Hgrs; fsetdec).
    (* ---- the CORE at Θb ---- *)
    destruct (@lift_typing_abs_core mode_tc Θb (ptyp_to_pskl B0) ea B1 Ξ Θc
                x (abind_var_typ A)
                Ht IHt Hsuf Hxf Hxe I HbdfA (a_ty_mode_compat__tc B0)
                S1s Θb' (ptyp_to_pskl B0') eb2 (abind_var_typ A') (ρs ++ ρ0) V
                HrΘb HrB0s HrEb1
                (rel_abind__var_typ HrAs) I Hbd'f
                Hagrs Hinj1 Hfun1 HwfXb HwfQs Hwfeo HuqΘb' HftvΘb' Hscp1
                HblkX HdΘb' HcovX HcovPX)
      as (S2 & x2 & ρe2 & Ξ2 & Θc2' & B1' & Hx2S & De & HsufΞ2 & HrF
          & HrFΞ & HrFΘ & HagrF & HrB1' & HextF & HdomF & Hdm2).
    (* ---- the junk strip ---- *)
    assert (HwfQsX : {{ ((x ~ abind_var_typ A) ++ Θb) ⨟ empty ⊢ₚₛ
                       (ptyp_to_pskl B0) }}a)
      by (eapply a_wf_pskl_weaken;
          [ intros z b1 Hb1; apply binds_app_3; exact Hb1 | exact HwfQs ]).
    destruct (a_typing_sound Ht HwfXb HwfQsX (a_ty_mode_compat__tc B0) Hwfeo)
      as [_ [HwfOutB _]].
    assert (HcovDe : ftvar_in_ptyp A' ∪ ftvar_in_pskl (ptyp_to_pskl B0')
                     ∪ ftvar_in_exp eb2 ∪ fvar_in_exp eb2 [<=] S1s)
      by (clear - HftA' HcovPX; fsetdec).
    destruct (lift_check_base_strip Hρ0incl HΞcols Hinj Hfun Hcov Hwf Hscp Hblk
                Hexts Hdoms Hgrs HdΘb' HuqΘb' HftvΘb' Hdm0 Hdmout Huq Hinj1
                HcovX HwfOutB Hx2S HcovDe De HrFΞ HrFΘ HrB1' HextF HdomF Hdm2
                Hgam HrAs (a_wf_ptyp_ftv_dom HwfA))
      as (Huq2Ξ & Hγ2 & HrΘfin & Hagrfin & HrQfin & Hextfin & Hdomef).
    assert (Dc : {{ S0 ↝ S2 ⊨ Θ0' ⊢[ mode_tc ; (ptyp_to_pskl A0') ]
                    (exp_abs eb2) ⦂ (ptyp_arrow A' B1') ⊣ Θc2' }}e).
    { apply e_typing__abs_check_base with (x := x2) (Ξ := Ξ2)
        (S1 := S1s) (Θ1 := Θb') (B := B0');
        [ exact Dsp
        | eapply rel_aenv_suffix; [ exact HrFΞ | exact Hsuf ]
        | exact Huq2Ξ
        | exact Hγ2
        | exact Hx2S
        | exact De ]. }
    exists S2, (restrict_l (dom Ξ) (ρe2 ++ ρs)), Θc2', (ptyp_arrow A' B1').
    exact (conj Dc (conj HrΘfin (conj Hagrfin (conj HrQfin
            (conj Hextfin Hdomef))))).
  - (* ⭐⭐ AT-AbsAnnoCheckStep — the landed S-ForallR row (prop_lift.v §10) at
       the typing level: [lift_typing_check_step_of_rule]. *)
    inversion HrE; subst.
    eapply (@lift_typing_check_step_of_rule (exp_abs_anno Aan ea));
      try eassumption.
    intros; eapply e_typing__abs_anno_check_step; eassumption.
  - (* ⭐⭐ AT-AbsAnnoCheckBase — the [_check_base] shape with the consis
       stage between split and body: split lift, [lift_consis_nil], the
       CORE, then the JUNK STRIP.  The conclusion's domain is the SPLIT's
       [A'] (the [paper-gap] on the rule), the binder's type is the
       ANNOTATION [A] — side 2's [Aan2] comes from the expression rel. *)
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEbx
                     | Aan1 Aan2 eb1 eb2 HrAan HrEb
                     | a1 a2 b1 b2 HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEbx HrA0x | eb1 eb2 HrEbx ]; subst.
    destruct (@rel_pskl_ptyp_image_r ρ V A0 P0' HrP0) as (A0' & -> & HrA0).
    destruct Hchk as [Qc Hcc].
    (* ---- side 1's packages at the split and the consis ---- *)
    destruct (a_split_wf Hsp Hwf Hwfp0) as [Hle0 [HwfΘb [HwfPs HwfQs]]].
    assert (HwfAp : a_wf_ptyp Θb A')
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfPs).
    inversion Hwfe as [ | | | | | Lw Θw Aw ew HwfAan Hwfb | ]; subst.
    assert (HwfAanb : a_wf_ptyp Θb A)
      by (eapply a_wf_ptyp_isub; [ exact HwfAan | exact Hle0 ]).
    assert (HwfcAb : {{ Θb ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfAanb).
    destruct (a_consis_isub_wf_nil Hcc HwfΘb HwfcAb HwfPs)
      as [Hlebc HwfΘc].
    assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hdm0 : dom Θa [<=] dom Θb) by (exact (a_split_dom_mono Hsp)).
    assert (Hdmc : dom Θb [<=] dom Θc) by (exact (auc_dom_mono_consis Hcc)).
    pose proof (a_typing_dom_mono Ht) as Hdmb.
    pose proof Hxf as Hxf2. rewrite dom_app in Hxf2.
    assert (HxΘc : x `notin` dom Θc) by (clear - Hxf2; fsetdec).
    assert (HxΘb : x `notin` dom Θb) by (clear - HxΘc Hdmc; fsetdec).
    assert (HxΘa : x `notin` dom Θa) by (clear - HxΘb Hdm0; fsetdec).
    assert (Hxfv : x `notin` fvar_in_exp ea) by (clear - Hxf2; fsetdec).
    assert (HfteF : ftvar_in_exp (exp_abs_anno A ea) [<=] dom Θa)
      by (apply a_wf_exp_ftv_dom; exact Hwfe).
    assert (Hfte : ftvar_in_exp ea [<=] dom Θa)
      by (simpl in HfteF; clear - HfteF; fsetdec).
    assert (HftAan : ftvar_in_ptyp A [<=] dom Θa)
      by (simpl in HfteF; clear - HfteF; fsetdec).
    assert (Hxe : x `notin` ftvar_in_exp ea) by (clear - Hfte HxΘa; fsetdec).
    assert (Hfvb : fvar_in_exp ea [<=] dom Θc).
    { intros z Hz.
      assert (Hz' : z `in` fvar_in_exp (open_exp_wrt_exp ea (exp_var_f x))).
      { pose proof (fvar_in_exp_open_exp_wrt_exp_lower ea (exp_var_f x))
          as Hl. clear - Hz Hl. fsetdec. }
      destruct (a_typing_fvar_binds Ht Hz') as (bd & Hb & Htm).
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[E Ebd] | Hb0];
        [ exfalso; subst z; exact (Hxfv Hz) | eapply binds_In; exact Hb0 ]. }
    (* the run reaches the conclusion's output *)
    assert (HdisjΞ : disjoint Ξ Θc) by (clear - Huq; solve_uniq).
    unfold disjoint in HdisjΞ.
    assert (Hdmout : dom Θc [<=] dom Θd).
    { intros a Ha.
      assert (Hax : a <> x) by (intros ->; exact (HxΘc Ha)).
      assert (Ha1 : a `in` dom ((x ~ abind_var_typ A) ++ Θc))
        by (simpl_env; clear - Ha; fsetdec).
      apply Hdmb in Ha1. simpl_env in Ha1.
      assert (HaΞ : a `notin` dom Ξ)
        by (clear - HdisjΞ Ha; fsetdec).
      clear - Ha1 Hax HaΞ. fsetdec. }
    (* ⭐ FIRST restrict at the JUNK SUFFIX's domain (§8c.39) *)
    assert (HΞΘa : dom Ξ ∩ ftvar_in_aenv Θa [=] empty)
      by (clear - HdisjΞ Hsc0 Hdm0 Hdmc; fsetdec).
    assert (HΞP0 : dom Ξ ∩ ftvar_in_pskl (ptyp_to_pskl A0) [=] empty).
    { assert (Hsub : ftvar_in_pskl (ptyp_to_pskl A0) [<=] dom Θa).
      { intros z Hz. apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds Hwfp0 Hz). }
      clear - HdisjΞ Hsub Hdm0 Hdmc. fsetdec. }
    assert (HΞeb : dom Ξ ∩ (fvar_in_exp ea ∪ ftvar_in_exp ea) [=] empty)
      by (clear - HdisjΞ Hfvb Hfte Hdm0 Hdmc; fsetdec).
    assert (HΞAan : dom Ξ ∩ ftvar_in_pskl (ptyp_to_pskl A) [=] empty).
    { pose proof (ftvar_ptyp_to_pskl A) as He.
      clear - He HdisjΞ HftAan Hdm0 Hdmc. fsetdec. }
    destruct (lift_restrict_junk HΞΘa HrΘ Hagr Hinj Hfun Hcov)
      as (Hρ0incl & Hρ0in & Hcl00 & Hcr00 & HΞcols & HrΘ0 & Hagr0 & Hinj0
          & Hfun0 & Hcov0).
    assert (HrA00 : rel_pskl (restrict_l (dom Ξ) ρ) V (ptyp_to_pskl A0) (ptyp_to_pskl A0'))
      by (apply rel_pskl_restrict_l; [ exact HrA0 | exact HΞP0 ]).
    assert (HrEb0 : rel_exp (restrict_l (dom Ξ) ρ) V ea eb2)
      by (apply rel_exp_restrict_l; [ exact HrEb | exact HΞeb ]).
    assert (HrAan0 : rel_pskl (restrict_l (dom Ξ) ρ) V (ptyp_to_pskl A) (ptyp_to_pskl Aan2))
      by (apply rel_pskl_restrict_l; [ exact HrAan | exact HΞAan ]).
    set (ρ0 := restrict_l (dom Ξ) ρ) in *. clearbody ρ0.
    assert (Hblk0X : forall a, a `in` dom (Ξ ++ Θd) -> a `notin` dom Θa ->
                     a `notin` cols_l ρ0).
    { intros a Ha Hn. rewrite dom_app in Ha.
      destruct (AtomSetProperties.In_dec a (dom Ξ)) as [HaΞ | HaΞ];
        [ exact (HΞcols a HaΞ) | ].
      assert (Hc : a `notin` cols_l ρ)
        by (apply Hblk; [ clear - Ha HaΞ; fsetdec | exact Hn ]).
      clear - Hc Hcl00. fsetdec. }
    assert (HdmbX : dom Θb [<=] dom (Ξ ++ Θd))
      by (rewrite dom_app; clear - Hdm0 Hdmc Hdmout; fsetdec).
    assert (Hblksp0 : forall a, a `in` dom Θb -> a `notin` dom Θa ->
                      a `notin` cols_l ρ0)
      by (intros a Ha Hn; apply Hblk0X; [ apply HdmbX; exact Ha | exact Hn ]).
    (* ---- the SPLIT lift ---- *)
    assert (HcovP0 : ftvar_in_pskl (ptyp_to_pskl A0') [<=] S0)
      by (clear - HcovP; fsetdec).
    pose proof (a_split_rel_e Hsp) as Hsplift.
    unfold lift_split_concl in Hsplift.
    destruct (Hsplift S0 Θ0' (ptyp_to_pskl A0') ρ0 V HrΘ0 HrA00 Hagr0 Hinj0
                Hfun0 Hwf Huq2p Hftv2 Hscp Hblksp0 HdΘ Hcov0 HcovP0 Hwfp0)
      as (S1s & ρs & Θb' & P' & Q' & Dsp & HrΘb & Hagrs & HrPs & HrQs
          & Hexts & Hdoms).
    destruct (@rel_pskl_ptyp_image_r (ρs ++ ρ0) V A' P' HrPs)
      as (Ap' & -> & HrApw).
    destruct (@rel_pskl_ptyp_image_r (ρs ++ ρ0) V B0 Q' HrQs)
      as (B0' & -> & HrB0s).
    (* ---- side 2's package after the split ---- *)
    pose proof (e_split_supply_grows Dsp) as Hgrs.
    assert (HcovSp : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl (ptyp_to_pskl A0')
                     [<=] S0)
      by (clear - Hftv2 HcovP0; fsetdec).
    destruct (e_split_sound Dsp Huq2p HcovSp)
      as (HaSp & HuqΘb' & HftvΘb' & HftPQ').
    assert (HdΘb' : dom Θb' [<=] S1s).
    { pose proof (e_split_dom_upper Dsp) as Hup.
      clear - Hup HdΘ Hgrs. fsetdec. }
    (* ---- side 1's packages at Θb, and the widened relation ---- *)
    destruct (lift_seq_widen Hinj0 Hfun0 Hexts Hdoms Hwf Hscp Hcov0 Hblk0X Hdm0
                HdmbX Hgrs HdΘb')
      as (Hinj1 & Hfun1 & Hscp1 & Hcov1 & HblkX).
    assert (HrAanW : rel_pskl (ρs ++ ρ0) V (ptyp_to_pskl A)
                       (ptyp_to_pskl Aan2))
      by (apply rel_pskl_widen; exact HrAan0).
    (* ---- the CONSIS lift, at the split's output ---- *)
    assert (HdmcX : dom Θc [<=] dom (Ξ ++ Θd))
      by (rewrite dom_app; clear - Hdmout; fsetdec).
    assert (Hblkc : forall a, a `in` dom Θc -> a `notin` dom Θb ->
                    a `notin` cols_l (ρs ++ ρ0))
      by (intros a Ha Hn; apply HblkX; [ apply HdmcX; exact Ha | exact Hn ]).
    assert (HftAan2 : ftvar_in_pskl (ptyp_to_pskl Aan2) [<=] S0).
    { pose proof (ftvar_ptyp_to_pskl Aan2) as He.
      simpl in HcovP. clear - He HcovP. fsetdec. }
    assert (HcovCc : ftvar_in_pskl (ptyp_to_pskl Aan2)
                     ∪ ftvar_in_pskl (ptyp_to_pskl Ap') [<=] S1s)
      by (clear - HftAan2 HftPQ' Hgrs; fsetdec).
    destruct (lift_consis_nil_out Hcc HrΘb HrAanW HrApw Hagrs Hinj1 Hfun1
                HwfΘb HuqΘb' HftvΘb' Hscp1 Hblkc HdΘb' Hcov1 HcovCc
                HwfcAb HwfPs)
      as (S1c & ρc & Θc' & Qc' & Dchk & HrΘc & Hagrc & HrQcU & Hextc
          & Hdomc & Hgrc & HdΘc' & Hftvc & Huqc' & _ & _).
    assert (Hdmc2 : dom Θb' [<=] dom Θc').
    { assert (HcovE2 : ftvar_in_aenv Θb' ∪ ftvar_in_pskl (ptyp_to_pskl Aan2)
                       ∪ ftvar_in_pskl (ptyp_to_pskl Ap') ∪ empty ∪ empty
                       [<=] S1s)
        by (clear - HftvΘb' HcovCc; fsetdec).
      exact (auc_dom_mono_consis (e_consis_sound Dchk HuqΘb' HcovE2)). }
    destruct (lift_seq_widen Hinj1 Hfun1 Hextc Hdomc HwfΘb Hscp1 Hcov1 HblkX
                Hdmc HdmcX Hgrc HdΘc')
      as (Hinj2 & Hfun2 & Hscp2 & Hcov2 & Hblk2c).
    (* ---- side 1's packages at Θc ---- *)
    assert (HwfAc : a_wf_ptyp Θc A)
      by (eapply a_wf_ptyp_isub; [ exact HwfAanb | exact Hlebc ]).
    assert (HwfXc : {{ ⊢ ((x ~ abind_var_typ A) ++ Θc) }}a)
      by (apply a_wf_aenv__var_typ; [ exact HxΘc | exact HwfAc | exact HwfΘc ]).
    assert (HbdfAc : ftvar_in_abind (abind_var_typ A) [<=] dom Θc)
      by (simpl; apply a_wf_ptyp_ftv_dom; exact HwfAc).
    assert (HwfQc : {{ Θc ⨟ empty ⊢ₚₛ (ptyp_to_pskl B0) }}a)
      by (eapply a_isub_wf_pskl; [ exact Hlebc | exact HwfQs ]).
    assert (Hwfeo : {{ ((x ~ abind_var_typ A) ++ Θc) ⊢ᵉ
                       (open_exp_wrt_exp ea (exp_var_f x)) }}a)
      by (apply a_wf_exp_weaken_cons; eapply a_wf_exp_abs_anno_pick;
          eapply a_wf_exp_isub;
          [ eapply a_wf_exp_isub; [ exact Hwfe | exact Hle0 ] | exact Hlebc ]).
    (* ---- the relation, widened by the consis's pairs ---- *)
    assert (HrEb2 : rel_exp (ρc ++ ρs ++ ρ0) V ea eb2)
      by (eapply rel_exp_mono;
          [ exact HrEb0
          | intros u v Hu; apply in_or_app; right; apply in_or_app; right;
            exact Hu
          | intros u Hu; exact Hu ]).
    assert (HrB0w : rel_pskl (ρc ++ ρs ++ ρ0) V (ptyp_to_pskl B0)
                      (ptyp_to_pskl B0'))
      by (apply rel_pskl_widen; exact HrB0s).
    assert (HrAanW2 : rel_pskl (ρc ++ ρs ++ ρ0) V (ptyp_to_pskl A)
                        (ptyp_to_pskl Aan2))
      by (apply rel_pskl_widen; exact HrAanW).
    assert (HftAan2c : ftvar_in_abind (abind_var_typ Aan2) [<=] S1c).
    { simpl. pose proof (ftvar_ptyp_to_pskl Aan2) as He.
      clear - He HftAan2 Hgrs Hgrc. fsetdec. }
    assert (HcovPc : ftvar_in_pskl (ptyp_to_pskl B0') ∪ ftvar_in_exp eb2
                     ∪ fvar_in_exp eb2 [<=] S1c)
      by (simpl in HcovP; clear - HcovP HftPQ' Hgrs Hgrc; fsetdec).
    (* ---- the CORE at Θc ---- *)
    destruct (@lift_typing_abs_core mode_tc Θc (ptyp_to_pskl B0) ea B1 Ξ Θd
                x (abind_var_typ A)
                Ht IHt Hsuf Hxf Hxe I HbdfAc (a_ty_mode_compat__tc B0)
                S1c Θc' (ptyp_to_pskl B0') eb2 (abind_var_typ Aan2)
                (ρc ++ ρs ++ ρ0) V
                HrΘc HrB0w HrEb2
                (rel_abind__var_typ HrAanW2) I HftAan2c
                Hagrc Hinj2 Hfun2 HwfXc HwfQc Hwfeo Huqc' Hftvc Hscp2
                Hblk2c HdΘc' Hcov2 HcovPc)
      as (S2 & x2 & ρe2 & Ξ2 & Θd2' & B1' & Hx2S & De & HsufΞ2 & HrF
          & HrFΞ & HrFΘ & HagrF & HrB1' & HextF & HdomF & Hdm2).
    (* ---- the junk strip, at the middle stage's pairs [ρc ++ ρs] ---- *)
    assert (HwfQcX : {{ ((x ~ abind_var_typ A) ++ Θc) ⨟ empty ⊢ₚₛ
                       (ptyp_to_pskl B0) }}a)
      by (eapply a_wf_pskl_weaken;
          [ intros z b1 Hb1; apply binds_app_3; exact Hb1 | exact HwfQc ]).
    destruct (a_typing_sound Ht HwfXc HwfQcX (a_ty_mode_compat__tc B0) Hwfeo)
      as [_ [HwfOutB _]].
    destruct (lift_seq_ext Hexts Hextc Hdoms Hdomc Hwf Hdm0 Hdmc Hgrs HdΘb'
                Hdmc2) as [Hextm Hdomm].
    assert (Hgrm : S0 [<=] S1c) by (clear - Hgrs Hgrc; fsetdec).
    assert (Hdm0c : dom Θa [<=] dom Θc) by (clear - Hdm0 Hdmc; fsetdec).
    assert (HcovDe : ftvar_in_ptyp Aan2 ∪ ftvar_in_pskl (ptyp_to_pskl B0')
                     ∪ ftvar_in_exp eb2 ∪ fvar_in_exp eb2 [<=] S1c)
      by (simpl in HftAan2c; clear - HftAan2c HcovPc; fsetdec).
    assert (HrApm : rel_ptyp ((ρc ++ ρs) ++ ρ0) V A' Ap')
      by (unfold rel_ptyp; rewrite app_assoc; apply rel_pskl_widen; exact HrApw).
    assert (HftAp : ftvar_in_ptyp A' [<=] dom Θc)
      by (pose proof (a_wf_ptyp_ftv_dom HwfAp) as Hd; clear - Hd Hdmc; fsetdec).
    rewrite <- (app_assoc _ ρc ρs ρ0) in HrFΞ, HrFΘ, HrB1', Hinj2, Hcov2.
    destruct (lift_check_base_strip Hρ0incl HΞcols Hinj Hfun Hcov Hwf Hscp Hblk
                Hextm Hdomm Hgrm HdΘc' Huqc' Hftvc Hdm0c Hdmout Huq Hinj2
                Hcov2 HwfOutB Hx2S HcovDe De HrFΞ HrFΘ HrB1' HextF HdomF Hdm2
                Hgam HrApm HftAp)
      as (Huq2Ξ & Hγ2 & HrΘfin & Hagrfin & HrQfin & Hextfin & Hdomef).
    assert (Dc : {{ S0 ↝ S2 ⊨ Θ0' ⊢[ mode_tc ; (ptyp_to_pskl A0') ]
                    (exp_abs_anno Aan2 eb2) ⦂ (ptyp_arrow Ap' B1')
                    ⊣ Θd2' }}e).
    { apply e_typing__abs_anno_check_base with (x := x2) (Ξ := Ξ2)
        (S1 := S1s) (S2 := S1c) (Θ1 := Θb') (Θ2 := Θc') (B := B0');
        [ exact Dsp
        | exists Qc'; exact Dchk
        | eapply rel_aenv_suffix; [ exact HrFΞ | exact Hsuf ]
        | exact Huq2Ξ
        | exact Hγ2
        | exact Hx2S
        | exact De ]. }
    exists S2, (restrict_l (dom Ξ) (ρe2 ++ ρc ++ ρs)), Θd2', (ptyp_arrow Ap' B1').
    exact (conj Dc (conj HrΘfin (conj Hagrfin (conj HrQfin
            (conj Hextfin Hdomef))))).
  - (* ⭐⭐ AT-App — THREE threaded calls: the argument's SKELETON pass
       (a_pat, via [a_pat_rel_e]), the function, then the argument's TYPE
       pass at the function's domain. *)
    inversion HrE as [ | | x1 y1 Hat | eb1 eb2 HrEb0
                     | A1 A2 eb1 eb2 HrA0 HrEb0
                     | f1' e2' f1 e2c HrE1 HrE2
                     | eb1 eb2 A1 A2 HrEb0 HrA0 | eb1 eb2 HrEb0 ]; subst.
    destruct (a_wf_exp_app_inv Hwfe) as [Hwfe1 Hwfe2].
    assert (Hdm0 : dom Θa [<=] dom Θb) by (exact (a_pat_dom_mono Hp2)).
    assert (Hdm1 : dom Θb [<=] dom Θc) by (exact (a_typing_dom_mono Ht1)).
    assert (Hdm2 : dom Θc [<=] dom Θd) by (exact (a_typing_dom_mono Ht2)).
    (* ================= STAGE 1: the skeleton pass ================= *)
    assert (Hblk1 : forall a, a `in` dom Θb -> a `notin` dom Θa ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk;
          [ clear - Ha Hdm1 Hdm2; fsetdec | exact Hn ]).
    assert (HcovP1 : ftvar_in_pskl pskl_ghost ∪ ftvar_in_exp e2c
                     ∪ fvar_in_exp e2c [<=] S0)
      by (simpl; simpl in HcovP; clear - HcovP; fsetdec).
    destruct (a_pat_rel_e Hp2 HrΘ
                (rel_pskl__ghost ρ V) HrE2 Hagr Hinj Hfun Hwf Huq2p Hftv2
                Hscp Hblk1 HdΘ Hcov HcovP1 (a_wf_pskl__ghost Θa empty)
                Hwfe2 a_sk_mode_compat__tc)
      as (S1 & ρe1 & Θb' & Pa' & D1e & HrΘ1 & Hagr1 & HrPa' & Hext1 & Hdom1).
    pose proof (e_pat_supply_grows D1e) as Hgr1.
    assert (HcovE1 : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl pskl_ghost
                     ∪ fvar_in_exp e2c ∪ ftvar_in_exp e2c [<=] S0)
      by (simpl; simpl in HcovP; clear - Hftv2 HcovP; fsetdec).
    destruct (e_pat_sound D1e Huq2p HcovE1)
      as (Ha1p & Huq1' & Hftv1 & HftPa').
    assert (HdΘ1 : dom Θb' [<=] S1)
      by (pose proof (dom_subset_ftvar_in_aenv Θb') as Hd;
          clear - Hd Hftv1; fsetdec).
    destruct (a_pat_sound Hp2 Hwf (a_wf_pskl__ghost Θa empty)
                a_sk_mode_compat__tc Hwfe2) as [Hle01 [HwfΘb _]].
    (* ================= STAGE 2: the function ================= *)
    assert (Hdm12 : dom Θb [<=] dom Θd) by (clear - Hdm1 Hdm2; fsetdec).
    destruct (lift_seq_widen Hinj Hfun Hext1 Hdom1 Hwf Hscp Hcov Hblk Hdm0
                Hdm12 Hgr1 HdΘ1)
      as (Hinj1 & Hfun1 & Hscp1 & Hcov1 & Hblk2d).
    assert (Hblk2 : forall a, a `in` dom Θc -> a `notin` dom Θb ->
                    a `notin` cols_l (ρe1 ++ ρ))
      by (intros a Ha Hn; apply Hblk2d; [ apply Hdm2; exact Ha | exact Hn ]).
    assert (HrQ0w : rel_pskl (ρe1 ++ ρ) V Q0 P0')
      by (apply rel_pskl_widen; exact HrP0).
    assert (Hrarr : rel_pskl (ρe1 ++ ρ) V (pskl_arrow Pa Q0)
                      (pskl_arrow Pa' P0'))
      by (constructor; [ exact HrPa' | exact HrQ0w ]).
    assert (HrE1' : rel_exp (ρe1 ++ ρ) V e1 f1)
      by (eapply rel_exp_mono;
          [ exact HrE1 | intros u v Hu; apply in_or_app; right; exact Hu
          | intros u Hu; exact Hu ]).
    assert (HcovP2 : ftvar_in_pskl (pskl_arrow Pa' P0')
                     ∪ ftvar_in_exp f1 ∪ fvar_in_exp f1 [<=] S1).
    { pose proof (@rel_pskl_ftv_r (ρe1 ++ ρ) V Pa Pa' HrPa') as HfP.
      simpl. simpl in HcovP.
      clear - HfP HcovP Hcov1 Hgr1. fsetdec. }
    assert (HwfPab : {{ Θb ⨟ empty ⊢ₚₛ Pa }}a)
      by (eapply a_pat_output_wf;
          [ exact Hp2 | exact Hwf | apply a_wf_pskl__ghost
          | exact a_sk_mode_compat__tc | exact Hwfe2 ]).
    assert (HwfQ0b : {{ Θb ⨟ empty ⊢ₚₛ Q0 }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hwfp0 ]).
    assert (Hwfarr : {{ Θb ⨟ empty ⊢ₚₛ (pskl_arrow Pa Q0) }}a)
      by (apply a_wf_pskl__arrow; [ exact HwfPab | exact HwfQ0b ]).
    assert (Hwfe1b : {{ Θb ⊢ᵉ e1 }}a)
      by (eapply a_wf_exp_isub; [ exact Hwfe1 | exact Hle01 ]).
    destruct (IHt1 S1 Θb' (pskl_arrow Pa' P0') f1 (ρe1 ++ ρ) V
                HrΘ1 Hrarr HrE1' Hagr1 Hinj1 Hfun1 HwfΘb Huq1' Hftv1
                Hscp1 Hblk2 HdΘ1 Hcov1 HcovP2 Hwfarr Hwfe1b
                (a_ty_mode_compat__fn Pa Hmod))
      as (S2 & ρe2 & Θc' & Tarr & D2e & HrΘ2 & Hagr2 & HrTarr & Hext2
          & Hdom2).
    destruct (rel_ptyp_arrow_inv HrTarr) as (A2 & B2 & -> & HrA2 & HrB2).
    pose proof (e_typing_supply_grows D2e) as Hgr2.
    assert (HcovE2 : ftvar_in_aenv Θb' ∪ ftvar_in_pskl (pskl_arrow Pa' P0')
                     ∪ fvar_in_exp f1 ∪ ftvar_in_exp f1 [<=] S1)
      by (clear - Hftv1 HcovP2; fsetdec).
    destruct (e_typing_sound D2e Huq1' HcovE2)
      as (Ha2p & Huq2' & Hftv2' & HftTarr).
    assert (HdΘ2 : dom Θc' [<=] S2)
      by (pose proof (dom_subset_ftvar_in_aenv Θc') as Hd;
          clear - Hd Hftv2'; fsetdec).
    destruct (a_typing_sound Ht1 HwfΘb Hwfarr
                (a_ty_mode_compat__fn Pa Hmod) Hwfe1b)
      as [Hle12 [HwfΘc [HwfArrC _]]].
    destruct (a_wf_ptyp_arrow_inv HwfArrC) as [HwfAc HwfB0c].
    (* ================= STAGE 3: the argument's TYPE pass ============= *)
    destruct (lift_seq_widen Hinj1 Hfun1 Hext2 Hdom2 HwfΘb Hscp1 Hcov1 Hblk2d
                Hdm1 Hdm2 Hgr2 HdΘ2)
      as (Hinj2 & Hfun2 & Hscp2 & Hcov2 & Hblk3).
    assert (HrAc : rel_pskl (ρe2 ++ ρe1 ++ ρ) V (ptyp_to_pskl A)
                     (ptyp_to_pskl A2))
      by (exact HrA2).
    assert (HrE2' : rel_exp (ρe2 ++ ρe1 ++ ρ) V e2 e2c)
      by (eapply rel_exp_mono;
          [ exact HrE2
          | intros u v Hu; apply in_or_app; right; apply in_or_app; right;
            exact Hu
          | intros u Hu; exact Hu ]).
    assert (HcovP3 : ftvar_in_pskl (ptyp_to_pskl A2) ∪ ftvar_in_exp e2c
                     ∪ fvar_in_exp e2c [<=] S2).
    { rewrite ftvar_ptyp_to_pskl.
      simpl in HftTarr. simpl in HcovP.
      clear - HftTarr HcovP Hgr1 Hgr2. fsetdec. }
    assert (HwfcAc : {{ Θc ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfAc).
    assert (Hwfe2c : {{ Θc ⊢ᵉ e2 }}a)
      by (eapply a_wf_exp_isub;
          [ eapply a_wf_exp_isub; [ exact Hwfe2 | exact Hle01 ]
          | exact Hle12 ]).
    destruct (IHt2 S2 Θc' (ptyp_to_pskl A2) e2c (ρe2 ++ ρe1 ++ ρ) V
                HrΘ2 HrAc HrE2' Hagr2 Hinj2 Hfun2 HwfΘc Huq2' Hftv2'
                Hscp2 Hblk3 HdΘ2 Hcov2 HcovP3 HwfcAc Hwfe2c
                (a_ty_mode_compat__tc A))
      as (S3 & ρe3 & Θd' & A2' & D3e & HrΘ3 & Hagr3 & HrA2' & Hext3
          & Hdom3).
    (* ---- side 2's dom mono across the third call ---- *)
    assert (HcovE3 : ftvar_in_aenv Θc' ∪ ftvar_in_pskl (ptyp_to_pskl A2)
                     ∪ fvar_in_exp e2c ∪ ftvar_in_exp e2c [<=] S2)
      by (clear - Hftv2' HcovP3; fsetdec).
    assert (Hdm3' : dom Θc' [<=] dom Θd').
    { destruct (e_typing_sound D3e Huq2' HcovE3) as (Ha3p & _).
      exact (a_typing_dom_mono Ha3p). }
    assert (Hdm2e : dom Θb' [<=] dom Θc').
    { destruct (e_typing_sound D2e Huq1' HcovE2) as (Ha2q & _).
      exact (a_typing_dom_mono Ha2q). }
    destruct (lift_seq_ext Hext1 Hext2 Hdom1 Hdom2 Hwf Hdm0 Hdm1 Hgr1 HdΘ1
                Hdm2e) as [Hext12 Hdom12].
    assert (Hdm01 : dom Θa [<=] dom Θc) by (clear - Hdm0 Hdm1; fsetdec).
    assert (Hgr12 : S0 [<=] S2) by (clear - Hgr1 Hgr2; fsetdec).
    destruct (lift_seq_ext Hext12 Hext3 Hdom12 Hdom3 Hwf Hdm01 Hdm2 Hgr12
                HdΘ2 Hdm3') as [Hext123 Hdom123].
    (* ---- the answer ---- *)
    exists S3, (ρe3 ++ ρe2 ++ ρe1), Θd', B2.
    split; [ eapply e_typing__app; [ exact D1e | exact D2e | exact D3e ] | ].
    rewrite ! app_assoc.
    split; [ exact HrΘ3 | ].
    split; [ exact Hagr3 | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrB2
        | intros u v Hu; apply in_or_app; right; exact Hu
        | intros u Hu; exact Hu ]. }
    exact (conj Hext123 Hdom123).
Qed.
