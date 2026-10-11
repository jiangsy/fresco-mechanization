(** Assignment, unification and consistency: lifting from [a_*] to supply-threaded [e_*] derivations. *)

Require Import Coq.Lists.List.
Require Import src.fresco.prop_atom_sets.
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


(* ===================================================================== *)
(*  §9  ⭐⭐⭐ THE CONSIS RUNG — [a_assign] / [a_unify] / [a_consis] LIFT     *)
(*                                                                        *)
(*  ONE mutual induction, 28 rows.  The motives are below; what they say  *)
(*  is that an [a_]-side run of the trio is MIRRORED by a supply-threaded  *)
(*  one, up to a pair list ρ that grows by the pairs each generative row   *)
(*  invents ([rel_ext] is that growth's spec, and it is what lets the      *)
(*  caller rebuild [rel_inj] / [rel_fun] at the wider list).               *)
(*                                                                        *)
(*  ⭐ SIDE 2 CARRIES NO WELL-FORMEDNESS.  [uniq Θ0'] and                   *)
(*  [ftvar_in_aenv Θ0' ⊆ S0] cover every use, and both are re-established  *)
(*  at the output ([e_consis_sound] + [a_assign_unify_consis_uniq], and    *)
(*  [e_assign_unify_consis_ctx_ftvar]).  That is what made the arrow row   *)
(*  tractable — see the hand-off §8c.32.                                   *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  THE MOTIVES                                                           *)
(* ===================================================================== *)

Definition lift_assign_post (Θ0 Ξ : aenv) (P : pskl) (Θ1 : aenv)
    (S0 : atoms) (Θ0' Ξ' : aenv) (α' : atom) (P' : pskl)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1',
    {{ S0 ↝ S1 ⊨ Θ0' ⊲[ Ξ' ] α' ≔ P' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_ext ρe (ftvar_in_aenv (Ξ ++ Θ0)) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_assign_concl (Θ0 Ξ : aenv) (α : atom) (P : pskl)
    (Θ1 : aenv) : Prop :=
  forall S0 Θ0' Ξ' α' P' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_aenv ρ V Ξ Ξ' ->
    rel_atom ρ V α α' ->
    rel_pskl ρ V P P' ->
    flex_agree_rel ρ V (Ξ ++ Θ0) (Ξ' ++ Θ0') ->
    rel_inj ρ V ->
    rel_fun ρ V (dom (Ξ ++ Θ0)) ->
    a_flex_tvar (Ξ ++ Θ0) α ->
    {{ ⊢ (Ξ ++ Θ0) }}a ->
    a_decls Ξ ->
    a_decls Ξ' ->
    uniq (Ξ' ++ Θ0') ->
    ftvar_in_aenv (Ξ' ++ Θ0') [<=] S0 ->
    V [<=] ftvar_in_aenv (Ξ ++ Θ0) ->
    (forall a, a `in` dom Θ1 -> a `notin` dom (Ξ ++ Θ0) -> a `notin` cols_l ρ) ->
    dom (Ξ' ++ Θ0') [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P' [<=] S0 ->
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a ->
    lift_assign_post Θ0 Ξ P Θ1 S0 Θ0' Ξ' α' P' ρ V.

Definition lift_unify_post (Θ0 : aenv) (Θ1 : aenv)
    (S0 : atoms) (Θ0' : aenv) (α' β' : atom)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1',
    {{ S0 ↝ S1 ⊨ Θ0' ⊲ α' ≈ᵘ β' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_unify_concl (Θ0 : aenv) (α β : atom) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' α' β' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_atom ρ V α α' ->
    rel_atom ρ V β β' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    a_flex_tvar Θ0 α ->
    a_flex_tvar Θ0 β ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    lift_unify_post Θ0 Θ1 S0 Θ0' α' β' ρ V.

Definition lift_consis_post (Θ0 : aenv) (Q : pskl) (Θ1 : aenv)
    (S0 : atoms) (Θ0' : aenv) (Δ1' Δ2' : atoms) (P0' P' : pskl)
    (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' Q',
    {{ S0 ↝ S1 ⊨ Θ0' ⊢[ Δ1' | Δ2' | P0' ] P' ∼ Q' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_consis_concl (Δ1 Δ2 : atoms) (Θ0 : aenv)
    (P0 P Q : pskl) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' Δ1' Δ2' P0' P' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    rel_pskl ρ V P P' ->
    rel_atoms ρ V Δ1 Δ1' ->
    rel_atoms ρ V Δ2 Δ2' ->
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
    ftvar_in_pskl P0' ∪ ftvar_in_pskl P' [<=] S0 ->
    Δ1' ∪ Δ2' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
    (forall α, α `in` (Δ1 ∪ Δ2) -> binds α abind_tvar Θ0) ->
    no_flex_dep (Δ1 ∪ Δ2) Θ0 ->
    flex_above_free (Δ1 ∪ Δ2) Θ0 ->
    Δ1 ∪ Δ2 [<=] ftvar_in_aenv Θ0 ->
    lift_consis_post Θ0 Q Θ1 S0 Θ0' Δ1' Δ2' P0' P' ρ V.

Lemma rel_aenv_nil_inv_l : forall ρ V Θ2,
  rel_aenv ρ V nil Θ2 -> Θ2 = nil.
Proof. intros ρ V Θ2 H; inversion H; reflexivity. Qed.


(* ===================================================================== *)
(*  ⭐⭐ THE ∀ ROWS' SHARED CLOSER                                          *)
(*                                                                        *)
(*  All three binder rows of [a_consis] restrict ρ, push the opener PAIR,  *)
(*  run the premise and then have to hand the caller a relation that no    *)
(*  longer mentions either opener.  Everything after the IH is the same    *)
(*  for the three, so it lives here once.  The one step that is not        *)
(*  bookkeeping is the DELETED PAIR: injectivity at the caller's pair     *)
(*  list and the final context relation show that its partner cannot be   *)
(*  bound when the source opener is absent from the final context.        *)
(* ===================================================================== *)

Lemma lift_consis_forall_close :
  forall Θ0 Θ1 Q α S0 Θ0' Δ1' Δ2' P0' P' ρ V α2 S1 ρe Θ1' Q',
  {{ ⊢ ((α ~ abind_tvar) ++ Θ1) }}a ->
  α `notin` V ->
  α2 `notin` V ->
  α2 `notin` cols_r ρ ->
  uniq ((α2 ~ abind_tvar) ++ Θ1') ->
  rel_inj ρ V ->
  rel_inj ((α, α2) :: restrict_pairs α α2 ρ) V ->
  rel_ext ρe (ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0)) (add α2 S0) ->
  V ∪ cols_r ((α, α2) :: restrict_pairs α α2 ρ) [<=] add α2 S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  rel_aenv (ρe ++ (α, α2) :: restrict_pairs α α2 ρ) V
    ((α ~ abind_tvar) ++ Θ1) ((α2 ~ abind_tvar) ++ Θ1') ->
  flex_agree_rel (ρe ++ (α, α2) :: restrict_pairs α α2 ρ) V
    ((α ~ abind_tvar) ++ Θ1) ((α2 ~ abind_tvar) ++ Θ1') ->
  rel_pskl (ρe ++ (α, α2) :: restrict_pairs α α2 ρ) V Q Q' ->
  (forall a b, In (a, b) ρe ->
     a `in` dom ((α ~ abind_tvar) ++ Θ1)
     /\ b `in` dom ((α2 ~ abind_tvar) ++ Θ1')) ->
  {{ S0 ↝ S1 ⊨ Θ0' ⊢[ Δ1' | Δ2' | P0' ] P'
     ∼ (pskl_all_syn (close_pskl_wrt_pskl α2 Q')) ⊣ Θ1' }}e ->
  lift_consis_post Θ0 (pskl_all_syn (close_pskl_wrt_pskl α Q)) Θ1
    S0 Θ0' Δ1' Δ2' P0' P' ρ V.
Proof.
  intros Θ0 Θ1 Q α S0 Θ0' Δ1' Δ2' P0' P' ρ V α2 S1 ρe Θ1' Q'
    Hwf1α HαV Hα2V Hα2c Huq1out Hinj Hinj' Hext Hcov' Hcov
    HrΘout Hagrout HrQ Hdomout Dc.
  assert (HαΘ1 : α `notin` dom Θ1) by (inversion Hwf1α; subst; assumption).
  assert (HwfΘ1 : {{ ⊢ Θ1 }}a) by (inversion Hwf1α; subst; assumption).
  assert (HαfΘ1 : α `notin` ftvar_in_aenv Θ1).
  { pose proof (a_wf_aenv_ftv_dom HwfΘ1) as Hs. clear - HαΘ1 Hs. fsetdec. }
  assert (Hα2Θ1 : α2 `notin` dom Θ1') by (clear - Huq1out; solve_uniq).
  (* ---- the pair list the premise ran at, and its injectivity ---- *)
  assert (Hinjout : rel_inj (ρe ++ (α, α2) :: restrict_pairs α α2 ρ) V)
    by (eapply rel_inj_app; [ exact Hinj' | exact Hext | exact Hcov' ]).
  assert (Hαρe : forall b, ~ In (α, b) ρe).
  { intros b Hin. destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin) as [Hna _].
    apply Hna. simpl. clear; fsetdec. }
  assert (Hα2ρe : forall a, ~ In (a, α2) ρe).
  { intros a Hin. destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin) as [_ Hnb].
    apply Hnb. clear; fsetdec. }
  (* ⭐ the opener is related to ITS OWN counterpart and to nothing else *)
  assert (Hαonly : forall y,
            rel_atom (ρe ++ (α, α2) :: restrict_pairs α α2 ρ) V α y -> y = α2).
  { intros y Hat. inversion Hat as [ a0 b0 Hin | a0 HinV ]; subst.
    - apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
      + exfalso. exact (Hαρe _ Hin).
      + inversion Ehd; reflexivity.
      + exfalso. apply (@restrict_pairs_notin_l α α2 ρ).
        eapply cols_l_in; exact Hin.
    - exfalso. exact (HαV HinV). }
  (* ---- peel the opener off BOTH contexts ---- *)
  inversion HrΘout as [ | a0 b0 bd1 bd2 Θa Θb Hat0 Hbd0 HrΘtail Ea Eb ]; subst.
  assert (HrΘfin : rel_aenv (ρe ++ ρ) V Θ1 Θ1').
  { eapply rel_aenv_restore_pairs; eassumption. }
  (* ---- and the FLEX AGREEMENT, which is where the owed fact is spent ---- *)
  assert (Hagrpeel : flex_agree_rel (ρe ++ (α, α2) :: restrict_pairs α α2 ρ)
                       V Θ1 Θ1').
  { eapply flex_agree_peel_cons;
      [ exact Hagrout
      | apply rel_atom__pair; apply in_or_app; right; left; reflexivity
      | exact Hinjout
      | exact Hαonly
      | exact HαΘ1
      | exact Hα2Θ1
      | intros x Hx; exact Hx
      | intros y Hy Ey; subst; contradiction ]. }
  assert (Hextfin : rel_ext ρe (ftvar_in_aenv Θ0) S0).
  { eapply rel_ext_mono;
      [ exact Hext | intros a b Hin; exact Hin
      | simpl; clear; fsetdec | clear; fsetdec ]. }
  assert (Hinjfin : rel_inj (ρe ++ ρ) V)
    by (eapply rel_inj_app; [ exact Hinj | exact Hextfin | exact Hcov ]).
  assert (Hagrfin : flex_agree_rel (ρe ++ ρ) V Θ1 Θ1').
  { destruct Hagrpeel as [HagV Hagp]. split; [ exact HagV | ].
  intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - apply Hagp. apply in_or_app; left; exact Hin.
    - destruct (a == α) as [-> | Hne].
      + (* ⭐ THE PAIR [restrict_pairs] DELETED: both halves are FALSE *)
      assert (Hb2 : ~ a_flex_tvar Θ1' b).
      { intros Hf.
        destruct (rel_aenv_dom_r_inv HrΘfin (a_flex_tvar_in_dom Hf))
          as (a & Ha & Hat).
        assert (a = α)
          by (eapply Hinjfin; [ exact Hat | apply rel_atom__pair;
                apply in_or_app; right; exact Hin ]).
        subst a. exact (HαΘ1 Ha). }
      split; intros Hf; exfalso;
          [ apply HαΘ1; apply a_flex_tvar_in_dom; exact Hf | exact (Hb2 Hf) ].
      + assert (Hbne : b <> α2)
          by (intros ->; apply Hα2c; eapply cols_r_in; exact Hin).
        apply Hagp. apply in_or_app; right; right.
        apply restrict_pairs_in; assumption. }
  (* ---- assemble ---- *)
  exists S1, ρe, Θ1', (pskl_all_syn (close_pskl_wrt_pskl α2 Q')).
  split; [ exact Dc | ].
  split; [ exact HrΘfin | ].
  split; [ exact Hagrfin | ].
  split.
  { apply rel_pskl__all_syn.
    eapply rel_pskl_close_pair_restrict;
      [ exact HrQ | exact HαV
      | intros Hc; destruct (cols_l_in_inv _ _ Hc) as [y Hin];
        exact (Hαρe _ Hin)
      | exact Hα2V
      | intros Hc; destruct (cols_r_in_inv _ _ Hc) as [y Hin];
        exact (Hα2ρe _ Hin)
      | intros a b Hin; apply in_or_app; left; exact Hin
      | intros a b Hin; apply in_or_app; right; exact Hin ]. }
  split; [ exact Hextfin | ].
  intros a b Hin. destruct (Hdomout _ _ Hin) as [Hd1 Hd2].
  assert (Hne1 : a <> α) by (intros ->; exact (Hαρe _ Hin)).
  assert (Hne2 : b <> α2) by (intros ->; exact (Hα2ρe _ Hin)).
  simpl in Hd1, Hd2.
  split; [ clear - Hd1 Hne1; fsetdec | clear - Hd2 Hne2; fsetdec ].
Qed.

(** Restrict obsolete opener pairs, then relate the extended rigid contexts. *)
Lemma lift_consis_open_pair : forall ρ V Θ Θ' α α',
  rel_aenv ρ V Θ Θ' -> flex_agree_rel ρ V Θ Θ' ->
  rel_inj ρ V -> rel_fun ρ V (dom Θ) ->
  α `notin` ftvar_in_aenv Θ -> α' `notin` ftvar_in_aenv Θ' ->
  α `notin` V -> α' `notin` V ->
  rel_aenv ((α, α') :: restrict_pairs α α' ρ) V
    ((α ~ abind_tvar) ++ Θ) ((α' ~ abind_tvar) ++ Θ') /\
  flex_agree_rel ((α, α') :: restrict_pairs α α' ρ) V
    ((α ~ abind_tvar) ++ Θ) ((α' ~ abind_tvar) ++ Θ') /\
  rel_inj ((α, α') :: restrict_pairs α α' ρ) V /\
  rel_fun ((α, α') :: restrict_pairs α α' ρ) V
    (dom ((α ~ abind_tvar) ++ Θ)).
Proof.
  intros * Hr Hagr Hinj Hfun Hα Hα' HαV Hα'V.
  assert (Hincl : forall x y, In (x, y) (restrict_pairs α α' ρ) -> In (x, y) ρ)
    by (intros; eapply restrict_pairs_incl; eassumption).
  pose proof (@restrict_pairs_notin_l α α' ρ) as Hl.
  pose proof (@restrict_pairs_notin_r α α' ρ) as Hr'.
  split.
  - apply rel_aenv__cons;
      [ apply rel_atom__pair; left; reflexivity | constructor | ].
    eapply rel_aenv_mono;
      [ apply rel_aenv_restrict; eauto
      | intros x y Hin; right; exact Hin | intros x Hx; exact Hx ].
  - split.
    + apply flex_agree_rel_push_look.
      * eapply flex_agree_rel_weaken; [ exact Hagr | exact Hincl | intros x Hx; exact Hx ].
      * pose proof (dom_subset_ftvar_in_aenv Θ); clear - Hα H; fsetdec.
      * pose proof (dom_subset_ftvar_in_aenv Θ'); clear - Hα' H; fsetdec.
    + split.
      * apply rel_inj_push; [ eapply rel_inj_sub; eauto | exact Hα'V | exact Hr' ].
      * simpl. apply rel_fun_push;
          [ eapply rel_fun_weaken; [ exact Hfun | exact Hincl | intros x Hx; exact Hx ]
          | exact HαV | exact Hl ].
Qed.

(** Context well-formedness and scope survive the paired rigid extension. *)
Lemma lift_consis_open_scope : forall ρ V Θ Θr (Θout : aenv) S α β,
  {{ ⊢ Θ }}a -> uniq Θr -> ftvar_in_aenv Θr [<=] S ->
  V [<=] ftvar_in_aenv Θ ->
  (forall a, a `in` dom Θout -> a `notin` dom Θ -> a `notin` cols_l ρ) ->
  dom Θr [<=] S -> V ∪ cols_r ρ [<=] S ->
  α `notin` dom Θ -> β `notin` dom Θr ->
  {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a /\
  uniq ((β ~ abind_tvar) ++ Θr) /\
  ftvar_in_aenv ((β ~ abind_tvar) ++ Θr) [<=] add β S /\
  V [<=] ftvar_in_aenv ((α ~ abind_tvar) ++ Θ) /\
  (forall a, a `in` dom ((α ~ abind_tvar) ++ Θout) ->
    a `notin` dom ((α ~ abind_tvar) ++ Θ) ->
    a `notin` cols_l ((α, β) :: restrict_pairs α β ρ)) /\
  dom ((β ~ abind_tvar) ++ Θr) [<=] add β S /\
  V ∪ cols_r ((α, β) :: restrict_pairs α β ρ) [<=] add β S.
Proof.
  intros * Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov Hα Hβ.
  pose proof (cols_l_restrict_pairs α β ρ) as Hcl0.
  pose proof (cols_r_restrict_pairs α β ρ) as Hcr0.
  repeat apply conj.
  - apply a_wf_aenv__tvar; auto.
  - clear - Huq2p Hβ; solve_uniq.
  - simpl; clear - Hftv2; fsetdec.
  - simpl; clear - Hscp; fsetdec.
  - intros a Ha Hn. simpl in Ha, Hn |- *.
    assert (Hne : a <> α) by (clear - Hn; fsetdec).
    assert (Hc : a `notin` cols_l ρ)
      by (apply Hblk; [ clear - Ha Hne; fsetdec | clear - Hn; fsetdec ]).
    clear - Hne Hc Hcl0; fsetdec.
  - simpl; clear - HdΘ; fsetdec.
  - simpl; clear - Hcov Hcr0; fsetdec.
Qed.

Arguments lift_consis_open_scope {ρ V Θ Θr Θout S α β} _ _ _ _ _ _ _ _ _.

(* ===================================================================== *)
(*  ⭐⭐ THE THREE ∀ ROWS, ONE PROOF.                                       *)
(*                                                                        *)
(*  ForallInh, ForallSyn and UnivGhost1 differ only in which side of the   *)
(*  consistency OPENS at the binder (the other keeps its [∀◇]) and in     *)
(*  which Δ-tracker gains the opener.  [binder_head] / [binder_body] /     *)
(*  [binder_delta] (prop_lift_context.v) name those two choices, and       *)
(*  [lift_consis_binder_row] is the restrict-push-run-close proof once;    *)
(*  each row instantiates the flags and hands over its e-rule.             *)
(* ===================================================================== *)

Lemma a_wf_pskl_binder_body : forall Θ opens P α,
  {{ Θ ⨟ empty ⊢ₚₛ (binder_head opens P) }}a ->
  α `notin` dom Θ ∪ ftvar_in_pskl P ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ (binder_body opens P α) }}a.
Proof.
  intros Θ [] P α Hwf Hα; simpl in Hwf |- *.
  - apply a_wf_pskl_all_syn_open_tvar; [ exact Hwf | clear - Hα; fsetdec ].
  - eapply a_wf_pskl_tvar_mono;
      [ exact Hwf
      | intros γ Hγ; apply (a_binds_tvar_weaken_mid nil (α ~ abind_tvar));
        exact Hγ ].
Qed.

Lemma rel_atoms_binder_delta : forall ρ V grows Δ Δ' α α2,
  rel_atoms ρ V Δ Δ' ->
  α `notin` V -> α `notin` cols_l ρ ->
  α2 `notin` V -> α2 `notin` cols_r ρ ->
  α `notin` Δ -> α2 `notin` Δ' ->
  rel_atoms ((α, α2) :: ρ) V (binder_delta grows α Δ)
    (binder_delta grows α2 Δ').
Proof.
  intros ρ V [] Δ Δ' α α2 Hd HαV Hαl Hα2V Hα2r HαD Hα2D; simpl.
  - apply rel_atoms_push; assumption.
  - apply rel_atoms_push_absent; assumption.
Qed.

Lemma lift_consis_binder_row :
  forall (opens0 opens grows1 grows2 : bool) {Δ1 Δ2 Θ0 Θ1 P0 P Q α},
  (forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α,
     α `notin` S0 ->
     {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
        ⊢[ (binder_delta grows1 α Δ1) | (binder_delta grows2 α Δ2)
         | (binder_body opens0 P0 α) ]
        (binder_body opens P α) ∼ Q ⊣ ((α ~ abind_tvar) ++ Θ1) }}e ->
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (binder_head opens0 P0) ]
        (binder_head opens P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q))
        ⊣ Θ1 }}e) ->
  α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
    `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
  {{ ((α ~ abind_tvar) ++ Θ0)
     ⊢[ (binder_delta grows1 α Δ1) | (binder_delta grows2 α Δ2)
      | (binder_body opens0 P0 α) ] (binder_body opens P α) ∼ Q
     ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
  lift_consis_concl (binder_delta grows1 α Δ1) (binder_delta grows2 α Δ2)
    ((α ~ abind_tvar) ++ Θ0) (binder_body opens0 P0 α) (binder_body opens P α)
    Q ((α ~ abind_tvar) ++ Θ1) ->
  lift_consis_concl Δ1 Δ2 Θ0 (binder_head opens0 P0) (binder_head opens P)
    (pskl_all_syn (close_pskl_wrt_pskl α Q)) Θ1.
Proof.
  intros opens0 opens grows1 grows2 Δ1 Δ2 Θ0 Θ1 P0 P Q α Hrule Hfr HD IH.
  intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
    Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
    Hfaf HΔsc.
  destruct (rel_pskl_binder_head_inv HrP0) as (P0b2 & -> & HrP0b).
  destruct (rel_pskl_binder_head_inv HrP) as (P12 & -> & HrPb).
  rewrite !ftvar_in_pskl_binder_head in HcovP.
  destruct (atom_fresh S0) as [α2 Hα2].
  assert (HfrΘ : α `notin` ftvar_in_aenv Θ0) by (clear - Hfr; solve_notin_auto).
  assert (HfrP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfr; solve_notin_auto).
  assert (HfrP : α `notin` ftvar_in_pskl P) by (clear - Hfr; solve_notin_auto).
  assert (HfrD1 : α `notin` Δ1) by (clear - Hfr; solve_notin_auto).
  assert (HfrD2 : α `notin` Δ2) by (clear - Hfr; solve_notin_auto).
  assert (HαV : α `notin` V) by (intros Hin; apply HfrΘ; apply Hscp; exact Hin).
  assert (Hαd : α `notin` dom Θ0)
    by (intros Hin; apply HfrΘ; apply (dom_subset_ftvar_in_aenv Θ0); exact Hin).
  assert (Hα2d : α2 `notin` dom Θ0') by (clear - Hα2 HdΘ; fsetdec).
  assert (Hα2V : α2 `notin` V) by (clear - Hα2 Hcov; fsetdec).
  assert (Hα2c : α2 `notin` cols_r ρ) by (clear - Hα2 Hcov; fsetdec).
  assert (Hα2f : α2 `notin` ftvar_in_aenv Θ0') by (clear - Hα2 Hftv2; fsetdec).
  assert (Hα2D1 : α2 `notin` Δ1') by (clear - Hα2 HcovΔ; fsetdec).
  assert (Hα2D2 : α2 `notin` Δ2') by (clear - Hα2 HcovΔ; fsetdec).
  (* ---- the PAIR RESTRICTION, then the push ---- *)
  assert (Hαl : α `notin` cols_l (restrict_pairs α α2 ρ))
    by apply restrict_pairs_notin_l.
  assert (Hα2r : α2 `notin` cols_r (restrict_pairs α α2 ρ))
    by apply restrict_pairs_notin_r.
  assert (Hρr : forall x y, In (x, y) (restrict_pairs α α2 ρ) -> In (x, y) ρ)
    by (intros x y Hx; eapply restrict_pairs_incl; exact Hx).
  destruct (lift_consis_open_pair HrΘ Hagr Hinj Hfun HfrΘ Hα2f HαV Hα2V)
    as (HrΘ' & Hagr' & Hinj' & Hfun').
  assert (HrP0' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ) V
                    (binder_body opens0 P0 α) (binder_body opens0 P0b2 α2)).
  { apply rel_pskl_binder_body. apply rel_pskl_restrict;
      [ exact HrP0b | exact HfrP0 | clear - Hα2 HcovP; fsetdec ]. }
  assert (HrP' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ) V
                   (binder_body opens P α) (binder_body opens P12 α2)).
  { apply rel_pskl_binder_body. apply rel_pskl_restrict;
      [ exact HrPb | exact HfrP | clear - Hα2 HcovP; fsetdec ]. }
  assert (Hrd1' : rel_atoms ((α, α2) :: restrict_pairs α α2 ρ) V
                    (binder_delta grows1 α Δ1) (binder_delta grows1 α2 Δ1'))
    by (apply rel_atoms_binder_delta;
        [ eapply rel_atoms_weaken; [ exact Hrd1 | exact Hρr | intros x Hx; exact Hx ]
        | exact HαV | exact Hαl | exact Hα2V | exact Hα2r
        | exact HfrD1 | exact Hα2D1 ]).
  assert (Hrd2' : rel_atoms ((α, α2) :: restrict_pairs α α2 ρ) V
                    (binder_delta grows2 α Δ2) (binder_delta grows2 α2 Δ2'))
    by (apply rel_atoms_binder_delta;
        [ eapply rel_atoms_weaken; [ exact Hrd2 | exact Hρr | intros x Hx; exact Hx ]
        | exact HαV | exact Hαl | exact Hα2V | exact Hα2r
        | exact HfrD2 | exact Hα2D2 ]).
  destruct (lift_consis_open_scope Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov Hαd Hα2d)
    as (Hwf' & Huq2' & Hftv2' & Hscp' & Hblk' & HdΘ' & Hcov').
  destruct (binder_delta_upper grows1 α Δ1) as [Hd1l Hd1u].
  destruct (binder_delta_upper grows2 α Δ2) as [Hd2l Hd2u].
  destruct (binder_delta_upper grows1 α2 Δ1') as [_ Hd1u'].
  destruct (binder_delta_upper grows2 α2 Δ2') as [_ Hd2u'].
  assert (HcovP' : ftvar_in_pskl (binder_body opens0 P0b2 α2)
                   ∪ ftvar_in_pskl (binder_body opens P12 α2) [<=] add α2 S0).
  { pose proof (ftvar_in_pskl_binder_body_upper opens0 P0b2 α2) as Hu1.
    pose proof (ftvar_in_pskl_binder_body_upper opens P12 α2) as Hu2.
    clear - Hu1 Hu2 HcovP. fsetdec. }
  assert (HcovΔ' : binder_delta grows1 α2 Δ1' ∪ binder_delta grows2 α2 Δ2'
                   [<=] add α2 S0)
    by (clear - HcovΔ Hd1u' Hd2u'; fsetdec).
  assert (Hwfp0' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                     (binder_body opens0 P0 α) }}a)
    by (apply a_wf_pskl_binder_body; [ exact Hwfp0 | clear - Hαd HfrP0; fsetdec ]).
  assert (Hwfp' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                    (binder_body opens P α) }}a)
    by (apply a_wf_pskl_binder_body; [ exact Hwfp | clear - Hαd HfrP; fsetdec ]).
  assert (HΔsub : binder_delta grows1 α Δ1 ∪ binder_delta grows2 α Δ2
                  [<=] add α (Δ1 ∪ Δ2))
    by (clear - Hd1u Hd2u; fsetdec).
  destruct (delta_inv_open_tvar Hwf Hαd HΔsub HΔtv Hnfd Hfaf)
    as (HΔtv' & Hnfd' & Hfaf').
  assert (HΔsc' : binder_delta grows1 α Δ1 ∪ binder_delta grows2 α Δ2
                  [<=] ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0))
    by (simpl; clear - HΔsc Hd1u Hd2u; fsetdec).
  destruct (IH (add α2 S0) ((α2 ~ abind_tvar) ++ Θ0')
              (binder_delta grows1 α2 Δ1') (binder_delta grows2 α2 Δ2')
              (binder_body opens0 P0b2 α2) (binder_body opens P12 α2)
              ((α, α2) :: restrict_pairs α α2 ρ) V
              HrΘ' HrP0' HrP' Hrd1' Hrd2' Hagr' Hinj' Hfun' Hwf' Huq2' Hftv2'
              Hscp' Hblk' HdΘ' Hcov' HcovP' HcovΔ' Hwfp0' Hwfp' HΔtv' Hnfd'
              Hfaf' HΔsc')
    as (S1 & ρe & Θ1out & Q' & De & HrΘout & Hagrout & HrQ & Hext & Hdomout).
  (* ---- side 1's output context, via SOUNDNESS of the premise ---- *)
  destruct ((proj2 (proj2 a_assign_unify_consis_sound)) _ _ _ _ _ _ _ HD
              Hwf' Hwfp0' Hwfp' HΔtv' Hnfd' Hfaf')
    as (Hinc1 & HwfΘ1α & _).
  (* ---- side 2's output: the OPENER SURVIVES as a rigid prefix ---- *)
  assert (HcovS : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0')
                  ∪ ftvar_in_pskl (binder_body opens0 P0b2 α2)
                  ∪ ftvar_in_pskl (binder_body opens P12 α2)
                  ∪ binder_delta grows1 α2 Δ1' ∪ binder_delta grows2 α2 Δ2'
                  [<=] add α2 S0)
    by (clear - Hftv2' HcovP' HcovΔ'; fsetdec).
  pose proof (e_consis_sound De Huq2' HcovS) as HaD.
  destruct ((proj2 (proj2 a_assign_unify_consis_tvar_prefix))
              _ _ _ _ _ _ _ HaD (α2 ~ abind_tvar) Θ0' eq_refl
              (@tvar_prefix_cons α2 nil tvar_prefix_nil)) as (Θ1' & Eout).
  subst Θ1out.
  assert (Huq1out : uniq ((α2 ~ abind_tvar) ++ Θ1'))
    by (exact ((proj2 (proj2 a_assign_unify_consis_uniq))
                 _ _ _ _ _ _ _ HaD Huq2')).
  (* ---- the e-side conclusion, and the shared closer ---- *)
  eapply lift_consis_forall_close;
    [ exact HwfΘ1α | exact HαV | exact Hα2V | exact Hα2c
    | exact Huq1out | exact Hinj | exact Hinj' | exact Hext
    | exact Hcov' | exact Hcov | exact HrΘout | exact Hagrout | exact HrQ
    | exact Hdomout | apply Hrule; [ exact Hα2 | exact De ] ].
Qed.

Lemma lift_consis_forall_inh_row : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,
  α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
    `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
  {{ ((α ~ abind_tvar) ++ Θ0)
     ⊢[ (add α Δ1) | (add α Δ2) | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ] (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
     ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
  lift_consis_concl (add α Δ1) (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
    (open_pskl_wrt_pskl P0 (pskl_var_f α)) (open_pskl_wrt_pskl P (pskl_var_f α)) Q ((α ~ abind_tvar) ++ Θ1) ->
  lift_consis_concl Δ1 Δ2 Θ0 (pskl_all_syn P0) (pskl_all_syn P)
    (pskl_all_syn (close_pskl_wrt_pskl α Q)) Θ1.
Proof.
  intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
  exact (lift_consis_binder_row true true true true e_consis__forall_inh Hfr HD IH).
Qed.

Lemma lift_consis_forall_syn_row : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,
  α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
    `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
  {{ ((α ~ abind_tvar) ++ Θ0)
     ⊢[ Δ1 | (add α Δ2) | (pskl_univ_ghost P0) ] (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
     ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
  lift_consis_concl Δ1 (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
    (pskl_univ_ghost P0) (open_pskl_wrt_pskl P (pskl_var_f α)) Q ((α ~ abind_tvar) ++ Θ1) ->
  lift_consis_concl Δ1 Δ2 Θ0 (pskl_univ_ghost P0) (pskl_all_syn P)
    (pskl_all_syn (close_pskl_wrt_pskl α Q)) Θ1.
Proof.
  intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
  exact (lift_consis_binder_row false true false true e_consis__forall_syn Hfr HD IH).
Qed.

Lemma lift_consis_univ_ghost1_row : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,
  α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
    `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
  {{ ((α ~ abind_tvar) ++ Θ0)
     ⊢[ (add α Δ1) | Δ2 | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ] (pskl_univ_ghost P) ∼ Q
     ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
  lift_consis_concl (add α Δ1) Δ2 ((α ~ abind_tvar) ++ Θ0)
    (open_pskl_wrt_pskl P0 (pskl_var_f α)) (pskl_univ_ghost P) Q ((α ~ abind_tvar) ++ Θ1) ->
  lift_consis_concl Δ1 Δ2 Θ0 (pskl_all_syn P0) (pskl_univ_ghost P)
    (pskl_all_syn (close_pskl_wrt_pskl α Q)) Θ1.
Proof.
  intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
  exact (lift_consis_binder_row true false true false e_consis__univ_ghost1 Hfr HD IH).
Qed.

(* ===================================================================== *)
(*  Flex-Flex-Skip / Flex-Flex-Skip', at either untouched head.            *)
(*                                                                        *)
(*  Both rows peel a head [c : bc] the unification does not touch (a      *)
(*  flexible one, or a rigid / term one), and their lifts are one proof   *)
(*  up to that head: why [α, β <> c] ([Hne_of] — Skip's own premises, or  *)
(*  Skip''s non-flexibility), and, for side 2's binding read off          *)
(*  [rel_abind], whether the heads are flexible ([Hside2]'s first half)   *)
(*  and the e-rule (its second half).                                     *)
(* ===================================================================== *)

Lemma lift_unify_skip_head_of_rule : forall Θ0 Θ1 c bc α β,
  (c `notin` dom Θ0 -> a_flex_tvar ((c ~ bc) ++ Θ0) α ->
   a_flex_tvar ((c ~ bc) ++ Θ0) β -> α <> c /\ β <> c) ->
  (forall ρ V bdd, rel_abind ρ V bc bdd ->
     (forall Θ1 Θ1' b0, c `notin` dom Θ1 -> b0 `notin` dom Θ1' ->
        (a_flex_tvar ((c ~ bc) ++ Θ1) c <-> a_flex_tvar ((b0 ~ bdd) ++ Θ1') b0))
     /\ (forall S0 S1 Θ0 Θ1 α β b0,
           α <> b0 -> β <> b0 ->
           {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
           {{ S0 ↝ S1 ⊨ ((b0 ~ bdd) ++ Θ0) ⊲ α ≈ᵘ β
              ⊣ ((b0 ~ bdd) ++ Θ1) }}e)) ->
  c `notin` dom Θ1 ->
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  lift_unify_concl Θ0 α β Θ1 ->
  lift_unify_concl ((c ~ bc) ++ Θ0) α β ((c ~ bc) ++ Θ1).
Proof.
  intros Θ0 Θ1 c bc α β Hne_of Hside2 Hcd HD IH.
  intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
    Hscp Hblk HdΘ Hcov.
  destruct (rel_aenv_cons_inv_l HrΘ)
    as (b0 & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
  subst Θ0'.
  assert (Huq1 : uniq ((c ~ bc) ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Huq2 : uniq ((b0 ~ bdd) ++ Θ0'')) by (exact Huq2p).
  assert (HwfC : {{ ⊢ Θ0 }}a)
    by (eapply (@a_wf_aenv_strip_prefix ((c ~ bc))); exact Hwf).
  assert (Huq2C : uniq Θ0'') by (clear - Huq2p; solve_uniq).
  assert (Hftv2C : ftvar_in_aenv Θ0'' [<=] S0)
    by (simpl in Hftv2; clear - Hftv2; fsetdec).
  assert (Hcnd : c `notin` dom Θ0) by (clear - Huq1; destruct_uniq; fsetdec).
  assert (Hbnd : b0 `notin` dom Θ0'') by (clear - Huq2; destruct_uniq; fsetdec).
  assert (Hpay : ftvar_in_abind bc [<=] dom Θ0)
    by (eapply a_wf_aenv_cons_payload_ftv; exact Hwf).
  assert (Hsc : ftvar_in_aenv ((c ~ bc) ++ Θ0) [<=] dom ((c ~ bc) ++ Θ0))
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HVdom : V [<=] dom ((c ~ bc) ++ Θ0))
    by (clear - Hscp Hsc; fsetdec).
  assert (HscC : ftvar_in_aenv Θ0 [<=] dom Θ0)
    by (apply a_wf_aenv_ftv_dom; exact HwfC).
  assert (Hcd0 : c `in` dom ((c ~ bc) ++ Θ0)) by (simpl; clear; fsetdec).
  assert (Hcfun : forall y, rel_atom ρ V c y -> y = b0)
    by (intros y Hy; exact (Hfun c y b0 Hcd0 Hy Hab)).
  destruct (Hside2 _ _ _ Hbd) as [Hflag Hrule2].
  destruct (Hne_of Hcnd Hfl1 Hfl2) as [Hneα Hneβ].
  assert (Hne2α : α' <> b0).
  { intros Ex. apply Hneα. rewrite Ex in Hrα.
    exact (Hinj α c b0 Hrα Hab). }
  assert (Hne2β : β' <> b0).
  { intros Ex. apply Hneβ. rewrite Ex in Hrβ.
    exact (Hinj β c b0 Hrβ Hab). }
  remember (V ∩ ftvar_in_aenv Θ0) as VS eqn:EVS.
  assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
  assert (HVSsplit : forall y, y `in` V -> y <> c -> y `in` VS).
  { intros y Hy Hne0. subst VS.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
    assert (Hyd : y `in` dom ((c ~ bc) ++ Θ0)) by (clear - Hy HVdom; fsetdec).
    simpl in Hyd. clear - Hy Hne0 Hyd Hds. fsetdec. }
  assert (HVSne : forall y, y `in` VS -> y <> c).
  { intros y Hy Ex. rewrite Ex in Hy.
    assert (Hin : c `in` ftvar_in_aenv Θ0) by (subst VS; clear - Hy; fsetdec).
    clear - Hin HscC Hcnd. fsetdec. }
  assert (HrΘS : rel_aenv ρ VS Θ0 Θ0'').
  { eapply rel_aenv_shrink_V; [ exact Hrest | ].
    intros y Hy Hf. subst VS.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
    clear - Hy Hf Hds. fsetdec. }
  assert (HrαS : rel_atom ρ VS α α').
  { inversion Hrα; subst.
    - apply rel_atom__pair; assumption.
    - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hneα ]. }
  assert (HrβS : rel_atom ρ VS β β').
  { inversion Hrβ; subst.
    - apply rel_atom__pair; assumption.
    - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hneβ ]. }
  assert (HagrS : flex_agree_rel ρ VS Θ0 Θ0'')
    by (eapply flex_agree_peel_cons;
        [ exact Hagr | exact Hab | exact Hinj | exact Hcfun | exact Hcnd
        | exact Hbnd | exact HVS | exact HVSne ]).
  assert (HinjS : rel_inj ρ VS)
    by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVS ]).
  assert (HfunS : rel_fun ρ VS (dom Θ0)).
  { eapply rel_fun_weaken;
      [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVS ]
      | intros y z Hy; exact Hy | simpl; clear; fsetdec ]. }
  assert (HflαS : a_flex_tvar Θ0 α)
    by (rewrite <- (@a_flex_tvar_cons_other c bc Θ0 α Hneα); exact Hfl1).
  assert (HflβS : a_flex_tvar Θ0 β)
    by (rewrite <- (@a_flex_tvar_cons_other c bc Θ0 β Hneβ); exact Hfl2).
  assert (HscpS : VS [<=] ftvar_in_aenv Θ0) by (subst VS; clear; fsetdec).
  assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom Θ0 ->
                  a0 `notin` cols_l ρ).
  { intros a0 Ha0 Hn0. apply Hblk.
    - simpl. clear - Ha0. fsetdec.
    - assert (Hne0 : a0 <> c) by (intros Ex; rewrite Ex in Ha0; contradiction).
      simpl. clear - Hn0 Hne0. fsetdec. }
  assert (HdΘS : dom Θ0'' [<=] S0) by (simpl in HdΘ; clear - HdΘ; fsetdec).
  assert (HcovS : VS ∪ cols_r ρ [<=] S0) by (clear - Hcov HVS; fsetdec).
  destruct (IH S0 Θ0'' α' β' ρ VS HrΘS HrαS HrβS HagrS HinjS HfunS
              HflαS HflβS HwfC Huq2C Hftv2C HscpS HblkS HdΘS HcovS)
    as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
  assert (Hbnd1 : b0 `notin` dom Θ1').
  { pose proof ((proj1 (proj2 e_assign_unify_consis_dom_upper))
                  _ _ _ _ _ _ D2) as Hup.
    assert (HbS0 : b0 `in` S0) by (simpl in HdΘ; clear - HdΘ; fsetdec).
    clear - Hup Hbnd HbS0. fsetdec. }
  exists S1, ρe, ((b0 ~ bdd) ++ Θ1').
  split; [ apply Hrule2; [ exact Hne2α | exact Hne2β | exact D2 ] | ].
  split.
  { apply rel_aenv__cons.
    - eapply rel_atom_incl; [ exact Hab | ].
      intros y z Hy. apply in_or_app. right. exact Hy.
    - eapply rel_abind_mono;
        [ exact Hbd | intros y z Hy; apply in_or_app; right; exact Hy
        | intros y Hy; exact Hy ].
    - eapply rel_aenv_mono;
        [ exact HrΘ1 | intros y z Hy; exact Hy | exact HVS ]. }
  assert (Hinj' : rel_inj (ρe ++ ρ) V)
    by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
  assert (Hab' : rel_atom (ρe ++ ρ) V c b0)
    by (eapply rel_atom_incl;
        [ exact Hab | intros y z Hy; apply in_or_app; right; exact Hy ]).
  assert (Hcfun' : forall y, rel_atom (ρe ++ ρ) V c y -> y = b0).
  { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
    - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
    - exact (Hcfun y Hat0). }
  split.
  { eapply flex_agree_reattach;
      [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hcfun'
      | exact HVSsplit
      | intros HcV; symmetry; apply Hcfun; apply rel_atom__id; exact HcV
      | apply Hflag; [ exact Hcd | exact Hbnd1 ] ]. }
  assert (Hftsub : ftvar_in_aenv ((c ~ bc) ++ Θ0)
                   [<=] add c (ftvar_in_aenv Θ0)).
  { simpl. pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
    clear - Hpay Hds. fsetdec. }
  split.
  { eapply rel_ext_add_scope_l; [ exact Hext1 | exact Hftsub | ].
    intros a_new b_new Hin_new Heq_new. destruct (Hdom1 _ _ Hin_new) as [Hd_new _].
    subst a_new; contradiction. }
  intros a0 b1 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
  split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
Qed.

(* ===================================================================== *)
(*  Assign-Skip / Assign-SkipRigid, at either type-variable head.          *)
(*                                                                        *)
(*  The two rows peel a flexible [β] / a rigid [β] the assignment does    *)
(*  not touch, and their lifts are one proof up to that head [bd]: why    *)
(*  [α <> β] ([Hne_of] — Assign-Skip's own premise, or SkipRigid's        *)
(*  non-flexibility), whether the head is flexible on both sides          *)
(*  ([Hflag]), and the e-rule ([Hrule2]) come in as hypotheses.           *)
(* ===================================================================== *)

Lemma lift_assign_skip_head_of_rule : forall Θ0 Θ1 Ξ α β bd P,
  (forall ρ V bd2, rel_abind ρ V bd bd2 -> bd2 = bd) ->
  ftvar_in_abind bd [<=] empty ->
  (uniq (Ξ ++ (β ~ bd) ++ Θ0) -> a_flex_tvar (Ξ ++ (β ~ bd) ++ Θ0) α ->
   α <> β) ->
  (forall Θ1 Θ1' b, β `notin` dom Θ1 -> b `notin` dom Θ1' ->
     (a_flex_tvar ((β ~ bd) ++ Θ1) β <-> a_flex_tvar ((b ~ bd) ++ Θ1') b)) ->
  (forall S0 S1 Θ0 Θ1 Ξ α β P,
     α <> β ->
     β `notin` ftvar_in_pskl P ->
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
     {{ S0 ↝ S1 ⊨ ((β ~ bd) ++ Θ0) ⊲[ Ξ ] α ≔ P
        ⊣ ((β ~ bd) ++ Θ1) }}e) ->
  β `notin` ftvar_in_pskl P ->
  β `notin` dom Θ1 ->
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  lift_assign_concl Θ0 Ξ α P Θ1 ->
  lift_assign_concl ((β ~ bd) ++ Θ0) Ξ α P ((β ~ bd) ++ Θ1).
Proof.
  intros Θ0 Θ1 Ξ α β bd P Hbd2 Hbdft Hne_of Hflag Hrule2 Hβp Hβd HD IH.
  intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
    Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
  destruct (rel_aenv_cons_inv_l HrΘ)
    as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
  subst Θ0'.
  pose proof (Hbd2 _ _ _ Hbd) as Ebd. subst bdd.
  assert (Huq1 : uniq (Ξ ++ (β ~ bd) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Huq2 : uniq (Ξ' ++ (b ~ bd) ++ Θ0''))
    by (exact Huq2p).
  assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
  assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
  assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
  { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
    clear - Hftv2. fsetdec. }
  assert (Hβnd : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
    destruct_uniq. fsetdec. }
  assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
  { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
    destruct_uniq. fsetdec. }
  assert (Hsc : ftvar_in_aenv (Ξ ++ (β ~ bd) ++ Θ0)
                [<=] dom (Ξ ++ (β ~ bd) ++ Θ0))
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HVdom : V [<=] dom (Ξ ++ (β ~ bd) ++ Θ0))
    by (clear - Hscp Hsc; fsetdec).
  assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
    by (apply a_wf_aenv_ftv_dom; exact HwfC).
  assert (Hβd0 : β `in` dom (Ξ ++ (β ~ bd) ++ Θ0))
    by (repeat rewrite dom_app; simpl; clear; fsetdec).
  assert (Hβfun : forall y, rel_atom ρ V β y -> y = b)
    by (intros y Hy; exact (Hfun β y b Hβd0 Hy Hab)).
  pose proof (Hne_of Huq1 Hfl) as Hne.
  assert (Hne2 : α' <> b).
  { intros Ex. apply Hne. rewrite Ex in Hrα. exact (Hinj α β b Hrα Hab). }
  assert (HbP : b `notin` ftvar_in_pskl P')
    by (eapply rel_pskl_notin_r_inj;
        [ exact HrP | exact Hinj | exact Hab | exact Hβp ]).
  remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VS eqn:EVS.
  assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
  assert (HVSsplit : forall x, x `in` V -> x <> β -> x `in` VS).
  { intros x Hx Hne0. subst VS.
    pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
    assert (Hxd : x `in` dom (Ξ ++ (β ~ bd) ++ Θ0))
      by (clear - Hx HVdom; fsetdec).
    repeat rewrite dom_app in Hxd. simpl in Hxd.
    repeat rewrite dom_app in Hds.
    clear - Hx Hne0 Hxd Hds. fsetdec. }
  assert (HVSne : forall x, x `in` VS -> x <> β).
  { intros x Hx Ex. rewrite Ex in Hx.
    assert (Hin : β `in` ftvar_in_aenv (Ξ ++ Θ0))
      by (subst VS; clear - Hx; fsetdec).
    clear - Hin HscC Hβnd. fsetdec. }
  assert (HrΘS : rel_aenv ρ VS Θ0 Θ0'').
  { eapply rel_aenv_shrink_V; [ exact Hrest | ].
    intros x Hx Hf. subst VS.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
    rewrite ftvar_in_aenv_app. clear - Hx Hf Hds. fsetdec. }
  assert (HrΞS : rel_aenv ρ VS Ξ Ξ').
  { eapply rel_aenv_shrink_V; [ exact HrΞ | ].
    intros x Hx Hf. subst VS.
    pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
    rewrite ftvar_in_aenv_app. clear - Hx Hf Hds. fsetdec. }
  assert (HrαS : rel_atom ρ VS α α').
  { inversion Hrα; subst.
    - apply rel_atom__pair; assumption.
    - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hne ]. }
  assert (HrPS : rel_pskl ρ VS P P').
  { eapply rel_pskl_shrink_V; [ exact HrP | ].
    intros x Hx Hf. apply HVSsplit; [ exact Hx | ].
    intros Ex. rewrite Ex in Hf. contradiction. }
  assert (HagrS : flex_agree_rel ρ VS (Ξ ++ Θ0) (Ξ' ++ Θ0''))
    by (eapply flex_agree_peel;
        [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
        | exact Hbnd | exact HVS | exact HVSne ]).
  assert (HinjS : rel_inj ρ VS)
    by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVS ]).
  assert (HfunS : rel_fun ρ VS (dom (Ξ ++ Θ0))).
  { eapply rel_fun_weaken;
      [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVS ]
      | intros x y Hx; exact Hx
      | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
  assert (HflS : a_flex_tvar (Ξ ++ Θ0) α)
    by (rewrite <- (@a_flex_tvar_mid_other Ξ β bd Θ0 α Hne);
        exact Hfl).
  assert (HscpS : VS [<=] ftvar_in_aenv (Ξ ++ Θ0))
    by (subst VS; clear; fsetdec).
  assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                  a0 `notin` cols_l ρ).
  { intros a0 Ha0 Hn0. apply Hblk.
    - simpl. clear - Ha0. fsetdec.
    - assert (Hne0 : a0 <> β)
        by (intros Ex; rewrite Ex in Ha0; contradiction).
      repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne0. fsetdec. }
  assert (HdΘS : dom (Ξ' ++ Θ0'') [<=] S0)
    by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
        clear - HdΘ; fsetdec).
  assert (HcovS : VS ∪ cols_r ρ [<=] S0) by (clear - Hcov HVS; fsetdec).
  assert (HwfpS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
    by (eapply a_wf_pskl_strip_mid; [ exact Hwfp | exact Hβp ]).
  destruct (IH S0 Θ0'' Ξ' α' P' ρ VS HrΘS HrΞS HrαS HrPS HagrS HinjS HfunS
              HflS HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS HdΘS HcovS HcovP HwfpS)
    as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
  assert (Hbnd1 : b `notin` dom Θ1').
  { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ D2)
      as Hup.
    assert (HbS0 : b `in` S0).
    { repeat rewrite dom_app in HdΘ. simpl in HdΘ. clear - HdΘ. fsetdec. }
    clear - Hup Hbnd HbS0. fsetdec. }
  exists S1, ρe, ((b ~ bd) ++ Θ1').
  split; [ apply Hrule2; [ exact Hne2 | exact HbP | exact D2 ] | ].
  split.
  { apply rel_aenv__cons.
    - eapply rel_atom_incl; [ exact Hab | ].
      intros x y Hx. apply in_or_app. right. exact Hx.
    - eapply rel_abind_mono;
        [ exact Hbd | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ].
    - eapply rel_aenv_mono;
        [ exact HrΘ1 | intros x y Hx; exact Hx | exact HVS ]. }
  assert (Hinj' : rel_inj (ρe ++ ρ) V)
    by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
  assert (Hab' : rel_atom (ρe ++ ρ) V β b)
    by (eapply rel_atom_incl;
        [ exact Hab | intros x y Hx; apply in_or_app; right; exact Hx ]).
  assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V β y -> y = b).
  { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
    - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
    - exact (Hβfun y Hat0). }
  split.
  { eapply flex_agree_reattach;
      [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
      | exact HVSsplit
      | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
      | apply Hflag; [ exact Hβd | exact Hbnd1 ] ]. }
  assert (Hftsub : ftvar_in_aenv (Ξ ++ (β ~ bd) ++ Θ0)
                   [<=] add β (ftvar_in_aenv (Ξ ++ Θ0))).
  { repeat rewrite ftvar_in_aenv_app. simpl. clear - Hbdft; fsetdec. }
  split.
  { eapply rel_ext_add_scope_l; [ exact Hext1 | exact Hftsub | ].
    intros a_new b_new Hin_new Heq_new. destruct (Hdom1 _ _ Hin_new) as [Hd_new _].
    subst a_new; contradiction. }
  intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
  split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
Qed.

(* ===================================================================== *)
(*  Assign-SkipTmVar, at either term binding.                              *)
(*                                                                        *)
(*  The mech splits the paper's one [x : P] entry into a TYPE binding and  *)
(*  a SKELETON binding, so the paper's one rule is two rows                *)
(*  ([a_assign__skip_tm_var] / [a_assign__skip_tm_skl]).  Their lifts are  *)
(*  one proof up to the binding [bd1]: what depends on its sort comes in   *)
(*  as hypotheses — that it is not flexible, that its payload is scoped    *)
(*  in the tail ([Hpay1]), that a term variable is not a type variable     *)
(*  ([Hnotv]) — and side 2's binding [bd2], read off [rel_abind], brings   *)
(*  its own non-flexibility and its e-rule ([Hside2]).                     *)
(*  ⭐ The row with NO [x ∉ ftvar P] premise: [V] keeps [x] as an          *)
(*  IDENTITY PAIR when it has to, and deletes it again after.             *)
(* ===================================================================== *)

Lemma lift_assign_skip_tm_of_rule : forall Θ0 Θ1 Ξ α x bd1 P,
  bd1 <> abind_flex_mono ->
  (forall t, bd1 <> abind_flex_mono_def t) ->
  (a_decls Ξ -> {{ ⊢ (Ξ ++ (x ~ bd1) ++ Θ0) }}a ->
   ftvar_in_abind bd1 [<=] ftvar_in_aenv (Ξ ++ Θ0)) ->
  (forall Γ, uniq Γ -> binds x bd1 Γ -> ~ a_binds_tvar x Γ) ->
  (forall ρ V bd2, rel_abind ρ V bd1 bd2 ->
     bd2 <> abind_flex_mono /\ (forall t, bd2 <> abind_flex_mono_def t) /\
     (forall S0 S1 Θ0 Θ1 Ξ α x P,
        {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
        {{ S0 ↝ S1 ⊨ ((x ~ bd2) ++ Θ0) ⊲[ Ξ ] α ≔ P
           ⊣ ((x ~ bd2) ++ Θ1) }}e)) ->
  x `notin` dom Θ1 ->
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  lift_assign_concl Θ0 Ξ α P Θ1 ->
  lift_assign_concl ((x ~ bd1) ++ Θ0) Ξ α P ((x ~ bd1) ++ Θ1).
Proof.
  intros Θ0 Θ1 Ξ α x bd1 P Hnf1 Hnf1' Hpay1 Hnotv Hside2 Hxd HD IH.
  intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
    Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
  destruct (rel_aenv_cons_inv_l HrΘ)
    as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
  subst Θ0'.
  destruct (Hside2 _ _ _ Hbd) as [Hnf2 [Hnf2' Hrule2]].
  assert (Huq1 : uniq (Ξ ++ (x ~ bd1) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Huq2 : uniq (Ξ' ++ (b ~ bdd) ++ Θ0''))
    by (exact Huq2p).
  assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
  assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
  assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
  { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
    clear - Hftv2. fsetdec. }
  assert (Hβnd : x `notin` dom (Ξ ++ Θ0)).
  { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
    destruct_uniq. fsetdec. }
  assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
  { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
    destruct_uniq. fsetdec. }
  assert (Hsc : ftvar_in_aenv (Ξ ++ (x ~ bd1) ++ Θ0)
                [<=] dom (Ξ ++ (x ~ bd1) ++ Θ0))
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HVdom : V [<=] dom (Ξ ++ (x ~ bd1) ++ Θ0))
    by (clear - Hscp Hsc; fsetdec).
  assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
    by (apply a_wf_aenv_ftv_dom; exact HwfC).
  assert (Hβd0 : x `in` dom (Ξ ++ (x ~ bd1) ++ Θ0))
    by (repeat rewrite dom_app; simpl; clear; fsetdec).
  assert (Hβfun : forall y, rel_atom ρ V x y -> y = b)
    by (intros y Hy; exact (Hfun x y b Hβd0 Hy Hab)).
  assert (Hne : α <> x).
  { intros Ex. rewrite Ex in Hfl.
    exact (@a_flex_tvar_mid_nonflex_absurd Ξ x bd1 Θ0 Huq1
             Hnf1 Hnf1' Hfl). }
  assert (HflS : a_flex_tvar (Ξ ++ Θ0) α)
    by (rewrite <- (@a_flex_tvar_mid_other Ξ x (bd1) Θ0 α Hne);
        exact Hfl).
  (* the peeled payload is scoped in the TAIL *)
  pose proof (Hpay1 Hdec Hwf) as Hpay.
  assert (Hxp : x `notin` ftvar_in_pskl P).
  { intros Hin.
    pose proof (a_wf_pskl_ftv_binds Hwfp Hin) as Htv.
    apply (Hnotv (Ξ ++ (x ~ bd1) ++ Θ0) Huq1
             ltac:(unfold binds; apply in_or_app; right; simpl;
                   left; reflexivity)).
    exact Htv. }
  assert (HwfpS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
    by (eapply a_wf_pskl_strip_mid; [ exact Hwfp | exact Hxp ]).
  assert (Hftsub : ftvar_in_aenv (Ξ ++ (x ~ bd1) ++ Θ0)
                   [<=] add x (ftvar_in_aenv (Ξ ++ Θ0))).
  { repeat rewrite ftvar_in_aenv_app. repeat rewrite ftvar_in_aenv_app in Hpay.
    simpl. simpl in Hpay. clear - Hpay. fsetdec. }
  assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                  a0 `notin` cols_l ρ).
  { intros a0 Ha0 Hn0. apply Hblk.
    - simpl. clear - Ha0. fsetdec.
    - assert (Hne0 : a0 <> x)
        by (intros Ex; rewrite Ex in Ha0; contradiction).
      repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne0. fsetdec. }
  assert (HdΘS : dom (Ξ' ++ Θ0'') [<=] S0)
    by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
        clear - HdΘ; fsetdec).
  assert (HbS0 : b `in` S0)
    by (repeat rewrite dom_app in HdΘ; simpl in HdΘ; clear - HdΘ; fsetdec).
  assert (HfunD : rel_fun ρ V (dom (Ξ ++ Θ0))).
  { eapply rel_fun_weaken;
      [ exact Hfun | intros y z Hy; exact Hy
      | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
  destruct (AtomSetProperties.In_dec x V) as [HxV | HxV].
  + (* ⭐ [x ∈ V]: [rel_fun] forces side 2's head to be [x] too, so the
       pair the shrink needs is the IDENTITY one, and it leaves again *)
    assert (Ebx : b = x)
      by (symmetry; apply Hβfun; apply rel_atom__id; exact HxV).
    subst b.
    remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VS eqn:EVS.
    assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
    assert (HVSsplit : forall y, y `in` V -> y <> x -> y `in` VS).
    { intros y Hy Hne0. subst VS.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      assert (Hyd : y `in` dom (Ξ ++ (x ~ bd1) ++ Θ0))
        by (clear - Hy HVdom; fsetdec).
      repeat rewrite dom_app in Hyd. simpl in Hyd.
      repeat rewrite dom_app in Hds.
      clear - Hy Hne0 Hyd Hds. fsetdec. }
    assert (HVSne : forall y, y `in` VS -> y <> x).
    { intros y Hy Ex. rewrite Ex in Hy.
      assert (Hin : x `in` ftvar_in_aenv (Ξ ++ Θ0))
        by (subst VS; clear - Hy; fsetdec).
      clear - Hin HscC Hβnd. fsetdec. }
    assert (HrΘS : rel_aenv ((x, x) :: ρ) VS Θ0 Θ0'').
    { eapply rel_aenv_mono;
        [ eapply rel_aenv_shrink_V; [ exact Hrest | ]
        | intros y z Hy; right; exact Hy | intros y Hy; exact Hy ].
      intros y Hy Hf. subst VS.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      rewrite ftvar_in_aenv_app. clear - Hy Hf Hds. fsetdec. }
    assert (HrΞS : rel_aenv ((x, x) :: ρ) VS Ξ Ξ').
    { eapply rel_aenv_mono;
        [ eapply rel_aenv_shrink_V; [ exact HrΞ | ]
        | intros y z Hy; right; exact Hy | intros y Hy; exact Hy ].
      intros y Hy Hf. subst VS.
      pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
      rewrite ftvar_in_aenv_app. clear - Hy Hf Hds. fsetdec. }
    assert (HrαS : rel_atom ((x, x) :: ρ) VS α α').
    { inversion Hrα; subst.
      - apply rel_atom__pair. right. assumption.
      - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hne ]. }
    assert (HrPS : rel_pskl ((x, x) :: ρ) VS P P').
    { eapply rel_pskl_shrink_V_id; [ exact HrP | ].
      intros y Hy Hf. destruct (y == x) as [-> | Hne0];
        [ left; reflexivity | right; apply HVSsplit; assumption ]. }
    assert (HagrS : flex_agree_rel ((x, x) :: ρ) VS (Ξ ++ Θ0) (Ξ' ++ Θ0'')).
    { apply flex_agree_rel_push_id_absent; [ | exact Hβnd | exact Hbnd ].
      eapply flex_agree_peel;
        [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
        | exact Hbnd | exact HVS | exact HVSne ]. }
    assert (HinjS : rel_inj ((x, x) :: ρ) VS)
      by (eapply rel_inj_push_id; [ exact Hinj | exact HxV | exact HVS ]).
    assert (HfunS : rel_fun ((x, x) :: ρ) VS (dom (Ξ ++ Θ0)))
      by (eapply rel_fun_push_absent;
          [ exact HfunD | exact HVS | exact Hβnd ]).
    assert (HscpS : VS [<=] ftvar_in_aenv (Ξ ++ Θ0))
      by (subst VS; clear; fsetdec).
    assert (HblkS' : forall a0, a0 `in` dom Θ1 ->
              a0 `notin` dom (Ξ ++ Θ0) -> a0 `notin` cols_l ((x, x) :: ρ)).
    { intros a0 Ha0 Hn0. simpl.
      assert (Hne0 : a0 <> x)
        by (intros Ex; rewrite Ex in Ha0; contradiction).
      pose proof (HblkS a0 Ha0 Hn0) as Hc. clear - Hc Hne0. fsetdec. }
    assert (HcovS : VS ∪ cols_r ((x, x) :: ρ) [<=] S0).
    { simpl. clear - Hcov HVS HxV. fsetdec. }
    destruct (IH S0 Θ0'' Ξ' α' P' ((x, x) :: ρ) VS HrΘS HrΞS HrαS HrPS
                HagrS HinjS HfunS HflS HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS'
                HdΘS HcovS HcovP HwfpS)
      as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
    assert (Hbnd1 : x `notin` dom Θ1').
    { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ D2)
        as Hup.
      clear - Hup Hbnd HbS0. fsetdec. }
    exists S1, ρe, ((x ~ bdd) ++ Θ1').
    split; [ apply Hrule2; exact D2 | ].
    assert (Hrel1' : rel_aenv (ρe ++ ρ) V Θ1 Θ1').
    { eapply rel_aenv_drop_id; [ | exact HxV ].
      eapply rel_aenv_mono;
        [ exact HrΘ1 | intros y z Hy; exact Hy | exact HVS ]. }
    assert (Hagr1' : flex_agree_rel (ρe ++ ρ) VS Θ1 Θ1').
    { eapply flex_agree_rel_weaken;
        [ exact Hagr1
        | intros y z Hy; apply in_app_or in Hy; apply in_or_app;
          destruct Hy as [Hy | Hy];
            [ left; exact Hy | right; right; exact Hy ]
        | intros y Hy; exact Hy ]. }
    split.
    { apply rel_aenv__cons.
      - apply rel_atom__id. exact HxV.
      - eapply rel_abind_mono; [ exact Hbd | intros y z Hy; apply in_or_app; right; exact Hy | intros y Hy; exact Hy ].
      - exact Hrel1'. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V x x)
      by (apply rel_atom__id; exact HxV).
    assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V x y -> y = x).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hβfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1' | exact Hab' | exact Hinj' | exact Hβfun'
        | exact HVSsplit
        | intros _; reflexivity
        | split; intros Hf; exfalso;
          [ exact (@a_flex_tvar_cons_absent x bd1 Θ1 x Hnf1 Hnf1' Hxd Hf)
          | exact (@a_flex_tvar_cons_absent x bdd Θ1' x Hnf2 Hnf2'
                     Hbnd1 Hf) ] ]. }
    split.
    { eapply rel_ext_add_scope_l; [ exact Hext1 | exact Hftsub | ].
      intros a_new b_new Hin_new Heq_new. destruct (Hdom1 _ _ Hin_new) as [Hd_new _].
      subst a_new; contradiction. }
    intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  + (* [x ∉ V]: nothing to shrink — the peeled entry was never in the
       identity support *)
    assert (HscpS : V [<=] ftvar_in_aenv (Ξ ++ Θ0)).
    { pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      repeat rewrite dom_app in HVdom, Hds. simpl in HVdom.
      clear - HVdom Hds HxV. fsetdec. }
    assert (HVSne : forall y, y `in` V -> y <> x)
      by (intros y Hy Ex; rewrite Ex in Hy; contradiction).
    assert (HagrS : flex_agree_rel ρ V (Ξ ++ Θ0) (Ξ' ++ Θ0''))
      by (eapply flex_agree_peel;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | intros y Hy; exact Hy | exact HVSne ]).
    destruct (IH S0 Θ0'' Ξ' α' P' ρ V Hrest HrΞ Hrα HrP HagrS Hinj HfunD
                HflS HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS HdΘS Hcov HcovP HwfpS)
      as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
    assert (Hbnd1 : b `notin` dom Θ1').
    { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ D2)
        as Hup.
      clear - Hup Hbnd HbS0. fsetdec. }
    exists S1, ρe, ((b ~ bdd) ++ Θ1').
    split; [ apply Hrule2; exact D2 | ].
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros y z Hy. apply in_or_app. right. exact Hy.
      - eapply rel_abind_mono; [ exact Hbd | intros y z Hy; apply in_or_app; right; exact Hy | intros y Hy; exact Hy ].
      - exact HrΘ1. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V x b)
      by (eapply rel_atom_incl;
          [ exact Hab | intros y z Hy; apply in_or_app; right; exact Hy ]).
    assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V x y -> y = b).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hβfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
        | intros y Hy _; exact Hy
        | intros HxV0; contradiction
        | split; intros Hf; exfalso;
          [ exact (@a_flex_tvar_cons_absent x bd1 Θ1 x Hnf1 Hnf1' Hxd Hf)
          | exact (@a_flex_tvar_cons_absent b bdd Θ1' b Hnf2 Hnf2'
                     Hbnd1 Hf) ] ]. }
    split.
    { eapply rel_ext_add_scope_l; [ exact Hext1 | exact Hftsub | ].
      intros a_new b_new Hin_new Heq_new. destruct (Hdom1 _ _ Hin_new) as [Hd_new _].
      subst a_new; contradiction. }
    intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
Qed.

Theorem a_assign_unify_consis_rel_e :
  (forall Θ0 Ξ α P Θ1, {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
     lift_assign_concl Θ0 Ξ α P Θ1) /\
  (forall Θ0 α β Θ1, {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
     lift_unify_concl Θ0 α β Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P Q Θ1, {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
     lift_consis_concl Δ1 Δ2 Θ0 P0 P Q Θ1).
Proof.
  apply a_assign_unify_consis_mutind.
  - (* Assign-UnivGhost-Id *)
    intros Θ0 α.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    apply rel_aenv_nil_inv_l in HrΞ. subst Ξ'.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & b2 & Θ0'' & -> & Hab & Hbd & Hrest).
    inversion Hbd; subst.
    assert (Hfun0 : rel_fun ρ V (dom ((α ~ abind_flex_mono) ++ Θ0))).
    { eapply rel_fun_weaken; [ exact Hfun | intros x y Hin; exact Hin | ].
      simpl_env. reflexivity. }
    assert (Hαd : α `in` dom ((α ~ abind_flex_mono) ++ Θ0))
      by (simpl; clear; fsetdec).
    assert (Eb : α' = b) by (exact (Hfun0 α α' b Hαd Hrα Hab)).
    subst α'.
    inversion HrP as [ | n0 | x0 y0 Hx0 | Pa Pb Qa Qb Ha Hb | Pa Qa Ha
                     | | Pa Qa Hin1 ]; subst.
    inversion Hin1 as [ | n1 | x1 c Hxc | Pc Pd Qc Qd Hc Hd | Pc Qc Hc
                      | | Pc Qc Hc ]; subst.
    assert (Ec : c = b) by (exact (Hfun0 α c b Hαd Hxc Hab)). subst c.
    unfold lift_assign_post.
    exists S0, (@nil (atom * atom)%type), ((b ~ abind_flex_mono) ++ Θ0'').
    split; [ apply e_assign__univ_ghost_id | ].
    simpl. simpl in Hagr.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* ⭐ Assign-SolveM *)
    intros Θ0 Ξ α P βs τ Hαp Hguess Hmono Huqβ Hfrβ.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Hαd : α `in` dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Eb : α' = b) by (exact (Hfun α α' b Hαd Hrα Hab)). subst α'.
    assert (HbP : b `notin` ftvar_in_pskl P')
      by (eapply rel_pskl_notin_r_inj;
          [ exact HrP | exact Hinj | exact Hab | exact Hαp ]).
    remember (V ∩ (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P)) as VG eqn:EVG.
    assert (HVG : VG [<=] V) by (subst VG; clear; fsetdec).
    assert (HrPG : rel_pskl ρ VG P P').
    { eapply rel_pskl_shrink_V; [ exact HrP | ].
      intros a Ha Hf. subst VG. clear - Ha Hf. fsetdec. }
    assert (Hscp1G : VG [<=] ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P)
      by (subst VG; clear; fsetdec).
    assert (HcovG : VG ∪ ftvar_in_pskl P' [<=] S0)
      by (clear - HVG Hcov HcovP; fsetdec).
    destruct (a_guess_mono_rel_e Hguess HrPG Hscp1G HcovG)
      as (S1 & ρn & Ξ2 & τ2 & HG2 & E1 & E2 & HrelT0).
    assert (HrelT : rel_ptyp (ρn ++ ρ) V τ τ2).
    { unfold rel_ptyp. eapply rel_pskl_mono;
        [ exact HrelT0 | intros x y Hx; exact Hx | exact HVG ]. }
    assert (Hmono2 : mono_ptyp τ2)
      by (eapply rel_ptyp_mono_ptyp; [ exact HrelT | exact Hmono ]).
    assert (Hb2fr : dom Ξ2 ∩ S0 [=] empty)
      by (exact (e_guess_mono_block_fresh HG2)).
    assert (Huq2b : uniq Ξ2) by (exact (e_guess_mono_uniq HG2)).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    assert (Hsc : ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0)
                  [<=] dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (Hβdom : forall a, a `in` dom βs ->
                    a `notin` dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0)).
    { intros a Ha. pose proof (Hfrβ a Ha) as Hn.
      repeat rewrite dom_app in Hn |- *. simpl. clear - Hn. fsetdec. }
    assert (Hβcols : forall a, a `in` dom βs -> a `notin` cols_l ρ).
    { intros a Ha. apply Hblk; [ | exact (Hβdom a Ha) ].
      repeat rewrite dom_app. simpl. clear - Ha. fsetdec. }
    assert (Hext : rel_ext ρn
                     (ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0)) S0).
    { apply rel_ext_flex_pairs.
      - rewrite <- E1; exact Huqβ.
      - rewrite <- E2; exact Huq2b.
      - rewrite <- Hdfl. apply inter_empty_pointwise. intros a Ha.
        pose proof (Hβdom a Ha) as Hna. clear - Hna Hsc; fsetdec.
      - rewrite <- Hdfr. clear - Hb2fr; fsetdec. }

    unfold lift_assign_post.
    exists S1, ρn, ((b ~ abind_flex_mono_def τ2) ++ Ξ2 ++ Ξ' ++ Θ0'').
    split.
    { apply e_assign__solve_m; [ exact HbP | exact HG2 | exact Hmono2 ]. }
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros x y Hx. apply in_or_app. right. exact Hx.
      - constructor. exact HrelT.
      - apply rel_aenv_app.
        + rewrite E1, E2. apply rel_aenv_flex_pairs.
        + apply rel_aenv_app; apply rel_aenv_widen; assumption. }
    split.
    { split.
      - intros x HxV.
        assert (Hxβ : x `notin` dom βs).
        { intros Hin. pose proof (Hβdom x Hin) as Hn.
          clear - Hn HVdom HxV. fsetdec. }
        assert (HxΞ2 : x `notin` dom Ξ2).
        { intros Hin. clear - Hin Hb2fr HxV Hcov. fsetdec. }
        rewrite (@a_flex_tvar_solve_m α τ βs Ξ Θ0 x Hxβ).
        rewrite (@a_flex_tvar_solve_m b τ2 Ξ2 Ξ' Θ0'' x HxΞ2).
        exact (proj1 Hagr x HxV).
      - intros x y Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        + assert (Hx : x `in` dom βs)
            by (rewrite Hdfl; eapply cols_l_in; exact Hin).
          assert (Hy : y `in` dom Ξ2)
            by (rewrite Hdfr; eapply cols_r_in; exact Hin).
          split; intros _.
          * rewrite E2 in Hy |- *. rewrite ! a_flex_tvar_app_iff.
            right. left.
            apply (proj2 (a_flex_tvar_decls y (a_decls_flex_pairs_r ρn))).
            exact Hy.
          * rewrite E1 in Hx |- *. rewrite ! a_flex_tvar_app_iff.
            right. left.
            apply (proj2 (a_flex_tvar_decls x (a_decls_flex_pairs_l ρn))).
            exact Hx.
        + assert (Hxβ : x `notin` dom βs).
          { intros Hb0. apply (Hβcols x Hb0). eapply cols_l_in; exact Hin. }
          assert (HyΞ2 : y `notin` dom Ξ2).
          { intros Hb0. pose proof (cols_r_in _ _ _ Hin) as Hyc.
            clear - Hb0 Hyc Hb2fr Hcov. fsetdec. }
          rewrite (@a_flex_tvar_solve_m α τ βs Ξ Θ0 x Hxβ).
          rewrite (@a_flex_tvar_solve_m b τ2 Ξ2 Ξ' Θ0'' y HyΞ2).
          exact (proj2 Hagr x y Hin). }
    split; [ exact Hext | ].
    intros a b0 Hin. split.
    { assert (Ha : a `in` dom βs)
        by (rewrite Hdfl; eapply cols_l_in; exact Hin).
      repeat rewrite dom_app. simpl. clear - Ha. fsetdec. }
    { assert (Hb0 : b0 `in` dom Ξ2)
        by (rewrite Hdfr; eapply cols_r_in; exact Hin).
      repeat rewrite dom_app. simpl. clear - Hb0. fsetdec. }
  - (* ⭐ Assign-Assign — the SUBSTITUTION row, and the walk's only descent
       into CONSISTENCY *)
    intros Θ0 Θ1 Ξ α β τ P Q Hfa Hβd HD IH.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'.
    inversion Hbd as [ | | t1 t2 Hrτ | A1 A2 HrA | Q1 Q2 HrQ ]; subst.
    assert (Huq1 : uniq (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq (Ξ' ++ (b ~ abind_flex_mono_def t2) ++ Θ0''))
      by (exact Huq2p).
    assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
    assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hτdom : ftvar_in_ptyp τ [<=] dom Θ0)
      by (apply a_wf_ptyp_ftv_dom;
          exact (proj1 (@a_wf_aenv_mid_def_inv Ξ β τ Θ0 Hdec Hwf))).
    assert (Hτ2dom : ftvar_in_ptyp t2 [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hsc : ftvar_in_aenv (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0)
                  [<=] dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (Hβnd : β `notin` dom (Ξ ++ Θ0)).
    { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
    { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hβd0 : β `in` dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Hβfun : forall y, rel_atom ρ V β y -> y = b)
      by (intros y Hy; exact (Hfun β y b Hβd0 Hy Hab)).
    assert (HαΞ : α `notin` dom Ξ).
    { pose proof (a_flex_tvar_in_dom Hfa) as Hin.
      assert (Hdisj : disjoint Ξ ((β ~ abind_flex_mono_def τ) ++ Θ0))
        by (clear - Huq1; solve_uniq).
      unfold disjoint in Hdisj. clear - Hdisj Hin. fsetdec. }
    assert (Hα'Ξ : α' `notin` dom Ξ').
    { intros Hin. destruct (rel_aenv_dom_r_inv HrΞ Hin) as (a0 & Ha0 & Hat0).
      apply HαΞ. assert (Ea : a0 = α) by (exact (Hinj a0 α α' Hat0 Hrα)).
      rewrite <- Ea. exact Ha0. }
    assert (Hfa2 : a_flex_tvar ((b ~ abind_flex_mono_def t2) ++ Θ0'') α').
    { assert (Hbig : a_flex_tvar (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) α)
        by (apply a_flex_tvar_weaken_app; exact Hfa).
      apply (proj1 (flex_agree_rel_use Hagr Hrα)) in Hbig.
      apply (proj1 (a_flex_tvar_app_notin _ _ Hα'Ξ)). exact Hbig. }
    remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VC eqn:EVC.
    assert (HVC : VC [<=] V) by (subst VC; clear; fsetdec).
    assert (HVCsplit : forall x, x `in` V -> x <> β -> x `in` VC).
    { intros x Hx Hne. subst VC.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      assert (Hxd : x `in` dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
        by (clear - Hx HVdom; fsetdec).
      repeat rewrite dom_app in Hxd. simpl in Hxd.
      repeat rewrite dom_app in Hds.
      clear - Hx Hne Hxd Hds. fsetdec. }
    assert (HVCne : forall x, x `in` VC -> x <> β).
    { intros x Hx Ex. rewrite Ex in Hx.
      assert (Hin : β `in` ftvar_in_aenv (Ξ ++ Θ0))
        by (subst VC; clear - Hx; fsetdec).
      clear - Hin HscC Hβnd. fsetdec. }
    assert (HrΘC : rel_aenv ρ VC (Ξ ++ Θ0) (Ξ' ++ Θ0'')).
    { eapply rel_aenv_shrink_V; [ apply rel_aenv_app; eassumption | ].
      intros x Hx Hf. apply HVCsplit; [ exact Hx | ].
      intros Ex. rewrite Ex in Hf.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      clear - Hf Hds HscC Hβnd. fsetdec. }
    assert (HrPsub : rel_pskl ρ V (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
                       (subst_pskl_in_pskl (ptyp_to_pskl t2) b P'))
      by (apply rel_pskl_subst;
          [ exact HrP | exact Hrτ | exact Hab | exact Hinj | exact Hβfun ]).
    assert (HrVsub : rel_pskl ρ V
                       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
                       (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α')))
      by (apply rel_pskl_subst;
          [ constructor; exact Hrα | exact Hrτ | exact Hab | exact Hinj
          | exact Hβfun ]).
    assert (Hshr : forall (R : pskl) x, x `in` V ->
              x `in` ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β R) ->
              x `in` VC).
    { intros R x Hx Hin.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper R (ptyp_to_pskl τ) β)
        as Hu.
      rewrite ftvar_ptyp_to_pskl in Hu.
      destruct (AtomSetProperties.In_dec x (ftvar_in_ptyp τ)) as [Hxτ | Hxτ].
      - subst VC.
        pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
        repeat rewrite dom_app in Hds.
        clear - Hx Hxτ Hτdom Hds. fsetdec.
      - apply HVCsplit; [ exact Hx | ].
        intros Ex. rewrite Ex in Hin. clear - Hin Hu Hxτ Ex. fsetdec. }
    assert (HrPsubC : rel_pskl ρ VC (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b P'))
      by (eapply rel_pskl_shrink_V;
          [ exact HrPsub | intros x Hx Hf; exact (Hshr P x Hx Hf) ]).
    assert (HrVsubC : rel_pskl ρ VC
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α')))
      by (eapply rel_pskl_shrink_V;
          [ exact HrVsub
          | intros x Hx Hf; exact (Hshr (pskl_var_f α) x Hx Hf) ]).
    assert (HatomsC : rel_atoms ρ VC empty empty)
      by (intros x y _; split; intros Hin0; exfalso; clear - Hin0; fsetdec).
    assert (HagrC : flex_agree_rel ρ VC (Ξ ++ Θ0) (Ξ' ++ Θ0''))
      by (eapply flex_agree_peel;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | exact HVC | exact HVCne ]).
    assert (HinjC : rel_inj ρ VC)
      by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVC ]).
    assert (HfunC : rel_fun ρ VC (dom (Ξ ++ Θ0))).
    { eapply rel_fun_weaken;
        [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVC ]
        | intros x y Hx; exact Hx
        | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (HblkC : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne : a0 <> β) by (intros Ex; rewrite Ex in Ha0; contradiction).
        repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne. fsetdec. }
    assert (HdΘC : dom (Ξ' ++ Θ0'') [<=] S0)
      by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
          clear - HdΘ; fsetdec).
    assert (HcovC : VC ∪ cols_r ρ [<=] S0) by (clear - Hcov HVC; fsetdec).
    assert (HcovS : ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl t2) b P')
                    ∪ ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b
                           (pskl_var_f α')) [<=] S0).
    { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P' (ptyp_to_pskl t2) b)
        as Hu1.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper (pskl_var_f α')
                    (ptyp_to_pskl t2) b) as Hu2.
      rewrite ftvar_ptyp_to_pskl in Hu1, Hu2.
      assert (Hα'd : ftvar_in_pskl (pskl_var_f α') [<=] S0).
      { simpl. pose proof (a_flex_tvar_in_dom Hfa2) as Hin.
        repeat rewrite dom_app in HdΘ. simpl in HdΘ, Hin.
        clear - Hin HdΘ. fsetdec. }
      repeat rewrite dom_app in HdΘ. simpl in HdΘ.
      clear - Hu1 Hu2 HcovP Hτ2dom HdΘ Hα'd. fsetdec. }
    assert (HcovΔ : empty ∪ empty [<=] S0) by (clear; fsetdec).
    (* ---- the wf package the consis premise wants ---- *)
    assert (Hbβ : binds β (abind_flex_mono_def τ)
                    (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (unfold binds; apply in_or_app; right; simpl; left; reflexivity).
    assert (Hτmono : mono_ptyp τ) by (exact (@a_wf_aenv_binds_def_mono _ β τ Hwf Hbβ)).
    assert (Hβτ : β `notin` ftvar_in_ptyp τ).
    { repeat rewrite dom_app in Hβnd. clear - Hτdom Hβnd. fsetdec. }
    assert (HwfPsub : {{ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ⨟ empty ⊢ₚₛ
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) }}a)
      by (apply a_wf_pskl_mono_subst;
          [ exact Hwfp | exact Hwf | exact Hbβ | exact Hτmono ]).
    assert (HwfVsub : {{ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ⨟ empty ⊢ₚₛ
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                           (pskl_var_f α)) }}a).
    { apply a_wf_pskl_mono_subst;
        [ | exact Hwf | exact Hbβ | exact Hτmono ].
      apply a_wf_pskl__var. destruct Hfa as [Hb | [t Hb]];
        [ right; left | right; right; exists t ];
        unfold binds in *; apply in_or_app; right; exact Hb. }
    assert (Hstrip : forall R, β `notin` ftvar_in_ptyp τ ->
              β `notin` ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β R)).
    { intros R _.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper R (ptyp_to_pskl τ) β)
        as Hu.
      rewrite ftvar_ptyp_to_pskl in Hu. clear - Hu Hβτ. fsetdec. }
    assert (HwfPsubC : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) }}a)
      by (eapply a_wf_pskl_strip_mid;
          [ exact HwfPsub | exact (Hstrip P Hβτ) ]).
    assert (HwfVsubC : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                         (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                            (pskl_var_f α)) }}a)
      by (eapply a_wf_pskl_strip_mid;
          [ exact HwfVsub | exact (Hstrip (pskl_var_f α) Hβτ) ]).
    pose proof (@rig_empty (Ξ ++ Θ0)) as HΔtv.
    pose proof (@no_flex_dep_empty (Ξ ++ Θ0)) as Hnfd.
    pose proof (@faf_empty (Ξ ++ Θ0)) as Hfaf.
    assert (HΔsc : empty ∪ empty [<=] ftvar_in_aenv (Ξ ++ Θ0))
      by (clear; fsetdec).
    destruct (IH S0 (Ξ' ++ Θ0'') empty empty
                (subst_pskl_in_pskl (ptyp_to_pskl t2) b P')
                (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α'))
                ρ VC HrΘC HrPsubC HrVsubC HatomsC HatomsC HagrC HinjC HfunC
                HwfC Huq2C Hftv2C ltac:(subst VC; clear; fsetdec) HblkC HdΘC HcovC
                HcovS HcovΔ HwfPsubC HwfVsubC HΔtv Hnfd Hfaf HΔsc)
      as (S1 & ρe & Θ1' & Q' & D2 & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
    assert (Hbnd1 : b `notin` dom Θ1').
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper)) _ _ _ _ _ _ _
                    _ _ D2) as Hup.
      assert (HbS0 : b `in` S0).
      { repeat rewrite dom_app in HdΘ. simpl in HdΘ. clear - HdΘ. fsetdec. }
      clear - Hup Hbnd HbS0. fsetdec. }
    unfold lift_assign_post.
    exists S1, ρe, ((b ~ abind_flex_mono_def t2) ++ Θ1').
    split.
    { apply e_assign__assign with (τ := t2) (Q := Q');
        [ exact Hfa2 | exact D2 ]. }
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros x y Hx. apply in_or_app. right. exact Hx.
      - constructor. unfold rel_ptyp in Hrτ |- *.
        eapply rel_pskl_mono;
          [ exact Hrτ | intros x y Hx; apply in_or_app; right; exact Hx
          | intros x Hx; exact Hx ].
      - eapply rel_aenv_mono;
          [ exact HrΘ1 | intros x y Hx; exact Hx | exact HVC ]. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V β b)
      by (eapply rel_atom_incl;
          [ exact Hab | intros x y Hx; apply in_or_app; right; exact Hx ]).
    assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V β y -> y = b).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hβfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
        | exact HVCsplit
        | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
        | split; intros _; apply a_flex_tvar_head_flexish;
          right; eexists; reflexivity ]. }
    assert (Hftsub : ftvar_in_aenv (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0)
                     [<=] add β (ftvar_in_aenv (Ξ ++ Θ0))).
    { repeat rewrite ftvar_in_aenv_app. simpl.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hτdom Hds. fsetdec. }
    split.
    { eapply rel_ext_add_scope_l; [ exact Hext1 | exact Hftsub | ].
      intros a_new b_new Hin_new Heq_new. destruct (Hdom1 _ _ Hin_new) as [Hd_new _].
      subst a_new; contradiction. }
    intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  - (* Assign-Depend — the entry MOVES into the pending suffix *)
    intros Θ0 Θ1 Ξ α β P Hne Hbin HD IH.
    intros S0 Θ0' Ξ' α' P' ρ V HrΘ HrΞ Hrα HrP Hagr Hinj Hfun Hfl Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Hne2 : α' <> b).
    { intros Ex. apply Hne. rewrite Ex in Hrα. exact (Hinj α β b Hrα Hab). }
    assert (Hβd0 : β `in` dom (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (HbinP : b `in` ftvar_in_pskl P').
    { destruct (rel_pskl_ftv_corr_l HrP Hbin) as (y & Hy & Hat).
      assert (Ey : y = b) by (exact (Hfun β y b Hβd0 Hat Hab)).
      rewrite <- Ey. exact Hy. }
    assert (HrΞ' : rel_aenv ρ V (Ξ ++ (β ~ abind_flex_mono))
                     (Ξ' ++ (b ~ abind_flex_mono))).
    { apply rel_aenv_app; [ exact HrΞ | ].
      apply rel_aenv__cons; [ exact Hab | constructor | constructor ]. }
    assert (Hagr' : flex_agree_rel ρ V ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)
                      ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0''))
      by (simpl_env; exact Hagr).
    assert (Hfun' : rel_fun ρ V (dom ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)))
      by (simpl_env; exact Hfun).
    assert (Hfl' : a_flex_tvar ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) α)
      by (simpl_env; exact Hfl).
    assert (Hwf' : {{ ⊢ ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) }}a)
      by (simpl_env; exact Hwf).
    assert (Huq2' : uniq ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0''))
      by (simpl_env; exact Huq2p).
    assert (Hftv2' : ftvar_in_aenv ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0'')
                     [<=] S0)
      by (simpl_env; exact Hftv2).
    assert (Hdec' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app; [ exact Hdec | apply a_decls_one ]).
    assert (Hdec2' : a_decls (Ξ' ++ (b ~ abind_flex_mono)))
      by (apply a_decls_app; [ exact Hdec2 | apply a_decls_one ]).
    assert (Hscp' : V [<=] ftvar_in_aenv ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0))
      by (simpl_env; exact Hscp).
    assert (Hblk' : forall a0, a0 `in` dom Θ1 ->
              a0 `notin` dom ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) ->
              a0 `notin` cols_l ρ)
      by (intros a0 Ha0 Hn0; apply Hblk;
          [ exact Ha0
          | repeat rewrite dom_app in Hn0 |- *; simpl in Hn0 |- *;
            clear - Hn0; fsetdec ]).
    assert (HdΘ' : dom ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0'') [<=] S0).
    { repeat rewrite dom_app in HdΘ |- *. simpl in HdΘ |- *.
      clear - HdΘ. fsetdec. }
    assert (Hwfp' : {{ ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (simpl_env; exact Hwfp).
    destruct (IH S0 Θ0'' (Ξ' ++ (b ~ abind_flex_mono)) α' P' ρ V
                Hrest HrΞ' Hrα HrP Hagr' Hinj Hfun' Hfl' Hwf' Hdec'
                Hdec2' Huq2' Hftv2' Hscp' Hblk' HdΘ' Hcov HcovP Hwfp')
      as (S1 & ρe & Θ1' & D2 & HrΘ1 & Hagr1 & Hext1 & Hdom1).
    exists S1, ρe, Θ1'.
    split; [ apply e_assign__depend;
             [ exact Hne2 | exact HbinP | exact D2 ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ simpl_env in Hext1; simpl_env; exact Hext1 | exact Hdom1 ].
  - (* Assign-Skip : [lift_assign_skip_head_of_rule] at a FLEXIBLE head *)
    intros Θ0 Θ1 Ξ α β P Hne Hβp Hβd HD IH.
    apply lift_assign_skip_head_of_rule;
      [ intros ρ0 V0 bd2 Hr; inversion Hr; reflexivity
      | simpl; clear; fsetdec
      | intros _ _; exact Hne
      | intros Θ1x Θ1x' b _ _; split; intros _;
        apply a_flex_tvar_head_flexish; left; reflexivity
      | intros; apply e_assign__skip; assumption
      | exact Hβp | exact Hβd | exact HD | exact IH ].
  - (* Assign-SkipRigid : [lift_assign_skip_head_of_rule] at a RIGID head *)
    intros Θ0 Θ1 Ξ α β P Hβp Hβd HD IH.
    apply lift_assign_skip_head_of_rule;
      [ intros ρ0 V0 bd2 Hr; inversion Hr; reflexivity
      | simpl; clear; fsetdec
      | intros Huq1 Hfl Ex; rewrite Ex in Hfl;
        exact (@a_flex_tvar_mid_nonflex_absurd Ξ β abind_tvar Θ0 Huq1
                 ltac:(discriminate) ltac:(intros t; discriminate) Hfl)
      | intros Θ1x Θ1x' b Hd1 Hd2; split; intros Hf; exfalso;
        [ exact (@a_flex_tvar_cons_absent β abind_tvar Θ1x β
                   ltac:(discriminate) ltac:(intros t; discriminate) Hd1 Hf)
        | exact (@a_flex_tvar_cons_absent b abind_tvar Θ1x' b
                   ltac:(discriminate) ltac:(intros t; discriminate) Hd2 Hf) ]
      | intros; apply e_assign__skip_rigid; assumption
      | exact Hβp | exact Hβd | exact HD | exact IH ].
  - (* Assign-SkipTmVar : [lift_assign_skip_tm_of_rule] at a TYPE binding *)
    intros Θ0 Θ1 Ξ α x A P Hxd HD IH.
    apply lift_assign_skip_tm_of_rule;
      [ discriminate | intros t; discriminate
      | intros Hdec Hwf;
        pose proof (a_wf_ptyp_ftv_dom
                      (@a_wf_aenv_mid_var_typ_inv Ξ x A Θ0 Hdec Hwf)) as Hd;
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds;
        rewrite ftvar_in_aenv_app; simpl; clear - Hd Hds; fsetdec
      | intros Γ Hu Hb; exact (@a_binds_tvar_not_var_typ Γ x A Hu Hb)
      | intros ρ0 V0 bd2 Hr; inversion Hr; subst;
        split; [ discriminate | split; [ intros t; discriminate | ] ];
        intros; apply e_assign__skip_tm_var; assumption
      | exact Hxd | exact HD | exact IH ].
  - (* Assign-SkipTmVar (skl) : [lift_assign_skip_tm_of_rule] at a
       SKELETON binding *)
    intros Θ0 Θ1 Ξ α x Q0 P Hxd HD IH.
    apply lift_assign_skip_tm_of_rule;
      [ discriminate | intros t; discriminate
      | intros Hdec Hwf;
        pose proof (a_wf_pskl_ftv_dom
                      (@a_wf_aenv_mid_var_skl_inv Ξ x Q0 Θ0 Hdec Hwf)) as Hd;
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds;
        rewrite ftvar_in_aenv_app; simpl; clear - Hd Hds; fsetdec
      | intros Γ Hu Hb; exact (@a_binds_tvar_not_var_skl Γ x Q0 Hu Hb)
      | intros ρ0 V0 bd2 Hr; inversion Hr; subst;
        split; [ discriminate | split; [ intros t; discriminate | ] ];
        intros; apply e_assign__skip_tm_skl; assumption
      | exact Hxd | exact HD | exact IH ].
  - (* Flex-Flex-Id *)
    intros Θ0 α Hflα.
    intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov.
    assert (Hαd : α `in` dom Θ0) by (exact (a_flex_tvar_in_dom Hflα)).
    assert (Eab : α' = β') by (exact (Hfun α α' β' Hαd Hrα Hrβ)).
    subst β'.
    assert (Hfl2' : a_flex_tvar Θ0' α')
      by (exact (proj1 (flex_agree_rel_use Hagr Hrα) Hflα)).
    exists S0, (@nil (atom * atom)%type), Θ0'.
    split; [ apply e_unify__flex_id; exact Hfl2' | ].
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* Flex-Flex-L *)
    intros Θ0 α β Hne Hflβ.
    intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Hαd : α `in` dom ((α ~ abind_flex_mono) ++ Θ0))
      by (simpl; clear; fsetdec).
    assert (Eb : α' = b) by (exact (Hfun α α' b Hαd Hrα Hab)). subst α'.
    assert (Hne2 : b <> β').
    { intros Ex. apply Hne. rewrite Ex in Hrα.
      exact (Hinj α β β' Hrα Hrβ). }
    assert (Hflβ2 : a_flex_tvar Θ0'' β').
    { assert (Hbig : a_flex_tvar ((α ~ abind_flex_mono) ++ Θ0) β)
        by (apply a_flex_tvar_weaken_app; exact Hflβ).
      apply (proj1 (flex_agree_rel_use Hagr Hrβ)) in Hbig.
      rewrite (@a_flex_tvar_cons_other b abind_flex_mono Θ0'' β'
                 ltac:(intros Ex; apply Hne2; symmetry; exact Ex)) in Hbig.
      exact Hbig. }
    exists S0, (@nil (atom * atom)%type),
      ((b ~ abind_flex_mono_def (ptyp_var_f β')) ++ Θ0'').
    split; [ apply e_unify__flex_l; [ exact Hne2 | exact Hflβ2 ] | ].
    simpl.
    split.
    { apply rel_aenv__cons; [ exact Hab | | exact Hrest ].
      constructor. unfold rel_ptyp. simpl. constructor. exact Hrβ. }
    split.
    { eapply flex_agree_rel_head_swap;
        [ exact Hagr | left; reflexivity | right; eexists; reflexivity
        | left; reflexivity | right; eexists; reflexivity ]. }
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* Flex-Flex-R *)
    intros Θ0 α β Hne Hflα.
    intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Hβd : β `in` dom ((β ~ abind_flex_mono) ++ Θ0))
      by (simpl; clear; fsetdec).
    assert (Eb : β' = b) by (exact (Hfun β β' b Hβd Hrβ Hab)). subst β'.
    assert (Hne2 : α' <> b).
    { intros Ex. apply Hne. rewrite Ex in Hrα.
      exact (Hinj α β b Hrα Hab). }
    assert (Hflα2 : a_flex_tvar Θ0'' α').
    { assert (Hbig : a_flex_tvar ((β ~ abind_flex_mono) ++ Θ0) α)
        by (apply a_flex_tvar_weaken_app; exact Hflα).
      apply (proj1 (flex_agree_rel_use Hagr Hrα)) in Hbig.
      rewrite (@a_flex_tvar_cons_other b abind_flex_mono Θ0'' α' Hne2) in Hbig.
      exact Hbig. }
    exists S0, (@nil (atom * atom)%type),
      ((b ~ abind_flex_mono_def (ptyp_var_f α')) ++ Θ0'').
    split; [ apply e_unify__flex_r; [ exact Hne2 | exact Hflα2 ] | ].
    simpl.
    split.
    { apply rel_aenv__cons; [ exact Hab | | exact Hrest ].
      constructor. unfold rel_ptyp. simpl. constructor. exact Hrα. }
    split.
    { eapply flex_agree_rel_head_swap;
        [ exact Hagr | left; reflexivity | right; eexists; reflexivity
        | left; reflexivity | right; eexists; reflexivity ]. }
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* ⭐ Flex-Flex-Assign — the unify layer's descent into CONSISTENCY *)
    intros Θ0 Θ1 α1 τ α β Q Hflα Hflβ Hα1d HD IH.
    intros S0 Θ0' α' β' ρ V HrΘ Hrα Hrβ Hagr Hinj Hfun Hfl1 Hfl2 Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'.
    inversion Hbd as [ | | t1 t2 Hrτ | A1 A2 HrA | Q1 Q2 HrQ ]; subst.
    assert (Huq1 : uniq ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq ((b ~ abind_flex_mono_def t2) ++ Θ0''))
      by (exact Huq2p).
    assert (HwfC : {{ ⊢ Θ0 }}a)
      by (eapply (@a_wf_aenv_strip_prefix ((α1 ~ abind_flex_mono_def τ)));
          exact Hwf).
    assert (Huq2C : uniq Θ0'') by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv Θ0'' [<=] S0)
      by (simpl in Hftv2; clear - Hftv2; fsetdec).
    assert (Hτdom : ftvar_in_ptyp τ [<=] dom Θ0)
      by (apply a_wf_ptyp_ftv_dom;
          exact (proj1 (@a_wf_aenv_mid_def_inv nil α1 τ Θ0 ltac:(constructor)
                          ltac:(simpl_env; exact Hwf)))).
    assert (Hτ2dom : ftvar_in_ptyp t2 [<=] S0)
      by (simpl in Hftv2; clear - Hftv2; fsetdec).
    assert (Hβnd : α1 `notin` dom Θ0)
      by (clear - Huq1; destruct_uniq; fsetdec).
    assert (Hbnd : b `notin` dom Θ0'')
      by (clear - Huq2; destruct_uniq; fsetdec).
    assert (Hsc : ftvar_in_aenv ((α1 ~ abind_flex_mono_def τ) ++ Θ0)
                  [<=] dom ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (HscC : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hα1d0 : α1 `in` dom ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      by (simpl; clear; fsetdec).
    assert (Hβfun : forall y, rel_atom ρ V α1 y -> y = b)
      by (intros y Hy; exact (Hfun α1 y b Hα1d0 Hy Hab)).
    remember (V ∩ ftvar_in_aenv Θ0) as VC eqn:EVC.
    assert (HVC : VC [<=] V) by (subst VC; clear; fsetdec).
    assert (HVCsplit : forall y, y `in` V -> y <> α1 -> y `in` VC).
    { intros y Hy Hne0. subst VC.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      assert (Hyd : y `in` dom ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
        by (clear - Hy HVdom; fsetdec).
      simpl in Hyd. clear - Hy Hne0 Hyd Hds. fsetdec. }
    assert (HVCne : forall y, y `in` VC -> y <> α1).
    { intros y Hy Ex. rewrite Ex in Hy.
      assert (Hin : α1 `in` ftvar_in_aenv Θ0)
        by (subst VC; clear - Hy; fsetdec).
      clear - Hin HscC Hβnd. fsetdec. }
    assert (HrΘC : rel_aenv ρ VC Θ0 Θ0'').
    { eapply rel_aenv_shrink_V; [ exact Hrest | ].
      intros y Hy Hf. subst VC.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hy Hf Hds. fsetdec. }
    assert (HrPsub : rel_ptyp ρ V (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β))
                       (subst_ptyp_in_ptyp t2 b (ptyp_var_f β'))).
    { apply rel_ptyp_subst;
        [ unfold rel_ptyp; simpl; constructor; exact Hrβ
        | exact Hrτ | exact Hab | exact Hinj | exact Hβfun ]. }
    assert (HrVsub : rel_ptyp ρ V (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))
                       (subst_ptyp_in_ptyp t2 b (ptyp_var_f α'))).
    { apply rel_ptyp_subst;
        [ unfold rel_ptyp; simpl; constructor; exact Hrα
        | exact Hrτ | exact Hab | exact Hinj | exact Hβfun ]. }
    assert (Hshr : forall (y0 : atom) x, x `in` V ->
              x `in` ftvar_in_pskl (ptyp_to_pskl
                        (subst_ptyp_in_ptyp τ α1 (ptyp_var_f y0))) ->
              x `in` VC).
    { intros y0 x Hx Hin.
      rewrite ftvar_ptyp_to_pskl in Hin.
      rewrite ftvar_in_ptyp_subst_ptyp_in_ptyp_upper in Hin.
      destruct (AtomSetProperties.In_dec x (ftvar_in_ptyp τ)) as [Hxτ | Hxτ].
      - subst VC.
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
        clear - Hx Hxτ Hτdom Hds. fsetdec.
      - apply HVCsplit; [ exact Hx | ].
        intros Ex. rewrite Ex in Hin, Hxτ. clear - Hin Hxτ.
        simpl in Hin. fsetdec. }
    assert (HrPsubC : rel_pskl ρ VC
              (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
              (ptyp_to_pskl (subst_ptyp_in_ptyp t2 b (ptyp_var_f β'))))
      by (eapply rel_pskl_shrink_V;
          [ exact HrPsub | intros x Hx Hf; exact (Hshr β x Hx Hf) ]).
    assert (HrVsubC : rel_pskl ρ VC
              (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α)))
              (ptyp_to_pskl (subst_ptyp_in_ptyp t2 b (ptyp_var_f α'))))
      by (eapply rel_pskl_shrink_V;
          [ exact HrVsub | intros x Hx Hf; exact (Hshr α x Hx Hf) ]).
    assert (HatomsC : rel_atoms ρ VC empty empty)
      by (intros y z _; split; intros Hin0; exfalso; clear - Hin0; fsetdec).
    assert (HagrC : flex_agree_rel ρ VC Θ0 Θ0'')
      by (eapply flex_agree_peel_cons;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | exact HVC | exact HVCne ]).
    assert (HinjC : rel_inj ρ VC)
      by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVC ]).
    assert (HfunC : rel_fun ρ VC (dom Θ0)).
    { eapply rel_fun_weaken;
        [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVC ]
        | intros y z Hy; exact Hy
        | simpl; clear; fsetdec ]. }
    assert (HblkC : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom Θ0 ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne0 : a0 <> α1)
          by (intros Ex; rewrite Ex in Ha0; contradiction).
        simpl. clear - Hn0 Hne0. fsetdec. }
    assert (HdΘC : dom Θ0'' [<=] S0)
      by (simpl in HdΘ; clear - HdΘ; fsetdec).
    assert (HcovC : VC ∪ cols_r ρ [<=] S0) by (clear - Hcov HVC; fsetdec).
    assert (Hα'S : α' `in` S0).
    { assert (Hbig : a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) α)
        by exact Hflα.
      apply (proj1 (flex_agree_rel_use Hagr Hrα)) in Hbig.
      pose proof (a_flex_tvar_in_dom Hbig) as Hin.
      simpl in HdΘ, Hin. clear - Hin HdΘ. fsetdec. }
    assert (Hβ'S : β' `in` S0).
    { assert (Hbig : a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β)
        by exact Hflβ.
      apply (proj1 (flex_agree_rel_use Hagr Hrβ)) in Hbig.
      pose proof (a_flex_tvar_in_dom Hbig) as Hin.
      simpl in HdΘ, Hin. clear - Hin HdΘ. fsetdec. }
    assert (HcovS : ftvar_in_pskl (ptyp_to_pskl
                      (subst_ptyp_in_ptyp t2 b (ptyp_var_f β')))
                    ∪ ftvar_in_pskl (ptyp_to_pskl
                      (subst_ptyp_in_ptyp t2 b (ptyp_var_f α'))) [<=] S0).
    { repeat rewrite ftvar_ptyp_to_pskl.
      repeat rewrite ftvar_in_ptyp_subst_ptyp_in_ptyp_upper.
      simpl. simpl in HdΘ.
      clear - Hτ2dom HdΘ Hα'S Hβ'S. fsetdec. }
    assert (HcovΔ : empty ∪ empty [<=] S0) by (clear; fsetdec).
    (* ---- the wf package the consis premise wants ---- *)
    assert (Hbα1 : binds α1 (abind_flex_mono_def τ)
                     ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      by (unfold binds; simpl; left; reflexivity).
    assert (Hτmono : mono_ptyp τ)
      by (exact (@a_wf_aenv_binds_def_mono _ α1 τ Hwf Hbα1)).
    assert (Hτwf : a_wf_ptyp Θ0 τ)
      by (exact (proj1 (@a_wf_aenv_mid_def_inv nil α1 τ Θ0
                          ltac:(constructor) ltac:(simpl_env; exact Hwf)))).
    assert (Hbt : forall y, a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) y ->
                  y <> α1 -> a_binds_tvar y Θ0).
    { intros y Hy Hne0.
      rewrite (@a_flex_tvar_cons_other α1 (abind_flex_mono_def τ) Θ0 y Hne0)
        in Hy.
      destruct Hy as [Hb0 | [t Hb0]];
        [ right; left | right; right; exists t ]; exact Hb0. }
    assert (Hwfsub : forall y,
              a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) y ->
              {{ Θ0 ⨟ empty ⊢ₚₛ
                 (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f y))) }}a).
    { intros y Hy. simpl.
      match goal with
      | |- context [ if ?X then _ else _ ] => destruct X as [Eyα | Hne0]
      end.
      - apply a_wf_pskl_mono_ptyp; [ exact Hτmono | exact Hτwf ].
      - apply a_wf_pskl__var. exact (Hbt y Hy Hne0). }
    pose proof (@rig_empty Θ0) as HΔtv.
    pose proof (@no_flex_dep_empty Θ0) as Hnfd.
    pose proof (@faf_empty Θ0) as Hfaf.
    assert (HΔsc : empty ∪ empty [<=] ftvar_in_aenv Θ0) by (clear; fsetdec).
    destruct (IH S0 Θ0'' empty empty
                (ptyp_to_pskl (subst_ptyp_in_ptyp t2 b (ptyp_var_f β')))
                (ptyp_to_pskl (subst_ptyp_in_ptyp t2 b (ptyp_var_f α')))
                ρ VC HrΘC HrPsubC HrVsubC HatomsC HatomsC HagrC HinjC HfunC
                HwfC Huq2C Hftv2C ltac:(subst VC; clear; fsetdec) HblkC HdΘC HcovC
                HcovS HcovΔ (Hwfsub β Hflβ) (Hwfsub α Hflα) HΔtv Hnfd Hfaf
                HΔsc)
      as (S1 & ρe & Θ1' & Q' & D2 & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
    assert (Hbnd1 : b `notin` dom Θ1').
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper)) _ _ _ _ _ _ _
                    _ _ D2) as Hup.
      assert (HbS0 : b `in` S0) by (simpl in HdΘ; clear - HdΘ; fsetdec).
      clear - Hup Hbnd HbS0. fsetdec. }
    exists S1, ρe, ((b ~ abind_flex_mono_def t2) ++ Θ1').
    split.
    { apply e_unify__flex_assign with (τ := t2) (Q := Q');
        [ | | exact D2 ].
      - assert (Hbig : a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) α)
          by exact Hflα.
        exact (proj1 (flex_agree_rel_use Hagr Hrα) Hbig).
      - assert (Hbig : a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β)
          by exact Hflβ.
        exact (proj1 (flex_agree_rel_use Hagr Hrβ) Hbig). }
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros y z Hy. apply in_or_app. right. exact Hy.
      - constructor. unfold rel_ptyp in Hrτ |- *.
        eapply rel_pskl_mono;
          [ exact Hrτ | intros y z Hy; apply in_or_app; right; exact Hy
          | intros y Hy; exact Hy ].
      - eapply rel_aenv_mono;
          [ exact HrΘ1 | intros y z Hy; exact Hy | exact HVC ]. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V α1 b)
      by (eapply rel_atom_incl;
          [ exact Hab | intros y z Hy; apply in_or_app; right; exact Hy ]).
    assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V α1 y -> y = b).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hβfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
        | exact HVCsplit
        | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
        | split; intros _; apply a_flex_tvar_head_flexish;
          right; eexists; reflexivity ]. }
    assert (Hftsub : ftvar_in_aenv ((α1 ~ abind_flex_mono_def τ) ++ Θ0)
                     [<=] add α1 (ftvar_in_aenv Θ0)).
    { simpl. pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hτdom Hds. fsetdec. }
    split.
    { eapply rel_ext_add_scope_l; [ exact Hext1 | exact Hftsub | ].
      intros a_new b_new Hin_new Heq_new. destruct (Hdom1 _ _ Hin_new) as [Hd_new _].
      subst a_new; contradiction. }
    intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; simpl; [ clear - Hd1; fsetdec | clear - Hd2; fsetdec ].
  - (* Flex-Flex-Skip : [lift_unify_skip_head_of_rule] at a FLEXIBLE head *)
    intros Θ0 Θ1 c α β Hneα0 Hneβ0 Hcd HD IH.
    apply lift_unify_skip_head_of_rule; [ | | exact Hcd | exact HD | exact IH ].
    + intros _ _ _.
      split; intros Ex; [ apply Hneα0 | apply Hneβ0 ]; symmetry; exact Ex.
    + intros ρ0 V0 bdd Hbd. inversion Hbd; subst. split.
      * intros Θ1x Θ1x' b0 _ _.
        split; intros _; apply a_flex_tvar_head_flexish; left; reflexivity.
      * intros S0x S1x Θ0x Θ1x αx βx b0 Hna Hnb D.
        apply e_unify__flex_skip;
          [ intros Ex; apply Hna; symmetry; exact Ex
          | intros Ex; apply Hnb; symmetry; exact Ex | exact D ].
  - (* Flex-Flex-Skip' : [lift_unify_skip_head_of_rule] at a rigid or
       term head *)
    intros Θ0 Θ1 c bc α β Hshape Hcd HD IH.
    assert (Hnf : bc <> abind_flex_mono
                  /\ (forall t, bc <> abind_flex_mono_def t)).
    { destruct Hshape as [-> | [[A0 ->] | [Q0 ->]]]; split;
        solve [ discriminate | intros t; discriminate ]. }
    destruct Hnf as [Hnf1 Hnf2].
    apply lift_unify_skip_head_of_rule; [ | | exact Hcd | exact HD | exact IH ].
    + intros Hcnd Hfl1 Hfl2.
      split; intros Ex; [ rewrite Ex in Hfl1 | rewrite Ex in Hfl2 ].
      * exact (@a_flex_tvar_cons_absent c bc Θ0 c Hnf1 Hnf2 Hcnd Hfl1).
      * exact (@a_flex_tvar_cons_absent c bc Θ0 c Hnf1 Hnf2 Hcnd Hfl2).
    + intros ρ0 V0 bdd Hbd.
      assert (Hshape2 : bdd = abind_tvar
                        \/ (exists A, bdd = abind_var_typ A)
                        \/ (exists Q, bdd = abind_var_skl Q)).
      { destruct Hshape as [E | [[A0 E] | [Q0 E]]]; rewrite E in Hbd;
          inversion Hbd; subst;
          [ left; reflexivity | right; left; eexists; reflexivity
          | right; right; eexists; reflexivity ]. }
      assert (Hnf2' : bdd <> abind_flex_mono
                      /\ (forall t, bdd <> abind_flex_mono_def t)).
      { destruct Hshape2 as [-> | [[A0 ->] | [Q0 ->]]]; split;
          solve [ discriminate | intros t; discriminate ]. }
      destruct Hnf2' as [Hnf1b Hnf2b].
      split.
      * intros Θ1x Θ1x' b0 Hd1 Hd2. split; intros Hf; exfalso.
        -- exact (@a_flex_tvar_cons_absent c bc Θ1x c Hnf1 Hnf2 Hd1 Hf).
        -- exact (@a_flex_tvar_cons_absent b0 bdd Θ1x' b0 Hnf1b Hnf2b Hd2 Hf).
      * intros S0x S1x Θ0x Θ1x αx βx b0 _ _ D.
        apply e_unify__skip_other; [ exact Hshape2 | exact D ].
  - (* C-Ghost *)
    intros Δ1 Δ2 Θ0 P0 Hdisj.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', P0'.
    split.
    { apply e_consis__ghost.
      eapply rel_atoms_disjoint; [ exact Hrd2 | exact HrP0 | exact Hdisj ]. }
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ exact HrP0 | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* C-Unit *)
    intros Δ1 Δ2 Θ0.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP; subst. inversion HrP0; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', pskl_unit.
    split; [ apply e_consis__unit | ].
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ constructor | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b0 Hin. inversion Hin.
  - (* C-Rigid *)
    intros Δ1 Δ2 Θ0 α Hb.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP as [ | n0 | x0 a2 Hat2 | | | | ]; subst.
    inversion HrP0 as [ | n1 | x1 a1 Hat1 | | | | ]; subst.
    assert (Hαd : α `in` dom Θ0) by (eapply binds_In; exact Hb).
    assert (Ea : a1 = a2) by (exact (Hfun α a1 a2 Hαd Hat1 Hat2)). subst a1.
    destruct (@rel_aenv_binds_l ρ V Θ0 Θ0' α abind_tvar HrΘ Hb)
      as (b0 & b2 & Hat0 & Hab0 & Hbd0).
    assert (Eb : b0 = a2) by (exact (Hfun α b0 a2 Hαd Hat0 Hat2)). subst b0.
    inversion Hab0; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', (pskl_var_f a2).
    split; [ apply e_consis__rigid; exact Hbd0 | ].
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ constructor; exact Hat2 | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b1 Hin. inversion Hin.
  - (* ⭐ U-Arrow — the second half runs at the FIRST half's output, so
       everything the motive says about the context is re-established there *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 HD1 IH1 HD2 IH2.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 P0a2 P0b2 HrP0a HrP0b
                      | A3 A4 Hu1 | | A5 A6 Hu2 ]; subst.
    inversion HrP as [ | n1 | u3 v3 Hu3 | B1 B2 P12 P22 HrP1 HrP2
                     | B3 B4 Hu4 | | B5 B6 Hu5 ]; subst.
    inversion Hwfp0 as [ Θx Δx | Θx Δx αx Hbx | Θx Δx Xa Xb Hw0a Hw0b
                       | Lx Θx Δx Xp Hallx | Θx Δx
                       | Θx Δx Xp Hgx Hwix ]; subst.
    inversion Hwfp as [ Θy Δy | Θy Δy αy Hby | Θy Δy Ya Yb Hw1a Hw1b
                      | Ly Θy Δy Yp Hally | Θy Δy
                      | Θy Δy Yp Hgy Hwiy ]; subst.
    assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hdm0 : dom Θ0 [<=] dom Θ1) by (exact (auc_dom_mono_consis HD1)).
    assert (Hdm1 : dom Θ1 [<=] dom Θ2) by (exact (auc_dom_mono_consis HD2)).
    (* ---- the first premise ---- *)
    assert (Hblk1 : forall a, a `in` dom Θ1 -> a `notin` dom Θ0 ->
                    a `notin` cols_l ρ).
    { intros a Ha Hn. apply Hblk; [ clear - Ha Hdm1; fsetdec | exact Hn ]. }
    assert (HcovP1 : ftvar_in_pskl P0a2 ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    destruct (IH1 S0 Θ0' Δ1' Δ2' P0a2 P12 ρ V HrΘ HrP0a HrP1 Hrd1 Hrd2 Hagr
                Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk1 HdΘ Hcov HcovP1 HcovΔ
                Hw0a Hw1a HΔtv Hnfd Hfaf HΔsc)
      as (S1 & ρe1 & Θ1' & Q1' & D1e & HrΘ1 & Hagr1 & HrQ1 & Hext1 & Hdom1).
    pose proof (e_consis_supply_grows D1e) as Hgr1.
    (* ---- side 2's context, re-established at the first half's output ---- *)
    assert (HdΘ1 : dom Θ1' [<=] S1).
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ _ _ _ D1e) as Hup.
      clear - Hup HdΘ Hgr1. fsetdec. }
    assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl P0a2
                    ∪ ftvar_in_pskl P12 [<=] S0)
      by (clear - Hftv2 HcovP1; fsetdec).
    assert (Hftv1 : ftvar_in_aenv Θ1' [<=] S1)
      by (eapply (proj2 (proj2 e_assign_unify_consis_ctx_ftvar));
          [ exact D1e | exact HcovE ]).
    assert (HcovE2 : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl P0a2
                     ∪ ftvar_in_pskl P12 ∪ Δ1' ∪ Δ2' [<=] S0)
      by (clear - HcovE HcovΔ; fsetdec).
    assert (Huq1' : uniq Θ1').
    { pose proof (e_consis_sound D1e Huq2p HcovE2) as Ha1.
      exact ((proj2 (proj2 a_assign_unify_consis_uniq)) _ _ _ _ _ _ _ Ha1
               Huq2p). }
    (* ---- side 1's context, via SOUNDNESS ---- *)
    pose proof ((proj2 (proj2 a_assign_unify_consis_sound)) _ _ _ _ _ _ _ HD1
                  Hwf Hw0a Hw1a HΔtv Hnfd Hfaf) as Hsnd1.
    destruct Hsnd1 as (Hinc1 & HwfΘ1 & Hdm1' & HΔinv1 & Hrest1).
    assert (HΔdom : Δ1 ∪ Δ2 [<=] dom Θ0) by (clear - HΔsc Hsc0; fsetdec).
    assert (Hside1 : (Δ1 ∪ Δ2) ∩ dom Θ1 [<=] dom Θ0)
      by (clear - HΔdom; fsetdec).
    assert (Hside2 : forall α, α `in` (Δ1 ∪ Δ2) -> α `notin` dom Θ0 ->
              α `notin` (ftvar_in_pskl P0a `union` ftvar_in_pskl P1))
      by (intros α Hα Hn; exfalso; clear - HΔdom Hα Hn; fsetdec).
    destruct (HΔinv1 (Δ1 ∪ Δ2) Hnfd Hfaf Hside1 Hside2)
      as (Hnfd1 & Hfaf1 & Hdlt1).
    assert (HΔtv1 : forall α, α `in` (Δ1 ∪ Δ2) -> binds α abind_tvar Θ1).
    { intros α Hα. destruct Hinc1 as [[κ [Hid Hinc]] _].
      eapply a_inc_binds_tvar; [ exact Hinc | exact (HΔtv α Hα) ]. }
    assert (Hd1s : dom Θ1 [<=] ftvar_in_aenv Θ1)
      by (apply dom_subset_ftvar_in_aenv).
    assert (HΔsc1 : Δ1 ∪ Δ2 [<=] ftvar_in_aenv Θ1)
      by (clear - HΔdom Hdm0 Hd1s; fsetdec).
    assert (Hscp1 : V [<=] ftvar_in_aenv Θ1)
      by (clear - Hscp Hsc0 Hdm0 Hd1s; fsetdec).
    assert (Hwfp0b1 : {{ Θ1 ⨟ empty ⊢ₚₛ P0b }}a)
      by (eapply a_isub_wf_pskl; [ exact Hinc1 | exact Hw0b ]).
    assert (Hwfp21 : {{ Θ1 ⨟ empty ⊢ₚₛ P2 }}a)
      by (eapply a_isub_wf_pskl; [ exact Hinc1 | exact Hw1b ]).
    (* ---- the relation, widened by the first half's new pairs ---- *)
    assert (Hinj1 : rel_inj (ρe1 ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (HVdom0 : V [<=] dom Θ0) by (clear - Hscp Hsc0; fsetdec).
    assert (Hfun1 : rel_fun (ρe1 ++ ρ) V (dom Θ1)).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hext1 | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; exact (Hblk1 a Ha Hn)
        | intros a Ha Hn; clear - HVdom0 Hn; fsetdec ]. }
    assert (Hrd1' : rel_atoms (ρe1 ++ ρ) V Δ1 Δ1')
      by (eapply rel_atoms_app;
          [ exact Hrd1 | exact Hext1 | clear - HΔsc; fsetdec
          | clear - HcovΔ; fsetdec ]).
    assert (Hrd2' : rel_atoms (ρe1 ++ ρ) V Δ2 Δ2')
      by (eapply rel_atoms_app;
          [ exact Hrd2 | exact Hext1 | clear - HΔsc; fsetdec
          | clear - HcovΔ; fsetdec ]).
    assert (HrP0b' : rel_pskl (ρe1 ++ ρ) V P0b P0b2)
      by (apply rel_pskl_widen; exact HrP0b).
    assert (HrP2' : rel_pskl (ρe1 ++ ρ) V P2 P22)
      by (apply rel_pskl_widen; exact HrP2).
    assert (Hc1r : cols_r ρe1 [<=] S1).
    { intros y Hy. destruct (cols_r_in_inv _ _ Hy) as (a & Hin).
      destruct (Hdom1 _ _ Hin) as [_ Hd2]. clear - Hd2 HdΘ1. fsetdec. }
    assert (Hcov1 : V ∪ cols_r (ρe1 ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hcov Hc1r Hgr1. fsetdec. }
    assert (Hblk2 : forall a, a `in` dom Θ2 -> a `notin` dom Θ1 ->
                    a `notin` cols_l (ρe1 ++ ρ)).
    { intros a Ha Hn. rewrite cols_l_app.
      assert (Hc1 : a `notin` cols_l ρe1).
      { intros Hy. destruct (cols_l_in_inv _ _ Hy) as (y & Hin).
        destruct (Hdom1 _ _ Hin) as [Hd1 _]. contradiction. }
      assert (Hc2 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn Hdm0; fsetdec ]).
      clear - Hc1 Hc2. fsetdec. }
    assert (HcovP2 : ftvar_in_pskl P0b2 ∪ ftvar_in_pskl P22 [<=] S1)
      by (simpl in HcovP; clear - HcovP Hgr1; fsetdec).
    assert (HcovΔ1 : Δ1' ∪ Δ2' [<=] S1) by (clear - HcovΔ Hgr1; fsetdec).
    destruct (IH2 S1 Θ1' Δ1' Δ2' P0b2 P22 (ρe1 ++ ρ) V HrΘ1 HrP0b' HrP2'
                Hrd1' Hrd2' Hagr1 Hinj1 Hfun1 HwfΘ1 Huq1' Hftv1 Hscp1 Hblk2
                HdΘ1 Hcov1 HcovP2 HcovΔ1 Hwfp0b1 Hwfp21 HΔtv1 Hnfd1 Hfaf1
                HΔsc1)
      as (S2 & ρe2 & Θ2' & Q2' & D2e & HrΘ2 & Hagr2 & HrQ2 & Hext2 & Hdom2).
    exists S2, (ρe2 ++ ρe1), Θ2', (pskl_arrow Q1' Q2').
    split; [ eapply e_consis__arrow; [ exact D1e | exact D2e ] | ].
    rewrite app_assoc.
    split; [ exact HrΘ2 | ].
    split; [ exact Hagr2 | ].
    split.
    { constructor; [ | exact HrQ2 ].
      eapply rel_pskl_mono;
        [ exact HrQ1 | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    assert (Hsc1 : ftvar_in_aenv Θ1 [<=] dom Θ1)
      by (apply a_wf_aenv_ftv_dom; exact HwfΘ1).
    split.
    { eapply rel_ext_app;
        [ exact Hext1 | exact Hext2
        | clear - Hsc0 Hdm0 Hd1s; fsetdec
        | exact Hgr1
        | intros a b Hin; destruct (Hdom1 _ _ Hin) as [Hd1 Hd2];
          split; [ clear - Hd1 Hd1s; fsetdec | clear - Hd2 HdΘ1; fsetdec ] ]. }
    assert (Hdm2' : dom Θ1' [<=] dom Θ2').
    { pose proof (e_consis_sound D2e Huq1'
                    ltac:(clear - Hftv1 HcovP2 HcovΔ1; fsetdec)) as Ha2.
      exact (auc_dom_mono_consis Ha2). }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hdom2 _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; [ clear - Hd1 Hdm1; fsetdec | clear - Hd2 Hdm2'; fsetdec ].
  - (* ⭐⭐ C-ForallInh *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
    eapply lift_consis_forall_inh_row; [ exact Hfr | exact HD | exact IH ].
  - (* ⭐⭐ C-ForallSyn *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
    eapply lift_consis_forall_syn_row; [ exact Hfr | exact HD | exact IH ].
  - (* C-UnivGhost : ⫯ on all three positions, and the IH strips it *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q HD IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 P0b2 HrP0b ]; subst.
    inversion HrP as [ | n1 | u3 v3 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 P12 HrPb ]; subst.
    assert (HcovP1 : ftvar_in_pskl P0b2 ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hwfp01 : {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a)
      by (inversion Hwfp0; subst; rewrite aenv_minus_empty in *; assumption).
    assert (Hwfp1 : {{ Θ0 ⨟ empty ⊢ₚₛ P }}a)
      by (inversion Hwfp; subst; rewrite aenv_minus_empty in *; assumption).
    destruct (IH S0 Θ0' Δ1' Δ2' P0b2 P12 ρ V
                HrΘ HrP0b HrPb Hrd1 Hrd2 Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov
                HcovP1 HcovΔ Hwfp01 Hwfp1 HΔtv Hnfd Hfaf HΔsc)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', (pskl_univ_ghost Q').
    split; [ apply e_consis__univ_ghost; exact De | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ apply rel_pskl__univ_ghost; exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* ⭐⭐ C-UnivGhost1 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr HD IH.
    eapply lift_consis_univ_ghost1_row; [ exact Hfr | exact HD | exact IH ].
  - (* C-UnivGhost2 : the ⫯ is stripped off the SUBJECT only *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf HD IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP as [ | n1 | u3 v3 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 P12 HrPb ]; subst.
    assert (HcovP1 : ftvar_in_pskl P0' ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hwfp1 : {{ Θ0 ⨟ empty ⊢ₚₛ P }}a)
      by (inversion Hwfp; subst; rewrite aenv_minus_empty in *; assumption).
    destruct (IH S0 Θ0' Δ1' Δ2' P0' P12 ρ V
                HrΘ HrP0 HrPb Hrd1 Hrd2 Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov
                HcovP1 HcovΔ Hwfp0 Hwfp1 HΔtv Hnfd Hfaf HΔsc)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split.
    { apply e_consis__univ_ghost2;
        [ eapply rel_pskl_guarded; [ exact HrP0 | exact Hg ]
        | eapply rel_pskl_non_flex; [ exact HrP0 | exact Hagr | exact Hnf ]
        | exact De ]. }
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* C-Flex : hand to the UNIFY IH *)
    intros Δ1 Δ2 Θ0 Θ1 α β HU IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 β2 Hatβ | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 C2 Hu4 ]; subst.
    inversion HrP as [ | n1 | u1 α2 Hatα | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 F2 Hu8 ]; subst.
    destruct ((proj1 (proj2 a_assign_unify_subject_flex)) _ _ _ _ HU)
      as [Hflα Hflβ].
    destruct (IH S0 Θ0' α2 β2 ρ V HrΘ Hatα Hatβ Hagr Hinj Hfun Hflα Hflβ Hwf
                Huq2p Hftv2 Hscp Hblk HdΘ Hcov)
      as (S1 & ρe & Θ1' & De & HrΘ1 & Hagr1 & Hext & Hdom1).
    exists S1, ρe, Θ1', (pskl_var_f α2).
    split; [ apply e_consis__flex; exact De | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrP | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    split; [ exact Hext | ]. exact Hdom1.
  - (* C-FlexL : hand to the ASSIGN IH at Ξ = nil *)
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hnhole HA IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP as [ | n1 | u1 α2 Hatα | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 F2 Hu8 ]; subst.
    assert (Hflα : a_flex_tvar (nil ++ Θ0) α)
      by (exact ((proj1 a_assign_unify_subject_flex) _ _ _ _ _ HA)).
    assert (HcovP0 : ftvar_in_pskl P0' [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (HagrN : flex_agree_rel ρ V (nil ++ Θ0) (nil ++ Θ0'))
      by (simpl_env; exact Hagr).
    assert (HfunN : rel_fun ρ V (dom (nil ++ Θ0))) by (simpl_env; exact Hfun).
    assert (HwfN : {{ ⊢ (nil ++ Θ0) }}a) by (simpl_env; exact Hwf).
    assert (HuqN : uniq (nil ++ Θ0')) by (simpl_env; exact Huq2p).
    assert (HftvN : ftvar_in_aenv (nil ++ Θ0') [<=] S0)
      by (simpl_env; exact Hftv2).
    assert (HscpN : V [<=] ftvar_in_aenv (nil ++ Θ0))
      by (simpl_env; exact Hscp).
    assert (HblkN : forall a, a `in` dom Θ1 -> a `notin` dom (nil ++ Θ0) ->
                    a `notin` cols_l ρ) by (simpl_env; exact Hblk).
    assert (HdΘN : dom (nil ++ Θ0') [<=] S0) by (simpl_env; exact HdΘ).
    assert (HwfpN : {{ (nil ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (simpl_env; exact Hwfp0).
    destruct (IH S0 Θ0' nil α2 P0' ρ V HrΘ (@rel_aenv__nil ρ V) Hatα HrP0
                HagrN Hinj HfunN Hflα HwfN a_decls__nil a_decls__nil HuqN
                HftvN HscpN HblkN HdΘN Hcov HcovP0 HwfpN)
      as (S1 & ρe & Θ1' & De & HrΘ1 & Hagr1 & Hext & Hdom1).
    exists S1, ρe, Θ1', (pskl_var_f α2).
    split; [ apply e_consis__flex_l;
             [ eapply rel_pskl_non_flex; [ exact HrP0 | exact Hagr | exact Hnf ]
             | intros Ehole; subst; inversion HrP0; subst; contradiction
             | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrP | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    split; [ simpl_env in Hext; exact Hext | ]. exact Hdom1.
  - (* C-FlexR : the same, with the SUBJECT assigned *)
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hnhole HA IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 α2 Hatα | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 C2 Hu4 ]; subst.
    assert (Hflα : a_flex_tvar (nil ++ Θ0) α)
      by (exact ((proj1 a_assign_unify_subject_flex) _ _ _ _ _ HA)).
    assert (HcovP1 : ftvar_in_pskl P' [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (HagrN : flex_agree_rel ρ V (nil ++ Θ0) (nil ++ Θ0'))
      by (simpl_env; exact Hagr).
    assert (HfunN : rel_fun ρ V (dom (nil ++ Θ0))) by (simpl_env; exact Hfun).
    assert (HwfN : {{ ⊢ (nil ++ Θ0) }}a) by (simpl_env; exact Hwf).
    assert (HuqN : uniq (nil ++ Θ0')) by (simpl_env; exact Huq2p).
    assert (HftvN : ftvar_in_aenv (nil ++ Θ0') [<=] S0)
      by (simpl_env; exact Hftv2).
    assert (HscpN : V [<=] ftvar_in_aenv (nil ++ Θ0))
      by (simpl_env; exact Hscp).
    assert (HblkN : forall a, a `in` dom Θ1 -> a `notin` dom (nil ++ Θ0) ->
                    a `notin` cols_l ρ) by (simpl_env; exact Hblk).
    assert (HdΘN : dom (nil ++ Θ0') [<=] S0) by (simpl_env; exact HdΘ).
    assert (HwfpN : {{ (nil ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (simpl_env; exact Hwfp).
    destruct (IH S0 Θ0' nil α2 P' ρ V HrΘ (@rel_aenv__nil ρ V) Hatα HrP
                HagrN Hinj HfunN Hflα HwfN a_decls__nil a_decls__nil HuqN
                HftvN HscpN HblkN HdΘN Hcov HcovP1 HwfpN)
      as (S1 & ρe & Θ1' & De & HrΘ1 & Hagr1 & Hext & Hdom1).
    exists S1, ρe, Θ1', (pskl_var_f α2).
    split; [ apply e_consis__flex_r;
             [ eapply rel_pskl_non_flex; [ exact HrP | exact Hagr | exact Hnf ]
             | intros Ehole; subst; inversion HrP; subst; contradiction
             | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrP0 | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    split; [ simpl_env in Hext; exact Hext | ]. exact Hdom1.
  - (* C-GhostR : identity, and the Δ₁-disjointness TRANSPORTS *)
    intros Δ1 Δ2 Θ0 P Hdisj.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 C2 Hu4 ]; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', P'.
    split.
    { apply e_consis__ghost_r.
      eapply rel_atoms_disjoint; [ exact Hrd1 | exact HrP | exact Hdisj ]. }
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ exact HrP | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* C-UnivGhostR : the ⫯ is stripped off the COUNTERPART only *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf HD IH.
    intros S0 Θ0' Δ1' Δ2' P0' P' ρ V HrΘ HrP0 HrP Hrd1 Hrd2 Hagr Hinj Hfun
      Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP HcovΔ Hwfp0 Hwfp HΔtv Hnfd
      Hfaf HΔsc.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 P0b2 HrP0b ]; subst.
    assert (HcovP1 : ftvar_in_pskl P0b2 ∪ ftvar_in_pskl P' [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hwfp01 : {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a)
      by (inversion Hwfp0; subst; rewrite aenv_minus_empty in *; assumption).
    destruct (IH S0 Θ0' Δ1' Δ2' P0b2 P' ρ V
                HrΘ HrP0b HrP Hrd1 Hrd2 Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov
                HcovP1 HcovΔ Hwfp01 Hwfp HΔtv Hnfd Hfaf HΔsc)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split.
    { apply e_consis__univ_ghost_r;
        [ eapply rel_pskl_guarded; [ exact HrP | exact Hg ]
        | eapply rel_pskl_non_flex; [ exact HrP | exact Hagr | exact Hnf ]
        | exact De ]. }
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
Qed.
