(** SOUNDNESS OF SKELETON INFERENCE — section D, thm:sound-skeleton-inference
    (paper proofs.tex, app:proof-skeleton-inference).

    An [a_pat] run yields a solution to its skeleton inference problem: the
    output context is an information increase of the input, and in it the
    DECLARATIVE judgement [ad_pat] holds at a colouring of the output, which
    refines the (inherited painting of the) input skeleton.  Mirrors
    [a_sub_sound] (prop_decorate_key.v), which it consumes at the three
    base rules; [a_consis_sound] (prop_soundness_consis.v) covers AbsAnno.

    ⭐ WHAT THE PAPER'S PROOF LEAVES TO THE MECHANIZATION:

    1. "Stability" (proofs.tex:19-26) is NOT free: [⊴] preserves a term
       entry only up to [≡ᵗ] ([a_inc__var]), so transporting [ad_pat] along
       the runs' increases uses the tm-verbatim invariant of
       prop_stability.v ([a_pat_tm_le] and friends) — the algorithm never
       rewrites a term entry, which the paper leaves implicit.
    2. The Abs cases need NO refinement transitivity and NO split-refines:
       under the judgement's own [skmod{SK}] side condition the split is
       the ARROW or HOLE row (the flex row needs a flexible input skeleton,
       which [a_sk_mode_compat] has no rule for — that row is reachable
       only from TYPE inference).  At the arrow shape the composed
       refinement is one [__arrow] of a reflexivity and the IH; at the hole
       shape it is one [__hole] over the IH's syn-painting inversion.
       This sidesteps the wf side conditions [ad_refine_syn_trans] would
       demand of the composed result (refinement does NOT preserve wf —
       cex/cex_refine_not_transitive.v — so those conditions are not
       derivable from the pieces).

    [a_wf_exp] renders the problem definition's "M is well-formed in Θ0"
    (algorithmic.tex, Definition problems-and-solutions): annotations are
    well-formed types.  Term-variable OCCURRENCES need no condition — the
    run's own [binds] premises supply them. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_typing.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.prop_ctx_mono.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.sub.prop_soundness_sub.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.sub.prop_completeness_sub_gen.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.sub.prop_looksub.
Require Import src.frost.algo.prop_wf_preservation.
Require Import src.frost.decorated_algo.prop_decorate.
Require Import src.frost.decorated_algo.prop_decorate_key.

Set Implicit Arguments.

(* the judgement notation below lives in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope frost_a_scope.

(* ===================================================================== *)
(*  §1  Term well-formedness (the problem definition's "M wf in Θ")       *)
(* ===================================================================== *)

Reserved Notation "{{ Θ ⊢ᵉ e }}a"
  (at level 0, e at level 74, format "'{{'  Θ  ⊢ᵉ  e  '}}a'").

Inductive a_wf_exp : aenv -> exp -> Prop :=
| a_wf_exp__unit : forall Θ,
    {{ Θ ⊢ᵉ exp_unit }}a
| a_wf_exp__var : forall Θ x,
    {{ Θ ⊢ᵉ (exp_var_f x) }}a
| a_wf_exp__anno : forall Θ e A,
    a_wf_ptyp Θ A ->
    {{ Θ ⊢ᵉ e }}a ->
    {{ Θ ⊢ᵉ (exp_anno e A) }}a
| a_wf_exp__freeze : forall Θ e,
    {{ Θ ⊢ᵉ e }}a ->
    {{ Θ ⊢ᵉ (exp_freeze e) }}a
| a_wf_exp__abs : forall L Θ e,
    (forall x, x `notin` L ->
       {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a) ->
    {{ Θ ⊢ᵉ (exp_abs e) }}a
| a_wf_exp__abs_anno : forall L Θ A e,
    a_wf_ptyp Θ A ->
    (forall x, x `notin` L ->
       {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a) ->
    {{ Θ ⊢ᵉ (exp_abs_anno A e) }}a
| a_wf_exp__app : forall Θ e1 e2,
    {{ Θ ⊢ᵉ e1 }}a ->
    {{ Θ ⊢ᵉ e2 }}a ->
    {{ Θ ⊢ᵉ (exp_app e1 e2) }}a
where "{{ Θ ⊢ᵉ e }}a" := (a_wf_exp Θ e) : frost_a_scope.

(** Only type-level entries are read (through [a_wf_ptyp]), so the term
    judgement transports along the term-blind relation — weakening by any
    entry and dropping term entries are both instances. *)
Lemma a_wf_exp_mono : forall Θ e,
  {{ Θ ⊢ᵉ e }}a ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Θ' ⊢ᵉ e }}a.
Proof.
  intros Θ e H; induction H; intros Θ' Hle.
  - apply a_wf_exp__unit.
  - apply a_wf_exp__var.
  - apply a_wf_exp__anno; [ eapply a_wf_ptyp_mono; eauto | auto ].
  - apply a_wf_exp__freeze; auto.
  - apply a_wf_exp__abs with (L := L). intros x Hx. auto.
  - apply a_wf_exp__abs_anno with (L := L);
      [ eapply a_wf_ptyp_mono; eauto | intros x Hx; auto ].
  - apply a_wf_exp__app; auto.
Qed.

Lemma a_wf_exp_isub : forall Θ e,
  {{ Θ ⊢ᵉ e }}a ->
  forall Θ', Θ ⊴ Θ' -> {{ Θ' ⊢ᵉ e }}a.
Proof.
  intros Θ e H; induction H; intros Θ' Hle.
  - apply a_wf_exp__unit.
  - apply a_wf_exp__var.
  - apply a_wf_exp__anno; [ eapply a_wf_ptyp_isub; eauto | auto ].
  - apply a_wf_exp__freeze; auto.
  - apply a_wf_exp__abs with (L := L). intros x Hx. auto.
  - apply a_wf_exp__abs_anno with (L := L);
      [ eapply a_wf_ptyp_isub; eauto | intros x Hx; auto ].
  - apply a_wf_exp__app; auto.
Qed.

(* ===================================================================== *)
(*  §2  Stability of [ad_pat] under the algorithm's increases             *)
(*                                                                        *)
(*  [⊴] alone rewrites term entries up to [≡ᵗ]; paired with the           *)
(*  tm-verbatim invariant the Var rule reads the SAME entry, and no        *)
(*  equivalence-slack machinery is needed.                                 *)
(* ===================================================================== *)

(** [⊴] extended by the SAME term entry on both sides (mirrors
    [a_isub_cons_tvar]; the [≡]-premise of [a_inc__var] is reflexivity). *)
(** A term entry looked up through [abind_to_pskl] is a term entry. *)
Lemma abind_to_pskl_is_tm : forall (b : abind) P,
  abind_to_pskl b = Some P -> abind_is_tm b.
Proof. intros [] P H; simpl in *; congruence || exact I. Qed.

Lemma ad_pat_isub_tm : forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θ', Θ ⊴ Θ' -> aenv_tm_le Θ Θ' ->
  {{ Θ' ⊢ˢ[ M ] e ⦂ Q }}ad.
Proof.
  intros M Θ e Q H; induction H; intros Θ' Hle Htm.
  - (* unit *)
    apply ad_pat__unit;
      [ eapply a_wf_pskl_isub; eauto | eapply ad_pat_sub_v_isub; eauto ].
  - (* var *)
    eapply ad_pat__var;
      [ apply Htm; [ eapply abind_to_pskl_is_tm; eauto | exact H ]
      | eassumption
      | eapply a_wf_pskl_isub; eauto
      | eapply ad_pat_sub_v_isub; eauto ].
  - (* anno *)
    apply ad_pat__anno;
      [ eapply a_wf_ptyp_isub; eauto | eapply a_wf_pskl_isub; eauto
      | eapply ad_pat_sub_v_isub; eauto ].
  - (* freeze *) apply ad_pat__freeze; auto.
  - (* abs *)
    apply ad_pat__abs with (L := L);
      [ assumption | eapply a_wf_pskl_isub; eauto | assumption | ].
    intros x Hx. apply H3;
      [ exact Hx
      | apply a_isub_cons_var_skl;
          [ exact Hle | eapply a_wf_pskl_lc; eauto ]
      | apply aenv_tm_le_cons; exact Htm ].
  - (* abs_anno *)
    eapply ad_pat__abs_anno with (L := L);
      [ assumption | eapply a_wf_ptyp_isub; eauto | eassumption
      | assumption | ].
    intros x Hx. apply H4;
      [ exact Hx
      | apply a_isub_cons_var_typ;
          [ exact Hle | eapply a_wf_ptyp_lc; eauto ]
      | apply aenv_tm_le_cons; exact Htm ].
  - (* app *)
    eapply ad_pat__app;
      [ auto | eapply ad_refine_syn_isub; eauto | auto ].
  - (* abs_check *)
    apply ad_pat__abs_check with (L := L). intros x Hx.
    apply H0;
      [ exact Hx
      | apply a_isub_cons_var_skl; [ exact Hle | apply lc_pskl_hole ]
      | apply aenv_tm_le_cons; exact Htm ].
  - (* abs_anno_check *)
    apply ad_pat__abs_anno_check with (L := L);
      [ eapply a_wf_ptyp_isub; eauto | ].
    intros x Hx. apply H1;
      [ exact Hx
      | apply a_isub_cons_var_typ;
          [ exact Hle | eapply a_wf_ptyp_lc; eauto ]
      | apply aenv_tm_le_cons; exact Htm ].
Qed.

(* ===================================================================== *)
(*  §3  Kit                                                               *)
(* ===================================================================== *)

(* --- §3a  reverse term-verbatim: a run's output has NO NEW term entries  *)
(*     (the suffixes every rule inserts are flexible-only, [a_decls]).     *)
(*     Together with §"tm_le" of prop_stability.v the two directions say   *)
(*     the term entries of input and output are the SAME — which is what   *)
(*     lets a context invariant about term entries survive a run.          *)

Lemma binds_app_mid : forall (y : atom) (b : abind) Ξ (mid : aenv) Θ,
  binds y b (Ξ ++ Θ) -> binds y b (Ξ ++ mid ++ Θ).
Proof.
  intros * H. apply binds_app_1 in H as [H | H];
    [ apply binds_app_2; exact H
    | apply binds_app_3; apply binds_app_3; exact H ].
Qed.

(** [binds_tm_cons_inv] with the binds premise BEFORE the negation, so a
    forward [eapply] resolves the head entry before the negation goal runs. *)
Lemma binds_tm_cons_inv' : forall x (b : abind) y (c : abind) Θ,
  abind_is_tm b -> binds x b ((y ~ c) ++ Θ) -> ~ abind_is_tm c -> binds x b Θ.
Proof. intros; eapply binds_tm_cons_inv; eauto. Qed.

Lemma aenv_tm_le_mid_intro : forall Ξ (mid : aenv) Θ,
  aenv_tm_le (Ξ ++ Θ) (Ξ ++ mid ++ Θ).
Proof. intros Ξ mid Θ y b _ H. apply binds_app_mid; exact H. Qed.

Lemma aenv_tm_le_src_strip_suffix : forall Ξs Θ Θ',
  a_suffix Ξs ->
  aenv_tm_le Θ Θ' -> aenv_tm_le (Ξs ++ Θ) Θ'.
Proof.
  intros * Hsuf Hle y b Htm Hb.
  apply Hle; [ exact Htm | eapply binds_tm_strip_suffix; eauto ].
Qed.

(** Re-attach a walked head when the target also interposes a suffix. *)
Lemma aenv_tm_le_cons_mid : forall (x : atom) (c : abind) Ξ Θ Θ0,
  aenv_tm_le Θ (Ξ ++ Θ0) ->
  aenv_tm_le ((x ~ c) ++ Θ) (Ξ ++ (x ~ c) ++ Θ0).
Proof.
  intros * Hle y b Htm Hb.
  apply binds_app_1 in Hb as [Hb | Hb].
  - apply binds_app_3; apply binds_app_2; exact Hb.
  - specialize (Hle y b Htm Hb).
    apply binds_app_1 in Hle as [Hle | Hle];
      [ apply binds_app_2; exact Hle
      | apply binds_app_3; apply binds_app_3; exact Hle ].
Qed.

Lemma a_assign_unify_consis_tm_ge :
  (forall Θ0 Ξ α P Θ1, {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> aenv_tm_le Θ1 (Ξ ++ Θ0)) /\
  (forall Θ0 α β Θ1, {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> aenv_tm_le Θ1 Θ0) /\
  (forall Δ1 Δ2 Θ0 P0 P Q Θ1,
     a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 -> aenv_tm_le Θ1 Θ0).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun Θ0 Ξ α P Θ1 _ => aenv_tm_le Θ1 (Ξ ++ Θ0))
           (fun Θ0 α β Θ1 _ => aenv_tm_le Θ1 Θ0)
           (fun Δ1 Δ2 Θ0 P0 P Q Θ1 _ => aenv_tm_le Θ1 Θ0)).
  (* ---------- a_assign ---------- *)
  - (* univ_ghost_id : Ξ = nil *) intros; apply aenv_tm_le_refl.
  - (* solve_m *)
    intros Θ0 Ξ α P βs τ Hαn Hg Hm Hu Hfr.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    apply aenv_tm_le_src_strip_suffix;
      [ apply a_decls_suffix; eapply a_guess_mono_decls; eauto | ].
    apply aenv_tm_le_mid_intro.
  - (* assign *)
    intros Θ0 Θ1 Ξ α β τ P Q Hflex Hβ Hc IH.
    apply aenv_tm_le_cons_mid; exact IH.
  - (* depend *)
    intros Θ0 Θ1 Ξ α β P Hne Hβ Ha IH.
    simpl_env in IH; exact IH.
  - (* skip *) intros; apply aenv_tm_le_cons_mid; assumption.
  - (* skip_rigid *) intros; apply aenv_tm_le_cons_mid; assumption.
  - (* skip_tm_var *) intros; apply aenv_tm_le_cons_mid; assumption.
  - (* skip_tm_skl *) intros; apply aenv_tm_le_cons_mid; assumption.
  (* ---------- a_unify ---------- *)
  - (* flex_id *) intros; apply aenv_tm_le_refl.
  - (* flex_l *)
    intros Θ0 α β Hne Hβ.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    apply aenv_tm_le_weaken_r; apply aenv_tm_le_refl.
  - (* flex_r *)
    intros Θ0 α β Hne Hα.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    apply aenv_tm_le_weaken_r; apply aenv_tm_le_refl.
  - (* flex_assign : the consistency premise runs at Θ0 *)
    intros Θ0 Θ1 α1 τ α β Q Hfα Hfβ Hα1 Hc IH.
    apply aenv_tm_le_cons; exact IH.
  - (* flex_skip *) intros; apply aenv_tm_le_cons; assumption.
  - (* skip_other *) intros; apply aenv_tm_le_cons; assumption.
  (* ---------- a_consis ---------- *)
  - (* ghost *) intros; apply aenv_tm_le_refl.
  - (* unit *) intros; apply aenv_tm_le_refl.
  - (* rigid *) intros; apply aenv_tm_le_refl.
  - (* arrow *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2.
    eapply aenv_tm_le_trans; [ exact IH2 | exact IH1 ].
  - (* forall_inh *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar);
      [ intros [] | exact IH ].
  - (* forall_syn *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar);
      [ intros [] | exact IH ].
  - (* univ_ghost *) intros; assumption.
  - (* univ_ghost1 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar);
      [ intros [] | exact IH ].
  - (* univ_ghost2 *) intros; assumption.
  - (* flex *) intros; assumption.
  - (* flex_l : the assign premise has Ξ = nil *) intros; assumption.
  - (* flex_r *) intros; assumption.
  - (* ghost_r *) intros; apply aenv_tm_le_refl.
  - (* univ_ghost_r *) intros; assumption.
Qed.

Lemma a_consis_tm_ge : forall Δ1 Δ2 Θ0 P0 P Q Θ1,
  a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 -> aenv_tm_le Θ1 Θ0.
Proof. intros; eapply (proj2 (proj2 a_assign_unify_consis_tm_ge)); eauto. Qed.

Lemma a_consis_chk_tm_ge : forall Θ0 P P0 Θ1,
  a_consis_chk Θ0 P P0 Θ1 -> aenv_tm_le Θ1 Θ0.
Proof. intros * [Q Hc]; eapply a_consis_tm_ge; eauto. Qed.

Lemma a_sub_sub_flex_tm_ge :
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 -> aenv_tm_le Θ1 Θ0) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 -> aenv_tm_le Θ1 (Ξ ++ Θ0)).
Proof.
  apply (a_sub_sub_flex_tm_mutind
           (fun NM M P0 Θ0 P Q Θ1 _ => aenv_tm_le Θ1 Θ0)
           (fun NM M P0 Θ0 Ξ α Q Θ1 _ => aenv_tm_le Θ1 (Ξ ++ Θ0))).
  (* ---------- a_sub ---------- *)
  - (* infer *) intros; apply aenv_tm_le_refl.
  - (* check *)
    intros Θ0 Θ1 A B Hgf1 Hgf2 Hg1 Hg2 Hchk.
    eapply a_consis_chk_tm_ge; exact Hchk.
  - (* forall_r *)
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huniq Hnotin Hrun IH.
    intros y b Htm Hb.
    assert (Hb1 : binds y b (Ξ ++ (α ~ abind_tvar) ++ Θ1))
      by (apply binds_app_3; apply binds_app_3; exact Hb).
    assert (Hb2 : binds y b ((α ~ abind_tvar) ++ Θ0))
      by (apply IH; [ exact Htm | exact Hb1 ]).
    eapply binds_tm_cons_inv'; [ exact Htm | exact Hb2 | intros [] ].
  - (* univ_ghost_r *) intros; apply aenv_tm_le_refl.
  - (* flex_mono : Ξ = nil *) intros; assumption.
  - (* arrow *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH.
    eapply aenv_tm_le_trans; [ exact IH | eapply a_consis_tm_ge; exact Hc ].
  - (* forall_l *)
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hm Hg Hα Hext Huniq Hwf Hs IH.
    eapply aenv_tm_le_strip_suffix_tgt;
      [ apply a_decls_suffix; eapply a_extract_decls; eauto | exact IH ].
  - (* ghost *) intros; apply aenv_tm_le_refl.
  - (* univ_ghost_l *) intros; assumption.
  (* ---------- a_sub_flex ---------- *)
  - (* solve : the premise deposits three type-level entries below Ξ *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hα Hβ Hs IH.
    intros y b Htm Hb.
    specialize (IH y b Htm Hb).
    apply binds_app_1 in IH as [IH | IH];
      [ apply binds_app_2; exact IH | ].
    assert (IH1 : binds y b ((β ~ abind_flex_mono)
                              ++ (α ~ abind_flex_mono) ++ Θ0))
      by (eapply binds_tm_cons_inv'; [ exact Htm | exact IH | intros [] ]).
    assert (IH2 : binds y b ((α ~ abind_flex_mono) ++ Θ0))
      by (eapply binds_tm_cons_inv'; [ exact Htm | exact IH1 | intros [] ]).
    assert (IH3 : binds y b Θ0)
      by (eapply binds_tm_cons_inv'; [ exact Htm | exact IH2 | intros [] ]).
    apply binds_app_3; apply binds_app_3; exact IH3.
  - (* assign *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβ Hs IH.
    apply aenv_tm_le_cons_mid; exact IH.
  - (* depend *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hβ Hs IH.
    simpl_env in IH; exact IH.
  - (* skip *) intros; apply aenv_tm_le_cons_mid; assumption.
  - (* skip_rigid *) intros; apply aenv_tm_le_cons_mid; assumption.
  - (* skip_tm_var *) intros; apply aenv_tm_le_cons_mid; assumption.
  - (* skip_tm_skl *) intros; apply aenv_tm_le_cons_mid; assumption.
Qed.

Lemma a_sub_tm_ge : forall NM M P0 Θ0 P Q Θ1,
  a_sub NM M P0 Θ0 P Q Θ1 -> aenv_tm_le Θ1 Θ0.
Proof. intros; eapply (proj1 a_sub_sub_flex_tm_ge); eauto. Qed.

Lemma a_split_tm_ge : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a -> aenv_tm_le Θ1 Θ0.
Proof.
  intros * H; inversion H; subst; try apply aenv_tm_le_refl.
  match goal with
  | Hc : a_consis _ _ _ _ _ _ _ |- _ => apply a_consis_tm_ge in Hc
  end.
  eapply aenv_tm_le_strip_cons_tgt with (c := abind_flex_mono);
    [ intros [] | ].
  eapply aenv_tm_le_strip_cons_tgt with (c := abind_flex_mono);
    [ intros [] | ].
  eassumption.
Qed.

(** The mirror of [aenv_tm_le_via_binder] (prop_stability.v): crossing a
    binder row in the OUTPUT-to-INPUT direction.  No [a_suffix] premise is
    needed here — the pending suffix is crossed on the SOURCE side, where a
    lookup only has to be weakened ([binds_app_mid]). *)
Lemma aenv_tm_le_via_binder_ge : forall Ξ x (bx : abind) Θ Θ',
  aenv_tm_le (Ξ ++ (x ~ bx) ++ Θ') ((x ~ bx) ++ Θ) ->
  forall y b, abind_is_tm b -> y <> x -> binds y b (Ξ ++ Θ') -> binds y b Θ.
Proof.
  intros * Hle y b Htm Hne Hb.
  assert (Hb1 : binds y b ((x ~ bx) ++ Θ))
    by (apply Hle; [ exact Htm | apply binds_app_mid; exact Hb ]).
  destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[Heq _] | Hb2];
    [ subst; contradiction | exact Hb2 ].
Qed.

(** Skeleton inference runs, reverse direction: the output has no term
    entry the input did not have.  With [a_pat_tm_le] this says the term
    entries are the SAME, which is what sustains a context invariant about
    term entries (the disciplined well-formedness of skeleton entries) all
    the way through a sequence of premises. *)
Lemma a_pat_tm_ge : forall m Θ0 P0 e P Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ P ⊣ Θ1 }}a -> aenv_tm_le Θ1 Θ0.
Proof.
  intros m Θ0 P0 e P Θ1 H; induction H.
  - (* unit *) eapply a_sub_tm_ge; eassumption.
  - (* var *) eapply a_sub_tm_ge; eassumption.
  - (* var_skl *) eapply a_sub_tm_ge; eassumption.
  - (* anno *) eapply a_sub_tm_ge; eassumption.
  - (* freeze *) assumption.
  - (* abs *)
    intros y b Htm Hb.
    apply a_split_tm_ge in H0.
    destruct (atom_fresh (L `union` singleton y)) as [x Hx].
    apply H0; [ exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ apply H3; clear - Hx; fsetdec | exact Htm
      | intros Heq; subst; clear - Hx; fsetdec | exact Hb ].
  - (* abs_anno *)
    intros y b Htm Hb.
    apply a_split_tm_ge in H0.
    apply a_consis_chk_tm_ge in H1.
    destruct (atom_fresh (L `union` singleton y)) as [x Hx].
    apply H0; [ exact Htm | ]. apply H1; [ exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ apply H4; clear - Hx; fsetdec | exact Htm
      | intros Heq; subst; clear - Hx; fsetdec | exact Hb ].
  - (* abs_check *)
    intros y b Htm Hb.
    destruct (atom_fresh (L `union` singleton y)) as [x Hx].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ apply H1; clear - Hx; fsetdec | exact Htm
      | intros Heq; subst; clear - Hx; fsetdec | exact Hb ].
  - (* abs_anno_check *)
    intros y b Htm Hb.
    destruct (atom_fresh (L `union` singleton y)) as [x Hx].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ apply H1; clear - Hx; fsetdec | exact Htm
      | intros Heq; subst; clear - Hx; fsetdec | exact Hb ].
  - (* app *)
    eapply aenv_tm_le_trans; [ exact IHa_pat2 | exact IHa_pat1 ].
Qed.

(* --- §3b  coercion bridge + split shapes + mode inversions ------------- *)

(** The two syn-erasures agree: painting a pskl syn and then forgetting
    the colour is the direct pskl→uskl embedding. *)
Lemma pskl_to_uskl_via_bskl_syn : forall P,
  bskl_to_uskl (pskl_to_bskl_syn P) = pskl_to_uskl P.
Proof. induction P; simpl; congruence. Qed.

(** ⭐ Under the judgement's own [skmod{SK}] side condition the split can
    only be the ARROW or HOLE row: the flex row's input is a flexible
    variable, for which [a_sk_mode_compat] has no rule.  (The flex row is
    reachable only from TYPE inference, whose [skmod{TY}] admits any type
    at TC.)  This is what spares skeleton-inference soundness both
    lemma:split-refine and refinement transitivity. *)
Lemma a_split_sk_shape : forall m Θ0 P0 P Q0 Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}a ->
  a_sk_mode_compat m P0 ->
  Θ1 = Θ0 /\
  ((P0 = pskl_hole /\ P = pskl_hole /\ Q0 = pskl_hole) \/
   P0 = pskl_arrow P Q0).
Proof.
  intros * Hs Hm; inversion Hs; subst.
  - split; [ reflexivity | right; reflexivity ].
  - split; [ reflexivity | left; auto ].
  - inversion Hm.
Qed.

Lemma a_sk_mode_compat_arrow_inv : forall m P Q,
  a_sk_mode_compat m (pskl_arrow P Q) ->
  exists m', m = mode_fn m' /\ a_sk_mode_compat m' Q.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma a_sk_mode_compat_hole_inv : forall m,
  a_sk_mode_compat m pskl_hole -> m = mode_ti \/ m = mode_tc.
Proof. intros * H; inversion H; auto. Qed.

(* --- §3c  the SK-sorted subtyping's target is mode-compatible ---------- *)

(** The inferred-skeleton half of the paper's (commented-out) "refinement
    preserves correspondence": an SK-sorted all-in-one subtyping run's
    target satisfies [skmod{SK}] — each leaf either states [is_sskl] or
    carries [mod_comp_sk] outright, and the structural rows rebuild it. *)
Lemma ad_pat_sub_mod_comp_sk : forall M Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] R ⩽ Q }}ad ->
  mod_comp_sk Q M.
Proof.
  intros M Ψ Θ R Q H.
  remember a_sub_mode_sk as NM eqn:HNM.
  induction H; subst; try discriminate.
  - (* infer *) apply mod_comp_sk__ti; assumption.
  - (* univ_ghost_r *)
    apply mod_comp_sk__tc. apply is_sskl__tophole; assumption.
  - (* arrow *) apply mod_comp_sk__fn; auto.
  - (* forall_l_tagged *) auto.
  - (* forall_l_untagged *) auto.
  - (* ghost *) assumption.
  - (* ghostg *) assumption.
  - (* univ_ghost_l *) auto.
  - (* univ_ghost_lg *) auto.
  - (* flex_mono *) auto.
Qed.

(* --- §3d  term-variable renaming for [ad_pat] ------------------------- *)

Lemma abind_is_tm_not_ty : forall b : abind,
  abind_is_tm b -> ~ abind_is_ty b.
Proof. intros [] Htm; simpl in *; auto. Qed.

(** Renaming a term key preserves every type-level lookup. *)
Lemma aenv_tbinds_le_rename_tm : forall Θa x y (b : abind) Θ0,
  ~ abind_is_ty b ->
  aenv_tbinds_le (Θa ++ (x ~ b) ++ Θ0) (Θa ++ (y ~ b) ++ Θ0).
Proof.
  intros * Hb α c Hc H.
  apply binds_app_mid.
  eapply aenv_tbinds_le_strip_tm; eauto.
Qed.

(** [ad_pat] is closed under substituting one term variable for another
    carrying the SAME entry: types and skeletons contain no term
    variables, so only the subject and the renamed KEY move; type-level
    premises transport by the term-blind kit. *)
Lemma ad_pat_subst_tm : forall M Θ' e Q,
  {{ Θ' ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θa x (b : abind) Θ0 y,
  Θ' = Θa ++ (x ~ b) ++ Θ0 ->
  abind_is_tm b ->
  x `notin` dom Θa `union` dom Θ0 ->
  {{ (Θa ++ (y ~ b) ++ Θ0) ⊢ˢ[ M ] (subst_exp_in_exp (exp_var_f y) x e) ⦂ Q }}ad.
Proof.
  intros M Θ' e Q H; induction H;
    intros Θa x0 b0 Θb y Heq Htm Hx0; subst; simpl.
  - (* unit *)
    apply ad_pat__unit;
      [ eapply a_wf_pskl_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | eapply ad_pat_sub_v_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ] ].
  - (* var *)
    destruct_if as [Heq | Hne].
    + (* the renamed variable itself: its entry is exactly [b0] *)
      subst x.
      assert (Hb0 : b = b0).
      { apply binds_app_1 in H as [H | H];
          [ exfalso; apply binds_In in H; clear - H Hx0; fsetdec | ].
        apply binds_app_1 in H as [H | H];
          [ | exfalso; apply binds_In in H; clear - H Hx0; fsetdec ].
        destruct H as [Hp | []]. inversion Hp; reflexivity. }
      subst b.
      eapply ad_pat__var with (b := b0);
        [ apply binds_app_3; unfold binds; simpl; left; reflexivity
        | eassumption
        | eapply a_wf_pskl_mono;
            [ eassumption | apply aenv_tbinds_le_rename_tm;
                            apply abind_is_tm_not_ty; exact Htm ]
        | eapply ad_pat_sub_v_mono;
            [ eassumption | apply aenv_tbinds_le_rename_tm;
                            apply abind_is_tm_not_ty; exact Htm ] ].
    + (* any other variable: its entry is untouched *)
      eapply ad_pat__var with (b := b);
        [ | eassumption
        | eapply a_wf_pskl_mono;
            [ eassumption | apply aenv_tbinds_le_rename_tm;
                            apply abind_is_tm_not_ty; exact Htm ]
        | eapply ad_pat_sub_v_mono;
            [ eassumption | apply aenv_tbinds_le_rename_tm;
                            apply abind_is_tm_not_ty; exact Htm ] ].
      apply binds_app_1 in H as [H | H];
        [ apply binds_app_2; exact H | ].
      apply binds_app_1 in H as [H | H];
        [ destruct H as [Hp | []]; inversion Hp; subst; exfalso; auto | ].
      apply binds_app_3; unfold binds; simpl; right; exact H.
  - (* anno *)
    apply ad_pat__anno;
      [ eapply a_wf_ptyp_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | eapply a_wf_pskl_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | eapply ad_pat_sub_v_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ] ].
  - (* freeze *)
    apply ad_pat__freeze. apply IHad_pat; auto.
  - (* abs *)
    apply ad_pat__abs with (L := L `union` singleton x0 `union` singleton y);
      [ assumption
      | eapply a_wf_pskl_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | assumption | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H3 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_skl P) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | ].
    simpl. clear - Hx0 Hz. fsetdec.
  - (* abs_anno *)
    apply ad_pat__abs_anno
      with (L := L `union` singleton x0 `union` singleton y) (B := B);
      [ assumption
      | eapply a_wf_ptyp_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | reflexivity | assumption | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H4 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_typ (btyp_to_ptyp B)) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | ].
    simpl. clear - Hx0 Hz. fsetdec.
  - (* app *)
    eapply ad_pat__app;
      [ apply IHad_pat1; auto
      | eapply ad_refine_syn_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | apply IHad_pat2; auto ].
  - (* abs_check *)
    apply ad_pat__abs_check
      with (L := L `union` singleton x0 `union` singleton y).
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H0 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_skl pskl_hole) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | ].
    simpl. clear - Hx0 Hz. fsetdec.
  - (* abs_anno_check *)
    apply ad_pat__abs_anno_check
      with (L := L `union` singleton x0 `union` singleton y);
      [ eapply a_wf_ptyp_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ] | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H1 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | ].
    simpl. clear - Hx0 Hz. fsetdec.
Qed.

(* --- §3e  context surgery: dropping the walked term entry -------------- *)

(** A term variable's TYPE entry is well-formed in its own context — the
    mirror of [a_wf_aenv_binds_def_wf] (prop_precise.v) for the other
    payload-carrying entry form.  [AP-Var] (type-bound) needs it to feed
    [a_sub_sound], which demands well-formedness of its subject. *)
Lemma a_wf_aenv_binds_var_typ_wf : forall Θ x A,
  {{ ⊢ Θ }}a ->
  binds x (abind_var_typ A) Θ ->
  a_wf_ptyp Θ A.
Proof.
  intros Θ x A Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
    try discriminate;
    try (eapply a_wf_ptyp_weaken;
         [ intros y b Hby; unfold binds; right; exact Hby | ];
         first [ apply IHHwf; exact Hb'
               | inversion Heqb; subst; assumption ]).
Qed.

(** ⭐ Dropping a term entry from the MIDDLE of a well-formed context keeps
    it well-formed.  The point is that no payload can mention a term KEY
    type-wise: every payload is checked by [a_wf_ptyp] / [a_scope_pskl],
    both of which read only type-level entries, so they transport along
    [aenv_tbinds_le_strip_tm].  Freshness only shrinks.  This is what turns
    the Abs rows' body context [Ξ,x:P,Θ2] into the rule's output [Ξ,Θ2]. *)
Lemma a_wf_aenv_strip_tm_mid : forall Ξ x (b : abind) Θ,
  ~ abind_is_ty b ->
  {{ ⊢ (Ξ ++ (x ~ b) ++ Θ) }}a ->
  {{ ⊢ (Ξ ++ Θ) }}a.
Proof.
  intros Ξ; induction Ξ as [ | [y c] Ξ' IH ]; intros x b Θ Hb Hwf.
  - rewrite app_nil_l in *. inversion Hwf; subst; assumption.
  - assert (Htail : {{ ⊢ (Ξ' ++ (x ~ b) ++ Θ) }}a)
      by (inversion Hwf; subst; assumption).
    assert (Hrest : {{ ⊢ (Ξ' ++ Θ) }}a) by (apply (IH x b Θ Hb Htail)).
    assert (Hy : y `notin` dom (Ξ' ++ Θ)).
    { assert (Hy0 : y `notin` dom (Ξ' ++ (x ~ b) ++ Θ))
        by (inversion Hwf; subst; assumption).
      simpl_env in Hy0. simpl_env. clear - Hy0. fsetdec. }
    assert (Hle : aenv_tbinds_le (Ξ' ++ (x ~ b) ++ Θ) (Ξ' ++ Θ))
      by (apply aenv_tbinds_le_strip_tm; exact Hb).
    inversion Hwf; subst.
    + apply a_wf_aenv__flex; assumption.
    + apply a_wf_aenv__flex_def; try assumption.
      eapply a_wf_ptyp_mono; eassumption.
    + apply a_wf_aenv__var; try assumption.
      eapply a_wf_pskl_mono; eassumption.
    + apply a_wf_aenv__var_typ; try assumption.
      eapply a_wf_ptyp_mono; eassumption.
    + apply a_wf_aenv__tvar; assumption.
Qed.

(** List surgery: a [uniq] context is cut in only one way at a given key. *)
Lemma uniq_mid_eq : forall (Ξ1 : aenv) x (b1 : abind) Θ1 Ξ2 (b2 : abind) Θ2,
  Ξ1 ++ (x ~ b1) ++ Θ1 = Ξ2 ++ (x ~ b2) ++ Θ2 ->
  uniq (Ξ1 ++ (x ~ b1) ++ Θ1) ->
  Ξ1 = Ξ2 /\ b1 = b2 /\ Θ1 = Θ2.
Proof.
  intros Ξ1; induction Ξ1 as [ | [y c] Ξ1' IH ];
    intros x b1 Θ1 Ξ2 b2 Θ2 Heq Hu.
  - destruct Ξ2 as [ | [z d] Ξ2' ].
    + inversion Heq; subst; auto.
    + (* the key would occur below its own entry *)
      exfalso.
      assert (Hnot : x `notin` dom Θ1)
        by (inversion Hu; subst; assumption).
      assert (HeqΘ : Θ1 = Ξ2' ++ (x ~ b2) ++ Θ2)
        by (inversion Heq; subst; first [ reflexivity | assumption ]).
      rewrite HeqΘ in Hnot. simpl_env in Hnot. clear - Hnot. fsetdec.
  - destruct Ξ2 as [ | [z d] Ξ2' ].
    + exfalso.
      assert (Hnot : y `notin` dom (Ξ1' ++ (x ~ b1) ++ Θ1))
        by (inversion Hu; subst; assumption).
      assert (Hyx : y = x) by (inversion Heq; reflexivity).
      rewrite Hyx in Hnot. simpl_env in Hnot. clear - Hnot. fsetdec.
    + assert (Hu' : uniq (Ξ1' ++ (x ~ b1) ++ Θ1))
        by (inversion Hu; subst; assumption).
      assert (Heq' : Ξ1' ++ (x ~ b1) ++ Θ1 = Ξ2' ++ (x ~ b2) ++ Θ2)
        by (inversion Heq; subst; first [ reflexivity | assumption ]).
      assert (Hyz : y = z) by (inversion Heq; reflexivity).
      assert (Hcd : c = d) by (inversion Heq; reflexivity).
      destruct (IH _ _ _ _ _ _ Heq' Hu') as [HΞ [Hb HΘ]]; subst.
      auto.
Qed.

Arguments uniq_mid_eq {Ξ1 x b1 Θ1 Ξ2 b2 Θ2} _ _.

(** The target of an identity increase may always grow a fresh flexible
    suffix ([a_inc_refl_gen] composed with transitivity). *)
Lemma a_inc_weaken_suffix_target : forall Θ κ Θ' Ξ,
  κ ∷ Θ ⊑ Θ' ->
  is_id_msubst κ ->
  lc_aenv Θ' ->
  a_suffix Ξ ->
  exists κ', is_id_msubst κ' /\ κ' ∷ Θ ⊑ (Ξ ++ Θ').
Proof.
  intros * Hinc Hid Hlc HΞ.
  destruct (a_inc_refl_gen (Ξ0 := Ξ) Hlc HΞ) as [κ2 [Hid2 Hinc2]].
  eapply a_inc_trans; eassumption.
Qed.

(** ⭐ THE ⊴-PEEL the Abs rows need: the body's increase runs from the
    context extended by the walked binder to the output extended by the
    SAME binder under a pending suffix, and what the rule's conclusion
    needs is the increase between the two contexts with that binder gone.

    Both components peel: [a_inc_var_skl_inv] cuts the target at the key
    (uniquely, by [uniq_mid_eq]) and hands back the increase between the
    tails, which then re-grows the suffix; and a DEFINITION can never be
    the peeled entry, so the definition-preservation component just drops
    the middle by payload shape — no freshness needed. *)
Lemma a_isub_peel_var_skl_mid : forall x P Θ1 Ξ Θ2,
  a_suffix Ξ ->
  uniq (Ξ ++ (x ~ abind_var_skl P) ++ Θ2) ->
  lc_aenv Θ2 ->
  ((x ~ abind_var_skl P) ++ Θ1) ⊴ (Ξ ++ (x ~ abind_var_skl P) ++ Θ2) ->
  Θ1 ⊴ (Ξ ++ Θ2).
Proof.
  intros * HΞ Hu Hlc [[κ [Hid Hinc]] Hd].
  destruct (a_inc_var_skl_inv Hinc) as [Ξ0 [P' [Θ0 [Heq [_ [_ Hinc']]]]]].
  destruct (uniq_mid_eq Heq Hu) as [-> [Heqb ->]]. inversion Heqb; subst.
  split.
  - eapply a_inc_weaken_suffix_target; eassumption.
  - intros α τ Hb.
    assert (Hb1 : binds α (abind_flex_mono_def τ)
                    (Ξ0 ++ (x ~ abind_var_skl P') ++ Θ0))
      by (apply Hd; apply binds_app_3; exact Hb).
    apply binds_app_1 in Hb1 as [Hb1 | Hb1];
      [ apply binds_app_2; exact Hb1 | ].
    apply binds_app_3.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[_ Heqd] | Hb2];
      [ discriminate | exact Hb2 ].
Qed.

Lemma a_isub_peel_var_typ_mid : forall x A Θ1 Ξ Θ2,
  a_suffix Ξ ->
  uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) ->
  lc_aenv Θ2 ->
  ((x ~ abind_var_typ A) ++ Θ1) ⊴ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) ->
  Θ1 ⊴ (Ξ ++ Θ2).
Proof.
  intros * HΞ Hu Hlc [[κ [Hid Hinc]] Hd].
  destruct (a_inc_var_inv Hinc) as [Ξ0 [A' [Θ0 [Heq [_ [_ Hinc']]]]]].
  destruct (uniq_mid_eq Heq Hu) as [-> [Heqb ->]]. inversion Heqb; subst.
  split.
  - eapply a_inc_weaken_suffix_target; eassumption.
  - intros α τ Hb.
    assert (Hb1 : binds α (abind_flex_mono_def τ)
                    (Ξ0 ++ (x ~ abind_var_typ A') ++ Θ0))
      by (apply Hd; apply binds_app_3; exact Hb).
    apply binds_app_1 in Hb1 as [Hb1 | Hb1];
      [ apply binds_app_2; exact Hb1 | ].
    apply binds_app_3.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[_ Heqd] | Hb2];
      [ discriminate | exact Hb2 ].
Qed.

(** The exists-fresh → cofinite bridge the Abs cases need: one fresh
    witness generates the whole family. *)
Corollary ad_pat_rename_tm : forall M x (b : abind) Θ0 e Q y,
  {{ ((x ~ b) ++ Θ0) ⊢ˢ[ M ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q }}ad ->
  abind_is_tm b ->
  x `notin` dom Θ0 `union` fvar_in_exp e ->
  {{ ((y ~ b) ++ Θ0) ⊢ˢ[ M ] (open_exp_wrt_exp e (exp_var_f y)) ⦂ Q }}ad.
Proof.
  intros * Hd Htm Hx.
  rewrite (subst_exp_in_exp_intro x); [ | clear - Hx; fsetdec ].
  change ((y ~ b) ++ Θ0) with (nil ++ (y ~ b) ++ Θ0).
  eapply ad_pat_subst_tm;
    [ exact Hd | reflexivity | exact Htm | simpl; clear - Hx; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §3f  small inversions and coercion identities the assembly quotes     *)
(* ===================================================================== *)

Lemma mod_comp_sk_ti_inv : forall Q, mod_comp_sk Q mode_ti -> is_sskl Q.
Proof. intros Q H; inversion H; subst; assumption. Qed.

Lemma mod_comp_sk_tc_inv : forall Q, mod_comp_sk Q mode_tc -> is_sskl Q.
Proof. intros Q H; inversion H; subst; assumption. Qed.

Lemma mod_comp_sk_fn_inv : forall Q1 Q2 m,
  mod_comp_sk (bskl_arrow Q1 Q2) (mode_fn m) -> mod_comp_sk Q2 m.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma btyp_to_bskl_ptyp_to_btyp_syn : forall A,
  btyp_to_bskl (ptyp_to_btyp_syn A) = pskl_to_bskl_syn (ptyp_to_pskl A).
Proof. induction A; simpl; congruence. Qed.

Lemma bskl_to_pskl_arrow_inv : forall Q P1 P2,
  bskl_to_pskl Q = pskl_arrow P1 P2 ->
  exists Q1 Q2, Q = bskl_arrow Q1 Q2 /\
                bskl_to_pskl Q1 = P1 /\ bskl_to_pskl Q2 = P2.
Proof.
  intros [ | | | Q1 Q2 | | | | ] P1 P2 Heq; simpl in Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Arguments bskl_to_pskl_arrow_inv {Q P1 P2} _.

(** The Δ-free reading of skeleton well-formedness at [Δ = ∅]. *)

Lemma a_wf_pskl_weaken_cons : forall Θ Δ P x (b : abind),
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> {{ ((x ~ b) ++ Θ) ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros * H. eapply a_wf_pskl_mono;
    [ exact H | apply aenv_tbinds_le_of_binds_le; apply aenv_binds_le_weaken_l ].
Qed.

Lemma a_wf_ptyp_weaken_cons : forall Θ A x (b : abind),
  a_wf_ptyp Θ A -> a_wf_ptyp ((x ~ b) ++ Θ) A.
Proof.
  intros * H. eapply a_wf_ptyp_mono;
    [ exact H | apply aenv_tbinds_le_of_binds_le; apply aenv_binds_le_weaken_l ].
Qed.

Lemma a_wf_exp_weaken_cons : forall Θ e x (b : abind),
  {{ Θ ⊢ᵉ e }}a -> {{ ((x ~ b) ++ Θ) ⊢ᵉ e }}a.
Proof.
  intros * H. eapply a_wf_exp_mono;
    [ exact H | apply aenv_tbinds_le_of_binds_le; apply aenv_binds_le_weaken_l ].
Qed.

(** Inversions of [a_wf_exp], so the main induction never has to guess the
    names [inversion] manufactures. *)
Lemma a_wf_exp_anno_inv : forall Θ e A,
  {{ Θ ⊢ᵉ (exp_anno e A) }}a -> a_wf_ptyp Θ A /\ {{ Θ ⊢ᵉ e }}a.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_exp_freeze_inv : forall Θ e,
  {{ Θ ⊢ᵉ (exp_freeze e) }}a -> {{ Θ ⊢ᵉ e }}a.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_exp_app_inv : forall Θ e1 e2,
  {{ Θ ⊢ᵉ (exp_app e1 e2) }}a -> {{ Θ ⊢ᵉ e1 }}a /\ {{ Θ ⊢ᵉ e2 }}a.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_exp_abs_inv : forall Θ e,
  {{ Θ ⊢ᵉ (exp_abs e) }}a ->
  exists L, forall x, x `notin` L ->
    {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma a_wf_exp_abs_anno_inv : forall Θ A e,
  {{ Θ ⊢ᵉ (exp_abs_anno A e) }}a ->
  a_wf_ptyp Θ A /\
  exists L, forall x, x `notin` L ->
    {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a.
Proof. intros * H; inversion H; subst; eauto. Qed.

(** The binder rows are EXISTS-FRESH on the algorithm side (2026-08-08), so
    soundness receives ONE binder name and must open the [a_wf_exp] families
    at exactly it.  Term-variable renaming is invisible to [a_wf_exp] — it
    reads only type-level entries — so the cofinite families are in fact
    name-independent. *)
Lemma a_wf_exp_subst_var : forall Θ e x z,
  {{ Θ ⊢ᵉ e }}a ->
  {{ Θ ⊢ᵉ (subst_exp_in_exp (exp_var_f x) z e) }}a.
Proof.
  intros Θ e x z H; induction H; simpl.
  - apply a_wf_exp__unit.
  - destruct_if; apply a_wf_exp__var.
  - apply a_wf_exp__anno; auto.
  - apply a_wf_exp__freeze; auto.
  - apply a_wf_exp__abs with (L := L `union` singleton z `union` singleton x).
    intros y Hy.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hy; fsetdec | apply lc_exp_var_f ].
    apply H0. clear - Hy; fsetdec.
  - apply a_wf_exp__abs_anno
      with (L := L `union` singleton z `union` singleton x);
      [ assumption | ].
    intros y Hy.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hy; fsetdec | apply lc_exp_var_f ].
    apply H1. clear - Hy; fsetdec.
  - apply a_wf_exp__app; auto.
Qed.

Lemma a_wf_exp_abs_pick : forall Θ e x,
  {{ Θ ⊢ᵉ (exp_abs e) }}a ->
  {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a.
Proof.
  intros Θ e x H; inversion H; subst.
  destruct (atom_fresh (L `union` fvar_in_exp e `union` singleton x))
    as [z Hz].
  rewrite (subst_exp_in_exp_intro z e (exp_var_f x));
    [ | clear - Hz; fsetdec ].
  apply a_wf_exp_subst_var.
  match goal with
  | Hf : forall y, y `notin` L -> {{ _ ⊢ᵉ _ }}a |- _ => apply Hf
  end.
  clear - Hz; fsetdec.
Qed.

Lemma a_wf_exp_abs_anno_pick : forall Θ A e x,
  {{ Θ ⊢ᵉ (exp_abs_anno A e) }}a ->
  {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a.
Proof.
  intros Θ A e x H; inversion H; subst.
  destruct (atom_fresh (L `union` fvar_in_exp e `union` singleton x))
    as [z Hz].
  rewrite (subst_exp_in_exp_intro z e (exp_var_f x));
    [ | clear - Hz; fsetdec ].
  apply a_wf_exp_subst_var.
  match goal with
  | Hf : forall y, y `notin` L -> {{ _ ⊢ᵉ _ }}a |- _ => apply Hf
  end.
  clear - Hz; fsetdec.
Qed.

(** ⭐ The paper's (commented-out) "refinement preserves correspondence",
    inferred-skeleton half, at the level of the DECLARATIVE judgement: a
    skeleton-inference colouring is mode-compatible.  The two Abs rows
    carry it outright; the base rows read it off their subtyping premise
    (§3c); [Freeze] and [App] invert their premise's. *)
Lemma ad_pat_mod_comp_sk : forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad -> mod_comp_sk Q M.
Proof.
  intros M Θ e Q H; induction H.
  - (* unit *) eapply ad_pat_sub_mod_comp_sk; apply ad_pat_sub_of_v; eassumption.
  - (* var *) eapply ad_pat_sub_mod_comp_sk; apply ad_pat_sub_of_v; eassumption.
  - (* anno *) eapply ad_pat_sub_mod_comp_sk; apply ad_pat_sub_of_v; eassumption.
  - (* freeze *) apply mod_comp_sk__tc. apply mod_comp_sk_ti_inv; assumption.
  - (* abs *) assumption.
  - (* abs_anno *) assumption.
  - (* app *) eapply mod_comp_sk_fn_inv; eassumption.
  - (* abs_check *)
    destruct (atom_fresh L) as [x Hx]. specialize (H0 x Hx).
    apply mod_comp_sk__tc. apply is_sskl__tophole. apply is_sskl__arrow;
      [ apply is_sskl__hole | apply mod_comp_sk_tc_inv; exact H0 ].
  - (* abs_anno_check *)
    destruct (atom_fresh L) as [x Hx]. specialize (H1 x Hx).
    apply mod_comp_sk__tc. apply is_sskl__tophole. apply is_sskl__arrow.
    + rewrite btyp_to_bskl_ptyp_to_btyp_syn.
      apply is_sskl_pskl_to_bskl_syn.
      apply lc_ptyp_to_pskl. eapply a_wf_ptyp_lc; eassumption.
    + apply mod_comp_sk_tc_inv; exact H1.
Qed.

(** Consistency soundness in the output-suppressed form the [AbsAnno] rows
    use, with the Δ-side conditions of [a_consis_sound_aux] discharged at
    [Δ1 = Δ2 = ∅] and the output context's well-formedness kept. *)
Corollary a_consis_chk_sound : forall Θ0 P P0 Θ1,
  a_consis_chk Θ0 P P0 Θ1 ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt, ({{ empty ⨟ Θ1 ⊢ˢ (pskl_to_uskl P) ∼ Qt }}ad) /\
             {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad.
Proof.
  intros * [Q Hc] Hwf HwfP0 HwfP.
  destruct (a_consis_sound_aux Hc Hwf HwfP0 HwfP
              ltac:(intros α Hα; clear - Hα; solve_notin_auto)
              ltac:(intros β τ Hb; apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; solve_notin_auto)
              ltac:(intros Θa β b Θb Heq Hne;
                    apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; solve_notin_auto))
    as [Hle [Hwf1 [_ [_ [[Qt [_ [Hcons Hrs]]] _]]]]].
  split; [ exact Hle | ]. split; [ exact Hwf1 | ].
  exists Qt. split; [ exact Hcons | ]. eapply ad_refine_syn_f_forget; exact Hrs.
Qed.

Lemma bskl_to_pskl_btyp_to_bskl : forall B,
  bskl_to_pskl (btyp_to_bskl B) = ptyp_to_pskl (btyp_to_ptyp B).
Proof. induction B; simpl; congruence. Qed.

Lemma ad_refine_syn_arrow_inv : forall Θ Δ Q1 Q2 P1 P2,
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow P1 P2) }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Q1 ⊳ P1 }}ad /\ {{ Θ ⨟ Δ ⊢ᵣ Q2 ⊳ P2 }}ad.
Proof. intros * H; inversion H; subst; auto. Qed.

(* ===================================================================== *)
(*  §4  AbsAnno's refinement-target transport                             *)
(*                                                                        *)
(*  The paper's inline step [by preservation of refinement under type     *)
(*  equivalence] (proofs.tex, AbsAnno case of thm:sound-skeleton-          *)
(*  inference), which exists NOWHERE as a lemma — docs/PAPER-GAPS.md.     *)
(*  thm:sound-consistency hands back the run's own output colouring and,  *)
(*  in the paper, [Θ2 ⊢ A' ≡ A]; the mechanized [a_consis_sound] hands    *)
(*  back that colouring plus its CONSISTENCY with the subject painting,   *)
(*  so what has to be supplied is a TARGET TRANSPORT: the refinement's    *)
(*  target must be re-coloured into a painting of the ANNOTATION.  §4a–4e *)
(*  are its kit, §4f the transport, and the lemma itself closes at the    *)
(*  end of this section.                                                  *)
(* ===================================================================== *)

(* --- §4a  the transport's kit (1): coercion identities ------------------ *)

Lemma ptyp_to_uskl_syn_via_pskl : forall A,
  ptyp_to_uskl_syn A = pskl_to_uskl (ptyp_to_pskl A).
Proof.
  intros A. unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  apply pskl_to_uskl_via_bskl_syn.
Qed.

Lemma btyp_to_ptyp_close_rec : forall B α k,
  btyp_to_ptyp (close_btyp_wrt_btyp_rec k α B)
  = close_ptyp_wrt_ptyp_rec k α (btyp_to_ptyp B).
Proof.
  intros B; induction B; intros α0 k; default_simp.
Qed.

Lemma btyp_to_ptyp_close : forall B α,
  btyp_to_ptyp (close_btyp_wrt_btyp α B)
  = close_ptyp_wrt_ptyp α (btyp_to_ptyp B).
Proof.
  intros. unfold close_btyp_wrt_btyp, close_ptyp_wrt_ptyp.
  apply btyp_to_ptyp_close_rec.
Qed.

Lemma btyp_to_bskl_close_rec : forall B α k,
  btyp_to_bskl (close_btyp_wrt_btyp_rec k α B)
  = close_bskl_wrt_bskl_rec k α (btyp_to_bskl B).
Proof.
  intros B; induction B; intros α0 k; default_simp.
Qed.

Lemma btyp_to_bskl_close : forall B α,
  btyp_to_bskl (close_btyp_wrt_btyp α B)
  = close_bskl_wrt_bskl α (btyp_to_bskl B).
Proof.
  intros. unfold close_btyp_wrt_btyp, close_bskl_wrt_bskl.
  apply btyp_to_bskl_close_rec.
Qed.

Lemma btyp_to_bskl_open_rec : forall B B' k,
  btyp_to_bskl (open_btyp_wrt_btyp_rec k B' B)
  = open_bskl_wrt_bskl_rec k (btyp_to_bskl B') (btyp_to_bskl B).
Proof.
  intros B; induction B; intros B' k; default_simp.
Qed.

Lemma btyp_to_bskl_open : forall B B',
  btyp_to_bskl (open_btyp_wrt_btyp B B')
  = open_bskl_wrt_bskl (btyp_to_bskl B) (btyp_to_bskl B').
Proof.
  intros. unfold open_btyp_wrt_btyp, open_bskl_wrt_bskl.
  apply btyp_to_bskl_open_rec.
Qed.

(** ⭐ A MONOTYPE HAS ONLY ONE COLOURING — which is what lets the two
    flexible rows of the transport rebuild their answer: a definition
    [α̂ ≔ τ] is a monotype ([a_wf_aenv__flex_def]), so whatever colouring
    the recursive call produces for it IS the synthesised painting the
    [__flex_l] / [__flex_r] refinement rows demand. *)
Lemma btyp_to_bskl_mono_syn : forall B,
  mono_ptyp (btyp_to_ptyp B) ->
  btyp_to_bskl B = ptyp_to_bskl_syn (btyp_to_ptyp B).
Proof.
  unfold ptyp_to_bskl_syn.
  intros B; induction B; intros Hm; simpl in *; try inversion Hm; subst; auto.
  f_equal; auto.
Qed.

(* --- §4b  the transport's kit (2): a Δ-variable moved into the context -- *)

(** Consistency binds a ∀'s witness in Θ, refinement binds it in Δ.  Going
    Δ → Θ is a WEAKENING and holds — [__var] already accepts either side and
    [__tophole]'s [{{ Θ ⨟ ∅ ⊢ₚₛ P }}a] only grows.  (The reverse direction is
    false; the transport is arranged so it is never needed.) *)
Lemma a_wf_pskl_delta_to_ctx : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall α Δ', Δ [<=] add α Δ' ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ' ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P H; induction H; intros α0 Δ' Hsub.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Ht].
    + destruct (α == α0) as [-> | Hne].
      * right. left. unfold binds; simpl; left; reflexivity.
      * left. clear - HΔ Hsub Hne. fsetdec.
    + right. destruct Ht as [Hb | [Hb | [τ Hb]]];
        [ left | right; left | right; right; exists τ ];
        unfold binds; simpl; right; exact Hb.
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L `union` singleton α0). intros β Hβ.
    apply H0; [ clear - Hβ; fsetdec | clear - Hsub; fsetdec ].
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole;
      [ assumption | apply IHa_wf_pskl; clear; fsetdec ].
Qed.

(* --- §4c  the transport's kit (3): renaming a Δ-variable --------------- *)

(** The refinement rules never look a Δ-variable up in Θ, so a Δ-member can
    be renamed.  This is what turns the ONE fresh witness the transport's
    [__all] row produces into the cofinite family the rule demands.
    [α ∉ dom Θ] is what makes the two payload-carrying rows ([__hole]'s
    fill, the flexible definitions) invisible to the substitution. *)
Lemma ad_refine_syn_rename_delta : forall Θ Δ0 Q P,
  {{ Θ ⨟ Δ0 ⊢ᵣ Q ⊳ P }}ad ->
  {{ ⊢ Θ }}a ->
  forall α β Δ,
  Δ0 [=] add α Δ ->
  α `notin` dom Θ `union` Δ ->
  {{ Θ ⨟ (add β Δ) ⊢ᵣ (subst_bskl_in_bskl (bskl_var_f β) α Q)
                  ⊳ (subst_bskl_in_bskl (bskl_var_f β) α P) }}ad.
Proof.
  intros Θ Δ0 Q P H; induction H; intros Hwf α0 β Δ' Heq Hα; simpl.
  - (* unit *) apply ad_refine_syn__unit.
  - (* var *)
    destruct_if as [Heqα | Hne].
    + apply ad_refine_syn__var. left. clear; fsetdec.
    + apply ad_refine_syn__var.
      destruct H as [HΔ | Ht]; [ left | right; exact Ht ].
      clear - HΔ Heq Hne. fsetdec.
  - (* arrow *) apply ad_refine_syn__arrow; auto.
  - (* all : the binder goes into Δ *)
    apply ad_refine_syn__all
      with (L := L `union` singleton α0 `union` singleton β
                   `union` dom Θ `union` Δ').
    intros γ Hγ.
    rewrite !subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      try solve [ clear - Hγ; fsetdec | apply lc_bskl_var_f ].
    eapply ad_refine_syn_delta_mono;
      [ apply (H0 γ ltac:(clear - Hγ; solve_notin_auto) Hwf α0 β (add γ Δ'));
          [ clear - Heq; fsetdec | clear - Hα Hγ; fsetdec ]
      | clear; fsetdec ].
  - (* hole : the fill is well-formed in Θ alone, so α0 cannot occur in it *)
    assert (Hfr : α0 `notin` ftvar_in_pskl P).
    { intros Hin.
      apply a_scope_pskl_of_wf in H.
      apply a_scope_pskl_ftv_dom in H.
      clear - H Hin Hα. fsetdec. }
    rewrite subst_bskl_in_bskl_fresh_eq;
      [ | rewrite ftvar_in_bskl_syn; exact Hfr ].
    apply ad_refine_syn__hole. exact H.
  - (* tophole_remove *) apply ad_refine_syn__tophole_remove; auto.
  - (* tophole_fill : the binder goes into Θ *)
    apply ad_refine_syn__tophole_fill
      with (L := L `union` singleton α0 `union` singleton β
                   `union` dom Θ `union` Δ').
    intros γ Hγ.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      try solve [ clear - Hγ; fsetdec | apply lc_bskl_var_f ].
    change (bskl_tophole (subst_bskl_in_bskl (bskl_var_f β) α0 Q))
      with (subst_bskl_in_bskl (bskl_var_f β) α0 (bskl_tophole Q)).
    apply (H0 γ ltac:(clear - Hγ; solve_notin_auto));
      [ apply a_wf_aenv__tvar; [ clear - Hγ; fsetdec | exact Hwf ]
      | exact Heq
      | simpl; clear - Hα Hγ; fsetdec ].
  - (* tophole_keep *)
    apply ad_refine_syn__tophole_keep; [ | auto ].
    inversion H; subst; simpl;
      [ apply guarded_bskl__unit
      | destruct_if; apply guarded_bskl__var
      | apply guarded_bskl__arrow; apply subst_bskl_in_bskl_lc_bskl;
        solve [ assumption | apply lc_bskl_var_f ] ].
  - (* flex_l : the definition lives in Θ, so α0 cannot occur in it *)
    assert (Hne : α <> α0)
      by (intros ->; apply binds_In in H; clear - H Hα; fsetdec).
    assert (Hfr : α0 `notin` ftvar_in_ptyp τ).
    { intros Hin.
      assert (Hwfτ : a_wf_ptyp Θ τ)
        by (eapply a_wf_aenv_binds_def_wf; eassumption).
      assert (Ht : a_binds_tvar α0 Θ)
        by (eapply a_wf_ptyp_ftv_tvarish; eassumption).
      destruct Ht as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb;
        clear - Hb Hα; fsetdec. }
    destruct_if as [Heqα | Hne2]; [ contradiction | ].
    eapply ad_refine_syn__flex_l; [ exact H | ].
    pose proof (IHad_refine_syn Hwf α0 β Δ' Heq Hα) as IH2.
    rewrite (subst_bskl_in_bskl_fresh_eq (ptyp_to_bskl_syn τ)
               (bskl_var_f β) α0) in IH2;
      [ exact IH2 | rewrite ftvar_in_bskl_ptyp_syn; exact Hfr ].
  - (* flex_r *)
    assert (Hne : α <> α0)
      by (intros ->; apply binds_In in H; clear - H Hα; fsetdec).
    assert (Hfr : α0 `notin` ftvar_in_ptyp τ).
    { intros Hin.
      assert (Hwfτ : a_wf_ptyp Θ τ)
        by (eapply a_wf_aenv_binds_def_wf; eassumption).
      assert (Ht : a_binds_tvar α0 Θ)
        by (eapply a_wf_ptyp_ftv_tvarish; eassumption).
      destruct Ht as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb;
        clear - Hb Hα; fsetdec. }
    destruct_if as [Heqα | Hne2]; [ contradiction | ].
    eapply ad_refine_syn__flex_r; [ exact H | ].
    pose proof (IHad_refine_syn Hwf α0 β Δ' Heq Hα) as IH2.
    rewrite (subst_bskl_in_bskl_fresh_eq (ptyp_to_bskl_syn τ)
               (bskl_var_f β) α0) in IH2;
      [ exact IH2 | rewrite ftvar_in_bskl_ptyp_syn; exact Hfr ].
Qed.

(* --- §4d  the transport's kit (4): the OCCURRENCE lemma ---------------- *)

Lemma ptyp_to_uskl_syn_open : forall A α,
  ptyp_to_uskl_syn (open_ptyp_wrt_ptyp A (ptyp_var_f α))
  = open_uskl_wrt_uskl (ptyp_to_uskl_syn A) (uskl_var_f α).
Proof.
  intros A α. unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  rewrite ptyp_to_pskl_open, pskl_to_bskl_syn_open, bskl_to_uskl_open.
  reflexivity.
Qed.

(** ⭐ A free variable of a TYPE-PAINTING subject either survives into the
    consistency's target or escapes through a DEFINITION (as the defined
    variable itself, at [__flex_l], or into a definition's body, at
    [__flex_r]).  This is what upgrades the transport's visibility invariant
    ("in Δ or a tvar of Θr") to the Δ-FREENESS that [ad_refine_syn__hole]
    demands of its fill: at that row the target is a synthesised painting
    well-formed at EMPTY Δ, so all three disjuncts land in [dom Θr], and a
    Δ-bound ∀ witness — fresh for Θr — is excluded. *)
Lemma ad_pat_consis_subject_ftv : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  forall A, R = ptyp_to_uskl_syn A ->
  forall γ, γ `in` ftvar_in_ptyp A ->
  γ `in` ftvar_in_bskl Qt \/ a_flex_tvar Θ γ \/
  (exists β τ, binds β (abind_flex_mono_def τ) Θ /\ γ `in` ftvar_in_ptyp τ).
Proof.
  intros Ψ Θ R Qt H; induction H; intros A HeqA γ Hγ;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in HeqA.
  - (* unit *)
    destruct A; simpl in HeqA, Hγ; try discriminate.
    clear - Hγ; fsetdec.
  - (* var *)
    destruct A; simpl in HeqA, Hγ; try discriminate;
      try solve [ clear - Hγ; fsetdec ].
    inversion HeqA; subst. left. simpl. exact Hγ.
  - (* arrow *)
    destruct A; simpl in HeqA, Hγ; try discriminate;
      try solve [ clear - Hγ; fsetdec ].
    inversion HeqA; subst.
    assert (Hd : γ `in` ftvar_in_ptyp A1 \/ γ `in` ftvar_in_ptyp A2)
      by (clear - Hγ; fsetdec).
    destruct Hd as [Hd | Hd];
      [ destruct (IHad_pat_consis1 _ eq_refl γ Hd) as [Hl | [Hm | Hr]]
      | destruct (IHad_pat_consis2 _ eq_refl γ Hd) as [Hl | [Hm | Hr]] ];
      solve [ left; simpl; clear - Hl; fsetdec
            | right; left; exact Hm
            | right; right; exact Hr ].
  - (* forall_inh_tagged : a type painting is never [uskl_all_etag] *)
    destruct A; simpl in HeqA, Hγ; try discriminate;
      try solve [ clear - Hγ; fsetdec ].
  - (* forall_inh_untagged *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA, Hγ;
      try discriminate; try solve [ clear - Hγ; fsetdec ].
    inversion HeqA; subst.
    destruct (atom_fresh (L `union` singleton γ `union` dom Θ
                            `union` ftvar_in_ptyp A0 `union` ftvar_in_bskl Q))
      as [β Hβ].
    assert (Hopen : γ `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A0 (ptyp_var_f β))).
    { pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A0 (ptyp_var_f β)) as Hlow.
      clear - Hγ Hlow. fsetdec. }
    destruct (H0 β ltac:(clear - Hβ; solve_notin_auto)
                (open_ptyp_wrt_ptyp A0 (ptyp_var_f β))
                ltac:(rewrite ptyp_to_uskl_syn_open; reflexivity)
                γ Hopen) as [Hl | [Hm | Hr]].
    + left. simpl.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β)) as Hup.
      simpl in Hup. clear - Hl Hup Hβ. fsetdec.
    + right; left.
      destruct Hm as [Hb | [τ Hb]]; [ left | right; exists τ ];
        (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
         [ discriminate | exact Hb' ]).
    + right; right. destruct Hr as [β' [τ [Hb Hin]]]. exists β', τ.
      split; [ | exact Hin ].
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate | exact Hb' ].
  - (* forall_syn_tagged *)
    destruct A; simpl in HeqA, Hγ; try discriminate;
      try solve [ clear - Hγ; fsetdec ].
  - (* forall_syn *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA, Hγ;
      try discriminate; try solve [ clear - Hγ; fsetdec ].
    inversion HeqA; subst.
    destruct (atom_fresh (L `union` singleton γ `union` dom Θ
                            `union` ftvar_in_ptyp A0 `union` ftvar_in_bskl Q))
      as [β Hβ].
    assert (Hopen : γ `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A0 (ptyp_var_f β))).
    { pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A0 (ptyp_var_f β)) as Hlow.
      clear - Hγ Hlow. fsetdec. }
    destruct (H0 β ltac:(clear - Hβ; solve_notin_auto)
                (open_ptyp_wrt_ptyp A0 (ptyp_var_f β))
                ltac:(rewrite ptyp_to_uskl_syn_open; reflexivity)
                γ Hopen) as [Hl | [Hm | Hr]].
    + left. simpl.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β)) as Hup.
      simpl in Hup. clear - Hl Hup Hβ. fsetdec.
    + right; left.
      destruct Hm as [Hb | [τ Hb]]; [ left | right; exists τ ];
        (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
         [ discriminate | exact Hb' ]).
    + right; right. destruct Hr as [β' [τ [Hb Hin]]]. exists β', τ.
      split; [ | exact Hin ].
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate | exact Hb' ].
  - (* ghostg *)
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  - (* topholeg *)
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  - (* hole *)
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  - (* tophole *)
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  - (* tophole_inh *)
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  - (* tophole_drop *)
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  - (* flex_l : the subject IS the defined variable *)
    destruct A; simpl in HeqA, Hγ; try discriminate;
      try solve [ clear - Hγ; fsetdec ].
    inversion HeqA; subst.
    apply singleton_1 in Hγ; subst.
    right; left; right; exists τ. assumption.
  - (* flex_r : escape into the definition's body *)
    destruct (IHad_pat_consis A ltac:(exact HeqA) γ Hγ) as [Hl | [Hm | Hr]].
    + right; right. exists α, τ. split; [ exact H | ].
      rewrite ftvar_in_bskl_ptyp_syn in Hl. exact Hl.
    + right; left; exact Hm.
    + right; right; exact Hr.
Qed.

(* --- §4e  the transport's kit (5): renaming a rigid Θ-variable --------- *)

(** The block of plain rigid variables the [__tophole_fill] rows stack on
    top of the context.  Only ever inspected to know that no DEFINITION
    sits above the renamed variable. *)
Inductive a_tvar_block : aenv -> Prop :=
| a_tvar_block__nil : a_tvar_block nil
| a_tvar_block__cons : forall α Θ,
    a_tvar_block Θ -> a_tvar_block ((α ~ abind_tvar) ++ Θ).

Lemma a_tvar_block_binds_def_inv : forall Θa α τ Θ,
  a_tvar_block Θa ->
  binds α (abind_flex_mono_def τ) (Θa ++ Θ) ->
  binds α (abind_flex_mono_def τ) Θ.
Proof.
  intros Θa α τ Θ Hb; induction Hb; intros Hbind; simpl_env in Hbind.
  - exact Hbind.
  - apply IHHb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hbind) as [[_ Hc] | Hb'];
      [ discriminate | exact Hb' ].
Qed.

Lemma a_wf_aenv_strip_prefix : forall Θa Θ,
  {{ ⊢ (Θa ++ Θ) }}a -> {{ ⊢ Θ }}a.
Proof.
  intros Θa; induction Θa as [ | [y c] Θa' IH ]; intros Θ Hwf.
  - rewrite app_nil_l in Hwf; exact Hwf.
  - apply IH. inversion Hwf; subst; assumption.
Qed.

Lemma binds_swap_mid_tvar : forall (x : atom) (c : abind) Θa α Θ β,
  binds x c (Θa ++ (α ~ abind_tvar) ++ Θ) ->
  x <> α ->
  binds x c (Θa ++ (β ~ abind_tvar) ++ Θ).
Proof.
  intros * Hb Hne.
  apply binds_app_1 in Hb as [Hb | Hb]; [ apply binds_app_2; exact Hb | ].
  apply binds_app_1 in Hb as [Hb | Hb].
  - destruct Hb as [Heq | []]; inversion Heq; subst; contradiction.
  - apply binds_app_3; unfold binds; simpl; right; exact Hb.
Qed.

Lemma subst_pskl_to_bskl_syn : forall P α β,
  subst_bskl_in_bskl (bskl_var_f β) α (pskl_to_bskl_syn P)
  = pskl_to_bskl_syn (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros P α β; induction P; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

(** Skeleton well-formedness under the same rename.  No condition on the
    block: [a_wf_pskl] reads the context only through [a_binds_tvar], and
    the renamed slot is a plain rigid variable on both sides. *)
Lemma a_wf_pskl_rename_tvar_eq : forall Θ0 Δ P,
  {{ Θ0 ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θa α Θ β,
  Θ0 = Θa ++ (α ~ abind_tvar) ++ Θ ->
  β `notin` Δ ->
  {{ (Θa ++ (β ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ₚₛ
    (subst_pskl_in_pskl (pskl_var_f β) α P) }}a.
Proof.
  intros Θ0 Δ P H; induction H; intros Θa α0 Θ' β Heq Hβ; subst; simpl.
  - apply a_wf_pskl__unit.
  - destruct_if as [Heqα | Hne].
    + apply a_wf_pskl__var. right. left.
      apply binds_app_3. unfold binds; simpl; left; reflexivity.
    + apply a_wf_pskl__var.
      destruct H as [HΔ | Ht]; [ left; exact HΔ | right ].
      destruct Ht as [Hb | [Hb | [τ Hb]]];
        [ left | right; left | right; right; exists τ ];
        (apply binds_swap_mid_tvar with (α := α0);
         [ exact Hb | exact Hne ]).
  - apply a_wf_pskl__arrow;
      [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      solve [ reflexivity | exact Hβ ].
  - apply a_wf_pskl__all with (L := L `union` singleton α0 `union` singleton β).
    intros γ Hγ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hγ; fsetdec | apply lc_pskl_var_f ].
    apply H0; [ clear - Hγ; fsetdec | reflexivity | clear - Hβ Hγ; fsetdec ].
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole.
    + inversion H; subst; simpl;
        [ apply guarded_pskl__unit
        | destruct_if; apply guarded_pskl__var
        | apply guarded_pskl__arrow; apply subst_pskl_in_pskl_lc_pskl;
          solve [ assumption | apply lc_pskl_var_f ] ].
    + apply IHa_wf_pskl; [ reflexivity | clear; fsetdec ].
Qed.

(** ⭐ Renaming a rigid variable of the CONTEXT.  This is what the
    transport's [__tophole_fill] row needs — the [__all] row's Δ analogue is
    §4c.  [a_tvar_block Θa] says no DEFINITION sits above the renamed slot,
    which is how the two flexible rows keep their payload untouched: a
    definition then lives BELOW [α], so [α] cannot occur in it. *)
Lemma ad_refine_syn_rename_tvar : forall Θ0 Δ Q P,
  {{ Θ0 ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
  forall Θa α Θ β,
  Θ0 = Θa ++ (α ~ abind_tvar) ++ Θ ->
  a_tvar_block Θa ->
  {{ ⊢ Θ0 }}a ->
  β `notin` dom Θ0 `union` Δ ->
  {{ (Θa ++ (β ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣ
    (subst_bskl_in_bskl (bskl_var_f β) α Q)
    ⊳ (subst_bskl_in_bskl (bskl_var_f β) α P) }}ad.
Proof.
  intros Θ0 Δ Q P H; induction H;
    intros Θa α0 Θ' β Heq Hblk Hwf Hβ; subst; simpl.
  - (* unit *) apply ad_refine_syn__unit.
  - (* var *)
    destruct_if as [Heqα | Hne].
    + apply ad_refine_syn__var. right. left.
      apply binds_app_3. unfold binds; simpl; left; reflexivity.
    + apply ad_refine_syn__var.
      destruct H as [HΔ | Ht]; [ left; exact HΔ | right ].
      destruct Ht as [Hb | [Hb | [τ Hb]]];
        [ left | right; left | right; right; exists τ ];
        (apply binds_swap_mid_tvar with (α := α0);
         [ exact Hb | exact Hne ]).
  - (* arrow *)
    apply ad_refine_syn__arrow;
      [ apply IHad_refine_syn1 | apply IHad_refine_syn2 ];
      solve [ reflexivity | exact Hblk | exact Hwf | exact Hβ ].
  - (* all : the binder goes into Δ *)
    apply ad_refine_syn__all
      with (L := L `union` singleton α0 `union` singleton β).
    intros γ Hγ.
    rewrite !subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      try solve [ clear - Hγ; fsetdec | apply lc_bskl_var_f ].
    apply H0;
      [ clear - Hγ; fsetdec | reflexivity | exact Hblk | exact Hwf
      | clear - Hβ Hγ; fsetdec ].
  - (* hole *)
    rewrite subst_pskl_to_bskl_syn.
    apply ad_refine_syn__hole.
    eapply a_wf_pskl_rename_tvar_eq; [ exact H | reflexivity | clear; fsetdec ].
  - (* tophole_remove *)
    apply ad_refine_syn__tophole_remove.
    apply IHad_refine_syn; solve [ reflexivity | exact Hblk | exact Hwf | exact Hβ ].
  - (* tophole_fill : the binder goes into Θ, on top of the block *)
    apply ad_refine_syn__tophole_fill
      with (L := L `union` singleton α0 `union` singleton β
                   `union` dom (Θa ++ (α0 ~ abind_tvar) ++ Θ')).
    intros γ Hγ.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      try solve [ clear - Hγ; fsetdec | apply lc_bskl_var_f ].
    change (bskl_tophole (subst_bskl_in_bskl (bskl_var_f β) α0 Q))
      with (subst_bskl_in_bskl (bskl_var_f β) α0 (bskl_tophole Q)).
    simpl_env.
    apply (H0 γ ltac:(clear - Hγ; solve_notin_auto)
             ((γ ~ abind_tvar) ++ Θa) α0 Θ' β);
      [ simpl_env; reflexivity
      | apply a_tvar_block__cons; exact Hblk
      | apply a_wf_aenv__tvar; [ clear - Hγ; fsetdec | exact Hwf ]
      | simpl_env in Hβ; simpl_env; clear - Hβ Hγ; fsetdec ].
  - (* tophole_keep *)
    apply ad_refine_syn__tophole_keep;
      [ | apply IHad_refine_syn;
          solve [ reflexivity | exact Hblk | exact Hwf | exact Hβ ] ].
    inversion H; subst; simpl;
      [ apply guarded_bskl__unit
      | destruct_if; apply guarded_bskl__var
      | apply guarded_bskl__arrow; apply subst_bskl_in_bskl_lc_bskl;
        solve [ assumption | apply lc_bskl_var_f ] ].
  - (* flex_l : the definition lives BELOW the renamed slot *)
    assert (Hbτ : binds α (abind_flex_mono_def τ) Θ')
      by (eapply a_tvar_block_binds_def_inv;
          [ exact Hblk
          | eapply binds_remove_mid;
              [ exact H
              | intros ->; apply binds_mid_eq in H;
                [ discriminate | eapply a_wf_aenv_uniq; exact Hwf ] ] ]).
    assert (Hne : α <> α0)
      by (intros ->; apply binds_mid_eq in H;
          [ discriminate | eapply a_wf_aenv_uniq; exact Hwf ]).
    assert (Hfr : α0 `notin` ftvar_in_ptyp τ).
    { intros Hin.
      assert (Hwf' : {{ ⊢ Θ' }}a)
        by (eapply a_wf_aenv_strip_prefix;
            eapply a_wf_aenv_strip_prefix with (Θa := Θa); simpl_env; exact Hwf).
      assert (Hwfτ : a_wf_ptyp Θ' τ)
        by (eapply a_wf_aenv_binds_def_wf; eassumption).
      assert (Ht : a_binds_tvar α0 Θ')
        by (eapply a_wf_ptyp_ftv_tvarish; eassumption).
      assert (Huq : uniq (Θa ++ (α0 ~ abind_tvar) ++ Θ'))
        by (eapply a_wf_aenv_uniq; exact Hwf).
      destruct Ht as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb;
        clear - Hb Huq; solve_uniq. }
    destruct_if as [Heqα | Hne2]; [ contradiction | ].
    eapply ad_refine_syn__flex_l;
      [ apply binds_app_3; unfold binds; simpl; right; exact Hbτ | ].
    pose proof (IHad_refine_syn Θa α0 Θ' β eq_refl Hblk Hwf Hβ) as IH2.
    rewrite (subst_bskl_in_bskl_fresh_eq (ptyp_to_bskl_syn τ)
               (bskl_var_f β) α0) in IH2;
      [ exact IH2 | rewrite ftvar_in_bskl_ptyp_syn; exact Hfr ].
  - (* flex_r *)
    assert (Hbτ : binds α (abind_flex_mono_def τ) Θ')
      by (eapply a_tvar_block_binds_def_inv;
          [ exact Hblk
          | eapply binds_remove_mid;
              [ exact H
              | intros ->; apply binds_mid_eq in H;
                [ discriminate | eapply a_wf_aenv_uniq; exact Hwf ] ] ]).
    assert (Hne : α <> α0)
      by (intros ->; apply binds_mid_eq in H;
          [ discriminate | eapply a_wf_aenv_uniq; exact Hwf ]).
    assert (Hfr : α0 `notin` ftvar_in_ptyp τ).
    { intros Hin.
      assert (Hwf' : {{ ⊢ Θ' }}a)
        by (eapply a_wf_aenv_strip_prefix;
            eapply a_wf_aenv_strip_prefix with (Θa := Θa); simpl_env; exact Hwf).
      assert (Hwfτ : a_wf_ptyp Θ' τ)
        by (eapply a_wf_aenv_binds_def_wf; eassumption).
      assert (Ht : a_binds_tvar α0 Θ')
        by (eapply a_wf_ptyp_ftv_tvarish; eassumption).
      assert (Huq : uniq (Θa ++ (α0 ~ abind_tvar) ++ Θ'))
        by (eapply a_wf_aenv_uniq; exact Hwf).
      destruct Ht as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb;
        clear - Hb Huq; solve_uniq. }
    destruct_if as [Heqα | Hne2]; [ contradiction | ].
    eapply ad_refine_syn__flex_r;
      [ apply binds_app_3; unfold binds; simpl; right; exact Hbτ | ].
    pose proof (IHad_refine_syn Θa α0 Θ' β eq_refl Hblk Hwf Hβ) as IH2.
    rewrite (subst_bskl_in_bskl_fresh_eq (ptyp_to_bskl_syn τ)
               (bskl_var_f β) α0) in IH2;
      [ exact IH2 | rewrite ftvar_in_bskl_ptyp_syn; exact Hfr ].
Qed.

(* --- §4f  the TARGET TRANSPORT ----------------------------------------- *)

(** The [__hole] answer, which every row of the transport shares: a hole
    source is always answered by the ALL-SYNTHESISED painting of the
    annotation.  Its well-formedness — the rule wants it at EMPTY Δ, i.e.
    Δ-FREE — is what the occurrence lemma (§4d) supplies: the target is a
    synthesised painting well-formed at empty Δ, so each of the three
    disjuncts lands in [Θr]. *)
Lemma transport_hole_answer : forall Ψ Θc A Qt Θr Δ P,
  {{ Ψ ⨟ Θc ⊢ˢ (ptyp_to_uskl_syn A) ∼ Qt }}ad ->
  {{ ⊢ Θr }}a ->
  lc_ptyp A ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θc ->
               binds β (abind_flex_mono_def τ) Θr) ->
  (forall γ, a_flex_tvar Θc γ -> a_binds_tvar γ Θr) ->
  Qt = pskl_to_bskl_syn P ->
  {{ Θr ⨟ empty ⊢ₚₛ P }}a ->
  exists B, btyp_to_ptyp B = A /\ {{ Θr ⨟ Δ ⊢ᵣ bskl_hole ⊳ (btyp_to_bskl B) }}ad.
Proof.
  intros Ψ Θc A Qt Θr Δ P Hc Hwfr HlcA Hdefs Hflex HQt HwfP.
  exists (ptyp_to_btyp_syn A). split; [ apply btyp_to_ptyp_ptyp_to_btyp_syn | ].
  rewrite btyp_to_bskl_ptyp_to_btyp_syn.
  apply ad_refine_syn__hole.
  apply a_scope_pskl_of_ptyp_vis; [ exact HlcA | ].
  intros γ Hγ. right.
  destruct (ad_pat_consis_subject_ftv Hc A eq_refl Hγ) as [Hl | [Hm | Hr]].
  - subst Qt. rewrite ftvar_in_bskl_syn in Hl.
    apply a_scope_pskl_of_wf in HwfP.
    eapply a_scope_pskl_ftv_tvarish; eassumption.
  - apply Hflex; exact Hm.
  - destruct Hr as [β [τ [Hb Hin]]].
    assert (Hwfτ : a_wf_ptyp Θr τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwfr | apply Hdefs; exact Hb ]).
    eapply a_wf_ptyp_ftv_tvarish; eassumption.
Qed.

(** ⭐ THE TARGET TRANSPORT.  See the plan below for why the two contexts
    are decoupled and what each hypothesis buys. *)
Lemma ad_refine_syn_target_transport : forall Ψ Θc R Qt,
  {{ Ψ ⨟ Θc ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θc }}a ->
  forall A, R = ptyp_to_uskl_syn A -> lc_ptyp A ->
  forall Θr Δ Qb,
  {{ ⊢ Θr }}a ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θc ->
               binds β (abind_flex_mono_def τ) Θr) ->
  (forall γ, a_flex_tvar Θc γ -> a_binds_tvar γ Θr) ->
  (forall γ, γ `in` ftvar_in_ptyp A -> γ `in` Δ \/ a_binds_tvar γ Θr) ->
  {{ Θr ⨟ Δ ⊢ᵣ Qb ⊳ Qt }}ad ->
  exists B, btyp_to_ptyp B = A /\ {{ Θr ⨟ Δ ⊢ᵣ Qb ⊳ (btyp_to_bskl B) }}ad.
Proof.
  intros Ψ Θc R Qt H; induction H;
    intros Hwfc A HeqA HlcA Θr Δ Qb Hwfr Hdefs Hflex Hvis Href;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in HeqA.
  - (* consis unit : the target IS the answer *)
    destruct A; simpl in HeqA; try discriminate.
    exists btyp_unit. split; [ reflexivity | exact Href ].
  - (* consis var : the target IS the answer *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA; try discriminate.
    assert (Heqv : α1 = α) by (inversion HeqA; reflexivity). subst α1.
    exists (btyp_var_f α). split; [ reflexivity | exact Href ].
  - (* consis arrow *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA; try discriminate.
    inversion HeqA; subst. clear HeqA.
    inversion HlcA; subst.
    revert Hwfr Hdefs Hflex Hvis.
    remember (bskl_arrow Q1 Q2) as Qt0 eqn:HQt.
    assert (Hc : {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn (ptyp_arrow A1 A2))
                   ∼ (bskl_arrow Q1 Q2) }}ad)
      by (unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl;
          eapply ad_pat_consis__arrow; eassumption).
    revert HQt.
    induction Href as
      [ Θx Δx
      | Θx Δx αx Hin
      | Θx Δx Qs1 Qs2 Pt1 Pt2 HrA IHA HrB IHB
      | Lx Θx Δx Qs Pt Hfam IHfam
      | Θx Δx Pf Hwff
      | Θx Δx Qs Pt Hr IHr
      | Lx Θx Δx Qs Pt Hfam IHfam
      | Θx Δx Qs Pt Hg Hr IHr
      | Θx Δx αx τx Pt Hb Hr IHr
      | Θx Δx αx τx Qs Hb Hr IHr ];
      intros HQt Hwfr Hdefs Hflex Hvis; try discriminate HQt.
    + (* refine arrow *)
      inversion HQt; subst.
      destruct (IHad_pat_consis1 Hwfc A1 eq_refl ltac:(assumption)
                  Θx Δx Qs1 Hwfr Hdefs Hflex
                  ltac:(intros γ Hγ; apply Hvis; simpl; clear - Hγ; solve_notin_auto)
                  HrA) as [B1 [HeqB1 HrA']].
      destruct (IHad_pat_consis2 Hwfc A2 eq_refl ltac:(assumption)
                  Θx Δx Qs2 Hwfr Hdefs Hflex
                  ltac:(intros γ Hγ; apply Hvis; simpl; clear - Hγ; solve_notin_auto)
                  HrB) as [B2 [HeqB2 HrB']].
      exists (btyp_arrow B1 B2). split;
        [ simpl; rewrite HeqB1, HeqB2; reflexivity
        | simpl; apply ad_refine_syn__arrow; assumption ].
    + (* refine hole *)
      eapply transport_hole_answer;
        [ exact Hc | exact Hwfr | exact HlcA | exact Hdefs | exact Hflex
        | symmetry; exact HQt | exact Hwff ].
    + (* refine tophole_remove *)
      destruct (IHr HQt Hwfr Hdefs Hflex Hvis) as [B [HeqB Href']].
      exists B. split;
        [ exact HeqB | apply ad_refine_syn__tophole_remove; exact Href' ].
    + (* refine flex_l *)
      destruct (IHr HQt Hwfr Hdefs Hflex Hvis) as [B [HeqB Href']].
      exists B. split;
        [ exact HeqB | eapply ad_refine_syn__flex_l; eassumption ].
  - (* consis forall_inh_tagged : dead on the subject's shape *)
    destruct A; simpl in HeqA; discriminate.
  - (* consis forall_inh_untagged *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA; try discriminate.
    inversion HeqA; subst. clear HeqA.
    revert Hwfr Hdefs Hflex Hvis.
    remember (bskl_all_inh Q) as Qt0 eqn:HQt.
    assert (Hc : {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn (ptyp_all A0)) ∼ (bskl_all_inh Q) }}ad)
      by (unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl;
          eapply ad_pat_consis__forall_inh_untagged with (L := L); eassumption).
    revert HQt.
    induction Href as
      [ Θx Δx
      | Θx Δx αx Hin
      | Θx Δx Qs1 Qs2 Pt1 Pt2 HrA IHA HrB IHB
      | Lx Θx Δx Qs Pt Hfam IHfam
      | Θx Δx Pf Hwff
      | Θx Δx Qs Pt Hr IHr
      | Lx Θx Δx Qs Pt Hfam IHfam
      | Θx Δx Qs Pt Hg Hr IHr
      | Θx Δx αx τx Pt Hb Hr IHr
      | Θx Δx αx τx Qs Hb Hr IHr ];
      intros HQt Hwfr Hdefs Hflex Hvis; try discriminate HQt.
    + (* refine all : the binder stays in Δ *)
      inversion HQt; subst.
      destruct (atom_fresh (L `union` Lx `union` dom Θ `union` dom Θx
                              `union` Δx `union` ftvar_in_ptyp A0
                              `union` ftvar_in_bskl Q `union` ftvar_in_bskl Qs))
        as [α Hα].
      destruct (H0 α ltac:(clear - Hα; solve_notin_auto)
                  ltac:(apply a_wf_aenv__tvar; [ clear - Hα; solve_notin_auto | exact Hwfc ])
                  (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))
                  ltac:(rewrite ptyp_to_uskl_syn_open; reflexivity)
                  ltac:(inversion HlcA; subst; auto)
                  Θx (add α Δx) (open_bskl_wrt_bskl Qs (bskl_var_f α))
                  Hwfr
                  ltac:(intros β τ Hbd;
                        destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hcx] | Hb'];
                        [ discriminate | apply Hdefs; exact Hb' ])
                  ltac:(intros γ [Hbd | [τ Hbd]];
                        (destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hcx] | Hb'];
                         [ discriminate
                         | apply Hflex; solve [ left; exact Hb'
                                              | right; exists τ; exact Hb' ] ]))
                  ltac:(intros γ Hγ;
                        pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper
                                      A0 (ptyp_var_f α)) as Hup;
                        simpl in Hup;
                        destruct (γ == α) as [Heγ | Hne];
                        [ left; subst; clear; fsetdec
                        | assert (Hγ0 : γ `in` ftvar_in_ptyp A0)
                            by (clear - Hγ Hup Hne; fsetdec);
                          destruct (Hvis γ ltac:(simpl; exact Hγ0)) as [Hd | Ht];
                          [ left; clear - Hd; fsetdec | right; exact Ht ] ])
                  (Hfam α ltac:(clear - Hα; solve_notin_auto)))
        as [B0 [HeqB0 Href0]].
      exists (btyp_all_inh (close_btyp_wrt_btyp α B0)). split.
      * simpl. rewrite btyp_to_ptyp_close, HeqB0.
        rewrite close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp;
          [ reflexivity | clear - Hα; fsetdec ].
      * simpl. apply ad_refine_syn__all
          with (L := L `union` Lx `union` dom Θx `union` Δx
                       `union` singleton α `union` ftvar_in_bskl Qs).
        intros β Hβ.
        pose proof (@ad_refine_syn_rename_delta _ _ _ _ Href0 Hwfr α β Δx
                      ltac:(clear; solve_notin_auto)
                      ltac:(clear - Hα; solve_notin_auto)) as Hren.
        rewrite <- subst_bskl_in_bskl_intro in Hren;
          [ | clear - Hα; fsetdec ].
        rewrite subst_bskl_in_bskl_spec in Hren.
        rewrite <- btyp_to_bskl_close in Hren.
        exact Hren.
    + (* refine hole *)
      eapply transport_hole_answer;
        [ exact Hc | exact Hwfr | exact HlcA | exact Hdefs | exact Hflex
        | symmetry; exact HQt | exact Hwff ].
    + (* refine tophole_remove *)
      destruct (IHr HQt Hwfr Hdefs Hflex Hvis) as [B [HeqB Href']].
      exists B. split;
        [ exact HeqB | apply ad_refine_syn__tophole_remove; exact Href' ].
    + (* refine flex_l *)
      destruct (IHr HQt Hwfr Hdefs Hflex Hvis) as [B [HeqB Href']].
      exists B. split;
        [ exact HeqB | eapply ad_refine_syn__flex_l; eassumption ].
  - (* consis forall_syn_tagged : dead *)
    destruct A; simpl in HeqA; discriminate.
  - (* consis forall_syn *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA; try discriminate.
    inversion HeqA; subst. clear HeqA.
    revert Hwfr Hdefs Hflex Hvis.
    remember (bskl_all_syn Q) as Qt0 eqn:HQt.
    assert (Hc : {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn (ptyp_all A0)) ∼ (bskl_all_syn Q) }}ad)
      by (unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl;
          eapply ad_pat_consis__forall_syn with (L := L); eassumption).
    revert HQt.
    induction Href as
      [ Θx Δx
      | Θx Δx αx Hin
      | Θx Δx Qs1 Qs2 Pt1 Pt2 HrA IHA HrB IHB
      | Lx Θx Δx Qs Pt Hfam IHfam
      | Θx Δx Pf Hwff
      | Θx Δx Qs Pt Hr IHr
      | Lx Θx Δx Qs Pt Hfam IHfam
      | Θx Δx Qs Pt Hg Hr IHr
      | Θx Δx αx τx Pt Hb Hr IHr
      | Θx Δx αx τx Qs Hb Hr IHr ];
      intros HQt Hwfr Hdefs Hflex Hvis; try discriminate HQt.
    + (* refine hole *)
      eapply transport_hole_answer;
        [ exact Hc | exact Hwfr | exact HlcA | exact Hdefs | exact Hflex
        | symmetry; exact HQt | exact Hwff ].
    + (* refine tophole_remove *)
      destruct (IHr HQt Hwfr Hdefs Hflex Hvis) as [B [HeqB Href']].
      exists B. split;
        [ exact HeqB | apply ad_refine_syn__tophole_remove; exact Href' ].
    + (* refine tophole_fill : the binder goes into Θr *)
      inversion HQt; subst.
      destruct (atom_fresh (L `union` Lx `union` dom Θ `union` dom Θx
                              `union` Δx `union` ftvar_in_ptyp A0
                              `union` ftvar_in_bskl Q `union` ftvar_in_bskl Qs))
        as [α Hα].
      destruct (H0 α ltac:(clear - Hα; solve_notin_auto)
                  ltac:(apply a_wf_aenv__tvar; [ clear - Hα; solve_notin_auto | exact Hwfc ])
                  (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))
                  ltac:(rewrite ptyp_to_uskl_syn_open; reflexivity)
                  ltac:(inversion HlcA; subst; auto)
                  ((α ~ abind_tvar) ++ Θx) Δx (bskl_tophole Qs)
                  ltac:(apply a_wf_aenv__tvar; [ clear - Hα; solve_notin_auto | exact Hwfr ])
                  ltac:(intros β τ Hbd;
                        destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hcx] | Hb'];
                        [ discriminate
                        | apply binds_app_3; apply Hdefs; exact Hb' ])
                  ltac:(intros γ [Hbd | [τ Hbd]];
                        (destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hcx] | Hb'];
                         [ discriminate
                         | eapply a_binds_tvar_mono;
                             [ apply aenv_tbinds_le_of_binds_le;
                               apply aenv_binds_le_weaken_l
                             | apply Hflex; solve [ left; exact Hb'
                                                  | right; exists τ; exact Hb' ] ] ]))
                  ltac:(intros γ Hγ;
                        pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper
                                      A0 (ptyp_var_f α)) as Hup;
                        simpl in Hup;
                        destruct (γ == α) as [Heγ | Hne];
                        [ right; left; subst;
                          unfold binds; simpl; left; reflexivity
                        | assert (Hγ0 : γ `in` ftvar_in_ptyp A0)
                            by (clear - Hγ Hup Hne; fsetdec);
                          destruct (Hvis γ ltac:(simpl; exact Hγ0)) as [Hd | Ht];
                          [ left; exact Hd
                          | right; eapply a_binds_tvar_mono;
                              [ apply aenv_tbinds_le_of_binds_le;
                                apply aenv_binds_le_weaken_l | exact Ht ] ] ])
                  (Hfam α ltac:(clear - Hα; solve_notin_auto)))
        as [B0 [HeqB0 Href0]].
      exists (btyp_all_syn (close_btyp_wrt_btyp α B0)). split.
      * simpl. rewrite btyp_to_ptyp_close, HeqB0.
        rewrite close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp;
          [ reflexivity | clear - Hα; fsetdec ].
      * simpl. apply ad_refine_syn__tophole_fill
          with (L := L `union` Lx `union` dom Θx `union` Δx
                       `union` singleton α `union` ftvar_in_bskl Qs).
        intros β Hβ.
        pose proof (@ad_refine_syn_rename_tvar _ _ _ _ Href0
                      (nil : aenv) α Θx β
                      ltac:(simpl_env; reflexivity)
                      a_tvar_block__nil
                      ltac:(apply a_wf_aenv__tvar;
                            [ clear - Hα; solve_notin_auto | exact Hwfr ])
                      ltac:(simpl_env; clear - Hβ Hα; solve_notin_auto)) as Hren.
        simpl_env in Hren. simpl in Hren.
        rewrite subst_bskl_in_bskl_fresh_eq in Hren;
          [ | clear - Hα; simpl; fsetdec ].
        rewrite subst_bskl_in_bskl_spec in Hren.
        rewrite <- btyp_to_bskl_close in Hren.
        exact Hren.
    + (* refine flex_l *)
      destruct (IHr HQt Hwfr Hdefs Hflex Hvis) as [B [HeqB Href']].
      exists B. split;
        [ exact HeqB | eapply ad_refine_syn__flex_l; eassumption ].
  - (* consis ghostg : dead *)
    destruct A; simpl in HeqA; discriminate.
  - (* consis topholeg : dead *)
    destruct A; simpl in HeqA; discriminate.
  - (* consis hole : dead *)
    destruct A; simpl in HeqA; discriminate.
  - (* consis tophole : dead *)
    destruct A; simpl in HeqA; discriminate.
  - (* consis tophole_inh : dead *)
    destruct A; simpl in HeqA; discriminate.
  - (* consis tophole_drop : dead *)
    destruct A; simpl in HeqA; discriminate.
  - (* consis flex_l : recurse at the definition, rebuild by __flex_r *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA; try discriminate.
    assert (Heqv : α1 = α) by (inversion HeqA; reflexivity). subst α1.
    assert (Hbr : binds α (abind_flex_mono_def τ) Θr) by (apply Hdefs; exact H).
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfr | exact Hbr ]).
    assert (Hwfτ : a_wf_ptyp Θr τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwfr | exact Hbr ]).
    destruct (IHad_pat_consis Hwfc τ eq_refl
                ltac:(eapply a_wf_ptyp_lc; exact Hwfτ)
                Θr Δ Qb Hwfr Hdefs Hflex
                ltac:(intros γ Hγ; right;
                      eapply a_wf_ptyp_ftv_tvarish; eassumption)
                Href) as [B [HeqB Href']].
    exists (btyp_var_f α). split; [ reflexivity | ].
    eapply ad_refine_syn__flex_r; [ exact Hbr | ].
    rewrite <- HeqB.
    rewrite <- btyp_to_bskl_mono_syn; [ exact Href' | rewrite HeqB; exact Hmono ].
  - (* consis flex_r : the output is a defined flexible *)
    assert (Hbr : binds α (abind_flex_mono_def τ) Θr) by (apply Hdefs; exact H).
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfr | exact Hbr ]).
    assert (Hwfτ : a_wf_ptyp Θr τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwfr | exact Hbr ]).
    subst R.
    revert Hwfr Hdefs Hflex Hvis Hbr Hmono Hwfτ.
    remember (bskl_var_f α) as Qt0 eqn:HQt.
    assert (Hc : {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (bskl_var_f α) }}ad)
      by (unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn;
          eapply ad_pat_consis__flex_r; eassumption).
    revert HQt.
    induction Href as
      [ Θx Δx
      | Θx Δx αx Hin
      | Θx Δx Qs1 Qs2 Pt1 Pt2 HrA IHA HrB IHB
      | Lx Θx Δx Qs Pt Hfam IHfam
      | Θx Δx Pf Hwff
      | Θx Δx Qs Pt Hr IHr
      | Lx Θx Δx Qs Pt Hfam IHfam
      | Θx Δx Qs Pt Hg Hr IHr
      | Θx Δx αx τx Pt Hb Hr IHr
      | Θx Δx αx τx Qs Hb Hr IHr ];
      intros HQt Hwfr Hdefs Hflex Hvis Hbr Hmono Hwfτ; try discriminate HQt.
    + (* refine var : go through __flex_l over the definition *)
      inversion HQt; subst.
      destruct (IHad_pat_consis Hwfc A eq_refl HlcA Θx Δx
                  (ptyp_to_bskl_syn τ) Hwfr Hdefs Hflex Hvis
                  ltac:(rewrite <- !(ptyp_to_bskl_inh_syn_eq Hmono);
                        apply ad_refine_syn_refl_inh;
                        apply a_wf_ptyp_to_wf_pskl; exact Hwfτ))
        as [B [HeqB Href']].
      exists B. split; [ exact HeqB | ].
      eapply ad_refine_syn__flex_l; [ exact Hbr | exact Href' ].
    + (* refine hole *)
      eapply transport_hole_answer;
        [ exact Hc | exact Hwfr | exact HlcA | exact Hdefs | exact Hflex
        | symmetry; exact HQt | exact Hwff ].
    + (* refine tophole_remove *)
      destruct (IHr HQt Hwfr Hdefs Hflex Hvis Hbr Hmono Hwfτ)
        as [B [HeqB Href']].
      exists B. split;
        [ exact HeqB | apply ad_refine_syn__tophole_remove; exact Href' ].
    + (* refine flex_l *)
      destruct (IHr HQt Hwfr Hdefs Hflex Hvis Hbr Hmono Hwfτ)
        as [B [HeqB Href']].
      exists B. split;
        [ exact HeqB | eapply ad_refine_syn__flex_l; eassumption ].
    + (* refine flex_r : the same definition, by uniqueness *)
      inversion HQt; subst.
      assert (Hτ : τx = τ)
        by (pose proof (binds_unique _ _ _ _ _ Hb Hbr
                          (a_wf_aenv_uniq Hwfr)) as Heq2;
            inversion Heq2; reflexivity).
      subst τx.
      destruct (IHad_pat_consis Hwfc A eq_refl HlcA Θx Δx Qs
                  Hwfr Hdefs Hflex Hvis Hr) as [B [HeqB Href']].
      exists B. split; [ exact HeqB | exact Href' ].
Qed.

(** ⭐ WHY THE TWO CONTEXTS ARE DECOUPLED (§4f), and what each hypothesis
    buys.  With a single shared Θ the transport CANNOT close its [__all]
    row: the consistency premise lives at [(α~tvar),Θ] and the refinement
    premise at [Θ ⨟ α,Δ], and moving the CONSTRUCTED output back (Θ → Δ) is
    unsound — [ad_refine_syn__hole]'s fill is Δ-free BY RULE, while the
    transport's fills are [ptyp_to_pskl A] for the sub-annotations, which do
    mention α.  Decoupled ([Θc] for the consistency, [Θr ⨟ Δ] for the
    refinement, tied by [Hdefs] and [Hflex]), BOTH ∀ rows land exactly where
    their own rule puts the binder and NO context move is needed: [__all]
    recurses at [Θc' = (α~tvar),Θc], [Θr' = Θr], [Δ' = α,Δ], and
    [__tophole_fill] at [Θc' = (α~tvar),Θc], [Θr' = (α~tvar),Θr], [Δ' = Δ].

    Going back through [a_consis] instead is the dead end that costs the
    most to discover: its ∀ rows put the binder in Θ where refinement's put
    it in Δ, which is exactly what [ad_refine_syn_f]'s hygiene set exists to
    manage, so that route re-does consistency soundness.

    The three loads the hypotheses carry:
    - [Hvis] ("every free variable of A is in Δ or a tvar of Θr") is what
      the ∀ rows can maintain.  The [__hole] row needs MORE — the rule wants
      the fill well-formed at EMPTY Δ, i.e. A must be Δ-FREE — and that is
      what the occurrence lemma (§4d) upgrades it to: at [__hole] the target
      is a synthesised painting well-formed at empty Δ, so each of the
      lemma's three disjuncts lands in [dom Θr], and a Δ-bound ∀ witness,
      fresh for Θr, is excluded.
    - [Hdefs] / [Hflex] are what let the two flexible rows rebuild in [Θr].
      ⭐ Those rows are sound because A DEFINITION IS A MONOTYPE
      ([a_wf_aenv__flex_def]), so the recursive answer is forced to be the
      synthesised painting the rules demand — [btyp_to_bskl_mono_syn] (§4a).
    - The cofinite families of the two ∀ rows come from ONE fresh witness by
      the renamings of §4c (a Δ-member, for [__all]) and §4e (a rigid
      Θ-variable, for [__tophole_fill]).

    ⚙ Read as consis-to-[≡ᵗ] the same fact is what
    thm:sound-type-inference's Freeze case needs (the paper's "which further
    gives [Θ2 ⊢ B ≡ A]"); derive it from this transport rather than
    rebuilding it. *)
Lemma a_consis_chk_annot_refine : forall Θ0 A P Θ1,
  a_consis_chk Θ0 (ptyp_to_pskl A) P Θ1 ->
  {{ ⊢ Θ0 }}a ->
  a_wf_ptyp Θ0 A ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  exists B, btyp_to_ptyp B = A /\
    {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B) }}ad.
Proof.
  intros Θ0 A P Θ1 Hchk Hwf HwfA HwfP.
  destruct (a_consis_chk_sound Hchk Hwf HwfP
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA))
    as [Hle [Hwf1 [Qt [Hcons Href]]]].
  assert (HwfA1 : a_wf_ptyp Θ1 A) by (eapply a_wf_ptyp_isub; eassumption).
  rewrite <- ptyp_to_uskl_syn_via_pskl in Hcons.
  eapply ad_refine_syn_target_transport;
    [ exact Hcons | exact Hwf1 | reflexivity
    | eapply a_wf_ptyp_lc; exact HwfA
    | exact Hwf1
    | intros β τ Hb; exact Hb
    | intros γ [Hb | [τ Hb]]; [ right; left | right; right; exists τ ]; exact Hb
    | intros γ Hγ; right; eapply a_wf_ptyp_ftv_tvarish; eassumption
    | exact Href ].
Qed.

(* ===================================================================== *)
(*  §5  thm:sound-skeleton-inference                                      *)
(* ===================================================================== *)

Theorem a_pat_sound : forall m Θ0 P0 e P Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ P ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat m P0 ->
  {{ Θ0 ⊢ᵉ e }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt, bskl_to_pskl Qt = P /\
    ({{ Θ1 ⊢ˢ[ m ] e ⦂ Qt }}ad) /\
    ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad).
Proof.
  intros m Θ0 P0 e P Θ1 H; induction H; intros Hwf HwfP0 Hmod Hexp;
    pose proof (fun y Ps Hb => @a_wf_aenv_binds_var_skl_wf _ y Ps Hwf Hb)
      as Hskl.
  - (* AP-Unit *)
    destruct (a_sub_sound_v H Hwf HwfP0
                ltac:(apply a_wf_pskl__unit)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    assert (HwfQt : {{ Θ1 ⨟ empty ⊢ₚₛ (bskl_to_pskl Qt) }}a)
      by (rewrite HeQt; eapply a_sub_output_wf;
          [ exact H | exact Hwf | exact HwfP0 | apply a_wf_pskl__unit ]).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ].
    split; [ apply ad_pat__unit; [ exact HwfQt | exact Hjoin ] | exact Href ].
  - (* AP-Var, type entry *)
    assert (HwfA : a_wf_ptyp Θ0 A)
      by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
    destruct (a_sub_sound_v H0 Hwf HwfP0
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    assert (HwfQt : {{ Θ1 ⨟ empty ⊢ₚₛ (bskl_to_pskl Qt) }}a)
      by (rewrite HeQt; eapply a_sub_output_wf;
          [ exact H0 | exact Hwf | exact HwfP0
          | apply a_wf_ptyp_to_wf_pskl; exact HwfA ]).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ]. split; [ | exact Href ].
    eapply ad_pat__var with (b := abind_var_typ A);
      [ apply (a_sub_tm_le H0); [ exact I | exact H ]
      | reflexivity
      | exact HwfQt
      | rewrite pskl_to_uskl_via_bskl_syn; exact Hjoin ].
  - (* AP-Var, skeleton entry *)
    destruct (a_sub_sound_v H0 Hwf HwfP0 (Hskl _ _ H)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    assert (HwfQt : {{ Θ1 ⨟ empty ⊢ₚₛ (bskl_to_pskl Qt) }}a)
      by (rewrite HeQt; eapply a_sub_output_wf;
          [ exact H0 | exact Hwf | exact HwfP0 | exact (Hskl _ _ H) ]).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ]. split; [ | exact Href ].
    eapply ad_pat__var with (b := abind_var_skl P);
      [ apply (a_sub_tm_le H0); [ exact I | exact H ]
      | reflexivity
      | exact HwfQt
      | rewrite pskl_to_uskl_via_bskl_syn; exact Hjoin ].
  - (* AP-Anno *)
    destruct (a_wf_exp_anno_inv Hexp) as [HwfA Hexp0].
    destruct (a_sub_sound_v H Hwf HwfP0
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    assert (HwfQt : {{ Θ1 ⨟ empty ⊢ₚₛ (bskl_to_pskl Qt) }}a)
      by (rewrite HeQt; eapply a_sub_output_wf;
          [ exact H | exact Hwf | exact HwfP0
          | apply a_wf_ptyp_to_wf_pskl; exact HwfA ]).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ]. split; [ | exact Href ].
    apply ad_pat__anno;
      [ eapply a_wf_ptyp_isub; [ exact HwfA | exact Hle ]
      | exact HwfQt
      | rewrite pskl_to_uskl_via_bskl_syn; exact Hjoin ].
  - (* AP-Freeze *)
    destruct (IHa_pat Hwf ltac:(apply a_wf_pskl__hole)
                a_sk_mode_compat__ti (a_wf_exp_freeze_inv Hexp))
      as [Hle [Hwf1 [Qt [HeQt [Hpat Href]]]]].
    destruct (ad_refine_syn_syn_l Href pskl_hole eq_refl) as [P' HQt].
    subst Qt.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists (pskl_to_bskl_syn P'). split; [ exact HeQt | ].
    split; [ apply ad_pat__freeze; exact Hpat | exact Href ].
  - (* AP-Abs *)
    destruct (a_split_sk_shape H0 Hmod) as [HeqΘ Hshape]; subst Θ1.
    destruct (a_wf_exp_abs_inv Hexp) as [L0 Hexp0].
    assert (Hpre : {{ Θ0 ⨟ empty ⊢ₚₛ P }}a /\ {{ Θ0 ⨟ empty ⊢ₚₛ Q0 }}a /\
                   a_sk_mode_compat (decr_mode m) Q0).
    { destruct Hshape as [[HP0 [HP HQ0]] | HP0]; subst.
      - repeat split; try apply a_wf_pskl__hole.
        destruct (a_sk_mode_compat_hole_inv Hmod) as [Hm | Hm]; subst m;
          [ apply a_sk_mode_compat__ti | congruence ].
      - inversion HwfP0; subst.
        destruct (a_sk_mode_compat_arrow_inv Hmod) as [m' [Hm Hm']]; subst m.
        repeat split; assumption. }
    destruct Hpre as [HwfPP [HwfQ0 Hmod']].
    destruct (atom_fresh (L `union` L0 `union` dom Θ0 `union` dom Ξ
                            `union` dom Θ2 `union` fvar_in_exp e)) as [x Hx].
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_skl P) ++ Θ0) }}a).
    { apply a_wf_aenv__var;
        [ clear - Hx; fsetdec | exact HwfPP | exact Hwf ]. }
    destruct (H3 x ltac:(clear - Hx; solve_notin_auto) Hwfx
                (a_wf_pskl_weaken_cons x (abind_var_skl P) HwfQ0) Hmod'
                (a_wf_exp_weaken_cons x (abind_var_skl P)
                   (Hexp0 x ltac:(clear - Hx; solve_notin_auto))))
      as [Hle [Hwfout [Qt [HeQt [Hpat Href]]]]].
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_skl P) ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfout).
    assert (Hlc2 : lc_aenv Θ2).
    { apply a_wf_aenv_lc_aenv in Hwfout.
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout].
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout]. exact Hwfout. }
    assert (Hisub : Θ0 ⊴ (Ξ ++ Θ2))
      by (eapply a_isub_peel_var_skl_mid; eassumption).
    assert (Hwf2 : {{ ⊢ (Ξ ++ Θ2) }}a)
      by (eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []).
    assert (Hmc : mod_comp_sk (bskl_arrow (pskl_to_bskl_inh P) Qt) m).
    { pose proof (ad_pat_mod_comp_sk Hpat) as Hmq.
      destruct Hshape as [[HP0 [HP HQ0]] | HP0]; subst; simpl.
      - destruct (a_sk_mode_compat_hole_inv Hmod) as [Hm | Hm]; subst m;
          [ | congruence ].
        apply mod_comp_sk__ti. apply is_sskl__arrow;
          [ apply is_sskl__hole | apply mod_comp_sk_ti_inv; exact Hmq ].
      - destruct (a_sk_mode_compat_arrow_inv Hmod) as [m' [Hm Hm']]; subst m.
        apply mod_comp_sk__fn; exact Hmq. }
    assert (Href2 : {{ (Ξ ++ Θ2) ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0)
                      ⊳ (bskl_arrow (pskl_to_bskl_inh P) Qt) }}ad).
    { destruct Hshape as [[HP0 [HP HQ0]] | HP0]; subst; simpl.
      - destruct (ad_refine_syn_syn_l Href pskl_hole eq_refl) as [P' HQt].
        subst Qt.
        change (bskl_arrow bskl_hole (pskl_to_bskl_syn P'))
          with (pskl_to_bskl_syn (pskl_arrow pskl_hole P')).
        apply ad_refine_syn__hole. apply a_wf_pskl__arrow;
          [ apply a_wf_pskl__hole | ].
        pose proof (ad_refine_syn_hole_l_target_wf Href) as Hw.
        rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw.
        eapply a_wf_pskl_mono;
          [ exact Hw | apply aenv_tbinds_le_strip_tm; intros [] ].
      - apply ad_refine_syn__arrow;
          [ apply ad_refine_syn_refl_inh;
              eapply a_wf_pskl_isub; [ exact HwfPP | exact Hisub ]
          | eapply ad_refine_syn_strip_tm_skl; exact Href ]. }
    split; [ exact Hisub | ]. split; [ exact Hwf2 | ].
    exists (bskl_arrow (pskl_to_bskl_inh P) Qt).
    split.
    { simpl. rewrite bskl_to_pskl_pskl_to_bskl_inh, HeQt. reflexivity. }
    split; [ | exact Href2 ].
    apply ad_pat__abs with (L := singleton x);
      [ exact H
      | eapply a_wf_pskl_isub; [ exact HwfPP | exact Hisub ]
      | exact Hmc
      | ].
    intros y Hy.
    apply ad_pat_rename_tm with (x := x);
      [ apply ad_pat_suffix_moving with (Ξ := Ξ) (Θ2 := (x ~ abind_var_skl P));
          exact Hpat
      | exact I
      | clear - Hx; simpl_env; fsetdec ].
  - (* AP-AbsAnno *)
    destruct (a_split_sk_shape H0 Hmod) as [HeqΘ Hshape]; subst Θ1.
    destruct (a_wf_exp_abs_anno_inv Hexp) as [HwfA [L0 Hexp0]].
    assert (Hpre : {{ Θ0 ⨟ empty ⊢ₚₛ P }}a /\ {{ Θ0 ⨟ empty ⊢ₚₛ Q0 }}a /\
                   a_sk_mode_compat (decr_mode m) Q0).
    { destruct Hshape as [[HP0 [HP HQ0]] | HP0]; subst.
      - repeat split; try apply a_wf_pskl__hole.
        destruct (a_sk_mode_compat_hole_inv Hmod) as [Hm | Hm]; subst m;
          [ apply a_sk_mode_compat__ti | congruence ].
      - inversion HwfP0; subst.
        destruct (a_sk_mode_compat_arrow_inv Hmod) as [m' [Hm Hm']]; subst m.
        repeat split; assumption. }
    destruct Hpre as [HwfPP [HwfQ0 Hmod']].
    destruct (a_consis_chk_sound H1 Hwf HwfPP
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA))
      as [Hlec [Hwfc _]].
    destruct (atom_fresh (L `union` L0 `union` dom Θ2 `union` dom Ξ
                            `union` dom Θ3 `union` fvar_in_exp e)) as [x Hx].
    assert (HwfAc : a_wf_ptyp Θ2 A) by (eapply a_wf_ptyp_isub; eassumption).
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ2) }}a)
      by (apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfAc | exact Hwfc ]).
    destruct (H4 x ltac:(clear - Hx; solve_notin_auto) Hwfx
                (a_wf_pskl_weaken_cons x (abind_var_typ A)
                   ltac:(eapply a_wf_pskl_isub; [ exact HwfQ0 | exact Hlec ]))
                Hmod'
                (a_wf_exp_weaken_cons x (abind_var_typ A)
                   (a_wf_exp_isub (Hexp0 x ltac:(clear - Hx; solve_notin_auto)) Hlec)))
      as [Hle [Hwfout [Qt [HeQt [Hpat Href]]]]].
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ3))
      by (apply a_wf_aenv_uniq; exact Hwfout).
    assert (Hlc3 : lc_aenv Θ3).
    { apply a_wf_aenv_lc_aenv in Hwfout.
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout].
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout]. exact Hwfout. }
    assert (Hisub : Θ2 ⊴ (Ξ ++ Θ3))
      by (eapply a_isub_peel_var_typ_mid; eassumption).
    assert (Hwf3 : {{ ⊢ (Ξ ++ Θ3) }}a)
      by (eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []).
    assert (Hisub0 : Θ0 ⊴ (Ξ ++ Θ3)) by (eapply a_isub_trans; eassumption).
    assert (Hbody : forall y,
              {{ ((y ~ abind_var_typ A) ++ (Ξ ++ Θ3)) ⊢ˢ[ decr_mode m ]
                (open_exp_wrt_exp e (exp_var_f y)) ⦂ Qt }}ad).
    { intros y. apply ad_pat_rename_tm with (x := x);
        [ apply ad_pat_suffix_moving with (Ξ := Ξ) (Θ2 := (x ~ abind_var_typ A));
            exact Hpat
        | exact I
        | clear - Hx; simpl_env; fsetdec ]. }
    (* the annotation's colouring: at the HOLE shape the refinement forces
       the all-synthesised painting; at the ARROW shape it is the one the
       consistency run's output transports to (§4) *)
    destruct Hshape as [[HP0 [HP HQ0]] | HP0].
    + (* □ ▹ □ ⇢ □ *)
      subst P0 P Q0.
      destruct (ad_refine_syn_syn_l Href pskl_hole eq_refl) as [P' HQt].
      subst Qt.
      assert (HwfP' : {{ (Ξ ++ Θ3) ⨟ empty ⊢ₚₛ P' }}a).
      { pose proof (ad_refine_syn_hole_l_target_wf Href) as Hw.
        rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw.
        eapply a_wf_pskl_mono;
          [ exact Hw | apply aenv_tbinds_le_strip_tm; intros [] ]. }
      split; [ exact Hisub0 | ]. split; [ exact Hwf3 | ].
      exists (bskl_arrow (btyp_to_bskl (ptyp_to_btyp_syn A))
                         (pskl_to_bskl_syn P')).
      split.
      { rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt.
        simpl. rewrite btyp_to_bskl_ptyp_to_btyp_syn.
        rewrite !bskl_to_pskl_pskl_to_bskl_syn. rewrite HeQt. reflexivity. }
      split.
      * eapply ad_pat__abs_anno with (L := singleton x)
                                     (B := ptyp_to_btyp_syn A);
          [ exact H
          | eapply a_wf_ptyp_isub; [ exact HwfA | exact Hisub0 ]
          | apply btyp_to_ptyp_ptyp_to_btyp_syn
          | | intros y Hy; apply Hbody ].
        destruct (a_sk_mode_compat_hole_inv Hmod) as [Hm | Hm]; subst m;
          [ | congruence ].
        apply mod_comp_sk__ti. apply is_sskl__arrow.
        -- rewrite btyp_to_bskl_ptyp_to_btyp_syn.
           apply is_sskl_pskl_to_bskl_syn. apply lc_ptyp_to_pskl.
           eapply a_wf_ptyp_lc; exact HwfA.
        -- apply mod_comp_sk_ti_inv. apply (ad_pat_mod_comp_sk (Hbody x)).
      * simpl. rewrite btyp_to_bskl_ptyp_to_btyp_syn.
        change (bskl_arrow (pskl_to_bskl_syn (ptyp_to_pskl A))
                           (pskl_to_bskl_syn P'))
          with (pskl_to_bskl_syn (pskl_arrow (ptyp_to_pskl A) P')).
        apply ad_refine_syn__hole. apply a_wf_pskl__arrow;
          [ apply a_wf_ptyp_to_wf_pskl;
              eapply a_wf_ptyp_isub; [ exact HwfA | exact Hisub0 ]
          | exact HwfP' ].
    + (* P0 = P → Q0 *)
      subst P0.
      destruct (a_consis_chk_annot_refine H1 Hwf HwfA HwfPP)
        as [B [HeqB HrefA]].
      destruct (a_sk_mode_compat_arrow_inv Hmod) as [m' [Hm Hm']]; subst m.
      split; [ exact Hisub0 | ]. split; [ exact Hwf3 | ].
      exists (bskl_arrow (btyp_to_bskl B) Qt).
      split.
      { simpl. rewrite bskl_to_pskl_btyp_to_bskl, HeqB, HeQt. reflexivity. }
      split.
      * eapply ad_pat__abs_anno with (L := singleton x) (B := B);
          [ exact H
          | eapply a_wf_ptyp_isub; [ exact HwfA | exact Hisub0 ]
          | exact HeqB
          | apply mod_comp_sk__fn; apply (ad_pat_mod_comp_sk (Hbody x))
          | intros y Hy; apply Hbody ].
      * simpl. apply ad_refine_syn__arrow;
          [ eapply ad_refine_syn_isub; [ exact HrefA | exact Hisub ]
          | eapply ad_refine_syn_strip_tm_typ; exact Href ].
  - (* AP-AbsCheck *)
    destruct (a_wf_exp_abs_inv Hexp) as [L0 Hexp0].
    destruct (atom_fresh (L `union` L0 `union` dom Θ0 `union` dom Ξ
                            `union` dom Θ1 `union` fvar_in_exp e)) as [x Hx].
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_skl pskl_hole) ++ Θ0) }}a)
      by (apply a_wf_aenv__var;
          [ clear - Hx; fsetdec | apply a_wf_pskl__hole | exact Hwf ]).
    destruct (H1 x ltac:(clear - Hx; solve_notin_auto) Hwfx
                ltac:(apply a_wf_pskl__hole) a_sk_mode_compat__tc
                (a_wf_exp_weaken_cons x (abind_var_skl pskl_hole)
                   (Hexp0 x ltac:(clear - Hx; solve_notin_auto))))
      as [Hle [Hwfout [Qt [HeQt [Hpat Href]]]]].
    destruct (ad_refine_syn_syn_l Href pskl_hole eq_refl) as [P' HQt].
    subst Qt.
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_skl pskl_hole) ++ Θ1))
      by (apply a_wf_aenv_uniq; exact Hwfout).
    assert (Hlc1 : lc_aenv Θ1).
    { apply a_wf_aenv_lc_aenv in Hwfout.
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout].
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout]. exact Hwfout. }
    assert (Hisub : Θ0 ⊴ (Ξ ++ Θ1))
      by (eapply a_isub_peel_var_skl_mid; eassumption).
    assert (Hwf1 : {{ ⊢ (Ξ ++ Θ1) }}a)
      by (eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []).
    assert (HwfP' : {{ (Ξ ++ Θ1) ⨟ empty ⊢ₚₛ P' }}a).
    { pose proof (ad_refine_syn_hole_l_target_wf Href) as Hw.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw.
      eapply a_wf_pskl_mono;
        [ exact Hw | apply aenv_tbinds_le_strip_tm; intros [] ]. }
    split; [ exact Hisub | ]. split; [ exact Hwf1 | ].
    exists (bskl_tophole (bskl_arrow bskl_hole (pskl_to_bskl_syn P'))).
    split.
    { rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt.
      simpl. rewrite bskl_to_pskl_pskl_to_bskl_syn, HeQt. reflexivity. }
    split.
    + apply ad_pat__abs_check with (L := singleton x) (P := P').
      intros y Hy.
      apply ad_pat_rename_tm with (x := x);
        [ apply ad_pat_suffix_moving with (Ξ := Ξ)
                                          (Θ2 := (x ~ abind_var_skl pskl_hole));
            exact Hpat
        | exact I
        | clear - Hx; simpl_env; fsetdec ].
    + change (bskl_tophole (bskl_arrow bskl_hole (pskl_to_bskl_syn P')))
        with (pskl_to_bskl_syn (pskl_tophole (pskl_arrow pskl_hole P'))).
      apply ad_refine_syn__hole. apply a_wf_pskl__tophole;
        [ apply guarded_pskl__arrow;
            [ apply lc_pskl_hole | eapply a_wf_pskl_lc; exact HwfP' ]
        | apply a_wf_pskl__arrow; [ apply a_wf_pskl__hole | exact HwfP' ] ].
  - (* AP-AbsAnnoCheck *)
    destruct (a_wf_exp_abs_anno_inv Hexp) as [HwfA [L0 Hexp0]].
    destruct (atom_fresh (L `union` L0 `union` dom Θ0 `union` dom Ξ
                            `union` dom Θ1 `union` fvar_in_exp e)) as [x Hx].
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ0) }}a)
      by (apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfA | exact Hwf ]).
    destruct (H1 x ltac:(clear - Hx; solve_notin_auto) Hwfx
                ltac:(apply a_wf_pskl__hole) a_sk_mode_compat__tc
                (a_wf_exp_weaken_cons x (abind_var_typ A)
                   (Hexp0 x ltac:(clear - Hx; solve_notin_auto))))
      as [Hle [Hwfout [Qt [HeQt [Hpat Href]]]]].
    destruct (ad_refine_syn_syn_l Href pskl_hole eq_refl) as [P' HQt].
    subst Qt.
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ1))
      by (apply a_wf_aenv_uniq; exact Hwfout).
    assert (Hlc1 : lc_aenv Θ1).
    { apply a_wf_aenv_lc_aenv in Hwfout.
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout].
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout]. exact Hwfout. }
    assert (Hisub : Θ0 ⊴ (Ξ ++ Θ1))
      by (eapply a_isub_peel_var_typ_mid; eassumption).
    assert (Hwf1 : {{ ⊢ (Ξ ++ Θ1) }}a)
      by (eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []).
    assert (HwfP' : {{ (Ξ ++ Θ1) ⨟ empty ⊢ₚₛ P' }}a).
    { pose proof (ad_refine_syn_hole_l_target_wf Href) as Hw.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw.
      eapply a_wf_pskl_mono;
        [ exact Hw | apply aenv_tbinds_le_strip_tm; intros [] ]. }
    assert (HwfA1 : a_wf_ptyp (Ξ ++ Θ1) A)
      by (eapply a_wf_ptyp_isub; [ exact HwfA | exact Hisub ]).
    split; [ exact Hisub | ]. split; [ exact Hwf1 | ].
    exists (bskl_tophole (bskl_arrow (btyp_to_bskl (ptyp_to_btyp_syn A))
                                     (pskl_to_bskl_syn P'))).
    split.
    { rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt.
      simpl. rewrite btyp_to_bskl_ptyp_to_btyp_syn.
      rewrite !bskl_to_pskl_pskl_to_bskl_syn, HeQt. reflexivity. }
    split.
    + apply ad_pat__abs_anno_check with (L := singleton x) (P := P');
        [ exact HwfA1 | ].
      intros y Hy.
      apply ad_pat_rename_tm with (x := x);
        [ apply ad_pat_suffix_moving with (Ξ := Ξ)
                                          (Θ2 := (x ~ abind_var_typ A));
            exact Hpat
        | exact I
        | clear - Hx; simpl_env; fsetdec ].
    + rewrite btyp_to_bskl_ptyp_to_btyp_syn.
      change (bskl_tophole (bskl_arrow (pskl_to_bskl_syn (ptyp_to_pskl A))
                                       (pskl_to_bskl_syn P')))
        with (pskl_to_bskl_syn
                (pskl_tophole (pskl_arrow (ptyp_to_pskl A) P'))).
      apply ad_refine_syn__hole. apply a_wf_pskl__tophole;
        [ apply guarded_pskl__arrow;
            [ apply lc_ptyp_to_pskl; eapply a_wf_ptyp_lc; exact HwfA1
            | eapply a_wf_pskl_lc; exact HwfP' ]
        | apply a_wf_pskl__arrow;
            [ apply a_wf_ptyp_to_wf_pskl; exact HwfA1 | exact HwfP' ] ].
  - (* AP-App *)
    destruct (a_wf_exp_app_inv Hexp) as [Hexp1 Hexp2].
    destruct (IHa_pat1 Hwf ltac:(apply a_wf_pskl__hole)
                a_sk_mode_compat__tc Hexp2)
      as [Hle1 [Hwf1 [Qt1 [HeQt1 [Hpat1 Href1]]]]].
    destruct (ad_refine_syn_syn_l Href1 pskl_hole eq_refl) as [P' HQt1].
    subst Qt1.
    assert (HwfPin : {{ Θ1 ⨟ empty ⊢ₚₛ P' }}a).
    { pose proof (ad_refine_syn_hole_l_target_wf Href1) as Hw.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw. exact Hw. }
    rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt1. subst P0.
    destruct (IHa_pat2 Hwf1
                ltac:(apply a_wf_pskl__arrow;
                      [ exact HwfPin
                      | eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hle1 ] ])
                ltac:(apply a_sk_mode_compat__fn; exact Hmod)
                (a_wf_exp_isub Hexp1 Hle1))
      as [Hle2 [Hwf2 [Qt2 [HeQt2 [Hpat2 Href2]]]]].
    destruct (bskl_to_pskl_arrow_inv HeQt2) as [Qa [Qb [HQt2 [HeQa HeQb]]]].
    subst Qt2. simpl in Href2.
    destruct (ad_refine_syn_arrow_inv Href2) as [HrefA HrefB].
    split; [ eapply a_isub_trans; eassumption | ]. split; [ exact Hwf2 | ].
    exists Qb. split; [ exact HeQb | ]. split; [ | exact HrefB ].
    eapply ad_pat__app with (P := P') (Q1 := Qa);
      [ eapply ad_pat_isub_tm;
          [ exact Hpat1 | exact Hle2 | eapply a_pat_tm_le; exact H0 ]
      | exact HrefA
      | exact Hpat2 ].
Qed.
