(** SOUNDNESS OF SKELETON INFERENCE — section D, thm:sound-skeleton-inference
    (paper proofs.tex, app:proof-skeleton-inference).

    An [a_pat] run yields a solution to its skeleton inference problem: the
    output context is an information increase of the input, and in it the
    DECLARATIVE judgement [ad_pat] holds at a colouring of the output, which
    refines the (inherited painting of the) input skeleton.  Mirrors
    [a_sub_sound_thm] (prop_decorate_key.v), which it consumes at the three
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
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_typing.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.prop_ctx_mono.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_soundness_consis.
Require Import src.frost.algo.prop_soundness_sub.
Require Import src.frost.algo.prop_completeness_consis.
Require Import src.frost.algo.prop_completeness_sub_gen.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.decorated_algo.prop_decorate.
Require Import src.frost.decorated_algo.prop_decorate_key.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Term well-formedness (the problem definition's "M wf in Θ")       *)
(* ===================================================================== *)

Inductive a_wf_exp : aenv -> exp -> Prop :=
| a_wf_exp__unit : forall Θ,
    a_wf_exp Θ exp_unit
| a_wf_exp__var : forall Θ x,
    a_wf_exp Θ (exp_var_f x)
| a_wf_exp__anno : forall Θ e A,
    a_wf_ptyp Θ A ->
    a_wf_exp Θ e ->
    a_wf_exp Θ (exp_anno e A)
| a_wf_exp__freeze : forall Θ e,
    a_wf_exp Θ e ->
    a_wf_exp Θ (exp_freeze e)
| a_wf_exp__abs : forall L Θ e,
    (forall x, x `notin` L ->
       a_wf_exp Θ (open_exp_wrt_exp e (exp_var_f x))) ->
    a_wf_exp Θ (exp_abs e)
| a_wf_exp__abs_anno : forall L Θ A e,
    a_wf_ptyp Θ A ->
    (forall x, x `notin` L ->
       a_wf_exp Θ (open_exp_wrt_exp e (exp_var_f x))) ->
    a_wf_exp Θ (exp_abs_anno A e)
| a_wf_exp__app : forall Θ e1 e2,
    a_wf_exp Θ e1 ->
    a_wf_exp Θ e2 ->
    a_wf_exp Θ (exp_app e1 e2).

(** Only type-level entries are read (through [a_wf_ptyp]), so the term
    judgement transports along the term-blind relation — weakening by any
    entry and dropping term entries are both instances. *)
Lemma a_wf_exp_mono : forall Θ e,
  a_wf_exp Θ e ->
  forall Θ', aenv_tbinds_le Θ Θ' -> a_wf_exp Θ' e.
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
  a_wf_exp Θ e ->
  forall Θ', Θ ⊴ Θ' -> a_wf_exp Θ' e.
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
Lemma a_isub_cons_var_typ : forall Θ Θ' x A,
  lc_ptyp A ->
  Θ ⊴ Θ' ->
  ((x ~ abind_var_typ A) ++ Θ) ⊴ ((x ~ abind_var_typ A) ++ Θ').
Proof.
  intros * Hlc [[κ [Hid Hinc]] Hd]. split.
  - exists κ. split; [ exact Hid | ].
    apply (a_inc__var (Ξ := nil)); [ exact Hinc | | constructor ].
    rewrite msubst_ptyp_id; auto. apply a_tyequiv__refl; exact Hlc.
  - intros α τ Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    unfold binds; apply in_or_app; right. apply Hd; auto.
Qed.

Lemma a_isub_cons_var_skl : forall Θ Θ' x P,
  lc_pskl P ->
  Θ ⊴ Θ' ->
  ((x ~ abind_var_skl P) ++ Θ) ⊴ ((x ~ abind_var_skl P) ++ Θ').
Proof.
  intros * Hlc [[κ [Hid Hinc]] Hd]. split.
  - exists κ. split; [ exact Hid | ].
    apply (a_inc__var_skl (Ξ := nil)); [ exact Hinc | | constructor ].
    rewrite msubst_pskl_id; auto. apply a_pskl_tyequiv__refl; exact Hlc.
  - intros α τ Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    unfold binds; apply in_or_app; right. apply Hd; auto.
Qed.

(** A term entry looked up through [abind_to_pskl] is a term entry. *)
Lemma abind_to_pskl_is_tm : forall (b : abind) P,
  abind_to_pskl b = Some P -> abind_is_tm b.
Proof. intros [] P H; simpl in *; congruence || exact I. Qed.

Lemma ad_pat_isub_tm : forall M Θ e Q,
  Θ ⊢ᵃ[ M ] e ⇨ Q ->
  forall Θ', Θ ⊴ Θ' -> aenv_tm_le Θ Θ' ->
  Θ' ⊢ᵃ[ M ] e ⇨ Q.
Proof.
  intros M Θ e Q H; induction H; intros Θ' Hle Htm.
  - (* unit *) apply ad_pat__unit. eapply ad_pat_sub_isub; eauto.
  - (* var *)
    eapply ad_pat__var;
      [ apply Htm; [ eapply abind_to_pskl_is_tm; eauto | exact H ]
      | eassumption
      | eapply ad_pat_sub_isub; eauto ].
  - (* anno *)
    apply ad_pat__anno;
      [ eapply a_wf_ptyp_isub; eauto | eapply ad_pat_sub_isub; eauto ].
  - (* freeze *) apply ad_pat__freeze; auto.
  - (* abs *)
    apply ad_pat__abs with (L := L);
      [ assumption | eapply a_wf_pskl_isub; eauto | assumption | ].
    intros x Hx. apply H3;
      [ exact Hx
      | apply a_isub_cons_var_skl;
          [ eapply a_wf_pskl_lc; eauto | exact Hle ]
      | apply aenv_tm_le_cons; exact Htm ].
  - (* abs_anno *)
    eapply ad_pat__abs_anno with (L := L);
      [ assumption | eapply a_wf_ptyp_isub; eauto | eassumption
      | assumption | ].
    intros x Hx. apply H4;
      [ exact Hx
      | apply a_isub_cons_var_typ;
          [ eapply a_wf_ptyp_lc; eauto | exact Hle ]
      | apply aenv_tm_le_cons; exact Htm ].
  - (* app *)
    eapply ad_pat__app;
      [ auto | eapply ad_refine_syn_isub; eauto | auto ].
  - (* abs_check *)
    apply ad_pat__abs_check with (L := L). intros x Hx.
    apply H0;
      [ exact Hx
      | apply a_isub_cons_var_skl; [ apply lc_pskl_hole | exact Hle ]
      | apply aenv_tm_le_cons; exact Htm ].
  - (* abs_anno_check *)
    apply ad_pat__abs_anno_check with (L := L);
      [ eapply a_wf_ptyp_isub; eauto | ].
    intros x Hx. apply H1;
      [ exact Hx
      | apply a_isub_cons_var_typ;
          [ eapply a_wf_ptyp_lc; eauto | exact Hle ]
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
  (forall Θ0 Ξ α P Θ1, Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 -> aenv_tm_le Θ1 (Ξ ++ Θ0)) /\
  (forall Θ0 α β Θ1, Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 -> aenv_tm_le Θ1 Θ0) /\
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
  Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 -> aenv_tm_le Θ1 Θ0.
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
  Θ0 ⊢ₐ[ m ; P0 ] e ⇨ P ⊣ Θ1 -> aenv_tm_le Θ1 Θ0.
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
  Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 ->
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
  Ψ ⨟ Θ ⊢ₛᵃ[ a_sub_mode_sk | M ] R ⩽ Q ->
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
  Θ' ⊢ᵃ[ M ] e ⇨ Q ->
  forall Θa x (b : abind) Θ0 y,
  Θ' = Θa ++ (x ~ b) ++ Θ0 ->
  abind_is_tm b ->
  x `notin` dom Θa `union` dom Θ0 ->
  (Θa ++ (y ~ b) ++ Θ0) ⊢ᵃ[ M ] (subst_exp_in_exp (exp_var_f y) x e) ⇨ Q.
Proof.
  intros M Θ' e Q H; induction H;
    intros Θa x0 b0 Θb y Heq Htm Hx0; subst; simpl.
  - (* unit *)
    apply ad_pat__unit.
    eapply ad_pat_sub_mono;
      [ eassumption | apply aenv_tbinds_le_rename_tm;
                      apply abind_is_tm_not_ty; exact Htm ].
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
        | eapply ad_pat_sub_mono;
            [ eassumption | apply aenv_tbinds_le_rename_tm;
                            apply abind_is_tm_not_ty; exact Htm ] ].
    + (* any other variable: its entry is untouched *)
      eapply ad_pat__var with (b := b);
        [ | eassumption
        | eapply ad_pat_sub_mono;
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
      | eapply ad_pat_sub_mono;
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
    apply (H3 z ltac:(clear - Hz; fsetdec)
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
    apply (H4 z ltac:(clear - Hz; fsetdec)
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
    apply (H0 z ltac:(clear - Hz; fsetdec)
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
    apply (H1 z ltac:(clear - Hz; fsetdec)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | ].
    simpl. clear - Hx0 Hz. fsetdec.
Qed.

(* --- §3e  context surgery: dropping the walked term entry -------------- *)

(** A term variable's TYPE entry is well-formed in its own context — the
    mirror of [a_wf_aenv_binds_def_wf] (prop_precise.v) for the other
    payload-carrying entry form.  [AP-Var] (type-bound) needs it to feed
    [a_sub_sound_thm], which demands well-formedness of its subject. *)
Lemma a_wf_aenv_binds_var_typ_wf : forall Θ x A,
  a_wf_aenv Θ ->
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
  a_wf_aenv (Ξ ++ (x ~ b) ++ Θ) ->
  a_wf_aenv (Ξ ++ Θ).
Proof.
  intros Ξ; induction Ξ as [ | [y c] Ξ' IH ]; intros x b Θ Hb Hwf.
  - rewrite app_nil_l in *. inversion Hwf; subst; assumption.
  - assert (Htail : a_wf_aenv (Ξ' ++ (x ~ b) ++ Θ))
      by (inversion Hwf; subst; assumption).
    assert (Hrest : a_wf_aenv (Ξ' ++ Θ)) by (apply (IH x b Θ Hb Htail)).
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
      eapply a_scope_pskl_mono; eassumption.
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
  ((x ~ b) ++ Θ0) ⊢ᵃ[ M ] (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q ->
  abind_is_tm b ->
  x `notin` dom Θ0 `union` fvar_in_exp e ->
  ((y ~ b) ++ Θ0) ⊢ᵃ[ M ] (open_exp_wrt_exp e (exp_var_f y)) ⇨ Q.
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
Lemma a_wf_pskl_scope : forall Θ P,
  Θ ⨟ empty ⊢ₚₛᵃ P -> a_scope_pskl Θ P.
Proof.
  intros Θ P H.
  eapply a_wf_pskl_to_a_scope_pskl;
    [ exact H | intros y b Hb; exact Hb | intros α Hα; clear - Hα; fsetdec ].
Qed.

Lemma a_wf_pskl_weaken_cons : forall Θ Δ P x (b : abind),
  Θ ⨟ Δ ⊢ₚₛᵃ P -> ((x ~ b) ++ Θ) ⨟ Δ ⊢ₚₛᵃ P.
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
  a_wf_exp Θ e -> a_wf_exp ((x ~ b) ++ Θ) e.
Proof.
  intros * H. eapply a_wf_exp_mono;
    [ exact H | apply aenv_tbinds_le_of_binds_le; apply aenv_binds_le_weaken_l ].
Qed.

(** Inversions of [a_wf_exp], so the main induction never has to guess the
    names [inversion] manufactures. *)
Lemma a_wf_exp_anno_inv : forall Θ e A,
  a_wf_exp Θ (exp_anno e A) -> a_wf_ptyp Θ A /\ a_wf_exp Θ e.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_exp_freeze_inv : forall Θ e,
  a_wf_exp Θ (exp_freeze e) -> a_wf_exp Θ e.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_exp_app_inv : forall Θ e1 e2,
  a_wf_exp Θ (exp_app e1 e2) -> a_wf_exp Θ e1 /\ a_wf_exp Θ e2.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_exp_abs_inv : forall Θ e,
  a_wf_exp Θ (exp_abs e) ->
  exists L, forall x, x `notin` L ->
    a_wf_exp Θ (open_exp_wrt_exp e (exp_var_f x)).
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma a_wf_exp_abs_anno_inv : forall Θ A e,
  a_wf_exp Θ (exp_abs_anno A e) ->
  a_wf_ptyp Θ A /\
  exists L, forall x, x `notin` L ->
    a_wf_exp Θ (open_exp_wrt_exp e (exp_var_f x)).
Proof. intros * H; inversion H; subst; eauto. Qed.

(** ⭐ The paper's (commented-out) "refinement preserves correspondence",
    inferred-skeleton half, at the level of the DECLARATIVE judgement: a
    skeleton-inference colouring is mode-compatible.  The two Abs rows
    carry it outright; the base rows read it off their subtyping premise
    (§3c); [Freeze] and [App] invert their premise's. *)
Lemma ad_pat_mod_comp_sk : forall M Θ e Q,
  Θ ⊢ᵃ[ M ] e ⇨ Q -> mod_comp_sk Q M.
Proof.
  intros M Θ e Q H; induction H.
  - (* unit *) eapply ad_pat_sub_mod_comp_sk; eassumption.
  - (* var *) eapply ad_pat_sub_mod_comp_sk; eassumption.
  - (* anno *) eapply ad_pat_sub_mod_comp_sk; eassumption.
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
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  exists Qt, (empty ⨟ Θ1 ⊢ₛᵃ (pskl_to_uskl P) ∼ Qt) /\
             Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P0) ⊳ Qt.
Proof.
  intros * [Q Hc] Hwf HwfP0 HwfP.
  destruct (a_consis_sound_aux Hc Hwf HwfP0 HwfP
              ltac:(intros α Hα; clear - Hα; fsetdec)
              ltac:(intros β τ Hb; apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; fsetdec)
              ltac:(intros Θa β b Θb Heq Hne;
                    apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; fsetdec))
    as [Hle [Hwf1 [_ [_ [[Qt [_ [Hcons Hrs]]] _]]]]].
  split; [ exact Hle | ]. split; [ exact Hwf1 | ].
  exists Qt. split; [ exact Hcons | ]. eapply ad_refine_syn_f_forget; exact Hrs.
Qed.

Lemma bskl_to_pskl_btyp_to_bskl : forall B,
  bskl_to_pskl (btyp_to_bskl B) = ptyp_to_pskl (btyp_to_ptyp B).
Proof. induction B; simpl; congruence. Qed.

Lemma ad_refine_syn_arrow_inv : forall Θ Δ Q1 Q2 P1 P2,
  Θ ⨟ Δ ⊢ᵣᵃ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow P1 P2) ->
  Θ ⨟ Δ ⊢ᵣᵃ Q1 ⊳ P1 /\ Θ ⨟ Δ ⊢ᵣᵃ Q2 ⊳ P2.
Proof. intros * H; inversion H; subst; auto. Qed.

(* ===================================================================== *)
(*  §4  ⛔ THE ONE OPEN LEMMA — AbsAnno's refinement-target transport      *)
(*                                                                        *)
(*  The paper's inline step [by preservation of refinement under type]     *)
(*  equivalence (proofs.tex, AbsAnno case of thm:sound-skeleton-           *)
(*  inference), which exists nowhere as a lemma.  thm:sound-consistency    *)
(*  hands back the run's OWN output colouring [A'] and, in the paper,      *)
(*  [Θ2 ⊢ A' ≡ A]; the mechanized [a_consis_sound] hands back the output   *)
(*  colouring plus its CONSISTENCY with the subject painting, so the       *)
(*  transport has two halves: consis-to-[≡ᵗ] at TYPE level (the poly       *)
(*  analogue of [consis_mono_join], prop_mono_bridge.v — needed AGAIN by   *)
(*  thm:sound-type-inference's Freeze case) and a poly [tyequiv_refine_    *)
(*  syn] (only the MONO version exists, prop_precise_recover.v).           *)
(* ===================================================================== *)

(** THE PLAN (scouted 2026-08-06, second pass).  [a_consis_chk_sound] turns
    the run into the pair

      empty ⨟ Θ1 ⊢ₛᵃ (pskl_to_uskl (ptyp_to_pskl A)) ∼ Qt      (subject painting
                                                                ∼ output)
      Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ Qt                  (the refinement,
                                                                wrong target)

    so what is missing is a TARGET TRANSPORT, provable on the DECLARATIVE
    layer alone (going back through [a_consis] instead re-does consistency
    soundness: its ∀ rows put the binder in Θ while refinement's put it in
    Δ, which is what [ad_refine_syn_f]'s hygiene set exists to manage):

      forall Θ Δ Qb Qt A,
        a_wf_aenv Θ -> a_wf_ptyp Θ A ->
        empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (ptyp_to_pskl A)) ∼ Qt ->
        Θ ⨟ Δ ⊢ᵣᵃ Qb ⊳ Qt ->
        exists B, btyp_to_ptyp B = A /\ Θ ⨟ Δ ⊢ᵣᵃ Qb ⊳ (btyp_to_bskl B)

    NESTED induction: outer on the CONSISTENCY, inner (inside the rows whose
    target does not determine the refinement's last rule) on the REFINEMENT.
    Every row has an answer:

    - subject shape kills the ghost rows outright — a [ptyp] painting is
      never [uskl_hole] / [uskl_topholeg] / [uskl_all_etag], so __ghostg,
      __hole, __tophole, __topholeg, __tophole_inh, __tophole_drop and the
      two _tagged ∀ rows are DEAD.
    - __unit / __var: [Qt] already IS [btyp_to_bskl] of [btyp_unit] /
      [btyp_var_f α].  Nothing to do.
    - __arrow / __forall_inh_untagged / __forall_syn: invert the refinement.
      ⭐ [Qb = bskl_hole] (__hole) is always answerable by the ALL-SYNTHESISED
      painting [B := ptyp_to_btyp_syn A] — that is what [a_wf_ptyp Θ A] is
      for, and it is the same move the AbsAnno HOLE shape makes above.
      [__tophole_remove] and [__flex_l] shrink the refinement (inner IH);
      [__arrow] / [__all] recurse on the outer IH.
    - ⛔ the ∀ rows need [ad_refine_syn_delta_to_ctx]: consistency binds the
      fresh α in Θ, refinement in Δ.  The Δ→Θ direction is a WEAKENING and
      holds ([__var] already accepts either side; [__hole]'s
      [Θ ⨟ ∅ ⊢ₚₛᵃ P] only grows; [__tophole_fill] needs one exchange, by
      [ad_refine_syn_mono]).  The reverse direction does NOT hold and is not
      needed.  [__tophole_fill] additionally closes an α-dependent witness:
      [B := btyp_all_syn (close_btyp_wrt_btyp α B0)].
    - __flex_l (subject α ≔ τ): recurse at τ, then rebuild the answer
      [B := btyp_var_f α] with [ad_refine_syn__flex_r].  ⭐ This needs the
      recursive answer to be exactly [ptyp_to_bskl_syn τ], which holds
      because a DEFINITION IS A MONOTYPE ([a_wf_aenv__flex_def]) and a
      monotype has only one colouring — the missing one-liner is
      [mono_ptyp (btyp_to_ptyp B) -> btyp_to_bskl B
                                     = ptyp_to_bskl_syn (btyp_to_ptyp B)],
      the [ptyp_to_bskl_inh_syn_eq] (prop_mono_bridge.v) pattern.
    - __flex_r (output α ≔ τ): invert the refinement — [__flex_r] recurses,
      [__var] rebuilds through [ad_refine_syn__flex_l] over the refinement
      reflexivity [ad_refine_syn_refl_inh] at the monotype τ, [__hole] takes
      the all-synthesised painting again.

    The consis-to-[≡ᵗ] reading of the same fact (the paper's
    [Θ2 ⊢ A' ≡ A]) is what thm:sound-type-inference's Freeze case needs;
    build whichever of the two is more convenient FIRST and derive the
    other, but do not build both. *)
Lemma a_consis_chk_annot_refine : forall Θ0 A P Θ1,
  a_consis_chk Θ0 (ptyp_to_pskl A) P Θ1 ->
  a_wf_aenv Θ0 ->
  a_wf_ptyp Θ0 A ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  exists B, btyp_to_ptyp B = A /\
    Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B).
Admitted.  (* TODO[section-D]: thm:sound-skeleton-inference, AbsAnno at the
   ARROW split shape (the HOLE shape needs none of this and is proved).
   TRUE — every row of the transport has an answer, see the plan above;
   blocked on the poly target transport, which the paper asserts inline
   ("preservation of refinement under type equivalence") and never proves. *)

(* ===================================================================== *)
(*  §5  thm:sound-skeleton-inference                                      *)
(* ===================================================================== *)

Theorem a_pat_sound : forall m Θ0 P0 e P Θ1,
  Θ0 ⊢ₐ[ m ; P0 ] e ⇨ P ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  (forall x Ps, binds x (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat m P0 ->
  a_wf_exp Θ0 e ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  exists Qt, bskl_to_pskl Qt = P /\
    (Θ1 ⊢ᵃ[ m ] e ⇨ Qt) /\
    (Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P0) ⊳ Qt).
Proof.
  intros m Θ0 P0 e P Θ1 H; induction H; intros Hwf Hskl HwfP0 Hmod Hexp.
  - (* AP-Unit *)
    destruct (a_sub_sound_thm H Hwf HwfP0
                ltac:(apply a_wf_pskl__unit)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ].
    split; [ apply ad_pat__unit; exact Hjoin | exact Href ].
  - (* AP-Var, type entry *)
    assert (HwfA : a_wf_ptyp Θ0 A)
      by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
    destruct (a_sub_sound_thm H0 Hwf HwfP0
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ]. split; [ | exact Href ].
    eapply ad_pat__var with (b := abind_var_typ A);
      [ apply (a_sub_tm_le H0); [ exact I | exact H ]
      | reflexivity
      | rewrite pskl_to_uskl_via_bskl_syn; exact Hjoin ].
  - (* AP-Var, skeleton entry — the entry's DISCIPLINED wf comes from the
       theorem's hypothesis, [a_wf_aenv] storing only its scope *)
    destruct (a_sub_sound_thm H0 Hwf HwfP0 (Hskl _ _ H)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ]. split; [ | exact Href ].
    eapply ad_pat__var with (b := abind_var_skl P);
      [ apply (a_sub_tm_le H0); [ exact I | exact H ]
      | reflexivity
      | rewrite pskl_to_uskl_via_bskl_syn; exact Hjoin ].
  - (* AP-Anno *)
    destruct (a_wf_exp_anno_inv Hexp) as [HwfA Hexp0].
    destruct (a_sub_sound_thm H Hwf HwfP0
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ]. split; [ | exact Href ].
    apply ad_pat__anno;
      [ eapply a_wf_ptyp_isub; [ exact HwfA | exact Hle ]
      | rewrite pskl_to_uskl_via_bskl_syn; exact Hjoin ].
  - (* AP-Freeze *)
    destruct (IHa_pat Hwf Hskl ltac:(apply a_wf_pskl__hole)
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
    assert (Hpre : Θ0 ⨟ empty ⊢ₚₛᵃ P /\ Θ0 ⨟ empty ⊢ₚₛᵃ Q0 /\
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
    assert (Hwfx : a_wf_aenv ((x ~ abind_var_skl P) ++ Θ0)).
    { apply a_wf_aenv__var;
        [ clear - Hx; fsetdec | apply a_wf_pskl_scope; exact HwfPP | exact Hwf ]. }
    assert (Hsklx : forall y Ps,
              binds y (abind_var_skl Ps) ((x ~ abind_var_skl P) ++ Θ0) ->
              ((x ~ abind_var_skl P) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Ps).
    { intros y Ps Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ inversion Heqb; subst; apply a_wf_pskl_weaken_cons; exact HwfPP
        | apply a_wf_pskl_weaken_cons; exact (Hskl _ _ Hb') ]. }
    destruct (H3 x ltac:(clear - Hx; fsetdec) Hwfx Hsklx
                (a_wf_pskl_weaken_cons x (abind_var_skl P) HwfQ0) Hmod'
                (a_wf_exp_weaken_cons x (abind_var_skl P)
                   (Hexp0 x ltac:(clear - Hx; fsetdec))))
      as [Hle [Hwfout [Qt [HeQt [Hpat Href]]]]].
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_skl P) ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfout).
    assert (Hlc2 : lc_aenv Θ2).
    { apply a_wf_aenv_lc_aenv in Hwfout.
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout].
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout]. exact Hwfout. }
    assert (Hisub : Θ0 ⊴ (Ξ ++ Θ2))
      by (eapply a_isub_peel_var_skl_mid; eassumption).
    assert (Hwf2 : a_wf_aenv (Ξ ++ Θ2))
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
    assert (Href2 : (Ξ ++ Θ2) ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P0)
                      ⊳ (bskl_arrow (pskl_to_bskl_inh P) Qt)).
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
    assert (Hpre : Θ0 ⨟ empty ⊢ₚₛᵃ P /\ Θ0 ⨟ empty ⊢ₚₛᵃ Q0 /\
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
    assert (Hwfx : a_wf_aenv ((x ~ abind_var_typ A) ++ Θ2))
      by (apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfAc | exact Hwfc ]).
    assert (Hsklc : forall y Ps, binds y (abind_var_skl Ps) Θ2 ->
                      Θ2 ⨟ empty ⊢ₚₛᵃ Ps).
    { intros y Ps Hb. eapply a_wf_pskl_isub; [ | exact Hlec ].
      apply (Hskl y). apply (a_consis_chk_tm_ge H1); [ exact I | exact Hb ]. }
    assert (Hsklx : forall y Ps,
              binds y (abind_var_skl Ps) ((x ~ abind_var_typ A) ++ Θ2) ->
              ((x ~ abind_var_typ A) ++ Θ2) ⨟ empty ⊢ₚₛᵃ Ps).
    { intros y Ps Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ discriminate | apply a_wf_pskl_weaken_cons; exact (Hsklc _ _ Hb') ]. }
    destruct (H4 x ltac:(clear - Hx; fsetdec) Hwfx Hsklx
                (a_wf_pskl_weaken_cons x (abind_var_typ A)
                   ltac:(eapply a_wf_pskl_isub; [ exact HwfQ0 | exact Hlec ]))
                Hmod'
                (a_wf_exp_weaken_cons x (abind_var_typ A)
                   (a_wf_exp_isub (Hexp0 x ltac:(clear - Hx; fsetdec)) Hlec)))
      as [Hle [Hwfout [Qt [HeQt [Hpat Href]]]]].
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ3))
      by (apply a_wf_aenv_uniq; exact Hwfout).
    assert (Hlc3 : lc_aenv Θ3).
    { apply a_wf_aenv_lc_aenv in Hwfout.
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout].
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout]. exact Hwfout. }
    assert (Hisub : Θ2 ⊴ (Ξ ++ Θ3))
      by (eapply a_isub_peel_var_typ_mid; eassumption).
    assert (Hwf3 : a_wf_aenv (Ξ ++ Θ3))
      by (eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []).
    assert (Hisub0 : Θ0 ⊴ (Ξ ++ Θ3)) by (eapply a_isub_trans; eassumption).
    assert (Hbody : forall y,
              ((y ~ abind_var_typ A) ++ (Ξ ++ Θ3)) ⊢ᵃ[ decr_mode m ]
                (open_exp_wrt_exp e (exp_var_f y)) ⇨ Qt).
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
      assert (HwfP' : (Ξ ++ Θ3) ⨟ empty ⊢ₚₛᵃ P').
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
    assert (Hwfx : a_wf_aenv ((x ~ abind_var_skl pskl_hole) ++ Θ0))
      by (apply a_wf_aenv__var;
          [ clear - Hx; fsetdec | apply a_scope_pskl__hole | exact Hwf ]).
    assert (Hsklx : forall y Ps,
              binds y (abind_var_skl Ps) ((x ~ abind_var_skl pskl_hole) ++ Θ0) ->
              ((x ~ abind_var_skl pskl_hole) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Ps).
    { intros y Ps Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ inversion Heqb; subst; apply a_wf_pskl__hole
        | apply a_wf_pskl_weaken_cons; exact (Hskl _ _ Hb') ]. }
    destruct (H1 x ltac:(clear - Hx; fsetdec) Hwfx Hsklx
                ltac:(apply a_wf_pskl__hole) a_sk_mode_compat__tc
                (a_wf_exp_weaken_cons x (abind_var_skl pskl_hole)
                   (Hexp0 x ltac:(clear - Hx; fsetdec))))
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
    assert (Hwf1 : a_wf_aenv (Ξ ++ Θ1))
      by (eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []).
    assert (HwfP' : (Ξ ++ Θ1) ⨟ empty ⊢ₚₛᵃ P').
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
    assert (Hwfx : a_wf_aenv ((x ~ abind_var_typ A) ++ Θ0))
      by (apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfA | exact Hwf ]).
    assert (Hsklx : forall y Ps,
              binds y (abind_var_skl Ps) ((x ~ abind_var_typ A) ++ Θ0) ->
              ((x ~ abind_var_typ A) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Ps).
    { intros y Ps Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ discriminate | apply a_wf_pskl_weaken_cons; exact (Hskl _ _ Hb') ]. }
    destruct (H1 x ltac:(clear - Hx; fsetdec) Hwfx Hsklx
                ltac:(apply a_wf_pskl__hole) a_sk_mode_compat__tc
                (a_wf_exp_weaken_cons x (abind_var_typ A)
                   (Hexp0 x ltac:(clear - Hx; fsetdec))))
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
    assert (Hwf1 : a_wf_aenv (Ξ ++ Θ1))
      by (eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []).
    assert (HwfP' : (Ξ ++ Θ1) ⨟ empty ⊢ₚₛᵃ P').
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
    destruct (IHa_pat1 Hwf Hskl ltac:(apply a_wf_pskl__hole)
                a_sk_mode_compat__tc Hexp2)
      as [Hle1 [Hwf1 [Qt1 [HeQt1 [Hpat1 Href1]]]]].
    destruct (ad_refine_syn_syn_l Href1 pskl_hole eq_refl) as [P' HQt1].
    subst Qt1.
    assert (HwfPin : Θ1 ⨟ empty ⊢ₚₛᵃ P').
    { pose proof (ad_refine_syn_hole_l_target_wf Href1) as Hw.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw. exact Hw. }
    rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt1. subst P0.
    assert (Hskl1 : forall y Ps, binds y (abind_var_skl Ps) Θ1 ->
                      Θ1 ⨟ empty ⊢ₚₛᵃ Ps).
    { intros y Ps Hb. eapply a_wf_pskl_isub; [ | exact Hle1 ].
      apply (Hskl y). apply (a_pat_tm_ge H); [ exact I | exact Hb ]. }
    destruct (IHa_pat2 Hwf1 Hskl1
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
