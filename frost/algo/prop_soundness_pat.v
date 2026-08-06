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
