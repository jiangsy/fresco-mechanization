(** Stability of the declarative-over-Θ judgments under information
    increase (the paper's "stability" remark, proofs.tex:19-26): if
    [Θ ⊢ J] and [Θ ⊴ Θ'], then [Θ' ⊢ J].

    The judgments only consult the context through (i) tvar-ish variable
    lookups, (ii) flexible-definition lookups (FlexL/FlexR), and (iii)
    rigid-tvar extensions for binders — all transported by the [prop_inc]
    kit and the definition-preservation component of [⊴]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo.prop_inc.

Set Implicit Arguments.

(* ===================================================================== *)
(*  ⊴ transport wrappers                                                  *)
(* ===================================================================== *)

Lemma a_isub_binds_tvarish : forall Θ Θ' α,
  Θ ⊴ Θ' ->
  a_binds_tvar α Θ ->
  a_binds_tvar α Θ'.
Proof.
  intros * [[κ [Hid Hinc]] _] Hb. eauto using a_inc_binds_tvarish.
Qed.

Lemma a_isub_binds_flex_def : forall Θ Θ' α τ,
  Θ ⊴ Θ' ->
  binds α (abind_flex_mono_def τ) Θ ->
  binds α (abind_flex_mono_def τ) Θ'.
Proof. intros * [_ Hd] Hb. auto. Qed.

(** ⊴ is preserved by pushing a rigid tvar on both sides. *)
Lemma a_isub_cons_tvar : forall Θ Θ' α',
  Θ ⊴ Θ' ->
  ((α' ~ abind_tvar) ++ Θ) ⊴ ((α' ~ abind_tvar) ++ Θ').
Proof.
  intros * [[κ [Hid Hinc]] Hd]. split.
  - exists κ. split; auto.
    apply (a_inc__tvar (Ξ := nil)); auto. constructor.
  - intros α τ Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    unfold binds; apply in_or_app; right. apply Hd; auto.
Qed.

(* ===================================================================== *)
(*  Stability of the Θ-level declarative judgments                        *)
(* ===================================================================== *)

Lemma a_wf_pskl_isub : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ', Θ ⊴ Θ' ->
  {{ Θ' ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P H; induction H; intros Θ' Hle;
    eauto using a_wf_pskl.
  - (* var *)
    apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
Qed.

Lemma ad_pat_consis_isub : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Θ', Θ ⊴ Θ' ->
  {{ Ψ ⨟ Θ' ⊢ˢ R ∼ Q }}ad.
Proof.
  intros Ψ Θ R Q H; induction H; intros Θ' Hle.
  - apply ad_pat_consis__unit; auto.
  - apply ad_pat_consis__var; eauto using a_isub_binds_tvarish.
  - eapply ad_pat_consis__arrow; eauto.
  - eapply ad_pat_consis__forall_inh_tagged with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - eapply ad_pat_consis__forall_inh_untagged with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - eapply ad_pat_consis__forall_syn_tagged with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - eapply ad_pat_consis__forall_syn with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_pat_consis__ghostg; auto.
  - apply ad_pat_consis__topholeg; auto.
  - apply ad_pat_consis__hole; eauto using a_wf_pskl_isub.
  - apply ad_pat_consis__tophole; auto.
  - eapply ad_pat_consis__tophole_inh with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_pat_consis__tophole_drop; auto.
  - eapply ad_pat_consis__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_pat_consis__flex_r; eauto using a_isub_binds_flex_def.
Qed.

Lemma ad_refine_syn_isub : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Θ', Θ ⊴ Θ' ->
  {{ Θ' ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros Θ Δ Q Q' H; induction H; intros Θ' Hle.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
    destruct H as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
  - apply ad_refine_syn__arrow; auto.
  - eapply ad_refine_syn__all with (L := L); eauto.
  - apply ad_refine_syn__hole; eauto using a_wf_pskl_isub.
  - apply ad_refine_syn__tophole_remove; auto.
  - eapply ad_refine_syn__tophole_fill with (L := L).
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_refine_syn__flex_r; eauto using a_isub_binds_flex_def.
Qed.

Lemma ad_refine_pskl_isub : forall Θ Δ P P',
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
  forall Θ', Θ ⊴ Θ' ->
  {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros Θ Δ P P' H; induction H; intros Θ' Hle.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var.
    destruct H as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
  - apply ad_refine_pskl__arrow; auto.
  - eapply ad_refine_pskl__all with (L := L); eauto.
  - apply ad_refine_pskl__hole; eauto using a_wf_pskl_isub.
  - apply ad_refine_pskl__tophole_remove; auto.
  - eapply ad_refine_pskl__tophole_fill with (L := L).
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_refine_pskl__tophole_keep; auto.
  - eapply ad_refine_pskl__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_refine_pskl__flex_r; eauto using a_isub_binds_flex_def.
Qed.

(** The JOIN is stable because both of its halves are. *)
Lemma ad_consis_join_isub : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
  forall Θ', Θ ⊴ Θ' ->
  {{ Ψ ⨟ Θ' ⊢ˢ R ∼ᵣ Q }}ad.
Proof.
  intros Ψ Θ R Q [Hc Hr] Θ' Hle. split.
  - eapply ad_pat_consis_isub; eassumption.
  - eapply ad_refine_pskl_isub; eassumption.
Qed.

(* ===================================================================== *)
(*  §  Term entries survive every run VERBATIM                            *)
(*                                                                        *)
(*  The paper transports typing judgments along information increase and   *)
(*  calls it obvious (proofs.tex:19-26).  In the mechanization [⊴] alone   *)
(*  is NOT enough at the term-variable rules: [a_inc__var] preserves a     *)
(*  term entry only UP TO [≡ᵗ] (the semantic-entries relaxation that       *)
(*  optimality forced, def_meta.v:224).  What rescues the paper's          *)
(*  argument is a fact it leaves implicit: THE ALGORITHM NEVER REWRITES A  *)
(*  TERM ENTRY — every context-transforming row of every run re-attaches   *)
(*  term entries unchanged (the Skip-TmVar rows; every other row touches   *)
(*  only type-level entries).  This section proves that invariant across   *)
(*  the cluster; the [ad_pat] / [ad_sd_typing] stability lemmas combine    *)
(*  it with [⊴].  (The look / solve / extract layer never transforms its   *)
(*  context — it only EMITS suffixes — so it needs no lemma here.)         *)
(* ===================================================================== *)

(** The two term-entry forms — the entries [a_binds_tvar] and the flexible
    lookups cannot see, and the Var rules of [ad_pat] / [ad_sd_typing] read. *)
Definition abind_is_tm (b : abind) : Prop :=
  match b with
  | abind_var_typ _ | abind_var_skl _ => True
  | abind_tvar | abind_flex_mono | abind_flex_mono_def _ => False
  end.

(** Every term entry of [Θ] appears VERBATIM in [Θ']. *)
Definition aenv_tm_le (Θ Θ' : aenv) : Prop :=
  forall x b, abind_is_tm b -> binds x b Θ -> binds x b Θ'.

Lemma aenv_tm_le_refl : forall Θ, aenv_tm_le Θ Θ.
Proof. intros Θ x b _ H; exact H. Qed.

Lemma aenv_tm_le_trans : forall Θ1 Θ2 Θ3,
  aenv_tm_le Θ1 Θ2 -> aenv_tm_le Θ2 Θ3 -> aenv_tm_le Θ1 Θ3.
Proof. intros * H12 H23 x b Htm H; auto. Qed.

Lemma aenv_tm_le_cons : forall Θ Θ' y (c : abind),
  aenv_tm_le Θ Θ' -> aenv_tm_le ((y ~ c) ++ Θ) ((y ~ c) ++ Θ').
Proof.
  intros Θ Θ' y c Hle x b Htm Hb.
  apply binds_app_1 in Hb as [Hb | Hb]; [ apply binds_app_2; exact Hb | ].
  apply binds_app_3; auto.
Qed.

(** A non-term head cannot be the looked-up entry. *)
Lemma binds_tm_cons_inv : forall x (b : abind) y (c : abind) Θ,
  abind_is_tm b -> ~ abind_is_tm c ->
  binds x b ((y ~ c) ++ Θ) -> binds x b Θ.
Proof.
  intros * Htm Hc Hb.
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
    [ subst; contradiction | exact Hb' ].
Qed.

(** A pending-suffix block is flexible-only, hence term-free. *)
Lemma binds_tm_strip_suffix : forall Ξ x (b : abind) Θ,
  a_suffix Ξ -> abind_is_tm b ->
  binds x b (Ξ ++ Θ) -> binds x b Θ.
Proof.
  intros Ξ; induction Ξ as [ | [y c] Ξ' IH ]; intros x b Θ Hsuf Htm Hb.
  - exact Hb.
  - inversion Hsuf as [ | y0 c0 Ξ0 Hsuf' Hbind Heq ]; subst.
    apply (IH x b Θ Hsuf' Htm).
    eapply binds_tm_cons_inv with (y := y) (c := c);
      [ exact Htm | inversion Hbind; subst; intros [] | exact Hb ].
Qed.

Lemma aenv_tm_le_weaken_r : forall Ξ Θ Θ',
  aenv_tm_le Θ Θ' -> aenv_tm_le Θ (Ξ ++ Θ').
Proof. intros * Hle x b Htm Hb. apply binds_app_3; auto. Qed.

Lemma aenv_tm_le_src_cons_nontm : forall Θ Θ' y (c : abind),
  ~ abind_is_tm c ->
  aenv_tm_le Θ Θ' -> aenv_tm_le ((y ~ c) ++ Θ) Θ'.
Proof.
  intros * Hc Hle x b Htm Hb.
  apply Hle; [ exact Htm | eapply binds_tm_cons_inv; eauto ].
Qed.

(** Source-side weakening: a fact about the LARGER source restricts. *)
Lemma aenv_tm_le_of_app_src : forall Ξ Θ Θ',
  aenv_tm_le (Ξ ++ Θ) Θ' -> aenv_tm_le Θ Θ'.
Proof.
  intros * Hle x b Htm Hb. apply Hle; [ exact Htm | apply binds_app_3; exact Hb ].
Qed.

(** Target-side strips: what the ForallR-shaped rows need. *)
Lemma aenv_tm_le_strip_suffix_tgt : forall Ξ Θ Θ',
  a_suffix Ξ ->
  aenv_tm_le Θ (Ξ ++ Θ') -> aenv_tm_le Θ Θ'.
Proof.
  intros * Hsuf Hle x b Htm Hb.
  eapply binds_tm_strip_suffix; [ exact Hsuf | exact Htm | auto ].
Qed.

Lemma aenv_tm_le_strip_cons_tgt : forall y (c : abind) Θ Θ',
  ~ abind_is_tm c ->
  aenv_tm_le Θ ((y ~ c) ++ Θ') -> aenv_tm_le Θ Θ'.
Proof.
  intros * Hc Hle x b Htm Hb.
  eapply binds_tm_cons_inv; [ exact Htm | exact Hc | auto ].
Qed.

Lemma aenv_tm_le_peel_cons_nontm : forall y (c : abind) Θ Θ',
  ~ abind_is_tm c ->
  aenv_tm_le ((y ~ c) ++ Θ) ((y ~ c) ++ Θ') -> aenv_tm_le Θ Θ'.
Proof.
  intros * Hc Hle.
  eapply aenv_tm_le_strip_cons_tgt; [ exact Hc | ].
  eapply aenv_tm_le_of_app_src with (Ξ := (y ~ c)); exact Hle.
Qed.

(** The consistency cluster (3-way mutual). *)
Lemma a_assign_unify_consis_tm_le :
  (forall Θ0 Ξ α P Θ1, {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> aenv_tm_le Θ0 Θ1) /\
  (forall Θ0 α β Θ1, {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> aenv_tm_le Θ0 Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P Q Θ1,
     a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 -> aenv_tm_le Θ0 Θ1).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun Θ0 Ξ α P Θ1 _ => aenv_tm_le Θ0 Θ1)
           (fun Θ0 α β Θ1 _ => aenv_tm_le Θ0 Θ1)
           (fun Δ1 Δ2 Θ0 P0 P Q Θ1 _ => aenv_tm_le Θ0 Θ1)).
  (* ---------- a_assign ---------- *)
  - (* univ_ghost_id *) intros; apply aenv_tm_le_refl.
  - (* solve_m *)
    intros Θ0 Ξ α P βs τ Hαn Hg Hm Hu Hfr.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    repeat apply aenv_tm_le_weaken_r. apply aenv_tm_le_refl.
  - (* assign *)
    intros Θ0 Θ1 Ξ α β τ P Q Hflex Hβ Hc IH.
    apply aenv_tm_le_cons. eapply aenv_tm_le_of_app_src; exact IH.
  - (* depend *)
    intros Θ0 Θ1 Ξ α β P Hne Hβ Ha IH.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | exact IH ].
  - (* skip *) intros; apply aenv_tm_le_cons; assumption.
  - (* skip_rigid *) intros; apply aenv_tm_le_cons; assumption.
  - (* skip_tm_var *) intros; apply aenv_tm_le_cons; assumption.
  - (* skip_tm_skl *) intros; apply aenv_tm_le_cons; assumption.
  (* ---------- a_unify ---------- *)
  - (* flex_id *) intros; apply aenv_tm_le_refl.
  - (* flex_l *)
    intros Θ0 α β Hne Hβ.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    apply aenv_tm_le_weaken_r. apply aenv_tm_le_refl.
  - (* flex_r *)
    intros Θ0 α β Hne Hα.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    apply aenv_tm_le_weaken_r. apply aenv_tm_le_refl.
  - (* flex_assign *)
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
    eapply aenv_tm_le_trans; eassumption.
  - (* forall_inh *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar); [ intros [] | exact IH ].
  - (* forall_syn *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar); [ intros [] | exact IH ].
  - (* univ_ghost *) intros; assumption.
  - (* univ_ghost1 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar); [ intros [] | exact IH ].
  - (* univ_ghost2 *) intros; assumption.
  - (* flex *) intros; assumption.
  - (* flex_l *) intros; assumption.
  - (* flex_r *) intros; assumption.
  - (* ghost_r *) intros; apply aenv_tm_le_refl.
  - (* univ_ghost_r *) intros; assumption.
Qed.

Lemma a_consis_tm_le : forall Δ1 Δ2 Θ0 P0 P Q Θ1,
  a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 -> aenv_tm_le Θ0 Θ1.
Proof. intros; eapply (proj2 (proj2 a_assign_unify_consis_tm_le)); eauto. Qed.

Lemma a_consis_chk_tm_le : forall Θ0 P P0 Θ1,
  a_consis_chk Θ0 P P0 Θ1 -> aenv_tm_le Θ0 Θ1.
Proof. intros * [Q Hc]; eapply a_consis_tm_le; eauto. Qed.

(** The subtyping cluster (2-way mutual). *)
Scheme a_sub_tm_sind := Induction for a_sub Sort Prop
  with a_sub_flex_tm_sind := Induction for a_sub_flex Sort Prop.
Combined Scheme a_sub_sub_flex_tm_mutind
  from a_sub_tm_sind, a_sub_flex_tm_sind.

Lemma a_sub_sub_flex_tm_le :
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 -> aenv_tm_le Θ0 Θ1) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 -> aenv_tm_le Θ0 Θ1).
Proof.
  apply (a_sub_sub_flex_tm_mutind
           (fun NM M P0 Θ0 P Q Θ1 _ => aenv_tm_le Θ0 Θ1)
           (fun NM M P0 Θ0 Ξ α Q Θ1 _ => aenv_tm_le Θ0 Θ1)).
  (* ---------- a_sub ---------- *)
  - (* infer *) intros; apply aenv_tm_le_refl.
  - (* check *)
    intros Θ0 Θ1 A B Hgf1 Hgf2 Hg1 Hg2 Hchk.
    eapply a_consis_chk_tm_le; exact Hchk.
  - (* forall_r *)
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huniq Hnotin Hrun IH.
    eapply aenv_tm_le_strip_cons_tgt with (y := α) (c := abind_tvar);
      [ intros [] | ].
    eapply aenv_tm_le_strip_suffix_tgt; [ exact Hsuf | ].
    eapply aenv_tm_le_of_app_src with (Ξ := (α ~ abind_tvar)); exact IH.
  - (* univ_ghost_r *) intros; apply aenv_tm_le_refl.
  - (* flex_mono *) intros; assumption.
  - (* arrow *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH.
    eapply aenv_tm_le_trans; [ eapply a_consis_tm_le; exact Hc | exact IH ].
  - (* forall_l *)
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hm Hg Hα Hext Huniq Hwf Hs IH.
    eapply aenv_tm_le_of_app_src with (Ξ := Ξ); exact IH.
  - (* ghost *) intros; apply aenv_tm_le_refl.
  - (* univ_ghost_l *) intros; assumption.
  (* ---------- a_sub_flex ---------- *)
  - (* solve *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hα Hβ Hs IH.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    do 4 eapply aenv_tm_le_of_app_src. exact IH.
  - (* assign *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβ Hs IH.
    apply aenv_tm_le_cons. eapply aenv_tm_le_of_app_src; exact IH.
  - (* depend *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hβ Hs IH.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | exact IH ].
  - (* skip *) intros; apply aenv_tm_le_cons; assumption.
  - (* skip_rigid *) intros; apply aenv_tm_le_cons; assumption.
  - (* skip_tm_var *) intros; apply aenv_tm_le_cons; assumption.
  - (* skip_tm_skl *) intros; apply aenv_tm_le_cons; assumption.
Qed.

Lemma a_sub_tm_le : forall NM M P0 Θ0 P Q Θ1,
  a_sub NM M P0 Θ0 P Q Θ1 -> aenv_tm_le Θ0 Θ1.
Proof. intros; eapply (proj1 a_sub_sub_flex_tm_le); eauto. Qed.

Lemma a_split_tm_le : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a -> aenv_tm_le Θ0 Θ1.
Proof.
  intros * H; inversion H; subst; try apply aenv_tm_le_refl.
  (* flex : a full consistency run over two fresh flexibles *)
  match goal with
  | Hc : a_consis _ _ _ _ _ _ _ |- _ => apply a_consis_tm_le in Hc
  end.
  do 2 eapply aenv_tm_le_of_app_src; eassumption.
Qed.

(** The one step every binder row repeats: enter under the walked entry
    [x ~ bx], cross the body's run, then peel the pending suffix and the
    re-attached [x] off the output — legitimate because the looked-up name
    [y] is not the (freshly chosen) binder. *)
Lemma aenv_tm_le_via_binder : forall Ξ x (bx : abind) Θ Θ',
  a_suffix Ξ ->
  aenv_tm_le ((x ~ bx) ++ Θ) (Ξ ++ (x ~ bx) ++ Θ') ->
  forall y b, abind_is_tm b -> y <> x -> binds y b Θ -> binds y b Θ'.
Proof.
  intros * Hsuf Hle y b Htm Hne Hb.
  assert (Hb1 : binds y b (Ξ ++ (x ~ bx) ++ Θ'))
    by (apply Hle; [ exact Htm | apply binds_app_3; exact Hb ]).
  apply binds_tm_strip_suffix in Hb1; [ | exact Hsuf | exact Htm ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[Heq _] | Hb2];
    [ subst; contradiction | exact Hb2 ].
Qed.

(** Skeleton inference runs.  The Abs rows drop the walked binder [x] from
    the output; the invariant survives because the looked-up name [y] IS
    bound in the body run's input while [x], by the row's own side
    condition, is not — so the two are distinct.

    ⚙ Before the 2026-08-13 exists-fresh conversion these rows CHOSE an [x]
    away from [y] and instantiated the cofinite family there.  Exists-fresh
    hands the binder over, so the disequality is derived instead of arranged
    — one [binds_In] per row. *)
Lemma a_pat_tm_le : forall m Θ0 P0 e P Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ P ⊣ Θ1 }}a -> aenv_tm_le Θ0 Θ1.
Proof.
  intros m Θ0 P0 e P Θ1 H; induction H.
  - (* unit *) eapply a_sub_tm_le; eassumption.
  - (* var *) eapply a_sub_tm_le; eassumption.
  - (* var_skl *) eapply a_sub_tm_le; eassumption.
  - (* anno *) eapply a_sub_tm_le; eassumption.
  - (* freeze *) assumption.
  - (* abs *)
    intros y b Htm Hb.
    apply a_split_tm_le in H0.
    assert (Hb1 : binds y b Θ1) by (apply H0; [ exact Htm | exact Hb ]).
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H1 | exact IHa_pat | exact Htm | | exact Hb1 ].
    intros Heq; subst.
    apply binds_In in Hb1. simpl_env in H2. clear - H2 Hb1. fsetdec.
  - (* abs_anno *)
    intros y b Htm Hb.
    apply a_split_tm_le in H0.
    apply a_consis_chk_tm_le in H1.
    assert (Hb2 : binds y b Θ2)
      by (apply H1; [ exact Htm | apply H0; [ exact Htm | exact Hb ] ]).
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H2 | exact IHa_pat | exact Htm | | exact Hb2 ].
    intros Heq; subst.
    apply binds_In in Hb2. simpl_env in H3. clear - H3 Hb2. fsetdec.
  - (* abs_check *)
    intros y b Htm Hb.
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H | exact IHa_pat | exact Htm | | exact Hb ].
    intros Heq; subst.
    apply binds_In in Hb. simpl_env in H0. clear - H0 Hb. fsetdec.
  - (* abs_anno_check *)
    intros y b Htm Hb.
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H | exact IHa_pat | exact Htm | | exact Hb ].
    intros Heq; subst.
    apply binds_In in Hb. simpl_env in H0. clear - H0 Hb. fsetdec.
  - (* app *) eapply aenv_tm_le_trans; eassumption.
Qed.

(** Type inference runs — same shapes; the Check rows additionally drop
    the peeled binder and the pending suffix from the OUTPUT. *)
Lemma a_typing_tm_le : forall m Θ0 P0 e A Θ1,
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ A ⊣ Θ1 }}a -> aenv_tm_le Θ0 Θ1.
Proof.
  intros m Θ0 P0 e A Θ1 H; induction H.
  - (* unit *) eapply a_sub_tm_le; eassumption.
  - (* var *) eapply a_sub_tm_le; eassumption.
  - (* anno *)
    eapply aenv_tm_le_trans; [ eassumption | eapply a_sub_tm_le; eassumption ].
  - (* freeze *)
    eapply aenv_tm_le_trans;
      [ eassumption | eapply a_consis_chk_tm_le; eassumption ].
  - (* abs — the body also sits under the [a_guess_mono] flexibles [αs].
       The rule's own binder serves everywhere below: a tm entry pins
       y ∈ dom of the context the binder avoids. *)
    intros y b Htm Hb.
    apply a_split_tm_le in H0.
    assert (Hb1 : binds y b Θ1) by (apply H0; [ exact Htm | exact Hb ]).
    pose proof (binds_In _ y b _ Hb1) as Hy.
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H3 | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H4 Hy; rewrite !dom_app in H4; fsetdec
      | apply binds_app_3; exact Hb1 ].
  - (* abs_anno *)
    intros y b Htm Hb.
    apply a_split_tm_le in H0.
    apply a_consis_chk_tm_le in H1.
    assert (Hb1 : binds y b Θ2)
      by (apply H1; [ exact Htm | apply H0; [ exact Htm | exact Hb ] ]).
    pose proof (binds_In _ y b _ Hb1) as Hy.
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H2 | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H3 Hy; rewrite !dom_app in H3; fsetdec
      | exact Hb1 ].
  - (* abs_check_step — the α entry is type-level, so the strip is by shape *)
    intros y b Htm Hb.
    pose proof (binds_In _ y b _ Hb) as Hy.
    eapply aenv_tm_le_via_binder with (x := α);
      [ exact H | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H2 Hy; rewrite !dom_app in H2; fsetdec
      | exact Hb ].
  - (* abs_check_base *)
    intros y b Htm Hb.
    apply a_split_tm_le in H.
    assert (Hb1 : binds y b Θ1) by (apply H; [ exact Htm | exact Hb ]).
    pose proof (binds_In _ y b _ Hb1) as Hy.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H0 | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H3 Hy; rewrite !dom_app in H3; fsetdec
      | exact Hb1 ].
  - (* abs_anno_check_step *)
    intros y b Htm Hb.
    pose proof (binds_In _ y b _ Hb) as Hy.
    eapply aenv_tm_le_via_binder with (x := α);
      [ exact H | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H2 Hy; rewrite !dom_app in H2; fsetdec
      | exact Hb ].
  - (* abs_anno_check_base *)
    intros y b Htm Hb.
    apply a_split_tm_le in H.
    apply a_consis_chk_tm_le in H0.
    assert (Hb1 : binds y b Θ2)
      by (apply H0; [ exact Htm | apply H; [ exact Htm | exact Hb ] ]).
    pose proof (binds_In _ y b _ Hb1) as Hy.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H1 | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H4 Hy; rewrite !dom_app in H4; fsetdec
      | exact Hb1 ].
  - (* app *)
    eapply aenv_tm_le_trans; [ eapply a_pat_tm_le; eassumption | ].
    eapply aenv_tm_le_trans; eassumption.
Qed.
