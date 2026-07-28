(** Soundness of the flexible-variable machinery (paper
    thm:sound-consistency, part 2): a [unifyvar] run is an identity
    information increase (dom-preserving) whose target equates the two
    subjects.  For monotypes, declarative consistency coincides with type
    equivalence under the context's definitions, so the declarative
    conclusion is stated with [a_tyequiv]; ∼/⊳-shaped corollaries are
    derived at their decorated-soundness use sites. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Monotype / wf bookkeeping                                             *)
(* ===================================================================== *)

Lemma mono_ptyp_lc : forall A, mono_ptyp A -> lc_ptyp A.
Proof. intros A H; induction H; auto. Qed.

Lemma mono_ptyp_subst : forall A τ α1,
  mono_ptyp A -> mono_ptyp τ ->
  mono_ptyp (subst_ptyp_in_ptyp τ α1 A).
Proof.
  intros * HA Hτ; induction HA; simpl; eauto using mono_ptyp.
  destruct (eq_var α α1); eauto using mono_ptyp.
Qed.

Lemma a_wf_ptyp_weaken : forall Θ Θ' A,
  (forall x b, binds x b Θ -> binds x b Θ') ->
  a_wf_ptyp Θ A ->
  a_wf_ptyp Θ' A.
Proof.
  intros * Hmon Hwf; revert Θ' Hmon; induction Hwf; intros Θ' Hmon;
    eauto using a_wf_ptyp.
  - apply a_wf_ptyp__var.
    destruct H as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; auto.
  - apply a_wf_ptyp__all with (L := L). intros α Hα.
    apply H0; auto. intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
Qed.

Lemma a_tyequiv_weaken_cons : forall Θ (e : list (atom * abind)) A A',
  Θ ⊢ A ≡ᵗ A' ->
  (e ++ Θ) ⊢ A ≡ᵗ A'.
Proof.
  intros. eapply a_tyequiv_weaken; [ | eauto ].
  intros x b Hb. unfold binds; apply in_or_app; auto.
Qed.

(** Unfolding a definition inside a monotype: [A ≡ A[τ/α1̂]] when [α1̂:=τ]. *)
Lemma a_tyequiv_subst_def : forall Θ α1 τ A,
  binds α1 (abind_flex_mono_def τ) Θ ->
  mono_ptyp A ->
  lc_ptyp τ ->
  Θ ⊢ A ≡ᵗ (subst_ptyp_in_ptyp τ α1 A).
Proof.
  intros * Hb Hm Hlc; induction Hm; simpl.
  - apply a_tyequiv__refl; auto.
  - destruct (eq_var α α1); subst.
    + apply a_tyequiv__flex_def; auto.
    + apply a_tyequiv__refl; auto.
  - apply a_tyequiv__arrow; auto.
Qed.

(* ===================================================================== *)
(*  Target weakening of information increase, and ⊴ cons congruences      *)
(* ===================================================================== *)

Lemma a_inc_target_weaken : forall Θ ρ Θ' Ξ,
  ρ ∷ Θ ⊑ Θ' ->
  a_suffix Ξ ->
  ρ ∷ Θ ⊑ (Ξ ++ Θ').
Proof.
  intros * Hinc; revert Ξ; induction Hinc; intros Ξ0 HΞ0.
  - apply a_inc__empty. apply a_suffix_app; auto.
  - apply a_inc__flex; auto.
    eapply a_wf_ptyp_weaken; [ | eauto ].
    intros; unfold binds; apply in_or_app; auto.
  - apply a_inc__flex_def; auto.
    + eapply a_wf_ptyp_weaken; [ | eauto ].
      intros; unfold binds; apply in_or_app; auto.
    + apply a_tyequiv_weaken_cons; auto.
  - first [ rewrite <- app_assoc | rewrite app_assoc ].
    apply a_inc__var; auto using a_suffix_app.
  - first [ rewrite <- app_assoc | rewrite app_assoc ].
    apply a_inc__var_skl; auto using a_suffix_app.
  - first [ rewrite <- app_assoc | rewrite app_assoc ].
    apply a_inc__tvar; auto using a_suffix_app.
Qed.

(** ⊴ is preserved by pushing the SAME flexible declaration / definition /
    term-var / rigid entry on both sides. *)
Lemma a_isub_cons_flex : forall Θ Θ' α1,
  Θ ⊴ Θ' ->
  ((α1 ~ abind_flex_mono) ++ Θ) ⊴ ((α1 ~ abind_flex_mono) ++ Θ').
Proof.
  intros * [[ρ [Hid Hinc]] Hd]. split.
  - exists ((α1, ptyp_var_f α1) :: ρ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex.
    + apply a_inc_target_weaken; auto.
      apply (a_suffix__cons α1 (b := abind_flex_mono)); constructor.
    + apply a_wf_ptyp__var. right; left. unfold binds; left; reflexivity.
    + constructor.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

Lemma a_isub_cons_flex_def : forall Θ Θ' α1 τ,
  Θ ⊴ Θ' ->
  lc_ptyp τ ->
  ((α1 ~ abind_flex_mono_def τ) ++ Θ) ⊴ ((α1 ~ abind_flex_mono_def τ) ++ Θ').
Proof.
  intros * [[ρ [Hid Hinc]] Hd] Hlc. split.
  - exists ((α1, ptyp_var_f α1) :: ρ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex_def.
    + apply a_inc_target_weaken; auto.
      apply (a_suffix__cons α1 (b := abind_flex_mono_def τ)); constructor.
    + apply a_wf_ptyp__var. right; right. exists τ.
      unfold binds; left; reflexivity.
    + constructor.
    + rewrite msubst_ptyp_id; auto.
      apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb']; subst.
    + inversion Heq; subst. unfold binds; left; reflexivity.
    + unfold binds; right. apply Hd; auto.
Qed.

Lemma a_isub_cons_var_typ : forall Θ Θ' x A,
  Θ ⊴ Θ' ->
  lc_ptyp A ->
  ((x ~ abind_var_typ A) ++ Θ) ⊴ ((x ~ abind_var_typ A) ++ Θ').
Proof.
  intros * [[ρ [Hid Hinc]] Hd] Hlc. split.
  - exists ρ. split; auto.
    replace ((x ~ abind_var_typ A) ++ Θ')
      with (nil ++ (x ~ abind_var_typ A) ++ Θ') by reflexivity.
    apply a_inc__var; auto; [ | constructor ].
    rewrite msubst_ptyp_id; auto. apply a_tyequiv__refl; auto.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

Lemma a_isub_cons_var_skl : forall Θ Θ' x P,
  Θ ⊴ Θ' ->
  lc_pskl P ->
  ((x ~ abind_var_skl P) ++ Θ) ⊴ ((x ~ abind_var_skl P) ++ Θ').
Proof.
  intros * [[ρ [Hid Hinc]] Hd] Hlc. split.
  - exists ρ. split; auto.
    replace ((x ~ abind_var_skl P) ++ Θ')
      with (nil ++ (x ~ abind_var_skl P) ++ Θ') by reflexivity.
    apply a_inc__var_skl; auto; [ | constructor ].
    rewrite msubst_pskl_id; auto. apply a_pskl_tyequiv__refl; auto.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

(* ===================================================================== *)
(*  Soundness of variable unification (thm:sound-consistency part 2)      *)
(* ===================================================================== *)

(* [a_unify_sound] MOVED to prop_consis_sound.v: with the corrected
   [Flex-Flex-Assign] (whose premise is CONSISTENCY, not [unifyvar]),
   [a_unify] and [a_consis] are MUTUALLY inductive, so their soundness is one
   mutual induction ([a_unify_consis_mutind]).  That is also how the paper
   organises its own proof (consistency-proofs.tex:1562). *)


(* ===================================================================== *)
(*  Source-prefix machinery for assignvar (the [Θ0 | Ξ] split): flexible  *)
(*  declarations can be prepended to the SOURCE of an increase whenever   *)
(*  they are still visible in the target.                                 *)
(* ===================================================================== *)

Lemma a_wf_ptyp_lc : forall Θ A, a_wf_ptyp Θ A -> lc_ptyp A.
Proof.
  intros * H; induction H; auto.
Qed.

Lemma a_scope_pskl_lc : forall Θ P, a_scope_pskl Θ P -> lc_pskl P.
Proof.
  intros * H; induction H; auto.
Qed.

(** Well-formed contexts have locally closed binding payloads — the bridge
    that feeds [lc_aenv]-hypothesised reflexivity ([a_isub_refl] below). *)
Lemma a_wf_aenv_lc_aenv : forall Θ, a_wf_aenv Θ -> lc_aenv Θ.
Proof.
  intros Θ H; induction H; constructor; simpl; auto.
  - eapply a_scope_pskl_lc; eauto.
  - eapply a_wf_ptyp_lc; eauto.
Qed.

#[export] Hint Resolve a_wf_aenv_lc_aenv : core.

(** The unconditional [a_isub_refl] of the syntactic-middle era, restored
    for well-formed contexts. *)
Lemma a_isub_refl : forall Θ, a_wf_aenv Θ -> Θ ⊴ Θ.
Proof.
  intros Θ Hwf. apply a_isub_refl_lc; auto.
Qed.

(** Declaration-only suffixes (the paper's "Ξ only contains declarations
    of flexible variables"). *)
Inductive a_decls : aenv -> Prop :=
| a_decls__nil : a_decls nil
| a_decls__cons : forall α1 Ξ,
    a_decls Ξ ->
    a_decls ((α1 ~ abind_flex_mono) ++ Ξ).

Lemma a_decls_suffix : forall Ξ, a_decls Ξ -> a_suffix Ξ.
Proof.
  intros Ξ H; induction H; [ constructor | ].
  apply (a_suffix__cons α1 (b := abind_flex_mono)); auto; constructor.
Qed.

Lemma a_inc_prepend_flex_src : forall Θ ρ Θ' α1,
  ρ ∷ Θ ⊑ Θ' ->
  a_binds_tvar α1 Θ' ->
  (α1, ptyp_var_f α1) :: ρ ∷ ((α1 ~ abind_flex_mono) ++ Θ) ⊑ Θ'.
Proof.
  intros * Hinc Hb.
  apply a_inc__flex; auto;
    try (apply a_wf_ptyp__var; auto);
    try constructor.
Qed.

Lemma a_isub_prepend_decls_src : forall Ξ Θ Θ',
  a_decls Ξ ->
  (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ') ->
  Θ ⊴ Θ' ->
  (Ξ ++ Θ) ⊴ Θ'.
Proof.
  intros Ξ; induction Ξ as [ | [α1 b] Ξ' IH ]; intros Θ Θ' Hdecl Hvis Hle; auto.
  inversion Hdecl; subst.
  assert (Hle' : (Ξ' ++ Θ) ⊴ Θ').
  { apply IH; auto;
      try (intros α10 Hb0; apply Hvis; unfold binds; right; auto). }
  destruct Hle' as [[ρ [Hid Hinc]] Hd].
  split.
  - exists ((α1, ptyp_var_f α1) :: ρ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc_prepend_flex_src; auto;
      try (apply Hvis; unfold binds; left; reflexivity).
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | auto ].
Qed.

(** Every declaration in the source of an identity increase is still
    tvar-ish in the target (specialization of the transport kit). *)
Lemma a_isub_binds_flex : forall Θ Θ' α1,
  Θ ⊴ Θ' ->
  binds α1 abind_flex_mono Θ ->
  a_binds_tvar α1 Θ'.
Proof.
  intros * [[ρ [Hid Hinc]] _] Hb. eauto using a_inc_binds_flex.
Qed.

(** [guess^TY] emits a declaration-only fresh suffix. *)
Lemma a_decls_app : forall Ξ1 Ξ2,
  a_decls Ξ1 -> a_decls Ξ2 -> a_decls (Ξ1 ++ Ξ2).
Proof.
  intros * H1 H2; induction H1; simpl; auto.
  apply (a_decls__cons α1); auto.
Qed.

Lemma a_guess_mono_decls : forall Θ P βs τ,
  a_guess_mono Θ P βs τ ->
  a_decls βs.
Proof.
  intros * H;
    induction H as [ Θ α | Θ P Ξ A Hg IH | Θ α | Θ
                   | Θ P Q Ξ1 Ξ2 A B Hg1 IH1 Hg2 IH2
                   | L Θ P Ξ A Hg IH ].
  - apply (a_decls__cons α). constructor.
  - auto.
  - constructor.
  - constructor.
  - apply a_decls_app; auto.
  - pick fresh α. eauto.
Qed.


(* ===================================================================== *)
(*  Embedding/open commutation (local; coercions.v lacks these two)       *)
(* ===================================================================== *)

Lemma ptyp_to_pskl_open_rec : forall A1 A2 k,
  ptyp_to_pskl (open_ptyp_wrt_ptyp_rec k A2 A1)
  = open_pskl_wrt_pskl_rec k (ptyp_to_pskl A2) (ptyp_to_pskl A1).
Proof.
  induction A1; intros; simpl; f_equal; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma pskl_to_bskl_syn_open_rec : forall P1 P2 k,
  pskl_to_bskl_syn (open_pskl_wrt_pskl_rec k P2 P1)
  = open_bskl_wrt_bskl_rec k (pskl_to_bskl_syn P2) (pskl_to_bskl_syn P1).
Proof.
  induction P1; intros; simpl; f_equal; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma ptyp_to_bskl_syn_open_var : forall A α,
  ptyp_to_bskl_syn (open_ptyp_wrt_ptyp A (ptyp_var_f α))
  = open_bskl_wrt_bskl (ptyp_to_bskl_syn A) (bskl_var_f α).
Proof.
  intros. unfold ptyp_to_bskl_syn, open_ptyp_wrt_ptyp, open_bskl_wrt_bskl.
  rewrite ptyp_to_pskl_open_rec. rewrite pskl_to_bskl_syn_open_rec.
  reflexivity.
Qed.

Lemma a_binds_tvar_weaken_cons : forall α (e : list (atom * abind)) Θ,
  a_binds_tvar α Θ ->
  a_binds_tvar α (e ++ Θ).
Proof.
  intros. rewrite_env (nil ++ e ++ Θ). apply a_binds_tvar_weaken_mid; auto.
Qed.

(* ===================================================================== *)
(*  guess^TY is consistent with its input skeleton                         *)
(*  (the declarative content of Assign-SolveM's definition)               *)
(* ===================================================================== *)

Lemma a_guess_mono_consis : forall Θ P βs τ,
  a_guess_mono Θ P βs τ ->
  forall Θ1,
  (forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono βs -> a_binds_tvar α1 Θ1) ->
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (ptyp_to_bskl_syn τ).
Proof.
  intros * H;
    induction H as [ Θ α | Θ P Ξ A Hg IH | Θ α | Θ
                   | Θ P Q Ξ1 Ξ2 A B Hg1 IH1 Hg2 IH2
                   | L Θ P Ξ A Hg IH ];
    intros Θ1 Hvars Hβs.
  - (* hole ↦ fresh flexible variable *)
    replace (ptyp_to_bskl_syn (ptyp_var_f α))
      with (pskl_to_bskl_inh (pskl_var_f α)) by reflexivity.
    replace (pskl_to_uskl pskl_hole) with uskl_hole by reflexivity.
    apply ad_pat_consis__hole; [ fsetdec | ].
    apply a_wf_pskl__var. right. apply Hβs.
    unfold binds; left; reflexivity.
  - (* ⊤.P : the universal ghost is dropped *)
    replace (pskl_to_uskl (pskl_tophole P))
      with (uskl_tophole (pskl_to_uskl P)) by reflexivity.
    apply ad_pat_consis__tophole_drop. auto.
  - (* variable *)
    replace (pskl_to_uskl (pskl_var_f α))
      with (uskl_var_f α) by reflexivity.
    replace (ptyp_to_bskl_syn (ptyp_var_f α))
      with (bskl_var_f α) by reflexivity.
    apply ad_pat_consis__var; [ fsetdec | ].
    apply Hvars. simpl. fsetdec.
  - (* unit *)
    replace (pskl_to_uskl pskl_unit) with uskl_unit by reflexivity.
    replace (ptyp_to_bskl_syn ptyp_unit) with bskl_unit by reflexivity.
    apply ad_pat_consis__unit. fsetdec.
  - (* arrow *)
    replace (pskl_to_uskl (pskl_arrow P Q))
      with (uskl_arrow (pskl_to_uskl P) (pskl_to_uskl Q)) by reflexivity.
    replace (ptyp_to_bskl_syn (ptyp_arrow A B))
      with (bskl_arrow (ptyp_to_bskl_syn A) (ptyp_to_bskl_syn B))
      by reflexivity.
    apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IH1 | apply IH2 | fsetdec ].
    + intros α Hα. apply Hvars. simpl. fsetdec.
    + intros α1 Hb. apply Hβs. unfold binds in *. apply in_or_app; auto.
    + intros α Hα. apply Hvars. simpl. fsetdec.
    + intros α1 Hb. apply Hβs. unfold binds in *. apply in_or_app; auto.
  - (* forall: synthesised quantifier on both sides *)
    replace (pskl_to_uskl (pskl_all_syn P))
      with (uskl_all_syn (pskl_to_uskl P)) by reflexivity.
    replace (ptyp_to_bskl_syn (ptyp_all A))
      with (bskl_all_syn (ptyp_to_bskl_syn A)) by reflexivity.
    apply ad_pat_consis__forall_syn with (L := L `union` dom Θ1).
    intros α Hα.
    rewrite <- pskl_to_uskl_open_var.
    rewrite <- ptyp_to_bskl_syn_open_var.
    apply IH; [ fsetdec | | ].
    + intros β Hβ.
      apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in Hβ.
      simpl in Hβ.
      destruct (union_1 Hβ) as [HY' | HY'].
      * apply singleton_1 in HY'; subst.
        left. unfold binds; left; reflexivity.
      * apply a_binds_tvar_weaken_cons; auto.
    + intros α1 Hb. apply a_binds_tvar_weaken_cons; auto.
Qed.

(* ===================================================================== *)
(*  Definition folding for skeleton consistency: if [β̂ := τ] and the      *)
(*  τ-unfolded skeleton is consistent with [Q], so is the folded one      *)
(*  (each unfolded occurrence re-wraps with the FlexL lookup rule).       *)
(* ===================================================================== *)

Lemma ad_pat_consis_fold_def : forall Θ β τ Ψ R' Q,
  ad_pat_consis Ψ Θ R' Q ->
  binds β (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->
  forall S0x,
  R' = subst_bskl_in_uskl (ptyp_to_uskl_syn τ) β S0x ->
  ad_pat_consis Ψ Θ S0x Q.
Proof.
  intros Θ β τ Ψ R' Q H Hb Hm.
  assert (Hlcτ : lc_uskl (ptyp_to_uskl_syn τ)).
  { clear - Hm. induction Hm; unfold ptyp_to_uskl_syn in *; simpl; auto. }
  (* β̂-occurrence refolding and mono-embedding head contradictions *)
  induction H; intros S0x HeqS.
  - (* unit *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + apply ad_pat_consis__unit; auto.
    + destruct (eq_var X0x β) as [->|Hne].
      * apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
        rewrite <- HeqS. apply ad_pat_consis__unit; auto.
      * discriminate HeqS.
  - (* var *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    destruct (eq_var X0x β) as [->|Hne].
    + apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
      rewrite <- HeqS. apply ad_pat_consis__var; auto.
    + inversion HeqS; subst. apply ad_pat_consis__var; auto.
  - (* arrow *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne].
      * apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
        rewrite <- HeqS. eapply ad_pat_consis__arrow; eauto.
      * discriminate HeqS.
    + inversion HeqS; subst. eapply ad_pat_consis__arrow; eauto.
  - (* forall_inh_tagged *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_inh_tagged with (L := L `union` {{β}});
        eauto.
      intros α Hα. eapply H0; auto.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* forall_inh_untagged *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_inh_untagged with (L := L `union` {{β}}).
      intros α Hα. eapply H0; auto.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* forall_syn_tagged *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_syn_tagged with (L := L `union` {{β}}).
      intros α Hα. eapply H0; auto.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* forall_syn *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_syn with (L := L `union` {{β}}).
      intros α Hα. eapply H0; auto.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* ghostg *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + apply ad_pat_consis__ghostg; auto.
  - (* topholeg *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst. apply ad_pat_consis__topholeg; auto.
  - (* hole *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + apply ad_pat_consis__hole; auto.
  - (* tophole *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst. apply ad_pat_consis__tophole; auto.
  - (* tophole_inh *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__tophole_inh with (L := L);
        try (intros α Hα; eapply H0; auto; simpl; reflexivity).
  - (* tophole_drop *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst. apply ad_pat_consis__tophole_drop; auto.
  - (* flex_l *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    destruct (eq_var X0x β) as [->|Hne].
    + apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
      rewrite <- HeqS. eapply ad_pat_consis__flex_l; eauto.
    + inversion HeqS; subst. eapply ad_pat_consis__flex_l; eauto.
  - (* flex_r : same LHS, smaller derivation *)
    eapply ad_pat_consis__flex_r; eauto.
Qed.

(* ===================================================================== *)
(*  Support for a_assign soundness: ⊴-level wrappers, wf bookkeeping      *)
(*  across the [Θ0 | Ξ] split, and embedding/substitution commutation.    *)
(* ===================================================================== *)

Lemma a_isub_target_weaken : forall Θ Θ' Ξ,
  Θ ⊴ Θ' ->
  a_suffix Ξ ->
  Θ ⊴ (Ξ ++ Θ').
Proof.
  intros * [[ρ [Hid Hinc]] Hd] HΞ. split.
  - exists ρ. eauto using a_inc_target_weaken.
  - intros α τ0 Hb. unfold binds; apply in_or_app; right. apply Hd; auto.
Qed.

Lemma a_isub_strengthen_decls_src : forall Ξ Θ Θ',
  a_decls Ξ ->
  (Ξ ++ Θ) ⊴ Θ' ->
  Θ ⊴ Θ'.
Proof.
  intros * Hdecl [[ρ [Hid Hinc]] Hd]. split.
  - edestruct a_inc_strengthen_suffix_src as [ρ' [Hid' Hinc']];
      [ eapply a_decls_suffix; eauto | exact Hinc | ].
    exists ρ'. auto.
  - intros α τ0 Hb. apply Hd.
    unfold binds in *; apply in_or_app; auto.
Qed.

(** Stripping a middle entry below a declaration-only prefix preserves
    context well-formedness (declarations carry no scoping content). *)
Lemma a_wf_aenv_strip_mid : forall Ξ (c : atom) (b : abind) Θ,
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ (c ~ b) ++ Θ) ->
  a_wf_aenv (Ξ ++ Θ).
Proof.
  intros Ξ; induction Ξ as [ | [α1 bγ] Ξ' IH ]; intros * Hdecl Hwf.
  - simpl in Hwf. inversion Hwf; subst; auto.
  - inversion Hdecl; subst.
    inversion Hwf; subst.
    apply a_wf_aenv__flex.
    + match goal with
      | Hf : _ `notin` dom _ |- _ `notin` dom _ =>
          repeat rewrite dom_app in *; simpl in *; clear - Hf; fsetdec
      end.
    + apply (IH c b Θ); auto.
Qed.

(** Moving a flexible declaration to the front of a declaration-only
    prefix preserves context well-formedness. *)
Lemma a_wf_aenv_move_decl : forall Ξ β Θ,
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ (β ~ abind_flex_mono) ++ Θ) ->
  a_wf_aenv ((β ~ abind_flex_mono) ++ Ξ ++ Θ).
Proof.
  intros * Hdecl Hwf.
  apply a_wf_aenv__flex.
  - (* β fresh for Ξ ++ Θ *)
    revert Hwf; clear - Hdecl; induction Hdecl; intros Hwf; simpl_env in *.
    + inversion Hwf; subst. auto.
    + inversion Hwf; subst.
      match goal with H : a_wf_aenv _ |- _ => specialize (IHHdecl H) end.
      repeat rewrite dom_app in *; simpl in *.
      match goal with
      | Hα1 : ?g `notin` _ |- _ `notin` _ =>
          clear Hdecl; repeat match goal with
                              | Hw : a_wf_aenv _ |- _ => clear Hw
                              end; fsetdec
      end.
  - eapply a_wf_aenv_strip_mid; eauto.
Qed.

(** [binds] is stable under swapping a middle entry with a prefix. *)
Lemma binds_permute_mid : forall (b : abind) x Ξ (e : list (atom * abind)) Θ,
  binds x b (Ξ ++ e ++ Θ) ->
  binds x b (e ++ Ξ ++ Θ).
Proof.
  intros. unfold binds in *.
  apply in_app_or in H. apply in_or_app.
  destruct H as [H | H]; [ right; apply in_or_app; auto | ].
  apply in_app_or in H. destruct H as [H | H];
    [ auto | right; apply in_or_app; auto ].
Qed.

Lemma a_binds_tvar_permute_mid : forall α Ξ (e : list (atom * abind)) Θ,
  a_binds_tvar α (Ξ ++ e ++ Θ) ->
  a_binds_tvar α (e ++ Ξ ++ Θ).
Proof.
  intros * [Hb | [Hb | [τ0 Hb]]];
    [ left | right; left | right; right; exists τ0 ];
    auto using binds_permute_mid.
Qed.

(** Removing a middle entry that cannot witness the lookup: either the
    atoms differ, or the entry's payload has none of the tvar-ish shapes. *)
Lemma binds_strip_mid : forall (b b' : abind) x c Ξ Θ,
  binds x b (Ξ ++ (c ~ b') ++ Θ) ->
  (x, b) <> (c, b') ->
  binds x b (Ξ ++ Θ).
Proof.
  intros * Hb Hne. unfold binds in *.
  apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb | Hb]; auto.
  destruct Hb as [Hb | Hb]; [ congruence | auto ].
Qed.

Lemma a_binds_tvar_strip_mid : forall α c (b : abind) Ξ Θ,
  a_binds_tvar α (Ξ ++ (c ~ b) ++ Θ) ->
  ((α, abind_tvar) <> (c, b)) ->
  ((α, abind_flex_mono) <> (c, b)) ->
  (forall τ0, (α, abind_flex_mono_def τ0) <> (c, b)) ->
  a_binds_tvar α (Ξ ++ Θ).
Proof.
  intros * [Hb | [Hb | [τ0 Hb]]] Hn1 Hn2 Hn3;
    [ left | right; left | right; right; exists τ0 ];
    eauto using binds_strip_mid.
Qed.

(** Free variables of a well-formed type are tvar-ish in the context. *)
Lemma a_wf_ptyp_ftv_tvarish : forall Θ A α,
  a_wf_ptyp Θ A ->
  α `in` ftvar_in_ptyp A ->
  a_binds_tvar α Θ.
Proof.
  intros * Hwf; revert α; induction Hwf; intros β Hβ; simpl in Hβ.
  - fsetdec.
  (* [α] is the var rule's OWN binder ([a_wf_ptyp__var], algo/def_extra.v),
     auto-bound by [induction Hwf] — not this lemma's α, which [revert α]
     has just generalised away. *)
  - assert (β = α) by fsetdec. subst. auto.
  - destruct (union_1 Hβ); auto.
  - pick fresh α2 for (L `union` ftvar_in_ptyp A `union` {{β}}).
    assert (HZL : α2 `notin` L) by fsetdec.
    assert (Hyz : β <> α2) by fsetdec.
    assert (HY' : β `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A (ptyp_var_f α2))).
    { pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A (ptyp_var_f α2)).
      fsetdec. }
    assert (Htv : a_binds_tvar β ((α2 ~ abind_tvar) ++ Θ)) by (apply H0; auto).
    rewrite_env (nil ++ Θ).
    eapply a_binds_tvar_strip_mid with (c := α2) (b := abind_tvar);
      [ exact Htv
      | intro Hc; inversion Hc; subst; congruence
      | intro Hc; inversion Hc
      | intros τ0 Hc; inversion Hc ].
Qed.

(** Embedding composition and substitution commutation for the fold step. *)
Lemma pskl_to_uskl_ptyp : forall A,
  pskl_to_uskl (ptyp_to_pskl A) = ptyp_to_uskl_syn A.
Proof.
  induction A; unfold ptyp_to_uskl_syn in *; simpl; f_equal; auto.
Qed.

Lemma pskl_to_uskl_subst : forall P τ β,
  pskl_to_uskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
  = subst_bskl_in_uskl (ptyp_to_uskl_syn τ) β (pskl_to_uskl P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (eq_var α β); simpl; auto using pskl_to_uskl_ptyp.
Qed.

(* ===================================================================== *)
(*  Binds-monotone weakening of the Θ-level judgments, and the last two    *)
(*  extraction helpers for assignvar                                       *)
(* ===================================================================== *)

Lemma a_wf_pskl_weaken : forall Θ Θ' Δ P,
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  Θ' ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros * Hmon Hwf; revert Θ' Hmon; induction Hwf; intros Θ' Hmon;
    eauto using a_wf_pskl;
    try (apply a_wf_pskl__var;
         destruct H as [HΔ | [Hb | [Hb | [τ Hb]]]];
         [ left | right; left | right; right; left
         | right; right; right; exists τ ]; auto).
Qed.

Lemma ad_pat_consis_weaken : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Ψ ⨟ Θ' ⊢ₛᵃ R ∼ Q.
Proof.
  intros Ψ Θ R Q H; induction H; intros Θ' Hmon.
  - apply ad_pat_consis__unit; auto.
  - apply ad_pat_consis__var; auto.
    destruct H0 as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; auto.
  - eapply ad_pat_consis__arrow; eauto.
  - eapply ad_pat_consis__forall_inh_tagged with (L := L); eauto.
    intros α Hα. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - eapply ad_pat_consis__forall_inh_untagged with (L := L); eauto.
    intros α Hα. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - eapply ad_pat_consis__forall_syn_tagged with (L := L); eauto.
    intros α Hα. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - eapply ad_pat_consis__forall_syn with (L := L); eauto.
    intros α Hα. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_pat_consis__ghostg; auto.
  - apply ad_pat_consis__topholeg; auto.
  - apply ad_pat_consis__hole; eauto using a_wf_pskl_weaken.
  - apply ad_pat_consis__tophole; auto.
  - eapply ad_pat_consis__tophole_inh with (L := L); eauto.
    intros α Hα. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_pat_consis__tophole_drop; auto.
  - eapply ad_pat_consis__flex_l; eauto.
  - eapply ad_pat_consis__flex_r; eauto.
Qed.

Lemma ad_pat_consis_weaken_cons : forall Ψ Θ (e : list (atom * abind)) R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  Ψ ⨟ (e ++ Θ) ⊢ₛᵃ R ∼ Q.
Proof.
  intros. eapply ad_pat_consis_weaken; eauto;
    try (intros x b Hb; unfold binds; apply in_or_app; auto).
Qed.

Lemma ftvar_in_ptyp_to_pskl : forall τ,
  ftvar_in_pskl (ptyp_to_pskl τ) [=] ftvar_in_ptyp τ.
Proof.
  induction τ; simpl; try fsetdec.
Qed.

(** Extracting a definition's payload facts from a wf context with a
    declaration-only prefix. *)
Lemma a_wf_aenv_mid_def_inv : forall Ξ β τ Θ,
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ) ->
  a_wf_ptyp Θ τ /\ mono_ptyp τ.
Proof.
  intros * Hdecl; revert β τ Θ; induction Hdecl; intros * Hwf;
    simpl_env in *.
  - inversion Hwf; subst. auto.
  - inversion Hwf; subst.
    match goal with
    | Hw : a_wf_aenv _ |- _ => eapply IHHdecl; exact Hw
    end.
Qed.

(* ===================================================================== *)
(*  Skeleton wf: context strengthening and forward definition-folding     *)
(*  (the two [a_assign] motive obligations: Skip drops a flex binding,    *)
(*  Assign folds a definition into the assigned skeleton).                *)
(* ===================================================================== *)

(** Skeleton wf survives removing ANY entry the skeleton avoids.
    Generalises [a_wf_pskl_strip_tvar] (which only drops [abind_tvar]);
    [a_assign__skip] drops a *flex* binding. *)
Lemma a_wf_pskl_strip_mid : forall Θ1 c b Θ2 Δ P,
  (Θ1 ++ (c ~ b) ++ Θ2) ⨟ Δ ⊢ₚₛᵃ P ->
  c `notin` ftvar_in_pskl P ->
  (Θ1 ++ Θ2) ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros * H.
  remember (Θ1 ++ (c ~ b) ++ Θ2) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hfr; simpl in Hfr.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; auto | right ].
    assert (Hne : α <> c) by (clear - Hfr; fsetdec).
    eapply a_binds_tvar_strip_mid; eauto;
      try (intro Hc; inversion Hc; subst; congruence);
      try (intros τ0 Hc; inversion Hc; subst; congruence).
  - apply a_wf_pskl__arrow; [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      auto.
  - apply a_wf_pskl__all with (L := L `union` singleton c).
    intros α Hα. apply H0; auto.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                  P (pskl_var_f α)) as Hup.
    simpl in Hup. clear - Hup Hfr Hα. fsetdec.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; auto.
Qed.

(** A monotype's skeleton is guarded / locally closed.  (Duplicated from
    [prop_consis_sound], which is DOWNSTREAM of this file.) *)
Lemma mono_ptyp_to_pskl_lc : forall τ,
  mono_ptyp τ -> lc_pskl (ptyp_to_pskl τ).
Proof. induction 1; simpl; auto using lc_pskl. Qed.

Lemma mono_ptyp_to_pskl_guarded : forall τ,
  mono_ptyp τ -> guarded_pskl (ptyp_to_pskl τ).
Proof.
  destruct 1 as [ | α | A1 A2 ]; simpl;
    [ apply guarded_pskl__unit | apply guarded_pskl__var
    | apply guarded_pskl__arrow; apply mono_ptyp_to_pskl_lc; auto ].
Qed.

(** Guardedness is a HEAD-SHAPE property, so substituting a variable by a
    MONOTYPE preserves it (a variable is guarded; a monotype is guarded).
    This is the crux of the [tophole] case below. *)
Lemma guarded_pskl_mono_subst : forall P τ β,
  guarded_pskl P ->
  mono_ptyp τ ->
  guarded_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros * HG Hm; destruct HG; simpl.
  - apply guarded_pskl__unit.
  - destruct (eq_var α β);
      [ apply mono_ptyp_to_pskl_guarded; auto | apply guarded_pskl__var ].
  - apply guarded_pskl__arrow;
      apply subst_pskl_in_pskl_lc_pskl; auto using mono_ptyp_to_pskl_lc.
Qed.

(** A well-formed monotype's skeleton is a well-formed skeleton, in any [Δ]. *)
Lemma a_wf_pskl_mono_ptyp : forall Θ Δ τ,
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  Θ ⨟ Δ ⊢ₚₛᵃ (ptyp_to_pskl τ).
Proof.
  intros Θ Δ τ Hm; revert Δ; induction Hm; intros Δ Hwf; simpl;
    inversion Hwf; subst.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. right; auto.
  - apply a_wf_pskl__arrow; auto.
Qed.

(** A defined flexible variable's definition is well-formed in the whole
    well-formed context.  (Payload companion of [a_wf_aenv_binds_def_mono].) *)
Lemma a_wf_aenv_binds_def_wf : forall Θ β τ,
  a_wf_aenv Θ ->
  binds β (abind_flex_mono_def τ) Θ ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ β τ Hwf; induction Hwf; intros Hb; simpl_env in *;
    try solve [ inversion Hb ];
    (* every cons case: either the head binding IS the one we look for
       (only possible for [flex_def]) or we recurse and weaken. *)
    (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
     [ try discriminate Heqb
     | ]);
    try (eapply a_wf_ptyp_weaken;
         [ intros y b0 Hb0; unfold binds; simpl; right; exact Hb0
         | apply IHHwf; exact Hb' ]).
  (* [flex_def], head hit: [τ0 = τ]. *)
  inversion Heqb; subst.
  eapply a_wf_ptyp_weaken;
    [ intros y b0 Hb0; unfold binds; simpl; right; exact Hb0 | auto ].
Qed.

(** FORWARD monotype substitution: folding a defined flexible variable's
    definition INTO a well-formed skeleton keeps it well-formed.  (The BACK
    direction is [a_wf_pskl_mono_subst_back] in [prop_consis_sound].) *)
Lemma a_wf_pskl_mono_subst : forall Θ β τ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  a_wf_aenv Θ ->
  binds β (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->
  Θ ⨟ Δ ⊢ₚₛᵃ (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros Θ β τ Δ P H; induction H; intros Hwfenv Hb Hm; simpl.
  - apply a_wf_pskl__unit.
  - (* NB: the scrutinee of [subst_pskl_in_pskl] lives at [ptypvar], so the
       [eq_dec] instance must be given at that type for [destruct] to
       abstract the [if] in the goal. *)
    destruct (@eq_dec ptypvar EqDec_eq_of_X α β) as [Heq | Hne].
    + subst. apply a_wf_pskl_mono_ptyp; auto.
      eapply a_wf_aenv_binds_def_wf; eauto.
    + apply a_wf_pskl__var; auto.
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L `union` singleton β).
    intros α Hα.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα; fsetdec | apply mono_ptyp_to_pskl_lc; auto ].
    apply H0; auto.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole;
      [ apply guarded_pskl_mono_subst; auto | auto ].
Qed.

(* ===================================================================== *)
(*  [a_assign_sound] MOVED.  [a_assign] is now in the a_unify/a_consis    *)
(*  MUTUAL block (algo/def_extra.v): its Assign-Assign premise is a       *)
(*  CONSISTENCY derivation, so soundness of assignment can no longer be a *)
(*  standalone induction — there is no IH for that premise.  It lives in  *)
(*  the 3-motive bundle [a_assign_unify_consis_sound] (prop_consis_sound) *)
(*  and is re-exported from there under its original name.                *)
(* ===================================================================== *)

(* --- relocated from prop_consis_sound.v (pure base lemma needed by the
   metasubst layer prop_metasubst.v, which must not import consistency) --- *)
Lemma a_wf_aenv_uniq : forall Θ,
  a_wf_aenv Θ -> uniq Θ.
Proof.
  intros Θ H; induction H; solve_uniq.
Qed.
