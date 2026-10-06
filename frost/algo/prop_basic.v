(** Soundness of the flexible-variable machinery (paper
    thm:sound-consistency, part 2): a [unifyvar] run is an identity
    information increase (dom-preserving) whose target equates the two
    subjects.  For monotypes, declarative consistency coincides with type
    equivalence under the context's definitions, so the declarative
    conclusion is stated with [a_tyequiv]; ∼/⊳-shaped corollaries are
    derived at their decorated-soundness use sites. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.prop_stability.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Monotype / wf bookkeeping                                             *)
(* ===================================================================== *)

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
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ (e ++ Θ) ⊢ A ≡ᵗ A' }}a.
Proof.
  intros. eapply a_tyequiv_weaken; [ | eauto ].
  intros x b Hb. unfold binds; apply in_or_app; auto.
Qed.

(** Unfolding a definition inside a monotype: [A ≡ A[τ/α1̂]] when [α1̂:=τ]. *)
Lemma a_tyequiv_subst_def : forall Θ α1 τ A,
  binds α1 (abind_flex_mono_def τ) Θ ->
  mono_ptyp A ->
  lc_ptyp τ ->
  {{ Θ ⊢ A ≡ᵗ (subst_ptyp_in_ptyp τ α1 A) }}a.
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

Lemma a_inc_target_weaken : forall Θ κ Θ' Ξ,
  κ ∷ Θ ⊑ Θ' ->
  a_suffix Ξ ->
  κ ∷ Θ ⊑ (Ξ ++ Θ').
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
  intros * [[κ [Hid Hinc]] Hd]. split.
  - exists ((α1, ptyp_var_f α1) :: κ). split.
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
  intros * [[κ [Hid Hinc]] Hd] Hlc. split.
  - exists ((α1, ptyp_var_f α1) :: κ). split.
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
  intros * [[κ [Hid Hinc]] Hd] Hlc. split.
  - exists κ. split; auto.
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
  intros * [[κ [Hid Hinc]] Hd] Hlc. split.
  - exists κ. split; auto.
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

(* [a_unify_sound] MOVED to prop_soundness_consis.v: with the corrected
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
Lemma a_wf_aenv_lc_aenv : forall Θ, {{ ⊢ Θ }}a -> lc_aenv Θ.
Proof.
  intros Θ H; induction H; constructor; simpl; auto.
  - eapply a_scope_pskl_lc; eapply a_scope_pskl_of_wf; eauto.
  - eapply a_wf_ptyp_lc; eauto.
Qed.

#[export] Hint Resolve a_wf_aenv_lc_aenv : core.

(** The unconditional [a_isub_refl] of the syntactic-middle era, restored
    for well-formed contexts. *)
Lemma a_isub_refl : forall Θ, {{ ⊢ Θ }}a -> Θ ⊴ Θ.
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

(** A declaration block carries no payload, so its variables ARE its
    domain.  ⚙ Moved here from algo/sub/prop_completeness_sub_gen.v
    (2026-08-16): the extract level's look re-rootings need it below the
    P7 stack, and this is [a_decls]'s home. *)
Lemma a_decls_no_ftvar : forall Ξ,
  a_decls Ξ -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros Ξ H; induction H as [| α1 Ξ' Hd IH]; simpl;
    [ clear; fsetdec | clear - IH; fsetdec ].
Qed.

Lemma a_inc_prepend_flex_src : forall Θ κ Θ' α1,
  κ ∷ Θ ⊑ Θ' ->
  a_binds_tvar α1 Θ' ->
  (α1, ptyp_var_f α1) :: κ ∷ ((α1 ~ abind_flex_mono) ++ Θ) ⊑ Θ'.
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
  destruct Hle' as [[κ [Hid Hinc]] Hd].
  split.
  - exists ((α1, ptyp_var_f α1) :: κ). split.
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
  intros * [[κ [Hid Hinc]] _] Hb. eauto using a_inc_binds_flex.
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
(*  THE GUESS FRESHNESS KIT (freshness campaign, DESIGN.md §4.3).          *)
(*                                                                        *)
(*  [a_guess_mono] is exists-fresh with INPUT-only side conditions and an  *)
(*  explicit CLOSE; its ∀ rule's witness enters the avoid-input.  This     *)
(*  block derives the junk-freeness that makes the kit provable            *)
(*  ([a_guess_mono_generated_fresh]), the renaming lemma, and the          *)
(*  decl/algo boundary bridge ([a_guess_mono_open_at]).                    *)
(*                                                                        *)
(*  THE INDUCTIONS ARE ON THE SUBJECT'S SIZE, NOT THE DERIVATION.  In the  *)
(*  rename's ∀ case, when the target name γ IS the recorded witness the    *)
(*  derivation must be renamed TWICE — witness off to a fresh δ, then the  *)
(*  requested rename — and the second rename applies to the RESULT of the  *)
(*  first, which is no sub-derivation.  [a_guess_mono] is syntax-directed  *)
(*  on its input [P] and opening with a variable preserves [size_pskl],   *)
(*  so a size induction has an IH for both.                                *)
(* ===================================================================== *)

Lemma ftvar_in_aenv_app : forall Θ1 Θ2,
  ftvar_in_aenv (Θ1 ++ Θ2) [=] ftvar_in_aenv Θ1 `union` ftvar_in_aenv Θ2.
Proof.
  induction Θ1 as [ | [x bd] Θ1' IH ]; intros; simpl; [ fsetdec | ].
  rewrite IH. fsetdec.
Qed.

Lemma ftvar_in_aenv_cons : forall x bd Θ,
  ftvar_in_aenv ((x, bd) :: Θ)
  [=] add x (ftvar_in_abind bd `union` ftvar_in_aenv Θ).
Proof. intros. simpl. fsetdec. Qed.

Lemma ftvar_in_aenv_one : forall x bd,
  ftvar_in_aenv (x ~ bd) [=] add x (ftvar_in_abind bd).
Proof. intros. simpl. fsetdec. Qed.

Lemma dom_subset_ftvar_in_aenv : forall Θ, dom Θ [<=] ftvar_in_aenv Θ.
Proof. induction Θ as [ | [x bd] Θ' IH ]; simpl; fsetdec. Qed.

(** A flexible's DEFINITION is part of what the context mentions.  So a name
    chosen fresh for [ftvar_in_aenv Θ] is fresh for every definition in Θ —
    which is the shape the renaming lemmas ask their side condition in. *)
Lemma ftvar_in_aenv_binds_def : forall Θ β τ,
  binds β (abind_flex_mono_def τ) Θ ->
  ftvar_in_ptyp τ [<=] ftvar_in_aenv Θ.
Proof.
  induction Θ as [ | [x bd] Θ' IH ]; intros β τ Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [ [ Heq Hbd ] | Hb' ].
  - subst bd. simpl. fsetdec.
  - pose proof (IH _ _ Hb') as Hsub. simpl. fsetdec.
Qed.

(** ⭐ THE PROPERTY THAT MAKES THE KIT PROVABLE.  Every name guess^TY
    GENERATES avoids everything the ambient context mentions — DERIVED,
    not assumed: the hole rule picks fresh for [Θ] and the ∀ rule puts its
    witness INTO [Θ], so in the ∀ case the premise's block avoids the
    witness itself.  Exactly the fact a renaming lemma needs when its
    target happens to BE that witness, and the fact the ∀-opening bridge
    needs unconditionally. *)
Lemma a_guess_mono_generated_fresh : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A ->
  forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ.
Proof.
  intros Θ P Ξ A H; induction H; intros α0 Hα0; simpl in *.
  - assert (α0 = α) by (clear - Hα0; fsetdec). subst. assumption.
  - auto.
  - clear - Hα0; fsetdec.
  - clear - Hα0; fsetdec.
  - rewrite dom_app in Hα0.
    destruct (union_1 Hα0) as [H1 | H1]; auto.
  - (* ∀ : the premise ran at (β~tvar) ++ Θ, so its block dodges β too *)
    specialize (IHa_guess_mono α0 Hα0). simpl in IHa_guess_mono. fsetdec.
Qed.

Corollary a_guess_mono_generated_fresh_binder : forall Θ P Ξ A β,
  a_guess_mono ((β ~ abind_tvar) ++ Θ) P Ξ A ->
  β `notin` dom Ξ.
Proof.
  intros Θ P Ξ A β H Hin.
  assert (Hfr : β `notin` ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (eapply a_guess_mono_generated_fresh; eauto).
  simpl in Hfr. fsetdec.
Qed.

(** The generated block holds only bare flexibles, so it mentions exactly
    its own domain. *)
Lemma a_guess_mono_generated_ftvar : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros Θ P Ξ A H; induction H; simpl; try fsetdec.
  rewrite ftvar_in_aenv_app, dom_app. fsetdec.
Qed.

(** "Close after renaming": renaming [α] to a fresh [β] and closing at [β]
    is closing at [α] — [subst = open ∘ close] plus the close/open round
    trip, no induction needed. *)
Lemma close_ptyp_subst_var : forall A α β,
  β `notin` ftvar_in_ptyp A ->
  close_ptyp_wrt_ptyp β (subst_ptyp_in_ptyp (ptyp_var_f β) α A)
  = close_ptyp_wrt_ptyp α A.
Proof.
  intros A α β Hβ.
  rewrite subst_ptyp_in_ptyp_spec.
  apply close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp.
  assert (Hcl : ftvar_in_ptyp (close_ptyp_wrt_ptyp α A)
                  [=] AtomSetImpl.remove α (ftvar_in_ptyp A))
    by (apply ftvar_in_ptyp_close_ptyp_wrt_ptyp).
  clear - Hβ Hcl. fsetdec.
Qed.

(** [rename_aenv] basics. *)
Lemma rename_aenv_fresh_eq : forall Ξ γ β,
  β `notin` ftvar_in_aenv Ξ ->
  rename_aenv γ β Ξ = Ξ.
Proof.
  induction Ξ as [ | [x bd] Ξ' IH ]; intros γ β Hβ; simpl in *; auto.
  destruct (x == β); [ subst; clear - Hβ; fsetdec | ].
  rewrite IH by (clear - Hβ; fsetdec).
  f_equal. f_equal.
  destruct bd; simpl in *; try reflexivity; f_equal;
    first [ apply subst_ptyp_in_ptyp_fresh_eq; clear - Hβ; fsetdec
          | apply subst_pskl_in_pskl_fresh_eq; clear - Hβ; fsetdec ].
Qed.

Lemma rename_aenv_cons_tvar_eq : forall γ β Θ,
  rename_aenv γ β ((β ~ abind_tvar) ++ Θ)
  = (γ ~ abind_tvar) ++ rename_aenv γ β Θ.
Proof.
  intros. simpl. destruct (β == β); [ reflexivity | contradiction ].
Qed.

Lemma ftvar_in_aenv_rename_aenv : forall Θ γ β,
  ftvar_in_aenv (rename_aenv γ β Θ) [<=] add γ (ftvar_in_aenv Θ).
Proof.
  induction Θ as [ | [x bd] Θ' IH ]; intros γ β; simpl; [ fsetdec | ].
  assert (Hbd : ftvar_in_abind (rename_abind γ β bd)
                  [<=] add γ (ftvar_in_abind bd)).
  { destruct bd; simpl; try fsetdec;
      (etransitivity;
       [ first [ apply ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
               | apply ftvar_in_pskl_subst_pskl_in_pskl_upper ]
       | simpl; fsetdec ]). }
  specialize (IH γ β).
  destruct (x == β); subst; fsetdec.
Qed.

(** guess^TY scopes its result by the source and the generated names.
    (Moved here from prop_soundness_consis.v: the kit derives target-side
    freshness from it instead of assuming output-side hypotheses.) *)
Lemma a_guess_mono_ftv : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A ->
  ftvar_in_ptyp A [<=] (ftvar_in_pskl P `union` dom Ξ).
Proof.
  intros Θ P Ξ A H; induction H; simpl; try solve [ fsetdec ].
  - (* arrow *)
    repeat rewrite dom_app.
    clear - IHa_guess_mono1 IHa_guess_mono2. fsetdec.
  - (* ∀ : the payload is CLOSED at β, so β drops out of the bound *)
    assert (Hcl : ftvar_in_ptyp (close_ptyp_wrt_ptyp β A)
                    [=] AtomSetImpl.remove β (ftvar_in_ptyp A))
      by (apply ftvar_in_ptyp_close_ptyp_wrt_ptyp).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
    simpl in Hup.
    clear - IHa_guess_mono Hcl Hup. fsetdec.
Qed.

(** One-step domain arithmetic for a rigid cons.  ⚙ PERF: stated as a lemma
    rather than re-derived by [simpl; fsetdec] at each use site.  The three
    uses below sit under a context full of large set hypotheses, and
    [fsetdec] preprocesses ALL of them — the three [assert]s alone cost 160 s
    of build time before this (Ltac-profiled, 2026-08-06). *)
Lemma ftvar_in_aenv_cons_tvar : forall β Θ,
  ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] add β (ftvar_in_aenv Θ).
Proof. intros; simpl; fsetdec. Qed.

(** The ∀ introduction in OPENED form — the shape call sites have.  The
    rule takes the payload unclosed and closes it; when the caller already
    holds the [A] it means to re-bind, [β ∉ ftv A] makes the closure a
    round trip. *)
Lemma a_guess_mono_all_of_one : forall Θ P Ξ A β,
  a_guess_mono ((β ~ abind_tvar) ++ Θ)
    (open_pskl_wrt_pskl P (pskl_var_f β)) Ξ
    (open_ptyp_wrt_ptyp A (ptyp_var_f β)) ->
  β `notin` ftvar_in_aenv Θ ->
  β `notin` ftvar_in_pskl P -> β `notin` ftvar_in_ptyp A ->
  a_guess_mono Θ (pskl_all_syn P) Ξ (ptyp_all A).
Proof.
  intros Θ P Ξ A β Hg Hβ HβP HβA.
  rewrite <- (close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp A β) at 1 by exact HβA.
  apply a_guess_mono__forall with (β := β); [ fsetdec | exact Hg ].
Qed.

(** ⭐ THE decl/algo BOUNDARY BRIDGE.  Not cofinite quantification creeping
    back into the algorithmic layer: the DECLARATIVE targets stay cofinite
    (correctly — relations, no outputs to leak into), so wherever an
    exists-fresh algorithmic premise feeds one, the single recorded
    instance must become a family.  This is the packaged binder-move that
    does it.  Junk-freeness makes it TRUE: without the witness entering the
    premise's context, a hole below the ∀ could generate the witness
    itself, and this statement is false on that derivation.

    ⚙ The move is the TRANSPOSITION [b0 ⇄ α] ([a_guess_mono_swap],
    prop_swap.v), not a substitution-shaped rename: the recorded witness
    [b0] sits INSIDE the premise's context, so no "source dodges Θ" side
    condition can hold for it.  Both halves of the swap then collapse to
    the identity where they must — on [Θ] and on the generated block [Ξ],
    because both atoms dodge their free atoms — and on the payload the swap
    IS the rename ([swap_ptyp_as_subst], [α ∉ ftv A'] from
    [a_guess_mono_ftv]).  This retired the 150-line size-induction rename
    [a_guess_mono_rename_tvar] (DESIGN.md §4.3 ⚙). *)
Lemma a_guess_mono_open_at : forall Θ P Ξ A α,
  a_guess_mono Θ (pskl_all_syn P) Ξ (ptyp_all A) ->
  α `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` dom Ξ ->
  a_guess_mono ((α ~ abind_tvar) ++ Θ)
    (open_pskl_wrt_pskl P (pskl_var_f α)) Ξ
    (open_ptyp_wrt_ptyp A (ptyp_var_f α)).
Proof.
  intros Θ P Ξ A α H Hα.
  inversion H as [ | | | | | Θ' P' Ξ' A' b0 Hfr Hg ]; subst.
  pose proof (a_guess_mono_generated_fresh_binder Hg) as Hb0Ξ.
  pose proof (a_guess_mono_generated_ftvar Hg) as HΞftv.
  assert (Hb0Ξf : b0 `notin` ftvar_in_aenv Ξ) by (clear - Hb0Ξ HΞftv; fsetdec).
  destruct (α == b0) as [-> | Hne].
  { (* α IS the recorded witness: the instance is literally the premise *)
    rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp. exact Hg. }
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b0)) as Hup.
  cbn in Hup.
  assert (HαA : α `notin` ftvar_in_ptyp A').
  { pose proof (a_guess_mono_ftv Hg) as HAftv.
    clear - HAftv Hup Hα Hne. fsetdec. }
  (* the payload IS the closure at b0, so opening at α is the b0 ⇄ α swap *)
  rewrite <- subst_ptyp_in_ptyp_spec.
  pose proof (a_guess_mono_swap b0 α _ _ _ _ Hg) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  rewrite (swap_aenv_fresh_id b0 α Θ) in Hr by (clear - Hfr Hα; fsetdec).
  rewrite (swap_aenv_fresh_id b0 α Ξ) in Hr by (clear - Hb0Ξf Hα HΞftv; fsetdec).
  rewrite swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b0 α P) in Hr by (clear - Hfr Hα; fsetdec).
  rewrite (swap_ptyp_as_subst b0 α A') in Hr by exact HαA.
  exact Hr.
Qed.

(* ===================================================================== *)
(*  guess^TY is consistent with its input skeleton                         *)
(*  (the declarative content of Assign-SolveM's definition)               *)
(* ===================================================================== *)

(* SIZE INDUCTION, not derivation induction: the TARGET [ad_pat_consis] is
   declarative, hence still COFINITE, while the source [a_guess_mono] is
   exists-fresh — the ∀ case turns ONE guess instance into a family with
   [a_guess_mono_open_at], whose output is no sub-derivation. *)
Lemma a_guess_mono_consis_size : forall n Θ P βs τ,
  size_pskl P <= n ->
  a_guess_mono Θ P βs τ ->
  forall Θ1,
  (forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono βs -> a_binds_tvar α1 Θ1) ->
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (ptyp_to_bskl_syn τ).
Proof.
  induction n as [| n IHn]; intros Θ P βs τ Hsz H;
    [ destruct H; cbn in Hsz; lia | ].
  destruct H as [ Θ α Hα | Θ P Ξ A Hg | Θ α | Θ
                | Θ P Q Ξ1 Ξ2 A B Hg1 Hg2
                | Θ P Ξ A β Hfr Hg ];
    cbn in Hsz; intros Θ1 Hvars Hβs.
  - (* hole ↦ fresh flexible variable *)
    replace (ptyp_to_bskl_syn (ptyp_var_f α))
      with (pskl_to_bskl_inh (pskl_var_f α)) by reflexivity.
    replace (pskl_to_uskl pskl_hole) with uskl_hole by reflexivity.
    apply ad_pat_consis__hole; [ fsetdec | ].
    apply a_wf_pskl__var. right. apply Hβs.
    unfold binds; left; reflexivity.
  - (* ∀◇P : the universal ghost is dropped *)
    replace (pskl_to_uskl (pskl_tophole P))
      with (uskl_tophole (pskl_to_uskl P)) by reflexivity.
    apply ad_pat_consis__tophole_drop.
    eapply IHn; [ lia | exact Hg | exact Hvars | exact Hβs ].
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
      [ eapply IHn with (P := P) | eapply IHn with (P := Q) | fsetdec ].
    + lia.
    + exact Hg1.
    + intros α Hα. apply Hvars. simpl. fsetdec.
    + intros α1 Hb. apply Hβs. unfold binds in *. apply in_or_app; auto.
    + lia.
    + exact Hg2.
    + intros α Hα. apply Hvars. simpl. fsetdec.
    + intros α1 Hb. apply Hβs. unfold binds in *. apply in_or_app; auto.
  - (* forall: synthesised quantifier on both sides.  EXISTS-FRESH source,
       COFINITE target — the family comes from [a_guess_mono_open_at]. *)
    replace (pskl_to_uskl (pskl_all_syn P))
      with (uskl_all_syn (pskl_to_uskl P)) by reflexivity.
    replace (ptyp_to_bskl_syn (ptyp_all (close_ptyp_wrt_ptyp β A)))
      with (bskl_all_syn (ptyp_to_bskl_syn (close_ptyp_wrt_ptyp β A)))
      by reflexivity.
    apply ad_pat_consis__forall_syn
      with (L := dom Ξ `union` dom Θ1 `union` ftvar_in_aenv Θ
                   `union` ftvar_in_pskl P `union` singleton β).
    intros α Hα.
    rewrite <- pskl_to_uskl_open_var.
    rewrite <- ptyp_to_bskl_syn_open_var.
    eapply IHn with (P := open_pskl_wrt_pskl P (pskl_var_f α))
                    (Θ := (α ~ abind_tvar) ++ Θ);
      [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia | | | ].
    + apply a_guess_mono_open_at;
        [ apply a_guess_mono__forall with (β := β); [ exact Hfr | exact Hg ]
        | clear - Hα; fsetdec ].
    + intros β0 Hβ0.
      apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in Hβ0.
      simpl in Hβ0.
      destruct (union_1 Hβ0) as [HY' | HY'].
      * apply singleton_1 in HY'; subst.
        left. unfold binds; left; reflexivity.
      * apply a_binds_tvar_weaken_cons; auto.
    + intros α1 Hb. apply a_binds_tvar_weaken_cons; auto.
Qed.

Corollary a_guess_mono_consis : forall Θ P βs τ,
  a_guess_mono Θ P βs τ ->
  forall Θ1,
  (forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono βs -> a_binds_tvar α1 Θ1) ->
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (ptyp_to_bskl_syn τ).
Proof.
  intros. eapply a_guess_mono_consis_size; eauto.
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
  R' = subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β S0x ->
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
      rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* forall_inh_untagged *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_inh_untagged with (L := L `union` {{β}}).
      intros α Hα. eapply H0; auto.
      rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* forall_syn_tagged *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_syn_tagged with (L := L `union` {{β}}).
      intros α Hα. eapply H0; auto.
      rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* forall_syn *)
    destruct S0x as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_syn with (L := L `union` {{β}}).
      intros α Hα. eapply H0; auto.
      rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var; auto.
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
  intros * [[κ [Hid Hinc]] Hd] HΞ. split.
  - exists κ. eauto using a_inc_target_weaken.
  - intros α τ0 Hb. unfold binds; apply in_or_app; right. apply Hd; auto.
Qed.

Lemma a_isub_strengthen_decls_src : forall Ξ Θ Θ',
  a_decls Ξ ->
  (Ξ ++ Θ) ⊴ Θ' ->
  Θ ⊴ Θ'.
Proof.
  intros * Hdecl [[κ [Hid Hinc]] Hd]. split.
  - edestruct a_inc_strengthen_suffix_src as [κ' [Hid' Hinc']];
      [ eapply a_decls_suffix; eauto | exact Hinc | ].
    exists κ'. auto.
  - intros α τ0 Hb. apply Hd.
    unfold binds in *; apply in_or_app; auto.
Qed.

(** Inverting a well-formed tophole: the body is GUARDED and well-formed at
    the EMPTY tag scope.
    ⚙ ONE name for this fact (2026-08-12): it used to exist three times —
    here in its strong form (consis/prop_consis_precise.v), a wf-only weak
    form (deco_algo/prop_decorate_sub.v) that COLLIDED with it, and a copy
    named [_x] (algo/prop_precise.v) that existed only to escape the shadow.
    Weak uses read the second component. *)
Lemma a_wf_pskl_tophole_inv : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_tophole P) }}a ->
  guarded_pskl P /\ ({{ Θ ⨟ empty ⊢ₚₛ P }}a).
Proof. intros * H; inversion H; subst; auto. Qed.

(** Removing a whole prefix preserves well-formedness of the tail. *)
Lemma a_wf_aenv_strip_prefix : forall Ξ Θ,
  {{ ⊢ (Ξ ++ Θ) }}a -> {{ ⊢ Θ }}a.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros Θ Hwf; simpl in *; auto.
  inversion Hwf; subst; eauto.
Qed.

(** Stripping a middle entry below a declaration-only prefix preserves
    context well-formedness (declarations carry no scoping content). *)
Lemma a_wf_aenv_strip_mid : forall Ξ (c : atom) (b : abind) Θ,
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ (c ~ b) ++ Θ) }}a ->
  {{ ⊢ (Ξ ++ Θ) }}a.
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
  (* [α] is the var rule's OWN binder ([a_wf_ptyp__var], algo/def_rules.v),
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

(** ** [wf] / [scope] bound the free variables by the domain.  ⚠️ These four
    and [a_wf_ptyp_ftv_tvarish] just above are ONE family and this is their
    only home — do not re-prove an instance in a downstream file. *)

Lemma a_wf_ptyp_ftv_dom : forall Θ A,
  a_wf_ptyp Θ A -> ftvar_in_ptyp A [<=] dom Θ.
Proof.
  intros Θ A H α Hα.
  apply (a_wf_ptyp_ftv_tvarish H) in Hα.
  destruct Hα as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

Lemma a_binds_tvar_in_dom : forall β Θ, a_binds_tvar β Θ -> β `in` dom Θ.
Proof. intros β Θ [Hb | [Hb | [τ Hb]]]; apply binds_In in Hb; exact Hb. Qed.

Lemma a_scope_pskl_ftv_dom : forall Θ P,
  a_scope_pskl Θ P -> ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros Θ P H; induction H; simpl; try fsetdec.
  - apply a_binds_tvar_in_dom in H. fsetdec.
  - destruct (atom_fresh (L `union` dom Θ `union` ftvar_in_pskl P))
      as [α Hα].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α)) as Hlo.
    specialize (H0 α ltac:(clear - Hα; solve_notin_auto)). simpl in H0.
    clear - H0 Hlo Hα. fsetdec.
Qed.

(** Embedding composition and substitution commutation for the fold step. *)
Lemma pskl_to_uskl_ptyp : forall A,
  pskl_to_uskl (ptyp_to_pskl A) = ptyp_to_uskl_syn A.
Proof.
  induction A; unfold ptyp_to_uskl_syn in *; simpl; f_equal; auto.
Qed.

Lemma pskl_to_uskl_subst : forall P τ β,
  pskl_to_uskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
  = subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β (pskl_to_uskl P).
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
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ' ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros * Hmon Hwf; revert Θ' Hmon; induction Hwf; intros Θ' Hmon;
    eauto using a_wf_pskl;
    try (apply a_wf_pskl__var;
         destruct H as [HΔ | [Hb | [Hb | [τ Hb]]]];
         [ left | right; left | right; right; left
         | right; right; right; exists τ ]; auto).
Qed.

Lemma ad_pat_consis_weaken : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  {{ Ψ ⨟ Θ' ⊢ˢ R ∼ Q }}ad.
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
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ Ψ ⨟ (e ++ Θ) ⊢ˢ R ∼ Q }}ad.
Proof.
  intros. eapply ad_pat_consis_weaken; eauto;
    try (intros x b Hb; unfold binds; apply in_or_app; auto).
Qed.

(** Extracting a definition's payload facts from a wf context with a
    declaration-only prefix. *)
Lemma a_wf_aenv_mid_def_inv : forall Ξ β τ Θ,
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ) }}a ->
  a_wf_ptyp Θ τ /\ mono_ptyp τ.
Proof.
  intros * Hdecl; revert β τ Θ; induction Hdecl; intros * Hwf;
    simpl_env in *.
  - inversion Hwf; subst. auto.
  - inversion Hwf; subst.
    match goal with
    | Hw : {{ ⊢ _ }}a |- _ => eapply IHHdecl; exact Hw
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
  {{ (Θ1 ++ (c ~ b) ++ Θ2) ⨟ Δ ⊢ₚₛ P }}a ->
  c `notin` ftvar_in_pskl P ->
  {{ (Θ1 ++ Θ2) ⨟ Δ ⊢ₚₛ P }}a.
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
  {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl τ) }}a.
Proof.
  intros Θ Δ τ Hm; revert Δ; induction Hm; intros Δ Hwf; simpl;
    inversion Hwf; subst.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. right; auto.
  - apply a_wf_pskl__arrow; auto.
Qed.

(** A definition is a monotype (it is stored that way). *)
Lemma a_wf_aenv_binds_def_mono : forall Θ α1 τ,
  {{ ⊢ Θ }}a ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ.
Proof.
  intros Θ α1 τ Hwf; induction Hwf; intros Hb;
    try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
    try discriminate; try (inversion Heqb; subst; assumption); auto.
Qed.

(** A defined flexible variable's definition is well-formed in the whole
    well-formed context.  (Payload companion of [a_wf_aenv_binds_def_mono].) *)
Lemma a_wf_aenv_binds_def_wf : forall Θ β τ,
  {{ ⊢ Θ }}a ->
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
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ ⊢ Θ }}a ->
  binds β (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->
  {{ Θ ⨟ Δ ⊢ₚₛ (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) }}a.
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
(*  MUTUAL block (algo/def_rules.v): its Assign-Assign premise is a       *)
(*  CONSISTENCY derivation, so soundness of assignment can no longer be a *)
(*  standalone induction — there is no IH for that premise.  It lives in  *)
(*  the 3-motive bundle [a_assign_unify_consis_sound] (prop_consis_sound) *)
(*  and is re-exported from there under its original name.                *)
(* ===================================================================== *)

(* --- relocated from prop_soundness_consis.v (pure base lemma needed by the
   metasubst layer prop_metasubst.v, which must not import consistency) --- *)
Lemma a_wf_aenv_uniq : forall Θ,
  {{ ⊢ Θ }}a -> uniq Θ.
Proof.
  intros Θ H; induction H; solve_uniq.
Qed.

(* ===================================================================== *)
(*  a_wf_ptyp / a_guess_mono / a_decls plumbing                           *)
(* ===================================================================== *)

(** The converse of [a_wf_ptyp_to_wf_pskl] on a painting.  The two
    judgements agree row by row except at [∀], where [a_wf_pskl] puts the
    binder in [Δ] and [a_wf_ptyp] in [Θ] — so the statement quantifies the
    target context and asks the caller to relate the two. *)
Lemma a_wf_ptyp_of_wf_pskl : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall A Θ', P = ptyp_to_pskl A ->
  (forall α, α `in` Δ -> a_binds_tvar α Θ') ->
  (forall α, a_binds_tvar α Θ -> a_binds_tvar α Θ') ->
  a_wf_ptyp Θ' A.
Proof.
  intros Θ Δ P H; induction H; intros A0 Θ' Heq HΔ HΘ;
    destruct A0; simpl in Heq; try discriminate.
  - (* unit *) apply a_wf_ptyp__unit.
  - (* var *)
    inversion Heq; subst. apply a_wf_ptyp__var.
    destruct H as [Hd | Ht]; [ apply HΔ | apply HΘ ]; assumption.
  - (* arrow *)
    inversion Heq; subst.
    apply a_wf_ptyp__arrow;
      [ eapply IHa_wf_pskl1 | eapply IHa_wf_pskl2 ];
      solve [ reflexivity | assumption ].
  - (* all : the binder moves from Δ to Θ' *)
    inversion Heq; subst.
    apply a_wf_ptyp__all with (L := L). intros α Hα.
    eapply (H0 α Hα);
      [ rewrite ptyp_to_pskl_open; reflexivity
      | intros β Hβ;
        destruct (eq_var β α) as [Heqβ | Hne];
          [ subst β; unfold a_binds_tvar; left;
            unfold binds; simpl; left; reflexivity
          | apply a_binds_tvar_weaken_cons; apply HΔ;
            clear - Hβ Hne; fsetdec ]
      | intros β Hβ; apply a_binds_tvar_weaken_cons; apply HΘ; exact Hβ ].
Qed.

Corollary a_wf_ptyp_of_wf_pskl_empty : forall Θ A,
  {{ Θ ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a -> a_wf_ptyp Θ A.
Proof.
  intros Θ A H. eapply a_wf_ptyp_of_wf_pskl;
    [ exact H | reflexivity
    | intros α Hα; exfalso; clear - Hα; fsetdec
    | intros α Hα; exact Hα ].
Qed.

(** The [a_guess_mono_refine] (§9) companion: [guess^TY]'s output type is
    well formed wherever its input skeleton's variables and its own
    generated block are.  Same SIZE induction, same reason. *)
Lemma a_guess_mono_wf_size : forall n Θ P Ξ A,
  size_pskl P <= n ->
  a_guess_mono Θ P Ξ A ->
  forall Θ1,
  (forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ1) ->
  a_wf_ptyp Θ1 A.
Proof.
  induction n as [| n IHn]; intros Θ P Ξ A Hsz H;
    [ destruct H; cbn in Hsz; lia | ].
  destruct H as [ Θ α Hα | Θ P Ξ A Hg | Θ α | Θ
                | Θ P Q Ξ1 Ξ2 A B Hg1 Hg2
                | Θ P Ξ A β Hfr Hg ];
    cbn in Hsz; intros Θ1 Hvars HΞ.
  - (* hole ↦ fresh flexible *)
    apply a_wf_ptyp__var. apply HΞ. unfold binds; left; reflexivity.
  - (* ⫯.P *)
    eapply IHn with (P := P); [ lia | exact Hg | exact Hvars | exact HΞ ].
  - (* variable *) apply a_wf_ptyp__var. apply Hvars. simpl. fsetdec.
  - (* unit *) apply a_wf_ptyp__unit.
  - (* arrow *)
    apply a_wf_ptyp__arrow;
      [ eapply IHn with (P := P) | eapply IHn with (P := Q) ];
      solve [ lia | eassumption
            | intros α Hα; apply Hvars; simpl; clear - Hα; fsetdec
            | intros α1 Hb; apply HΞ; unfold binds in *;
              apply in_or_app; auto ].
  - (* ∀ : exists-fresh source, cofinite target *)
    apply a_wf_ptyp__all
      with (L := dom Ξ `union` dom Θ1 `union` ftvar_in_aenv Θ
                   `union` ftvar_in_pskl P `union` ftvar_in_ptyp A
                   `union` singleton β).
    intros α Hα.
    eapply IHn with (P := open_pskl_wrt_pskl P (pskl_var_f α))
                    (Θ := (α ~ abind_tvar) ++ Θ);
      [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia | | | ].
    + apply a_guess_mono_open_at;
        [ apply a_guess_mono__forall with (β := β); [ exact Hfr | exact Hg ]
        | clear - Hα; fsetdec ].
    + intros β0 Hβ0.
      apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in Hβ0.
      simpl in Hβ0.
      destruct (union_1 Hβ0) as [HY' | HY'].
      * apply singleton_1 in HY'; subst.
        unfold a_binds_tvar; left; unfold binds; simpl; left; reflexivity.
      * apply a_binds_tvar_weaken_cons. apply Hvars; exact HY'.
    + intros α1 Hb. apply a_binds_tvar_weaken_cons. apply HΞ; exact Hb.
Qed.

Corollary a_guess_mono_wf : forall Θ P Ξ A Θ1,
  a_guess_mono Θ P Ξ A ->
  (forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ1) ->
  a_wf_ptyp Θ1 A.
Proof. intros. eapply a_guess_mono_wf_size; eauto. Qed.

(** [uniq] is what [AT-Abs]'s own premise supplies (algo/def_rules.v): the
    block is declaration-only, so nothing else is needed to put it in
    front of a well-formed context. *)
Lemma a_wf_aenv_decls_app : forall Ξ Θ,
  a_decls Ξ -> uniq (Ξ ++ Θ) -> {{ ⊢ Θ }}a -> {{ ⊢ (Ξ ++ Θ) }}a.
Proof.
  intros Ξ Θ Hd; induction Hd as [ | α1 Ξ' Hd IH ];
    intros Huq Hwf; simpl_env in *; [ exact Hwf | ].
  apply a_wf_aenv__flex;
    [ clear - Huq; destruct_uniq; simpl_env in *;
      unfold disjoint in *; fsetdec
    | apply IH; [ solve_uniq | exact Hwf ] ].
Qed.

Lemma a_wf_ptyp_arrow_inv : forall Θ A1 A2,
  a_wf_ptyp Θ (ptyp_arrow A1 A2) -> a_wf_ptyp Θ A1 /\ a_wf_ptyp Θ A2.
Proof. intros * H; inversion H; subst; split; assumption. Qed.

(** A monotype all of whose free variables are tvar-ish is well-formed. *)
Lemma mono_ptyp_wf : forall Θ τ,
  mono_ptyp τ ->
  (forall α, α `in` ftvar_in_ptyp τ -> a_binds_tvar α Θ) ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ τ H; induction H; intros Hvis; simpl in *.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply Hvis. fsetdec.
  - apply a_wf_ptyp__arrow;
      [ apply IHmono_ptyp1 | apply IHmono_ptyp2 ];
      intros α Hα; apply Hvis; fsetdec.
Qed.

(** ⚙ A well-formed context MENTIONS only its own domain: every payload is
    scoped in the tail.  This is what turns the uniform substitution back
    into the identity on the surviving context. *)
Lemma a_wf_aenv_ftv_dom : forall Θ,
  {{ ⊢ Θ }}a -> ftvar_in_aenv Θ [<=] dom Θ.
Proof.
  intros Θ H; induction H; simpl; try (clear - IHa_wf_aenv; fsetdec).
  - fsetdec.
  - assert (ftvar_in_ptyp τ [<=] dom Θ)
      by (intros β Hβ; apply a_binds_tvar_in_dom;
          eapply a_wf_ptyp_ftv_tvarish; eassumption).
    clear - IHa_wf_aenv H3. fsetdec.
  - assert (ftvar_in_pskl P [<=] dom Θ)
      by (apply a_scope_pskl_ftv_dom; eauto).
    clear - IHa_wf_aenv H2. fsetdec.
  - assert (ftvar_in_ptyp A [<=] dom Θ)
      by (intros β Hβ; apply a_binds_tvar_in_dom;
          eapply a_wf_ptyp_ftv_tvarish; eassumption).
    clear - IHa_wf_aenv H2. fsetdec.
Qed.

(** ⭐ A RIGID entry is INVISIBLE to [a_flex_tvar] — at EVERY atom, its own
    included, because [binds] is MEMBERSHIP: a rigid binding neither creates a
    flexible one nor hides one further down.  ⚙ The FlexR-priority guard's
    transports all rest on this (2026-08-18). *)
Lemma a_flex_tvar_cons_tvar_any : forall b (Θ : aenv) x,
  a_flex_tvar ((b ~ abind_tvar) ++ Θ) x <-> a_flex_tvar Θ x.
Proof.
  intros b Θ x; unfold a_flex_tvar; split.
  - intros [Hb | [τ Hb]]; analyze_binds Hb;
      solve [ left; assumption | right; exists τ; assumption ].
  - intros [Hb | [τ Hb]]; [ left | right; exists τ ];
      unfold binds; simpl; right; assumption.
Qed.

(** …and an atom outside a context's domain is not flexible in it. *)
Lemma a_flex_tvar_in_dom : forall (Θ : aenv) x,
  a_flex_tvar Θ x -> x `in` dom Θ.
Proof. intros Θ x [Hb | [τ Hb]]; eapply binds_In; eassumption. Qed.

Lemma a_flex_tvar_weaken_app : forall Ξ Θ α,
  a_flex_tvar Θ α -> a_flex_tvar (Ξ ++ Θ) α.
Proof.
  intros * [Hb | [τ Hb]]; [ left | right; exists τ ];
    unfold binds in *; apply in_or_app; right; assumption.
Qed.

(** ⭐ NON-FLEXIBILITY FROM A SCOPE BOUND, as LEMMAS rather than a tactic
    search: an atom outside a context's [ftvar_in_aenv] bound cannot be
    flexible in it.  ⚠️⚠️ The tactic version of this HANGS — [match goal] has to
    guess which scope hypothesis to use, and every wrong guess pays an
    exponential [fsetdec] on a context with dozens of set variables. *)
Lemma nonflex_of_scope : forall (Θ : aenv) S b,
  ftvar_in_aenv Θ [<=] S -> b `notin` S -> ~ a_flex_tvar Θ b.
Proof.
  intros Θ S b Hs Hb Hf. apply a_flex_tvar_in_dom in Hf.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hd.
  clear - Hs Hb Hd Hf. fsetdec.
Qed.

Lemma nonflex_of_scope_cons : forall (Θ : aenv) S b c,
  ftvar_in_aenv Θ [<=] S -> b `notin` S ->
  ~ a_flex_tvar ((c ~ abind_tvar) ++ Θ) b.
Proof.
  intros Θ S b c Hs Hb Hf.
  rewrite a_flex_tvar_cons_tvar_any in Hf.
  exact (nonflex_of_scope Hs Hb Hf).
Qed.

(** ⭐⭐ THE FLEXIBILITY-PRESERVING SHRINK (2026-08-18).  Under the
    FlexR-PRIORITY GUARD a consumer can no longer throw a collection's context
    away wholesale — the eq layer reads it for HATTEDNESS.  What it CAN do is
    keep exactly the flexibles the COUNTERPART mentions, with their payloads
    dropped: that is enough for the guard (whose condition is scoped to
    [ftv P']) and it lands [ftvar_in_aenv] inside [S], which is what the
    freshness side conditions wanted the shrink for in the first place. *)
Fixpoint flex_restrict (S : atoms) (Θ : aenv) : aenv :=
  match Θ with
  | nil => nil
  | (x, abind_flex_mono) :: Θ' =>
      if AtomSetImpl.mem x S
      then (x, abind_flex_mono) :: flex_restrict S Θ'
      else flex_restrict S Θ'
  | (x, abind_flex_mono_def _) :: Θ' =>
      if AtomSetImpl.mem x S
      then (x, abind_flex_mono) :: flex_restrict S Θ'
      else flex_restrict S Θ'
  | _ :: Θ' => flex_restrict S Θ'
  end.

Lemma flex_restrict_ftvar : forall S Θ,
  ftvar_in_aenv (flex_restrict S Θ) [<=] S.
Proof.
  intros S Θ; induction Θ as [ | [x b] Θ' IH ]; simpl; [ fsetdec | ].
  destruct b;
    try (destruct (AtomSetImpl.mem x S) eqn:Hm; simpl;
         [ assert (x `in` S) by (apply AtomSetImpl.mem_2; exact Hm);
           clear - IH H; fsetdec
         | exact IH ]);
    exact IH.
Qed.

Lemma flex_restrict_dom : forall S Θ,
  ftvar_in_aenv (flex_restrict S Θ) [<=] ftvar_in_aenv Θ.
Proof.
  intros S Θ; induction Θ as [ | [x b] Θ' IH ]; simpl; [ fsetdec | ].
  destruct b;
    try (destruct (AtomSetImpl.mem x S); simpl; clear - IH; fsetdec);
    clear - IH; fsetdec.
Qed.

(** Everything the restriction keeps is an UNDEFINED flexible drawn from [S]
    and flexible in the source. *)
Lemma flex_restrict_binds_inv : forall S Θ x bd,
  binds x bd (flex_restrict S Θ) ->
  x `in` S /\ a_flex_tvar Θ x.
Proof.
  intros S Θ; induction Θ as [ | [y b] Θ' IH ]; intros x bd Hb; simpl in Hb.
  - inversion Hb.
  - assert (Hup : x `in` S /\ a_flex_tvar Θ' x ->
                  x `in` S /\ a_flex_tvar ((y, b) :: Θ') x).
    { intros [HS [H1 | [τ H1]]]; split;
        [ exact HS | left | exact HS | right; exists τ ];
        unfold binds; simpl; right; exact H1. }
    destruct b;
      try (apply Hup; exact (IH x bd Hb));
      (destruct (AtomSetImpl.mem y S) eqn:Hm;
       [ destruct Hb as [E | Hb];
         [ inversion E; subst; split;
           [ apply AtomSetImpl.mem_2; exact Hm
           | solve [ left; unfold binds; simpl; left; reflexivity
                   | right; eexists; unfold binds; simpl; left; reflexivity ] ]
         | apply Hup; exact (IH x bd Hb) ]
       | apply Hup; exact (IH x bd Hb) ]).
Qed.

(** …and it keeps EVERY flexible of [S]. *)
Lemma flex_restrict_binds : forall S Θ x,
  x `in` S -> a_flex_tvar Θ x -> binds x abind_flex_mono (flex_restrict S Θ).
Proof.
  intros S Θ; induction Θ as [ | [y b] Θ' IH ]; intros x HS Hf; simpl.
  - destruct Hf as [Hb | [τ Hb]]; inversion Hb.
  - assert (Hmem : AtomSetImpl.mem x S = true)
      by (apply AtomSetImpl.mem_1; exact HS).
    destruct b;
      try (apply IH; [ exact HS | ];
           destruct Hf as [Hb | [τ Hb]]; analyze_binds Hb;
           solve [ left; assumption | right; exists τ; assumption ]);
      (destruct (AtomSetImpl.mem y S) eqn:Hm;
       [ destruct (x == y) as [-> | Hne];
         [ unfold binds; simpl; left; reflexivity
         | unfold binds; simpl; right; apply IH; [ exact HS | ];
           destruct Hf as [Hb | [τ Hb]]; analyze_binds Hb;
           solve [ left; assumption | right; exists τ; assumption ] ]
       | destruct (x == y) as [-> | Hne];
         [ exfalso; rewrite Hmem in Hm; discriminate
         | apply IH; [ exact HS | ];
           destruct Hf as [Hb | [τ Hb]]; analyze_binds Hb;
           solve [ left; assumption | right; exists τ; assumption ] ] ]).
Qed.

Lemma flex_restrict_iff : forall S Θ β,
  β `in` S -> (a_flex_tvar Θ β <-> a_flex_tvar (flex_restrict S Θ) β).
Proof.
  intros S Θ β HβS; split.
  - intros Hf. left. apply flex_restrict_binds; assumption.
  - intros [Hb | [τ Hb]];
      exact (proj2 (flex_restrict_binds_inv _ _ _ _ Hb)).
Qed.

(** …and a PREFIX the atom is not bound in is likewise invisible — the shape
    the FlexR-priority guard's context moves need (2026-08-18). *)
Lemma a_flex_tvar_app_notin : forall (Ξ Θ : aenv) α,
  α `notin` dom Ξ -> (a_flex_tvar (Ξ ++ Θ) α <-> a_flex_tvar Θ α).
Proof.
  intros Ξ Θ α Hα; split; [ | apply a_flex_tvar_weaken_app ].
  intros [Hb | [τ Hb]]; unfold binds in Hb; apply in_app_or in Hb;
    destruct Hb as [Hin | Hin];
    solve [ exfalso; apply Hα; eapply binds_In; exact Hin
          | left; exact Hin
          | right; exists τ; exact Hin ].
Qed.

(* ⚙ RENAMED from [binds_weaken_mid] 2026-08-09 (cleanup audit §8.1c): it collided with a
   DIFFERENT lemma of that name, and this one inserts Ξm INSIDE an existing Ξl++Θ0; prop_inc.v's weakens a bare Θ on both sides. *)
Lemma binds_weaken_inner : forall (x : atom) (b : abind) Ξl Ξm Θ0,
  binds x b (Ξl ++ Θ0) -> binds x b (Ξl ++ Ξm ++ Θ0).
Proof.
  intros x b Ξl Ξm Θ0 H. apply binds_app_1 in H as [H | H].
  - apply binds_app_2; exact H.
  - apply binds_app_3; apply binds_app_3; exact H.
Qed.

Lemma a_flex_tvar_weaken_mid : forall Ξl Ξm Θ0 α,
  a_flex_tvar (Ξl ++ Θ0) α -> a_flex_tvar (Ξl ++ Ξm ++ Θ0) α.
Proof.
  intros Ξl Ξm Θ0 α [Hb | [τ Hb]];
    [ left | right; exists τ ]; apply binds_weaken_inner; exact Hb.
Qed.

(** …and hence PEELING one head entry the atom is not the subject of.
    ⚙ MOVED here from ext_algo/prop_solve_rel.v §10 (2026-08-20): the consis
    rung's [a_assign_unify_consis_flex_rev] lives in [algo/] and needs it. *)
Lemma a_flex_tvar_cons_other : forall (c : atom) (bd : abind) (Θ : aenv) x,
  x <> c -> (a_flex_tvar ((c ~ bd) ++ Θ) x <-> a_flex_tvar Θ x).
Proof.
  intros c bd Θ x Hne. apply a_flex_tvar_app_notin.
  simpl_env. clear - Hne. fsetdec.
Qed.

(** …and anywhere under a PENDING SUFFIX.  ⚙ MOVED here from
    ext_algo/prop_solve_rel.v §10 with its cons-instance above (2026-08-20):
    the `a_sub` rung's [a_sub_sub_flex_flex_rev] lives in [algo/] and its
    Flex-Solve row peels THREE mid entries at once. *)
Lemma a_flex_tvar_mid_other : forall (Ξ : aenv) (c : atom) (bd : abind)
    (Θ : aenv) x,
  x <> c ->
  (a_flex_tvar (Ξ ++ (c ~ bd) ++ Θ) x <-> a_flex_tvar (Ξ ++ Θ) x).
Proof.
  intros Ξ c bd Θ x Hne; split; [ | apply a_flex_tvar_weaken_mid ].
  intros [Hb | [τ Hb]]; [ left | right; exists τ ];
    (unfold binds in *; apply in_app_or in Hb; destruct Hb as [H | H];
     [ apply in_or_app; left; exact H
     | destruct H as [E | H];
       [ exfalso; inversion E; subst; apply Hne; reflexivity
       | apply in_or_app; right; exact H ] ]).
Qed.

(** The [Ghost]/[GhostR] side condition transports through the rename:
    if [Δ] avoids [ftv P] then the renamed [Δ] avoids the renamed [ftv]. *)
(** [ftvar_in_pskl_open_pskl_wrt_pskl_upper] is stated as a [<=]; the
    [rewrite]s above need it as a set-level bound, so use it by [pose]. *)
Lemma notin_ftvar_open_pskl_var : forall β α P,
  β <> α -> β `notin` ftvar_in_pskl P ->
  β `notin` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof.
  intros β α P Hne HβP.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hs.
  simpl in Hs. clear - Hs Hne HβP. fsetdec.
Qed.

(* ⚙ These three mention [ptyp_to_bskl_syn] / [ptyp_to_uskl_syn], which are
   defined in algo_decl/def_consis_refine.v rather than frost/coercions.v — so
   unlike their siblings they cannot live in frost/prop_coercions.v. *)
(** On a MONOTYPE the inherited and synthesised paintings coincide — they only
    differ at quantifiers, and a monotype has none. *)
Lemma ptyp_to_bskl_inh_syn_eq : forall A,
  mono_ptyp A ->
  pskl_to_bskl_inh (ptyp_to_pskl A) = ptyp_to_bskl_syn A.
Proof.
  unfold ptyp_to_bskl_syn.
  intros A Hm; induction Hm; simpl; f_equal; auto.
Qed.

(** Free variables of monotype paintings. *)
Lemma ftvar_ptyp_to_uskl_syn : forall τ,
  ftvar_in_uskl (ptyp_to_uskl_syn τ) [=] ftvar_in_ptyp τ.
Proof.
  intros. rewrite <- pskl_to_uskl_ptyp.
  rewrite ftvar_in_uskl_pskl. apply ftvar_ptyp_to_pskl.
Qed.

Lemma ftvar_ptyp_to_bskl_syn : forall τ,
  ftvar_in_bskl (ptyp_to_bskl_syn τ) [=] ftvar_in_ptyp τ.
Proof.
  intros. rewrite <- (ftvar_bskl_to_pskl (ptyp_to_bskl_syn τ)).
  unfold ptyp_to_bskl_syn. rewrite bskl_to_pskl_pskl_to_bskl_syn.
  apply ftvar_ptyp_to_pskl.
Qed.

(* ===================================================================== *)
(*  ⭐ THE ABSENCE-FIRST GUARD'S TRANSPORT KIT                             *)
(*                                                                        *)
(*  The collection rules carry [α ∈ ftvar_in_pskl <subject>] (the         *)
(*  implementation's absence-first dispatch, rendered as a premise — see  *)
(*  algo/def_rules.v and docs/PAPER-GAPS.md).  Its structural lemmas      *)
(*  travel with it: the guard must survive every way a rule REBUILDS its  *)
(*  subject, and there are exactly two, an OPENING and a SUBSTITUTION.    *)
(*  The opening direction is lngen's                                      *)
(*  [ftvar_in_pskl_open_pskl_wrt_pskl_lower] verbatim; the substitution   *)
(*  direction needs the substituted variable to differ from the           *)
(*  looked-for one, which every consumer already carries.                 *)
(* ===================================================================== *)

Lemma ftvar_in_pskl_subst_keep : forall α β P0 P,
  β <> α ->
  α `in` ftvar_in_pskl P ->
  α `in` ftvar_in_pskl (subst_pskl_in_pskl P0 β P).
Proof.
  intros α β P0 P Hne Hin.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower P P0 β) as Hlo.
  clear - Hne Hin Hlo. fsetdec.
Qed.

Lemma ftvar_in_pskl_open_keep : forall α P Q,
  α `in` ftvar_in_pskl P ->
  α `in` ftvar_in_pskl (open_pskl_wrt_pskl P Q).
Proof.
  intros α P Q Hin.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P Q) as Hlo.
  clear - Hin Hlo. fsetdec.
Qed.

(** …and its REFLECTION, for the reverse (un-substitution) direction: if the
    looked-for variable survives the substitution and the substituted
    skeleton does not contain it, it was in the subject all along. *)
Lemma ftvar_in_pskl_subst_reflect : forall α β P0 P,
  α `notin` ftvar_in_pskl P0 ->
  α `in` ftvar_in_pskl (subst_pskl_in_pskl P0 β P) ->
  α `in` ftvar_in_pskl P.
Proof.
  intros α β P0 P Hn Hin.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β) as Hup.
  clear - Hn Hin Hup. fsetdec.
Qed.

(** A ghost-free body cannot OPEN to a ghost — the fact the ◇-dispatch guard
    needs in order to thread through [LS-ForallR], whose premise runs at the
    counterpart's opened body. *)
Lemma ghost_free_open_var_neq_hole : forall P β,
  pskl_ghost_free P ->
  open_pskl_wrt_pskl P (pskl_var_f β) <> pskl_hole.
Proof.
  intros P β Hgf. unfold open_pskl_wrt_pskl.
  destruct P; simpl in *; try contradiction; try discriminate.
  destruct (lt_eq_lt_dec n 0) as [ [ _ | _ ] | _ ]; discriminate.
Qed.

(** An OPENING at a variable other than the looked-for one cannot produce the
    looked-for one — the [≠ α] half of the ◇-dispatch guard, transported
    through a binder peel. *)
(** …and its INVERSION, which is what spares the reorder a decidable equality
    on skeletons: an opening that lands on the looked-for variable can only
    have come from that variable itself. *)
Lemma open_var_eq_var_inv : forall Q β α,
  open_pskl_wrt_pskl Q (pskl_var_f β) = pskl_var_f α -> β <> α ->
  Q = pskl_var_f α.
Proof.
  intros Q β α Heq Hne. unfold open_pskl_wrt_pskl in Heq.
  destruct Q; simpl in Heq; try discriminate Heq.
  - destruct (lt_eq_lt_dec n 0) as [ [ _ | _ ] | _ ]; simpl in Heq;
      [ discriminate Heq
      | injection Heq as Heq0; exfalso; apply Hne; exact Heq0
      | discriminate Heq ].
  - exact Heq.
Qed.

Lemma open_var_neq_var : forall P γ α,
  P <> pskl_var_f α -> γ <> α ->
  open_pskl_wrt_pskl P (pskl_var_f γ) <> pskl_var_f α.
Proof.
  intros P γ α Hne Hγ. unfold open_pskl_wrt_pskl.
  destruct P; simpl; try discriminate.
  - destruct (lt_eq_lt_dec n 0) as [ [ _ | _ ] | _ ]; simpl;
      [ discriminate
      | intros Hc; inversion Hc; congruence
      | discriminate ].
  - exact Hne.
Qed.

(** A ghost-free skeleton is not itself the ghost — the cheapest way to meet
    the ◇-dispatch guard wherever mode compatibility already gives
    ghost-freeness of the counterpart. *)
Lemma ghost_free_neq_hole : forall P, pskl_ghost_free P -> P <> pskl_hole.
Proof. intros P Hgf ->; exact Hgf. Qed.

(* ===================================================================== *)
(*  ⭐ SS-Vacuous, GENERALIZED PAST THE SOLVE-DISPATCH GUARD (2026-08-18)  *)
(*                                                                        *)
(*  Under guard 5 [SS-Vacuous] no longer fires at a [∀] or [⫯] subject —   *)
(*  the implementation peels there first (type.ml:494 matches              *)
(*  [SolS-ForallL] and [SolS-UnivGhostL] before [SolS-Vacuous]).  ⭐ But    *)
(*  the PEELED route gives the SAME answer: an empty block and the         *)
(*  subject back, because [∀]'s row re-CLOSES over the opener it drew and  *)
(*  [⫯]'s re-wraps.  So every old [apply a_solve_sub__vacuous] site can    *)
(*  read this lemma instead, with no change to what it proves.            *)
(*                                                                        *)
(*  ⚙ SIZE induction: the [∀] row opens, which preserves [size_pskl], so   *)
(*  a structural induction on the skeleton would not go through.          *)
(* ===================================================================== *)

Lemma a_solve_sub_vacuous_gen_n : forall n Θ m P,
  size_pskl P <= n ->
  {{ Θ ⊢ₛ P ≼[ m ] pskl_hole ⤳ nil ⨾ P }}a.
Proof.
  induction n as [ | n IH ]; intros Θ m P Hsz;
    [ exfalso; destruct P; simpl in Hsz; lia | ].
  destruct P as [ | k | α | P1 P2 | P0 | | P0 ];
    try solve [ apply a_solve_sub__vacuous;
                solve [ apply peel_l_off_unit | apply peel_l_off_var_b
                      | apply peel_l_off_var | apply peel_l_off_arrow
                      | apply peel_l_off_hole ] ].
  - (* ∀ — peel, then RE-CLOSE over the same opener *)
    simpl in Hsz.
    destruct (atom_fresh (ftvar_in_aenv Θ ∪ ftvar_in_pskl P0)) as [β Hβ].
    replace (pskl_all_syn P0)
      with (pskl_all_syn
              (close_pskl_wrt_pskl β (open_pskl_wrt_pskl P0 (pskl_var_f β))))
      at 2
      by (f_equal; apply close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          clear - Hβ; fsetdec).
    apply a_solve_sub__forall_l with (β := β).
    + simpl. clear - Hβ. fsetdec.
    + apply IH. rewrite size_pskl_open_pskl_wrt_pskl_var. lia.
  - (* ⫯ — strip, then RE-WRAP *)
    simpl in Hsz.
    apply a_solve_sub__univ_ghost_l. apply IH. lia.
Qed.

Lemma a_solve_sub_vacuous_gen : forall Θ m P,
  {{ Θ ⊢ₛ P ≼[ m ] pskl_hole ⤳ nil ⨾ P }}a.
Proof. intros. exact (a_solve_sub_vacuous_gen_n Θ m P (le_n _)). Qed.

(* ===================================================================== *)
(*  §  ⭐ TWO [a_flex_tvar] SHAPES THE a_sub LIFT NEEDS (2026-08-21)       *)
(*                                                                        *)
(*  Both are about what a WALK row does to the context's flexibility       *)
(*  picture; they sit here beside [a_flex_tvar_{cons,mid}_other] for the   *)
(*  same reason the consis rung's flex-reflect does.                       *)
(* ===================================================================== *)


(** ⭐ [Flex-Solve]'s CONTEXT SURGERY, as one flexibility equivalence: the
    head goes from undefined to defined and TWO fresh flexibles appear under
    it, and neither move changes any OTHER atom's flex status.  ⚙ The consis
    rung's [a_flex_tvar_solve_m] does NOT serve here — that row moves the
    definition to the FRONT, this one leaves it under [Ξ]. *)
Lemma a_flex_tvar_solve_shape : forall (Ξ : aenv) (c : atom) (t : ptyp)
    (β α : atom) (Θ : aenv) x,
  x <> α -> x <> β ->
  (a_flex_tvar (Ξ ++ (c ~ abind_flex_mono_def t) ++ (β ~ abind_flex_mono)
                  ++ (α ~ abind_flex_mono) ++ Θ) x
   <-> a_flex_tvar (Ξ ++ (c ~ abind_flex_mono) ++ Θ) x).
Proof.
  intros Ξ c t β α Θ x Hnα Hnβ.
  destruct (x == c) as [-> | Hnc].
  - split; intros _;
      [ left | right; exists t ];
      unfold binds; apply in_or_app; right; left; reflexivity.
  - rewrite (a_flex_tvar_mid_other Ξ (abind_flex_mono_def t) _ Hnc).
    rewrite (a_flex_tvar_mid_other Ξ abind_flex_mono _ Hnβ).
    rewrite (a_flex_tvar_mid_other Ξ abind_flex_mono Θ Hnα).
    rewrite (a_flex_tvar_mid_other Ξ abind_flex_mono Θ Hnc).
    reflexivity.
Qed.


(** ⚙ A RIGID or TERM head is not the flexible witness, so the witness is in
    the tail — which the Barendregt premises of the walk forbid. *)
Lemma a_flex_tvar_head_tail : forall (c : atom) (bd : abind) Θ,
  a_flex_tvar ((c ~ bd) ++ Θ) c ->
  bd <> abind_flex_mono ->
  (forall τ, bd <> abind_flex_mono_def τ) ->
  a_flex_tvar Θ c.
Proof.
  intros c bd Θ [Hb | [τ Hb]] Hn1 Hn2;
    apply binds_cons_1 in Hb as [[_ Heq] | Hb];
    solve [ exfalso; apply Hn1; symmetry; exact Heq
          | exfalso; apply (Hn2 τ); symmetry; exact Heq
          | left; exact Hb | right; exists τ; exact Hb ].
Qed.

(* ===================================================================== *)
(*  §  ⚙ TERM ENTRIES ARE INERT FOR THE FLEXIBILITY PICTURE (2026-08-22,   *)
(*  the a_pat rung) — inserting or stripping one changes nothing.          *)
(* ===================================================================== *)

Lemma a_flex_tvar_app_iff : forall (Ξ Θ : aenv) x,
  a_flex_tvar (Ξ ++ Θ) x <-> (a_flex_tvar Ξ x \/ a_flex_tvar Θ x).
Proof.
  intros Ξ Θ x. unfold a_flex_tvar, binds. split.
  - intros [Hb | [t Hb]]; apply in_app_or in Hb; destruct Hb as [Hb | Hb].
    + left; left; exact Hb.
    + right; left; exact Hb.
    + left; right; exists t; exact Hb.
    + right; right; exists t; exact Hb.
  - intros [[Hb | [t Hb]] | [Hb | [t Hb]]].
    + left; apply in_or_app; left; exact Hb.
    + right; exists t; apply in_or_app; left; exact Hb.
    + left; apply in_or_app; right; exact Hb.
    + right; exists t; apply in_or_app; right; exact Hb.
Qed.



(** ⚙ The two term-entry moves the abs rows make on the flexibility
    picture: a term entry never carries a flex binding, so INSERTING or
    STRIPPING one changes nothing (with the atom apart). *)
Lemma a_flex_tvar_insert_mid : forall (Ξ Θ : aenv) x (bd : abind) a,
  a <> x ->
  (a_flex_tvar (Ξ ++ (x ~ bd) ++ Θ) a <-> a_flex_tvar (Ξ ++ Θ) a).
Proof.
  intros Ξ Θ x bd a Hne.
  rewrite ! a_flex_tvar_app_iff.
  assert (Hone : ~ a_flex_tvar (x ~ bd) a).
  { intros [Hb | [t Hb]]; unfold binds in Hb; simpl in Hb;
      destruct Hb as [E | []]; inversion E; subst; apply Hne; reflexivity. }
  tauto.
Qed.

Definition abind_nonflex (bd : abind) : Prop :=
  bd <> abind_flex_mono /\ forall τ, bd <> abind_flex_mono_def τ.

Lemma abind_is_tm_nonflex : forall bd, abind_is_tm bd -> abind_nonflex bd.
Proof.
  intros bd Htm; destruct bd; simpl in Htm; try contradiction;
    split; intros; discriminate.
Qed.

(** A NON-FLEX cons is invisible to [a_flex_tvar] — at EVERY atom, the
    entry's own included (it carries no flex binding, and with the atom
    off the tail's domain nothing hides behind it). *)
Lemma a_flex_tvar_cons_nonflex : forall x (bd : abind) Θ a,
  abind_nonflex bd ->
  (a_flex_tvar ((x ~ bd) ++ Θ) a <-> a_flex_tvar Θ a).
Proof.
  intros x bd Θ a [Hn1 Hn2].
  destruct (a == x) as [-> | Hne];
    [ | apply a_flex_tvar_cons_other; exact Hne ].
  split; intros Hf.
  - eapply a_flex_tvar_head_tail; [ exact Hf | exact Hn1 | exact Hn2 ].
  - destruct Hf as [Hb | [τ Hb]]; [ left | right; exists τ ];
      unfold binds in *; simpl; right; assumption.
Qed.

Lemma a_flex_tvar_strip_tvar : forall b Θ α,
  a_flex_tvar ((b ~ abind_tvar) ++ Θ) α -> a_flex_tvar Θ α.
Proof.
  intros b Θ α [Hb | [τ Hb]];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
    solve [ discriminate Habs | left; exact Hb' | right; exists τ; exact Hb' ].
Qed.

(** [a_wf_pskl] reads Θ ONLY through [a_binds_tvar] (its context never grows —
    the binder rule extends Δ), so it weakens along any TVAR-ISH monotone map.
    [a_wf_pskl_weaken]'s [binds]-monotone form is too strong here: Flex-Solve
    turns [α̂0]'s DECLARATION into a DEFINITION. *)
Lemma a_wf_pskl_weaken_tvarish : forall Θ Θ' Δ P,
  (forall α, a_binds_tvar α Θ -> a_binds_tvar α Θ') ->
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ' ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Θ' Δ P Hmon Hwf; revert Θ' Hmon; induction Hwf; intros Θ' Hmon;
    eauto using a_wf_pskl.
  apply a_wf_pskl__var. destruct H as [HΔ | Htv];
    [ left; exact HΔ | right; exact (Hmon α Htv) ].
Qed.

(** Variable renaming is the variable instance of monotype substitution. *)
Lemma guarded_pskl_subst_var : forall P α β,
  guarded_pskl P ->
  guarded_pskl (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros P α β H.
  exact (@guarded_pskl_mono_subst P (ptyp_var_f β) α H (mono_ptyp__var β)).
Qed.
