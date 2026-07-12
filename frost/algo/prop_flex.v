(** Soundness of the flexible-variable machinery (paper
    thm:sound-consistency, part 2): a [unifyvar] run is an identity
    information increase (dom-preserving) whose target equates the two
    subjects.  For monotypes, declarative consistency coincides with type
    equivalence under the context's definitions, so the declarative
    conclusion is stated with [a_tyequiv]; ≈/⊳-shaped corollaries are
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
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Monotype / wf bookkeeping                                             *)
(* ===================================================================== *)

Lemma mono_ptyp_lc : forall A, mono_ptyp A -> lc_ptyp A.
Proof. intros A H; induction H; auto. Qed.

Lemma mono_ptyp_subst : forall A τ γ,
  mono_ptyp A -> mono_ptyp τ ->
  mono_ptyp (subst_ptyp_in_ptyp τ γ A).
Proof.
  intros * HA Hτ; induction HA; simpl; eauto using mono_ptyp.
  destruct (eq_var X γ); eauto using mono_ptyp.
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
  - apply a_wf_ptyp__all with (L := L). intros X HX.
    apply H0; auto. intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
Qed.

Lemma a_tyequiv_weaken_cons : forall Θ (e : list (atom * abind)) A B,
  Θ ⊢ A ≡ᵗ B ->
  (e ++ Θ) ⊢ A ≡ᵗ B.
Proof.
  intros. eapply a_tyequiv_weaken; [ | eauto ].
  intros x b Hb. unfold binds; apply in_or_app; auto.
Qed.

(** Unfolding a definition inside a monotype: [A ≡ A[τ/γ̂]] when [γ̂:=τ]. *)
Lemma a_tyequiv_subst_def : forall Θ γ τ A,
  binds γ (abind_flex_mono_def τ) Θ ->
  mono_ptyp A ->
  lc_ptyp τ ->
  Θ ⊢ A ≡ᵗ (subst_ptyp_in_ptyp τ γ A).
Proof.
  intros * Hb Hm Hlc; induction Hm; simpl.
  - apply a_tyequiv__refl; auto.
  - destruct (eq_var X γ); subst.
    + apply a_tyequiv__flex_def; auto.
    + apply a_tyequiv__refl; auto.
  - apply a_tyequiv__arrow; auto.
Qed.

(* ===================================================================== *)
(*  Target weakening of information increase, and ⊴ cons congruences      *)
(* ===================================================================== *)

Lemma a_inc_target_weaken : forall Θ θ Θ' Ξ,
  Θ ≤[ θ ] Θ' ->
  a_suffix Ξ ->
  Θ ≤[ θ ] (Ξ ++ Θ').
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
Lemma a_isub_cons_flex : forall Θ Θ' γ,
  Θ ⊴ Θ' ->
  ((γ ~ abind_flex_mono) ++ Θ) ⊴ ((γ ~ abind_flex_mono) ++ Θ').
Proof.
  intros * [[θ [Hid Hinc]] Hd]. split.
  - exists ((γ, ptyp_var_f γ) :: θ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex.
    + apply a_inc_target_weaken; auto.
      apply (a_suffix__cons γ (b := abind_flex_mono)); constructor.
    + apply a_wf_ptyp__var. right; left. unfold binds; left; reflexivity.
    + constructor.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

Lemma a_isub_cons_flex_def : forall Θ Θ' γ τ,
  Θ ⊴ Θ' ->
  lc_ptyp τ ->
  ((γ ~ abind_flex_mono_def τ) ++ Θ) ⊴ ((γ ~ abind_flex_mono_def τ) ++ Θ').
Proof.
  intros * [[θ [Hid Hinc]] Hd] Hlc. split.
  - exists ((γ, ptyp_var_f γ) :: θ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex_def.
    + apply a_inc_target_weaken; auto.
      apply (a_suffix__cons γ (b := abind_flex_mono_def τ)); constructor.
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
  ((x ~ abind_var_typ A) ++ Θ) ⊴ ((x ~ abind_var_typ A) ++ Θ').
Proof.
  intros * [[θ [Hid Hinc]] Hd]. split.
  - exists θ. split; auto.
    replace ((x ~ abind_var_typ A) ++ Θ')
      with (nil ++ (x ~ abind_var_typ (msubst_ptyp θ A)) ++ Θ')
      by (simpl; rewrite msubst_ptyp_id; auto).
    apply a_inc__var; auto. constructor.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

Lemma a_isub_cons_var_skl : forall Θ Θ' x P,
  Θ ⊴ Θ' ->
  ((x ~ abind_var_skl P) ++ Θ) ⊴ ((x ~ abind_var_skl P) ++ Θ').
Proof.
  intros * [[θ [Hid Hinc]] Hd]. split.
  - exists θ. split; auto.
    replace ((x ~ abind_var_skl P) ++ Θ')
      with (nil ++ (x ~ abind_var_skl (msubst_pskl θ P)) ++ Θ')
      by (simpl; rewrite msubst_pskl_id; auto).
    apply a_inc__var_skl; auto. constructor.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

(* ===================================================================== *)
(*  Soundness of variable unification (thm:sound-consistency part 2)      *)
(* ===================================================================== *)

Lemma a_unify_sound : forall Θ0 A B Θ1,
  Θ0 ⊲ A ≈ᵘ B ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  mono_ptyp A ->
  mono_ptyp B ->
  Θ0 ⊴ Θ1 /\ dom Θ1 [=] dom Θ0 /\ (Θ1 ⊢ A ≡ᵗ B).
Proof.
  intros * Hu; induction Hu; intros Hctx HmA HmB.
  - (* Flex-Flex-Id *)
    split; [ apply a_isub_refl | split; [ fsetdec | ] ].
    apply a_tyequiv__refl. constructor.
  - (* Flex-Flex-L : α̂ := β̂ *)
    split; [ | split; [ simpl; fsetdec | ] ].
    + split.
      * destruct (a_inc_refl_gen Θ0
          (Ξ0 := (α ~ abind_flex_mono_def (ptyp_var_f β))))
          as [θ0 [Hid0 Hinc0]].
        { apply (a_suffix__cons α (b := abind_flex_mono_def (ptyp_var_f β)));
            constructor. }
        exists ((α, ptyp_var_f α) :: θ0). split.
        { constructor; auto. unfold is_id_entry; reflexivity. }
        apply a_inc__flex; auto;
          try (apply a_wf_ptyp__var; right; right;
               exists (ptyp_var_f β); unfold binds; left; reflexivity);
          try constructor.
      * intros γ τ0 Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | ].
        simpl. unfold binds. right. auto.
    + apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - (* Flex-Flex-R : β̂ := α̂ *)
    split; [ | split; [ simpl; fsetdec | ] ].
    + split.
      * destruct (a_inc_refl_gen Θ0
          (Ξ0 := (β ~ abind_flex_mono_def (ptyp_var_f α))))
          as [θ0 [Hid0 Hinc0]].
        { apply (a_suffix__cons β (b := abind_flex_mono_def (ptyp_var_f α)));
            constructor. }
        exists ((β, ptyp_var_f β) :: θ0). split.
        { constructor; auto. unfold is_id_entry; reflexivity. }
        apply a_inc__flex; auto;
          try (apply a_wf_ptyp__var; right; right;
               exists (ptyp_var_f α); unfold binds; left; reflexivity);
          try constructor.
      * intros γ τ0 Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | ].
        simpl. unfold binds. right. auto.
    + apply a_tyequiv__sym.
      apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - (* Flex-Flex-Assign *)
    inversion Hctx; subst.
    match goal with
    | Hmτ : mono_ptyp τ |- _ =>
      destruct IHHu as [Hle [Hdom Heq1]]; auto using mono_ptyp_subst
    end.
    assert (Hlcτ : lc_ptyp τ) by (apply mono_ptyp_lc; assumption).
    assert (Hbγ : binds γ (abind_flex_mono_def τ)
                    ((γ ~ abind_flex_mono_def τ) ++ Θ1))
      by (unfold binds; left; reflexivity).
    split; [ | split ].
    + apply a_isub_cons_flex_def; auto.
    + simpl. fsetdec.
    + eapply a_tyequiv__trans.
      { eapply a_tyequiv_subst_def; eauto. }
      eapply a_tyequiv__trans.
      { apply a_tyequiv_weaken_cons. exact Heq1. }
      apply a_tyequiv__sym.
      eapply a_tyequiv_subst_def; eauto.
  - (* Flex-Flex-Skip (flexible γ̂, absent from the subjects) *)
    inversion Hctx; subst.
    destruct IHHu as [Hle [Hdom Heq1]]; auto.
    split; [ | split ].
    + apply a_isub_cons_flex; auto.
    + simpl. fsetdec.
    + apply a_tyequiv_weaken_cons; auto.
  - (* Flex-Flex-Skip' (rigid / term-var entry) *)
    destruct H as [Hb | [[Q Hb] | [Q Hb]]]; subst;
      inversion Hctx; subst;
      destruct IHHu as [Hle [Hdom Heq1]]; auto;
      (split; [ | split; [ simpl; fsetdec
                         | apply a_tyequiv_weaken_cons; auto ] ]).
    + apply a_isub_cons_tvar; auto.
    + apply a_isub_cons_var_typ; auto.
    + apply a_isub_cons_var_skl; auto.
Qed.

(* ===================================================================== *)
(*  Source-prefix machinery for assignvar (the [Θ0 | Ξ] split): flexible  *)
(*  declarations can be prepended to the SOURCE of an increase whenever   *)
(*  they are still visible in the target.                                 *)
(* ===================================================================== *)

Lemma a_wf_ptyp_lc : forall Θ A, a_wf_ptyp Θ A -> lc_ptyp A.
Proof.
  intros * H; induction H; auto.
Qed.

(** Declaration-only suffixes (the paper's "Ξ only contains declarations
    of flexible variables"). *)
Inductive a_decls : aenv -> Prop :=
| a_decls__nil : a_decls nil
| a_decls__cons : forall γ Ξ,
    a_decls Ξ ->
    a_decls ((γ ~ abind_flex_mono) ++ Ξ).

Lemma a_decls_suffix : forall Ξ, a_decls Ξ -> a_suffix Ξ.
Proof.
  intros Ξ H; induction H; [ constructor | ].
  apply (a_suffix__cons γ (b := abind_flex_mono)); auto; constructor.
Qed.

Lemma a_inc_prepend_flex_src : forall Θ θ Θ' γ,
  Θ ≤[ θ ] Θ' ->
  a_binds_tvar γ Θ' ->
  ((γ ~ abind_flex_mono) ++ Θ) ≤[ (γ, ptyp_var_f γ) :: θ ] Θ'.
Proof.
  intros * Hinc Hb.
  apply a_inc__flex; auto;
    try (apply a_wf_ptyp__var; auto);
    try constructor.
Qed.

Lemma a_isub_prepend_decls_src : forall Ξ Θ Θ',
  a_decls Ξ ->
  (forall γ, binds γ abind_flex_mono Ξ -> a_binds_tvar γ Θ') ->
  Θ ⊴ Θ' ->
  (Ξ ++ Θ) ⊴ Θ'.
Proof.
  intros Ξ; induction Ξ as [ | [γ b] Ξ' IH ]; intros Θ Θ' Hdecl Hvis Hle; auto.
  inversion Hdecl; subst.
  assert (Hle' : (Ξ' ++ Θ) ⊴ Θ').
  { apply IH; auto;
      try (intros γ0 Hb0; apply Hvis; unfold binds; right; auto). }
  destruct Hle' as [[θ [Hid Hinc]] Hd].
  split.
  - exists ((γ, ptyp_var_f γ) :: θ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc_prepend_flex_src; auto;
      try (apply Hvis; unfold binds; left; reflexivity).
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | auto ].
Qed.

(** Every declaration in the source of an identity increase is still
    tvar-ish in the target (specialization of the transport kit). *)
Lemma a_isub_binds_flex : forall Θ Θ' γ,
  Θ ⊴ Θ' ->
  binds γ abind_flex_mono Θ ->
  a_binds_tvar γ Θ'.
Proof.
  intros * [[θ [Hid Hinc]] _] Hb. eauto using a_inc_binds_flex.
Qed.

(** [guess^TY] emits a declaration-only fresh suffix. *)
Lemma a_decls_app : forall Ξ1 Ξ2,
  a_decls Ξ1 -> a_decls Ξ2 -> a_decls (Ξ1 ++ Ξ2).
Proof.
  intros * H1 H2; induction H1; simpl; auto.
  apply (a_decls__cons γ); auto.
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
  - pick fresh X. eauto.
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

Lemma ptyp_to_bskl_syn_open_var : forall A X,
  ptyp_to_bskl_syn (open_ptyp_wrt_ptyp A (ptyp_var_f X))
  = open_bskl_wrt_bskl (ptyp_to_bskl_syn A) (bskl_var_f X).
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
  (forall X, X `in` ftvar_in_pskl P -> a_binds_tvar X Θ1) ->
  (forall γ, binds γ abind_flex_mono βs -> a_binds_tvar γ Θ1) ->
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
    apply ad_wf_pskl__var. right. apply Hβs.
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
    + intros X HX. apply Hvars. simpl. fsetdec.
    + intros γ Hb. apply Hβs. unfold binds in *. apply in_or_app; auto.
    + intros X HX. apply Hvars. simpl. fsetdec.
    + intros γ Hb. apply Hβs. unfold binds in *. apply in_or_app; auto.
  - (* forall: synthesised quantifier on both sides *)
    replace (pskl_to_uskl (pskl_all_syn P))
      with (uskl_all_syn (pskl_to_uskl P)) by reflexivity.
    replace (ptyp_to_bskl_syn (ptyp_all A))
      with (bskl_all_syn (ptyp_to_bskl_syn A)) by reflexivity.
    apply ad_pat_consis__forall_syn with (L := L `union` dom Θ1).
    intros X HX.
    rewrite <- pskl_to_uskl_open_var.
    rewrite <- ptyp_to_bskl_syn_open_var.
    apply IH; [ fsetdec | | ].
    + intros Y HY.
      apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in HY.
      simpl in HY.
      destruct (AtomSetImpl.union_1 HY) as [HY' | HY'].
      * apply AtomSetImpl.singleton_1 in HY'; subst.
        left. unfold binds; left; reflexivity.
      * apply a_binds_tvar_weaken_cons; auto.
    + intros γ Hb. apply a_binds_tvar_weaken_cons; auto.
Qed.

(* ===================================================================== *)
(*  Definition folding for skeleton consistency: if [β̂ := τ] and the      *)
(*  τ-unfolded skeleton is consistent with [Q], so is the folded one      *)
(*  (each unfolded occurrence re-wraps with the FlexL lookup rule).       *)
(* ===================================================================== *)

Lemma ad_pat_consis_fold_def : forall Θ β τ Ψ S' Q,
  ad_pat_consis Ψ Θ S' Q ->
  binds β (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->
  forall S0x,
  S' = subst_bskl_in_uskl (ptyp_to_uskl_syn τ) β S0x ->
  ad_pat_consis Ψ Θ S0x Q.
Proof.
  intros Θ β τ Ψ S' Q H Hb Hm.
  assert (Hlcτ : lc_uskl (ptyp_to_uskl_syn τ)).
  { clear - Hm. induction Hm; unfold ptyp_to_uskl_syn in *; simpl; auto. }
  (* β̂-occurrence refolding and mono-embedding head contradictions *)
  induction H; intros S0x HeqS.
  - (* unit *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + apply ad_pat_consis__unit; auto.
    + destruct (eq_var X0x β) as [->|Hne].
      * apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
        rewrite <- HeqS. apply ad_pat_consis__unit; auto.
      * discriminate HeqS.
  - (* var *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    destruct (eq_var X0x β) as [->|Hne].
    + apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
      rewrite <- HeqS. apply ad_pat_consis__var; auto.
    + inversion HeqS; subst. apply ad_pat_consis__var; auto.
  - (* arrow *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne].
      * apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
        rewrite <- HeqS. eapply ad_pat_consis__arrow; eauto.
      * discriminate HeqS.
    + inversion HeqS; subst. eapply ad_pat_consis__arrow; eauto.
  - (* forall_inh_tagged *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_inh_tagged with (L := L `union` {{β}});
        eauto.
      intros X HX. eapply H0; auto.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* forall_inh_untagged *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_inh_untagged with (L := L `union` {{β}}).
      intros X HX. eapply H0; auto.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* forall_syn_tagged *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_syn_tagged with (L := L `union` {{β}}).
      intros X HX. eapply H0; auto.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* forall_syn *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__forall_syn with (L := L `union` {{β}}).
      intros X HX. eapply H0; auto.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  - (* ghostg *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + apply ad_pat_consis__ghostg; auto.
  - (* topholeg *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst. apply ad_pat_consis__topholeg; auto.
  - (* hole *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + apply ad_pat_consis__hole; auto.
  - (* tophole *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst. apply ad_pat_consis__tophole; auto.
  - (* tophole_inh *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst.
      eapply ad_pat_consis__tophole_inh with (L := L);
        try (intros X HX; eapply H0; auto; simpl; reflexivity).
  - (* tophole_drop *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
      simpl in HeqS; try discriminate HeqS.
    + destruct (eq_var X0x β) as [->|Hne];
        [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS
        | ]; discriminate HeqS.
    + inversion HeqS; subst. apply ad_pat_consis__tophole_drop; auto.
  - (* flex_l *)
    destruct S0x as [ | n0x | X0x | S1 S2 | S0 | ε0 S0 | | S0 | | S0 ];
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
  intros * [[θ [Hid Hinc]] Hd] HΞ. split.
  - exists θ. eauto using a_inc_target_weaken.
  - intros α τ0 Hb. unfold binds; apply in_or_app; right. apply Hd; auto.
Qed.

Lemma a_isub_strengthen_decls_src : forall Ξ Θ Θ',
  a_decls Ξ ->
  (Ξ ++ Θ) ⊴ Θ' ->
  Θ ⊴ Θ'.
Proof.
  intros * Hdecl [[θ [Hid Hinc]] Hd]. split.
  - edestruct a_inc_strengthen_suffix_src as [θ' [Hid' Hinc']];
      [ eapply a_decls_suffix; eauto | exact Hinc | ].
    exists θ'. auto.
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
  intros Ξ; induction Ξ as [ | [γ bγ] Ξ' IH ]; intros * Hdecl Hwf.
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
      | Hγ : ?g `notin` _ |- _ `notin` _ =>
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
Lemma a_wf_ptyp_ftv_tvarish : forall Θ A X,
  a_wf_ptyp Θ A ->
  X `in` ftvar_in_ptyp A ->
  a_binds_tvar X Θ.
Proof.
  intros * Hwf; revert X; induction Hwf; intros Y HY; simpl in HY.
  - fsetdec.
  - assert (Y = X) by fsetdec. subst. auto.
  - destruct (AtomSetImpl.union_1 HY); auto.
  - pick fresh Z for (L `union` ftvar_in_ptyp A `union` {{Y}}).
    assert (HZL : Z `notin` L) by fsetdec.
    assert (Hyz : Y <> Z) by fsetdec.
    assert (HY' : Y `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A (ptyp_var_f Z))).
    { pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A (ptyp_var_f Z)).
      fsetdec. }
    assert (Htv : a_binds_tvar Y ((Z ~ abind_tvar) ++ Θ)) by (apply H0; auto).
    rewrite_env (nil ++ Θ).
    eapply a_binds_tvar_strip_mid with (c := Z) (b := abind_tvar);
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
  destruct (eq_var Xps β); simpl; auto using pskl_to_uskl_ptyp.
Qed.

(* ===================================================================== *)
(*  Binds-monotone weakening of the Θ-level judgments, and the last two    *)
(*  extraction helpers for assignvar                                       *)
(* ===================================================================== *)

Lemma ad_wf_pskl_weaken : forall Θ Θ' Δ P,
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  Θ' ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros * Hmon Hwf; revert Θ' Hmon; induction Hwf; intros Θ' Hmon;
    eauto using ad_wf_pskl;
    try (apply ad_wf_pskl__var;
         destruct H as [HΔ | [Hb | [Hb | [τ Hb]]]];
         [ left | right; left | right; right; left
         | right; right; right; exists τ ]; auto).
Qed.

Lemma ad_pat_consis_weaken : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Ψ ⨟ Θ' ⊨ₛᵃ S ≈ Q.
Proof.
  intros Ψ Θ S Q H; induction H; intros Θ' Hmon.
  - apply ad_pat_consis__unit; auto.
  - apply ad_pat_consis__var; auto.
    destruct H0 as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; auto.
  - eapply ad_pat_consis__arrow; eauto.
  - eapply ad_pat_consis__forall_inh_tagged with (L := L); eauto.
    intros X HX. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - eapply ad_pat_consis__forall_inh_untagged with (L := L); eauto.
    intros X HX. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - eapply ad_pat_consis__forall_syn_tagged with (L := L); eauto.
    intros X HX. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - eapply ad_pat_consis__forall_syn with (L := L); eauto.
    intros X HX. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_pat_consis__ghostg; auto.
  - apply ad_pat_consis__topholeg; auto.
  - apply ad_pat_consis__hole; eauto using ad_wf_pskl_weaken.
  - apply ad_pat_consis__tophole; auto.
  - eapply ad_pat_consis__tophole_inh with (L := L); eauto.
    intros X HX. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_pat_consis__tophole_drop; auto.
  - eapply ad_pat_consis__flex_l; eauto.
  - eapply ad_pat_consis__flex_r; eauto.
Qed.

Lemma ad_pat_consis_weaken_cons : forall Ψ Θ (e : list (atom * abind)) S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  Ψ ⨟ (e ++ Θ) ⊨ₛᵃ S ≈ Q.
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
(*  Soundness of assignment (thm:sound-consistency part 3):               *)
(*  [Θ0 | Ξ ⊲ α̂ := P ⊣ Θ1]  gives  (Ξ ++ Θ0) ⊴ Θ1  and, declaratively,   *)
(*  the assigned skeleton is consistent with the variable in Θ1.          *)
(* ===================================================================== *)

Lemma a_assign_sound : forall Θ0 Ξ α P Θ1,
  Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 ->
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (forall X, X `in` ftvar_in_pskl P -> a_binds_tvar X (Ξ ++ Θ0)) ->
  (Ξ ++ Θ0) ⊴ Θ1 /\
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (bskl_var_f α).
Proof.
  intros * Ha; induction Ha; intros Hdecl Hwf Hvis.
  - (* Assign-UnivGhost-Id : Ξ = ·, P = ⊤.α̂ *)
    split.
    + simpl. apply a_isub_refl.
    + replace (pskl_to_uskl (pskl_tophole (pskl_var_f α)))
        with (uskl_tophole (uskl_var_f α)) by reflexivity.
      apply ad_pat_consis__tophole_drop.
      apply ad_pat_consis__var; [ fsetdec | ].
      right; left. unfold binds; left; reflexivity.
  - (* Assign-SolveM : α̂ := guess^TY(P) with fresh βs *)
    assert (Hβsd : a_decls βs) by (eapply a_guess_mono_decls; eauto).
    assert (Hle : (Ξ ++ (α ~ abind_flex_mono) ++ Θ0) ⊴
                  ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0)).
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb. right; left.
        unfold binds. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; left. exact Hb. }
      apply a_isub_prepend_decls_src;
        [ apply (a_decls__cons α); constructor
        | intros γ Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ subst; right; right; exists τ; unfold binds;
            apply in_or_app; left; left; reflexivity
          | inversion Hb' ]
        | ].
      assert (Hs1 : Θ0 ⊴ ((βs ++ Ξ) ++ Θ0)).
      { apply a_isub_weaken_suffix.
        apply a_suffix_app; auto using a_decls_suffix. }
      first [ rewrite <- app_assoc in Hs1 | rewrite app_assoc in Hs1 ].
      apply a_isub_target_weaken with (Ξ := (α ~ abind_flex_mono_def τ))
        in Hs1; auto.
      apply (a_suffix__cons α (b := abind_flex_mono_def τ)); constructor. }
    split; [ exact Hle | ].
    apply ad_pat_consis__flex_r with (τ := τ);
      [ unfold binds; left; reflexivity | ].
    eapply a_guess_mono_consis; eauto.
    + intros X HX. eapply a_isub_binds_tvarish; eauto.
    + intros γ Hb. right; left.
      unfold binds. apply in_or_app; right.
      apply in_or_app; left. exact Hb.
  - (* Assign-Assign : continue on P[τ/β̂] under β̂ := τ *)
    assert (Hτ : a_wf_ptyp Θ0 τ /\ mono_ptyp τ)
      by (eapply a_wf_aenv_mid_def_inv; eauto).
    destruct Hτ as [Hτwf Hτm].
    assert (Hlcτ : lc_ptyp τ) by (eapply a_wf_ptyp_lc; eauto).
    destruct IHHa as [Hle Hcons]; auto.
    { eapply a_wf_aenv_strip_mid; eauto. }
    { intros X HX.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    P (ptyp_to_pskl τ) β) as Hup.
      assert (HX' : X `in` (ftvar_in_pskl (ptyp_to_pskl τ)
                            `union` remove β (ftvar_in_pskl P)))
        by (clear - HX Hup; fsetdec).
      destruct (AtomSetImpl.union_1 HX') as [HXτ | HXP].
      - rewrite ftvar_in_ptyp_to_pskl in HXτ.
        apply a_binds_tvar_weaken_cons.
        eapply a_wf_ptyp_ftv_tvarish; eauto.
      - assert (HXβ : X <> β) by (clear - HXP; fsetdec).
        assert (HXP' : X `in` ftvar_in_pskl P) by (clear - HXP; fsetdec).
        eapply a_binds_tvar_strip_mid with
          (c := β) (b := abind_flex_mono_def τ);
          [ apply Hvis; auto
          | intro Hc; inversion Hc; congruence
          | intro Hc; inversion Hc; congruence
          | intros τ0 Hc; inversion Hc; congruence ]. }
    split.
    + apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; eauto;
          try (unfold binds; apply in_or_app; left; exact Hb). }
      apply a_isub_cons_flex_def; auto.
      eapply a_isub_strengthen_decls_src; eauto.
    + eapply ad_pat_consis_fold_def with
        (β := β) (τ := τ)
        (S' := pskl_to_uskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P));
        [ apply ad_pat_consis_weaken_cons; exact Hcons
        | unfold binds; left; reflexivity
        | exact Hτm
        | apply pskl_to_uskl_subst ].
  - (* Assign-Depend : β̂ tunnels into Ξ *)
    destruct IHHa as [Hle Hcons]; auto.
    { apply (a_decls__cons β); auto. }
    { eapply a_wf_aenv_move_decl; eauto. }
    { intros X HX.
      apply (a_binds_tvar_permute_mid Ξ (β ~ abind_flex_mono) Θ0); auto. }
    split; [ | exact Hcons ].
    apply a_isub_prepend_decls_src; auto.
    { intros γ Hb.
      eapply a_isub_binds_flex; eauto;
        try (unfold binds; right; apply in_or_app; left; exact Hb). }
    apply a_isub_prepend_decls_src;
      [ apply (a_decls__cons β); constructor
      | intros γ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ subst; eapply a_isub_binds_flex; eauto;
          try (unfold binds; left; reflexivity)
        | inversion Hb' ]
      | ].
    eapply a_isub_strengthen_decls_src with
      (Ξ := (β ~ abind_flex_mono) ++ Ξ); eauto.
    apply (a_decls__cons β); auto.
  - (* Assign-Skip (flexible β̂ absent from P) *)
    destruct IHHa as [Hle Hcons]; auto.
    { eapply a_wf_aenv_strip_mid; eauto. }
    { intros X HX.
      assert (HXβ : X <> β) by (intro; subst; auto).
      eapply a_binds_tvar_strip_mid with (c := β) (b := abind_flex_mono);
        [ apply Hvis; auto
        | intro Hc; inversion Hc; congruence
        | intro Hc; inversion Hc; congruence
        | intros τ0 Hc; inversion Hc; congruence ]. }
    split.
    + apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; eauto;
          try (unfold binds; apply in_or_app; left; exact Hb). }
      apply a_isub_cons_flex.
      eapply a_isub_strengthen_decls_src; eauto.
    + apply ad_pat_consis_weaken_cons. exact Hcons.
  - (* Assign-SkipRigid *)
    destruct IHHa as [Hle Hcons]; auto.
    { eapply a_wf_aenv_strip_mid; eauto. }
    { intros X HX.
      assert (HXβ : X <> β) by (intro; subst; auto).
      eapply a_binds_tvar_strip_mid with (c := β) (b := abind_tvar);
        [ apply Hvis; auto
        | intro Hc; inversion Hc; congruence
        | intro Hc; inversion Hc; congruence
        | intros τ0 Hc; inversion Hc; congruence ]. }
    split.
    + apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; eauto;
          try (unfold binds; apply in_or_app; left; exact Hb). }
      apply a_isub_cons_tvar.
      eapply a_isub_strengthen_decls_src; eauto.
    + apply ad_pat_consis_weaken_cons. exact Hcons.
  - (* Assign-SkipTmVar *)
    destruct IHHa as [Hle Hcons]; auto.
    { eapply a_wf_aenv_strip_mid; eauto. }
    { intros X HX.
      eapply a_binds_tvar_strip_mid with (c := x) (b := abind_var_typ Q);
        [ apply Hvis; auto
        | intro Hc; inversion Hc
        | intro Hc; inversion Hc
        | intros τ0 Hc; inversion Hc ]. }
    split.
    + apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; eauto;
          try (unfold binds; apply in_or_app; left; exact Hb). }
      apply a_isub_cons_var_typ.
      eapply a_isub_strengthen_decls_src; eauto.
    + apply ad_pat_consis_weaken_cons. exact Hcons.
  - (* Assign-SkipTmSkl *)
    destruct IHHa as [Hle Hcons]; auto.
    { eapply a_wf_aenv_strip_mid; eauto. }
    { intros X HX.
      eapply a_binds_tvar_strip_mid with (c := x) (b := abind_var_skl Q);
        [ apply Hvis; auto
        | intro Hc; inversion Hc
        | intro Hc; inversion Hc
        | intros τ0 Hc; inversion Hc ]. }
    split.
    + apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; eauto;
          try (unfold binds; apply in_or_app; left; exact Hb). }
      apply a_isub_cons_var_skl.
      eapply a_isub_strengthen_decls_src; eauto.
    + apply ad_pat_consis_weaken_cons. exact Hcons.
Qed.
