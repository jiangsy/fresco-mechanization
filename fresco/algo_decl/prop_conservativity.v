Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_general_subsumption.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_syntax_directed.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.def_typing.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.basic.prop_suffix_erase.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.basic.prop_context.

Definition abind_of_dbind (d : dbind) : abind :=
  match d with
  | dbind_tvar => abind_tvar
  | dbind_typ A => abind_var_typ A
  | dbind_skl P => abind_var_skl P
  end.

Definition denv_to_aenv (Γ : denv) : aenv :=
  List.map (fun e => (fst e, abind_of_dbind (snd e))) Γ.

Lemma binds_denv_to_aenv : forall x d Γ,
  binds x d Γ -> binds x (abind_of_dbind d) (denv_to_aenv Γ).
Proof.
  intros x d Γ. induction Γ as [ | [y d'] Γ' IH ]; simpl; [ contradiction | ].
  intros [ Heq | Hin ]; [ inversion Heq; subst; left; reflexivity | ].
  right; apply IH; exact Hin.
Qed.

Lemma binds_denv_to_aenv_inv : forall x b Γ,
  binds x b (denv_to_aenv Γ) ->
  exists d, binds x d Γ /\ b = abind_of_dbind d.
Proof.
  intros x b Γ. induction Γ as [ | [y d'] Γ' IH ]; simpl; [ contradiction | ].
  intros [ Heq | Hin ].
  - inversion Heq; subst. exists d'.
    split; [ left; reflexivity | reflexivity ].
  - destruct (IH Hin) as [d [Hb Heq]]. exists d.
    split; [ right; exact Hb | exact Heq ].
Qed.

Lemma denv_to_aenv_no_flex_def : forall α τ Γ,
  binds α (abind_flex_mono_def τ) (denv_to_aenv Γ) -> False.
Proof.
  intros α τ Γ Hb.
  destruct (binds_denv_to_aenv_inv α (abind_flex_mono_def τ) Γ Hb) as [d [_ Heq]].
  destruct d; discriminate.
Qed.

Lemma a_binds_tvar_denv_to_aenv : forall α Γ,
  a_binds_tvar α (denv_to_aenv Γ) -> binds α dbind_tvar Γ.
Proof.
  intros α Γ [ Hb | [ Hb | [τ Hb] ] ];
    [ destruct (binds_denv_to_aenv_inv α abind_tvar Γ Hb) as [d [Hd Heq]]
    | destruct (binds_denv_to_aenv_inv α abind_flex_mono Γ Hb) as [d [Hd Heq]]
    | destruct (binds_denv_to_aenv_inv α (abind_flex_mono_def τ) Γ Hb)
        as [d [Hd Heq]] ];
    destruct d; try discriminate Heq; exact Hd.
Qed.

Lemma a_binds_tvar_of_denv : forall α Γ,
  binds α dbind_tvar Γ -> a_binds_tvar α (denv_to_aenv Γ).
Proof.
  intros α Γ Hb. left. exact (binds_denv_to_aenv α dbind_tvar Γ Hb).
Qed.

Lemma abind_to_pskl_of_dbind : forall d,
  abind_to_pskl (abind_of_dbind d) = dbind_to_pskl d.
Proof. destruct d; reflexivity. Qed.

Lemma denv_to_aenv_minus : forall Γ Δ,
  denv_to_aenv (denv_minus Γ Δ) = aenv_minus (denv_to_aenv Γ) Δ.
Proof.
  intros Γ Δ. induction Γ as [ | [x d] Γ' IH ]; [ reflexivity | ].
  unfold denv_minus, aenv_minus in *. simpl.
  destruct (AtomSetImpl.mem x Δ); simpl; [ exact IH | f_equal; exact IH ].
Qed.

Lemma a_tyequiv_denv_eq : forall Θ A B,
  a_tyequiv Θ A B -> forall Γ, Θ = denv_to_aenv Γ -> A = B.
Proof.
  intros Θ A B H; induction H; intros Γ0 HΘ; subst.
  - reflexivity.
  - symmetry. exact (IHa_tyequiv Γ0 eq_refl).
  - rewrite (IHa_tyequiv1 Γ0 eq_refl). exact (IHa_tyequiv2 Γ0 eq_refl).
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
  - rewrite (IHa_tyequiv1 Γ0 eq_refl), (IHa_tyequiv2 Γ0 eq_refl). reflexivity.
  - f_equal.
    pick fresh α for (L `union` ftvar_in_ptyp A `union` ftvar_in_ptyp B).
    apply open_ptyp_wrt_ptyp_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | ].
    exact (H0 α ltac:(clear - Fr; fsetdec) Γ0 eq_refl).
Qed.

Lemma a_wf_ptyp_to_d : forall Θ A,
  a_wf_ptyp Θ A -> forall Γ, Θ = denv_to_aenv Γ -> d_wf_ptyp Γ A.
Proof.
  intros Θ A H; induction H; intros Γ0 HΘ; subst;
    eauto 4 using d_wf_ptyp, a_binds_tvar_denv_to_aenv.
Qed.

Lemma d_wf_ptyp_to_a : forall Γ A,
  d_wf_ptyp Γ A -> a_wf_ptyp (denv_to_aenv Γ) A.
Proof.
  intros Γ A H; induction H; eauto 4 using a_wf_ptyp, a_binds_tvar_of_denv.
Qed.

Reserved Notation "{{ Γ ⊢ᵉ e }}d"
  (at level 0, e at level 74, format "'{{'  Γ  ⊢ᵉ  e  '}}d'").

Inductive d_wf_exp : denv -> exp -> Prop :=
| d_wf_exp__unit : forall Γ,
    {{ Γ ⊢ᵉ exp_unit }}d
| d_wf_exp__var : forall Γ x,
    {{ Γ ⊢ᵉ (exp_var_f x) }}d
| d_wf_exp__anno : forall Γ e A,
    d_wf_ptyp Γ A ->
    {{ Γ ⊢ᵉ e }}d ->
    {{ Γ ⊢ᵉ (exp_anno e A) }}d
| d_wf_exp__freeze : forall Γ e,
    {{ Γ ⊢ᵉ e }}d ->
    {{ Γ ⊢ᵉ (exp_freeze e) }}d
| d_wf_exp__abs : forall L Γ e,
    (forall x, x `notin` L ->
       {{ Γ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}d) ->
    {{ Γ ⊢ᵉ (exp_abs e) }}d
| d_wf_exp__abs_anno : forall L Γ A e,
    d_wf_ptyp Γ A ->
    (forall x, x `notin` L ->
       {{ Γ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}d) ->
    {{ Γ ⊢ᵉ (exp_abs_anno A e) }}d
| d_wf_exp__app : forall Γ e1 e2,
    {{ Γ ⊢ᵉ e1 }}d ->
    {{ Γ ⊢ᵉ e2 }}d ->
    {{ Γ ⊢ᵉ (exp_app e1 e2) }}d
where "{{ Γ ⊢ᵉ e }}d" := (d_wf_exp Γ e) : fresco_d_scope.

Lemma d_wf_exp_to_a : forall Γ e,
  {{ Γ ⊢ᵉ e }}d -> {{ (denv_to_aenv Γ) ⊢ᵉ e }}a.
Proof.
  intros Γ e H; induction H; eauto 4 using a_wf_exp, d_wf_ptyp_to_a.
Qed.

Lemma a_wf_pskl_to_d : forall Θ Δ P,
  a_wf_pskl Θ Δ P ->
  forall Γ, Θ = denv_to_aenv Γ -> d_wf_pskl Γ Δ P.
Proof.
  intros Θ Δ P H; induction H; intros Γ0 HΘ; subst;
    eauto 5 using d_wf_pskl, a_binds_tvar_denv_to_aenv,
      denv_to_aenv_minus, eq_sym.
Qed.

Lemma d_wf_pskl_to_a : forall Γ Δ P,
  d_wf_pskl Γ Δ P -> a_wf_pskl (denv_to_aenv Γ) Δ P.
Proof.
  intros Γ Δ P H; induction H;
    try solve [eauto 4 using a_wf_pskl, a_binds_tvar_of_denv].
  apply a_wf_pskl__univ_ghost; [ exact H | ].
  rewrite <- (denv_to_aenv_minus Γ Δ). exact IHd_wf_pskl.
Qed.

Lemma ad_pat_consis_to_d : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q -> forall Γ, Θ = denv_to_aenv Γ -> d_pat_consis Ψ Γ R Q.
Proof.
  intros Ψ Θ R Q H; induction H; intros Γ0 HΘ; subst;
    try solve [exfalso; eapply denv_to_aenv_no_flex_def; eassumption];
    eauto 5 using d_pat_consis, a_binds_tvar_denv_to_aenv.
Qed.

Lemma d_pat_consis_to_ad : forall Ψ Γ R Q,
  d_pat_consis Ψ Γ R Q -> ad_pat_consis Ψ (denv_to_aenv Γ) R Q.
Proof.
  intros Ψ Γ R Q H; induction H;
    eauto 4 using ad_pat_consis, a_binds_tvar_of_denv.
Qed.

Lemma ad_pat_consis_ty_to_d : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q ->
  forall Γ, Θ = denv_to_aenv Γ ->
  forall C B, R = utyp_to_uskl C -> Q = btyp_to_bskl B ->
  d_consis Ψ Γ C B.
Proof.
  intros Ψ Θ R Q H; induction H; intros Γ0 HΘ C0 B0 HR HQ; subst;
    try solve [exfalso; eapply denv_to_aenv_no_flex_def; eassumption];
    destruct C0; simpl in HR; try discriminate HR;
    destruct B0; simpl in HQ; try discriminate HQ; inversion HR; inversion HQ; subst;
    try solve [eauto 4 using d_consis, a_binds_tvar_denv_to_aenv].
  all: econstructor; try eassumption; intros α Hα;
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl
      (open_utyp_wrt_utyp C0 (utyp_var_f α))
      (open_btyp_wrt_btyp B0 (btyp_var_f α))
      ltac:(symmetry; apply utyp_to_uskl_open_var)
      ltac:(rewrite btyp_to_bskl_open; reflexivity)).
Qed.

Lemma d_consis_to_ad : forall Ψ Γ C B,
  d_consis Ψ Γ C B ->
  ad_pat_consis Ψ (denv_to_aenv Γ) (utyp_to_uskl C) (btyp_to_bskl B).
Proof.
  intros Ψ Γ C B H; induction H; simpl;
    try solve [eauto 4 using ad_pat_consis, a_binds_tvar_of_denv].
  all: econstructor; try eassumption; intros α Hα;
    pose proof (H0 α Hα) as Hx;
    rewrite utyp_to_uskl_open_var, (btyp_to_bskl_open B (btyp_var_f α)) in Hx; auto 2.
Qed.

Lemma ad_refine_syn_to_d : forall Θ Δ Q Q',
  ad_refine_syn Θ Δ Q Q' ->
  forall Γ, Θ = denv_to_aenv Γ -> d_refine_syn Γ Δ Q Q'.
Proof.
  intros Θ Δ Q Q' H; induction H; intros Γ0 HΘ; subst;
    try solve [exfalso; eapply denv_to_aenv_no_flex_def; eassumption];
    eauto 5 using d_refine_syn.
Qed.

Lemma d_refine_syn_to_ad : forall Γ Δ Q Q',
  d_refine_syn Γ Δ Q Q' -> ad_refine_syn (denv_to_aenv Γ) Δ Q Q'.
Proof.
  intros Γ Δ Q Q' H; induction H; eauto 4 using ad_refine_syn.
Qed.

Lemma ad_refine_pskl_to_d : forall Θ Δ P P',
  ad_refine_pskl Θ Δ P P' ->
  forall Γ, Θ = denv_to_aenv Γ -> d_refine_pskl Γ Δ P P'.
Proof.
  intros Θ Δ P P' H; induction H; intros Γ0 HΘ; subst;
    try solve [exfalso; eapply denv_to_aenv_no_flex_def; eassumption];
    eauto 5 using d_refine_pskl.
Qed.

Lemma d_refine_pskl_to_ad : forall Γ Δ P P',
  d_refine_pskl Γ Δ P P' -> ad_refine_pskl (denv_to_aenv Γ) Δ P P'.
Proof.
  intros Γ Δ P P' H; induction H; eauto 4 using ad_refine_pskl.
Qed.

Lemma d_refine_pskl_to_ad_closed : forall Γ P P',
  d_refine_pskl Γ empty P P' -> ad_refine_pskl (denv_to_aenv Γ) empty P P'.
Proof.
  intros Γ P P' H. exact (d_refine_pskl_to_ad Γ empty P P' H).
Qed.

Lemma ad_consis_join_to_d : forall Ψ Θ R Q,
  ad_consis_join Ψ Θ R Q -> forall Γ, Θ = denv_to_aenv Γ -> d_consis_join Ψ Γ R Q.
Proof.
  intros Ψ Θ R Q [Hc Hr] Γ0 HΘ; subst. split.
  - exact (ad_pat_consis_to_d Ψ (denv_to_aenv Γ0) R Q Hc Γ0 eq_refl).
  - eapply ad_refine_pskl_to_d; [ eassumption | reflexivity ].
Qed.

Lemma d_consis_join_to_ad : forall Ψ Γ R Q,
  d_consis_join Ψ Γ R Q -> ad_consis_join Ψ (denv_to_aenv Γ) R Q.
Proof.
  intros Ψ Γ R Q [Hc Hr]. split.
  - apply d_pat_consis_to_ad; assumption.
  - apply d_refine_pskl_to_ad_closed; assumption.
Qed.

Lemma d_wf_uskl_of_a_wf_pskl : forall Θ Δ P,
  a_wf_pskl Θ Δ P ->
  forall ψ, P = uskl_to_pskl ψ ->
  forall Γ, Θ = denv_to_aenv Γ -> d_wf_uskl Γ Δ ψ.
Proof.
  intros Θ Δ P H; induction H; intros ψ Hψ Γ0 HΘ; subst;
    destruct ψ; simpl in Hψ; try discriminate Hψ; inversion Hψ; subst;
    try solve [eauto 5 using d_wf_uskl, a_binds_tvar_denv_to_aenv,
      guarded_uskl_of_uskl_to_pskl, denv_to_aenv_minus, eq_sym].
  all: econstructor; intros α Hα;
    exact (H0 α Hα (open_uskl_wrt_uskl ψ (uskl_var_f α))
      ltac:(symmetry; apply uskl_to_pskl_open) ((α ~ dbind_tvar) ++ Γ0) eq_refl).
Qed.

Lemma a_wf_pskl_of_d_wf_uskl : forall Γ Δ ψ,
  d_wf_uskl Γ Δ ψ ->
  a_wf_pskl (denv_to_aenv Γ) Δ (uskl_to_pskl ψ).
Proof.
  intros Γ Δ ψ H; induction H; simpl;
    try solve [eauto 4 using a_wf_pskl, a_binds_tvar_of_denv].
  all: try solve [apply a_wf_pskl__all with (L := L); intros α Hα;
    pose proof (H0 α Hα) as Hx; rewrite uskl_to_pskl_open in Hx; auto 2].
  all: apply a_wf_pskl__univ_ghost;
    [eauto 2 using guarded_pskl_uskl_to_pskl |
     rewrite <- denv_to_aenv_minus; auto 2].
Qed.

Lemma uskl_ghost_free_utyp_to_uskl : forall R,
  uskl_ghost_free R -> utyp_to_uskl (uskl_to_utyp R) = R.
Proof.
  intros R H; induction H; simpl; try congruence.
  all: f_equal;
    pick fresh α for (L `union` ftvar_in_uskl R
                      `union` ftvar_in_uskl (utyp_to_uskl (uskl_to_utyp R)));
    apply open_uskl_wrt_uskl_inj with (α1 := α);
      [clear - Fr; fsetdec | clear - Fr; fsetdec |];
    rewrite <- utyp_to_uskl_open_var, <- uskl_to_utyp_open_var;
    apply H0; clear - Fr; fsetdec.
Qed.

Lemma is_dtyp_uskl_to_utyp : forall ψ,
  is_dskl ψ -> uskl_ghost_free ψ -> is_dtyp (uskl_to_utyp ψ).
Proof.
  intros ψ H; induction H; intros Hgf; simpl.
  - apply is_dtyp__unit.
  - apply is_dtyp__var.
  - inversion Hgf; subst. apply is_dtyp__arrow; auto.
  - inversion Hgf as [ | | | L0 ε0 R0 Hgf0 | ]; subst.
    apply is_dtyp__all_tag with (L := L `union` L0). intros α Hα.
    rewrite <- uskl_to_utyp_open_var.
    apply H0; [ clear - Hα; fsetdec | apply Hgf0; clear - Hα; fsetdec ].
  - inversion Hgf.
  - inversion Hgf.
Qed.

Lemma d_tags_uskl_to_utyp : forall Ψ ψ,
  d_tags_skl Ψ ψ -> uskl_ghost_free ψ -> d_tags Ψ (uskl_to_utyp ψ).
Proof.
  intros Ψ ψ H; induction H; intros Hgf; simpl.
  - apply d_tags__unit; assumption.
  - apply d_tags__var; assumption.
  - inversion Hgf; subst. apply d_tags__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); auto.
  - inversion Hgf as [ | | | L0 ε0 R0 Hgf0 | ]; subst.
    apply d_tags__all_tag with (L := L `union` L0) (Ψ0 := Ψ0);
      [ | assumption | assumption ].
    intros α Hα. rewrite <- uskl_to_utyp_open_var.
    apply H0; [ clear - Hα; fsetdec | apply Hgf0; clear - Hα; fsetdec ].
  - inversion Hgf.
  - inversion Hgf.
Qed.

Lemma d_wf_utyp_of_d_wf_uskl : forall Γ Δ ψ,
  d_wf_uskl Γ Δ ψ -> uskl_ghost_free ψ -> d_wf_utyp Γ (uskl_to_utyp ψ).
Proof.
  intros Γ Δ ψ H; induction H; intros Hgf; simpl.
  - inversion Hgf.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var. exact H.
  - inversion Hgf; subst. apply d_wf_utyp__arrow; auto.
  - inversion Hgf as [ | | | | L0 R0 Hgf0 ]; subst.
    apply d_wf_utyp__all_syn with (L := L `union` L0). intros α Hα.
    rewrite <- uskl_to_utyp_open_var.
    exact (H0 α ltac:(clear - Hα; fsetdec)
             (Hgf0 α ltac:(clear - Hα; fsetdec))).
  - inversion Hgf as [ | | | L0 ε0 R0 Hgf0 | ]; subst.
    apply d_wf_utyp__all_tag with (L := L `union` L0) (ε := ε). intros α Hα.
    rewrite <- uskl_to_utyp_open_var.
    exact (H0 α ltac:(clear - Hα; fsetdec)
             (Hgf0 α ltac:(clear - Hα; fsetdec))).
  - inversion Hgf.
  - inversion Hgf.
  - inversion Hgf.
Qed.

Lemma ad_pat_sub_sk_to_d : forall NM M Ψ Θ R Q,
  ad_pat_sub NM M Ψ Θ R Q -> NM = a_sub_mode_sk ->
  forall Γ, Θ = denv_to_aenv Γ -> d_pat_sub M Ψ Γ R Q.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros HNM Γ0 HΘ;
    try discriminate HNM; subst;
    try solve [exfalso; eapply denv_to_aenv_no_flex_def; eassumption];
    try solve [eauto 4 using d_pat_sub, ad_consis_join_to_d].
  all: match goal with Htag : a_tags_sort a_sub_mode_sk _ _ |- _ =>
    inversion Htag; subst
  end; eauto 5 using d_pat_sub, d_wf_uskl_of_a_wf_pskl.
Qed.

Lemma d_pat_sub_to_ad : forall M Ψ Γ R Q,
  d_pat_sub M Ψ Γ R Q -> ad_pat_sub a_sub_mode_sk M Ψ (denv_to_aenv Γ) R Q.
Proof.
  intros M Ψ Γ R Q H; induction H;
    eauto 5 using ad_pat_sub, d_consis_join_to_ad,
      a_tags_sort__sk, a_wf_pskl_of_d_wf_uskl.
Qed.

Lemma is_ityp_of_btyp_to_bskl : forall Q,
  is_iskl Q -> forall B, Q = btyp_to_bskl B -> is_ityp B.
Proof.
  intros Q H; induction H; intros B0 HQ;
    destruct B0; simpl in HQ; try discriminate HQ; inversion HQ; subst;
    try solve [eauto 5 using is_ityp].
  apply is_ityp__all with (L := L); intros α Hα.
  eapply H0; [ auto 2 | rewrite btyp_to_bskl_open; reflexivity ].
Qed.

Lemma inh_paint_btyp : forall P B,
  guarded_pskl P -> btyp_to_bskl B = pskl_to_bskl_inh P ->
  is_ityp B /\ guarded_btyp B.
Proof.
  intros P B Hg Heq.
  assert (Hi : is_ityp B).
  { apply (is_ityp_of_btyp_to_bskl (pskl_to_bskl_inh P));
      [ apply is_iskl_pskl_to_bskl_inh; apply guarded_pskl_lc; exact Hg
      | symmetry; exact Heq ]. }
  split; [ exact Hi | ].
  pose proof (is_ityp_lc Hi) as Hlc.
  destruct P; inversion Hg; subst;
    destruct B; simpl in Heq; try discriminate Heq;
    inversion Hlc; subst; eauto 3 using guarded_btyp.
Qed.

Lemma ad_pat_sub_ty_to_d : forall NM M Ψ Θ R Q,
  ad_pat_sub NM M Ψ Θ R Q -> NM = a_sub_mode_ty ->
  forall Γ, Θ = denv_to_aenv Γ ->
  forall C B, R = utyp_to_uskl C -> Q = btyp_to_bskl B ->
  d_sub M Ψ Γ C B.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros HNM Γ0 HΘ C0 B0 HR HQ;
    try discriminate HNM; subst.
  -  apply d_sub__infer;
      [ exact (ad_pat_consis_ty_to_d empty (denv_to_aenv Γ0) (utyp_to_uskl C0)
                 (btyp_to_bskl B0) (ad_consis_join_consis H0)
                 Γ0 eq_refl C0 B0 eq_refl eq_refl)
      | exact (is_styp_of_btyp_to_bskl (btyp_to_bskl B0) H1 B0 eq_refl)
      | assumption ].
  -
    destruct (inh_paint_btyp B B0 H0 (eq_sym HQ)) as [Hi Hgb].
    apply d_sub__check;
      [ apply guarded_utyp_of_guarded_uskl_incl; exact H
      | exact Hgb
      | exact (ad_pat_consis_ty_to_d Ψ (denv_to_aenv Γ0) (utyp_to_uskl C0)
                 (btyp_to_bskl B0)
                 ltac:(rewrite <- HQ; exact (ad_consis_join_consis H1))
                 Γ0 eq_refl C0 B0 eq_refl eq_refl)
      | exact Hi ].
  -  destruct B0; simpl in HQ; try discriminate HQ.
    inversion HQ; subst.
    apply d_sub__forall_r with (L := L).
    intros α Hα.
    exact (H0 α Hα eq_refl ((α ~ dbind_tvar) ++ Γ0) eq_refl C0
             (open_btyp_wrt_btyp B0 (btyp_var_f α)) eq_refl
             ltac:(rewrite btyp_to_bskl_open; reflexivity)).
  -
    destruct C0; simpl in HR; try discriminate HR.
    destruct B0; simpl in HQ; try discriminate HQ.
    inversion HR; inversion HQ; subst.
    apply d_sub__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ exact (ad_pat_consis_ty_to_d Ψ1 (denv_to_aenv Γ0) (utyp_to_uskl C0_1)
                 (btyp_to_bskl B0_1) (ad_consis_join_consis H)
                 Γ0 eq_refl C0_1 B0_1 eq_refl eq_refl)
      | exact (IHad_pat_sub eq_refl Γ0 eq_refl C0_2 B0_2 eq_refl eq_refl)
      | assumption ].
  -
    destruct C0; simpl in HR; try discriminate HR.
    inversion HR; subst. inversion H2; subst.
    apply d_sub__forall_l_tagged with (Ψ' := Ψ') (ph := uskl_to_utyp ψ);
      [ assumption | assumption
      |
        rewrite <- ftag_utyp_to_uskl; simpl in H1 |- *; exact H1
      | apply d_tags_uskl_to_utyp; assumption
      | exact (d_wf_utyp_of_d_wf_uskl Γ0 empty ψ
                 (d_wf_uskl_of_a_wf_pskl (denv_to_aenv Γ0) empty
                    (uskl_to_pskl ψ) H3 ψ eq_refl Γ0 eq_refl) H7)
      | apply is_dtyp_uskl_to_utyp; assumption
      | exact (IHad_pat_sub eq_refl Γ0 eq_refl
                 (open_utyp_wrt_utyp C0 (uskl_to_utyp ψ)) B0
                 ltac:(rewrite utyp_to_uskl_open;
                       rewrite (uskl_ghost_free_utyp_to_uskl ψ H7);
                       reflexivity)
                 eq_refl) ].
  -
    destruct C0; simpl in HR; try discriminate HR.
    inversion HR; subst. inversion H2; subst.
    apply d_sub__forall_l_untagged with (Ψ' := Ψ') (ph := uskl_to_utyp ψ);
      [ assumption | assumption
      |
        rewrite <- ftag_utyp_to_uskl; simpl in H1 |- *; exact H1
      | apply d_tags_uskl_to_utyp; assumption
      | exact (d_wf_utyp_of_d_wf_uskl Γ0 empty ψ
                 (d_wf_uskl_of_a_wf_pskl (denv_to_aenv Γ0) empty
                    (uskl_to_pskl ψ) H3 ψ eq_refl Γ0 eq_refl) H7)
      | apply is_dtyp_uskl_to_utyp; assumption
      | exact (IHad_pat_sub eq_refl Γ0 eq_refl
                 (open_utyp_wrt_utyp C0 (uskl_to_utyp ψ)) B0
                 ltac:(rewrite utyp_to_uskl_open;
                       rewrite (uskl_ghost_free_utyp_to_uskl ψ H7);
                       reflexivity)
                 eq_refl) ].
  -  exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
Qed.

Lemma ad_pat_to_d : forall M Θ e Q,
  ad_pat M Θ e Q -> forall Γ, Θ = denv_to_aenv Γ -> d_pat M Γ e Q.
Proof.
  intros M Θ e Q H; induction H; intros Γ0 HΘ; subst Θ;
    try solve [eauto 5 using d_pat, a_wf_pskl_to_d, a_wf_ptyp_to_d,
      ad_pat_sub_sk_to_d, ad_refine_syn_to_d].
  destruct (binds_denv_to_aenv_inv x b Γ0 H) as [d [Hd Heq]]; subst.
  eapply d_pat__var; eauto 4 using a_wf_pskl_to_d, ad_pat_sub_sk_to_d.
  rewrite <- abind_to_pskl_of_dbind; auto 2.
Qed.

Lemma ad_sd_typing_to_d : forall M Θ e B,
  ad_sd_typing M Θ e B -> forall Γ, Θ = denv_to_aenv Γ -> d_sd_typing M Γ e B.
Proof.
  intros M Θ e B H; induction H; intros Γ0 HΘ; subst Θ.
  -  apply d_sd_typing__unit.
    eapply ad_pat_sub_ty_to_d;
      [ eassumption | reflexivity | reflexivity | | reflexivity ];
    unfold ptyp_to_uskl_syn; symmetry; apply utyp_to_uskl_ptyp_to_utyp_syn.
  -
    destruct (binds_denv_to_aenv_inv x (abind_var_typ A) Γ0 H) as [d [Hd Heq]].
    destruct d as [ | A1 | P1 ]; simpl in Heq; try discriminate Heq.
    assert (HA : A = A1) by (injection Heq; auto). subst A1.
    apply d_sd_typing__var with (A := A);
      [ exact Hd
      | eapply ad_pat_sub_ty_to_d;
          [ eassumption | reflexivity | reflexivity | | reflexivity ];
        unfold ptyp_to_uskl_syn; symmetry; apply utyp_to_uskl_ptyp_to_utyp_syn ].
  -  apply d_sd_typing__anno with (A := A);
      [ exact (IHad_sd_typing Γ0 eq_refl)
      | eapply ad_pat_sub_ty_to_d;
          [ eassumption | reflexivity | reflexivity | | reflexivity ];
        unfold ptyp_to_uskl_syn; symmetry; apply utyp_to_uskl_ptyp_to_utyp_syn ].
  -
    rewrite (a_tyequiv_denv_eq (denv_to_aenv Γ0) B A H0 Γ0 eq_refl) in *.
    apply d_sd_typing__freeze. exact (IHad_sd_typing Γ0 eq_refl).
  -  apply d_sd_typing__abs_check_step with (L := L);
      intros α Hα; exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  -  apply d_sd_typing__abs_check_base with (L := L);
      [ exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H Γ0 eq_refl)
      | assumption
      | intros x Hx; exact (H2 x Hx ((x ~ dbind_typ A) ++ Γ0) eq_refl) ].
  -
    apply d_sd_typing__abs_anno_check_step with (L := L);
      intros α Hα; exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  -
    rewrite <- (a_tyequiv_denv_eq (denv_to_aenv Γ0) A A' H0 Γ0 eq_refl).
    apply d_sd_typing__abs_anno_check_base with (L := L);
      [ exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H Γ0 eq_refl)
      | assumption
      | intros x Hx; exact (H3 x Hx ((x ~ dbind_typ A) ++ Γ0) eq_refl) ].
  -  apply d_sd_typing__abs with (L := L);
      [ assumption
      | exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H0 Γ0 eq_refl)
      | assumption
      | intros x Hx; exact (H3 x Hx ((x ~ dbind_typ A) ++ Γ0) eq_refl) ].
  -
    apply d_sd_typing__abs_anno with (L := L);
      [ assumption
      | exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H0 Γ0 eq_refl)
      | rewrite H2; symmetry;
        exact (a_tyequiv_denv_eq (denv_to_aenv Γ0) A A' H1 Γ0 eq_refl)
      | assumption
      | intros x Hx; exact (H5 x Hx ((x ~ dbind_typ A) ++ Γ0) eq_refl) ].
  -
    assert (HA2 : btyp_to_ptyp B1 = A2)
      by exact (a_tyequiv_denv_eq (denv_to_aenv Γ0) (btyp_to_ptyp B1) A2
                  H2 Γ0 eq_refl).
    apply d_sd_typing__app with (P := P) (B1 := B1);
      [ exact (ad_pat_to_d mode_tc (denv_to_aenv Γ0) e2
                 (pskl_to_bskl_syn P) H Γ0 eq_refl)
      | exact (ad_refine_syn_to_d (denv_to_aenv Γ0) empty
                 (pskl_to_bskl_inh P) (btyp_to_bskl B1) H0 Γ0 eq_refl)
      | exact (IHad_sd_typing1 Γ0 eq_refl)
      | rewrite HA2; exact (IHad_sd_typing2 Γ0 eq_refl) ].
Qed.

Lemma msubst_btyp_nil : forall B, msubst_btyp nil B = B.
Proof. induction B; simpl; congruence. Qed.

Lemma msubst_btyp_ptyp_to_btyp_syn : forall ζ A,
  msubst_btyp ζ (ptyp_to_btyp_syn A) = ptyp_to_btyp_syn (msubst_ptyp ζ A).
Proof. induction A; simpl; congruence. Qed.

Definition msubst_mono (ζ : metasubst) : Prop :=
  forall α, mono_ptyp (msubst_lookup ζ α).

Lemma msubst_btyp_ptyp_to_btyp_inh : forall ζ A,
  msubst_mono ζ ->
  msubst_btyp ζ (ptyp_to_btyp_inh A) = ptyp_to_btyp_inh (msubst_ptyp ζ A).
Proof.
  intros ζ A Hm. induction A; simpl; try congruence.
  symmetry. apply ptyp_to_btyp_inh_mono_syn. apply Hm.
Qed.

Lemma msubst_btyp_cons_subst : forall ζ β τ B,
  msubst_btyp ((β, msubst_ptyp ζ τ) :: ζ) B
  = msubst_btyp ζ (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) β B).
Proof.
  intros ζ β τ B. induction B; try (simpl; congruence).
  cbn [subst_btyp_in_btyp]. destruct (α == β) as [ Heq | Hne ].
  - subst α. destruct (eq_var β β) as [ _ | Hc ]; [ | contradiction ].
    cbn [msubst_btyp]. rewrite msubst_lookup_cons_eq.
    symmetry. apply msubst_btyp_ptyp_to_btyp_syn.
  - destruct (eq_var α β) as [ Hc | _ ]; [ contradiction | ].
    cbn [msubst_btyp]. rewrite msubst_lookup_cons_neq by exact Hne.
    reflexivity.
Qed.

Definition msubst_closes (ζ : metasubst) (Θ : aenv) : Prop :=
  forall α, a_binds_tvar α Θ -> a_wf_ptyp nil (msubst_lookup ζ α).

Lemma a_binds_tvar_strengthen_cons : forall α β b Θ,
  α <> β -> a_binds_tvar α ((β ~ b) ++ Θ) -> a_binds_tvar α Θ.
Proof.
  intros α β b Θ Hne [ Hb | [ Hb | [τ Hb] ] ]; simpl in Hb;
    (destruct Hb as [ Heq | Hb ];
     [ inversion Heq; subst; contradiction | ]);
    [ left | right; left | right; right; exists τ ]; exact Hb.
Qed.

Lemma msubst_closes_ptyp : forall ζ Θ τ,
  msubst_mono ζ -> msubst_closes ζ Θ -> a_wf_ptyp Θ τ -> mono_ptyp τ ->
  mono_ptyp (msubst_ptyp ζ τ) /\ a_wf_ptyp nil (msubst_ptyp ζ τ).
Proof.
  intros ζ Θ τ Hmo Hc Hwf Hm. revert Hwf. induction Hm; intros Hwf; simpl.
  - split; [ apply mono_ptyp__unit | apply a_wf_ptyp__unit ].
  - inversion Hwf; subst.
    match goal with Hb : a_binds_tvar _ _ |- _ => exact (conj (Hmo _) (Hc _ Hb)) end.
  - inversion Hwf; subst.
    match goal with
    | Hw1 : a_wf_ptyp _ A1, Hw2 : a_wf_ptyp _ A2 |- _ =>
        destruct (IHHm1 Hw1) as [Hm1' Hw1']; destruct (IHHm2 Hw2) as [Hm2' Hw2']
    end.
    split; [ apply mono_ptyp__arrow | apply a_wf_ptyp__arrow ]; assumption.
Qed.

Lemma msubst_mono_nil : msubst_mono nil.
Proof. intros α. simpl. apply mono_ptyp__var. Qed.

Lemma msubst_mono_cons : forall ζ β σ,
  msubst_mono ζ -> mono_ptyp σ -> msubst_mono ((β, σ) :: ζ).
Proof.
  intros ζ β σ Hmo Hm α. simpl.
  destruct (α == β) as [ -> | Hne ]; [ exact Hm | apply Hmo ].
Qed.

Lemma msubst_closes_cons : forall ζ Θ β b σ,
  msubst_closes ζ Θ -> a_wf_ptyp nil σ ->
  msubst_closes ((β, σ) :: ζ) ((β ~ b) ++ Θ).
Proof.
  intros ζ Θ β b σ Hc Hw α Ha. simpl.
  destruct (α == β) as [ -> | Hne ]; [ exact Hw | ].
  apply Hc. exact (a_binds_tvar_strengthen_cons α β b Θ Hne Ha).
Qed.

Lemma a_inc_nil_suffix : forall κ Θ, κ ∷ nil ⊑ Θ -> a_suffix Θ.
Proof. intros κ Θ H. inversion H; subst. assumption. Qed.

Lemma ad_sd_typing_close_suffix : forall Ξ,
  a_suffix Ξ -> {{ ⊢ Ξ }}a ->
  forall M e B, ad_sd_typing M Ξ e B ->
  ftvar_in_exp e [<=] empty ->
  exists ζ, ζ ∷ Ξ ⊑ nil /\ msubst_mono ζ /\ msubst_closes ζ Ξ
         /\ ad_sd_typing M nil e (msubst_btyp ζ B).
Proof.
  induction Ξ as [ | [β b] Ξ' IH ]; intros Hsuf Hwf M e B Hd He.
  - exists nil. repeat split.
    + apply a_inc__empty. apply a_suffix__nil.
    + apply msubst_mono_nil.
    + intros α [ Hb | [ Hb | [τ Hb] ] ]; contradiction.
    + rewrite msubst_btyp_nil. exact Hd.
  - inversion Hsuf as [ | ? ? ? Hsuf' Hbind ]; subst.
    simpl_env in Hwf.
    destruct (solves_flex_of_wf_head Hbind Hwf) as [τs Hs].
    assert (Hwf' : {{ ⊢ Ξ' }}a) by (inversion Hwf; subst; assumption).
    assert (Hβd : β `notin` dom Ξ') by (inversion Hwf; subst; assumption).
    pose proof (@ad_sd_typing_subst_mid _ _ _ _ Hd τs β b nil Ξ'
                  ltac:(simpl_env; reflexivity) Hs
                  ltac:(simpl_env; apply a_wf_aenv_uniq; exact Hwf)) as Hx.
    simpl_env in Hx.
    assert (Hdd : ftvar_in_aenv Ξ' [<=] dom Ξ')
      by (apply a_wf_aenv_ftv_dom; exact Hwf').
    rewrite subst_aenv_fresh_eq in Hx by (clear - Hβd Hdd; fsetdec).
    rewrite subst_ptyp_in_exp_fresh_eq in Hx by (clear - He; fsetdec).
    destruct (IH Hsuf' Hwf' M e _ Hx He) as [ζ' [Hinc' [Hmo' [Hcl' Htd]]]].
    assert (Hmw : mono_ptyp (msubst_ptyp ζ' τs)
                  /\ a_wf_ptyp nil (msubst_ptyp ζ' τs))
      by (eapply msubst_closes_ptyp;
            [ exact Hmo' | exact Hcl' | eapply solves_flex_wf; exact Hs
            | eapply solves_flex_mono; exact Hs ]).
    destruct Hmw as [Hmono Hwfc].
    exists ((β, msubst_ptyp ζ' τs) :: ζ'). repeat split.
    + destruct Hs as [_ [_ [_ [Hb | Hb]]]]; subst b;
        [ apply a_inc__flex; assumption
        | apply a_inc__flex_def;
            [ assumption | assumption | assumption
            | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmono ] ].
    + apply msubst_mono_cons; assumption.
    + apply msubst_closes_cons; assumption.
    + rewrite msubst_btyp_cons_subst. exact Htd.
Qed.

Lemma uskl_ghost_free_incl : forall C,
  lc_utyp C -> uskl_ghost_free (utyp_to_uskl C).
Proof.
  intros C H; induction H; simpl; try solve [ constructor ].
  - apply uskl_ghost_free__arrow; assumption.
  - apply uskl_ghost_free__all_syn with (L := empty). intros α _.
    rewrite <- utyp_to_uskl_open_var. auto.
  - apply uskl_ghost_free__all_tag with (L := empty). intros α _.
    rewrite <- utyp_to_uskl_open_var. auto.
Qed.

Lemma is_sskl_of_is_styp : forall B, is_styp B -> is_sskl (btyp_to_bskl B).
Proof.
  intros B H; induction H; simpl; try solve [ constructor; auto ].
  apply is_sskl__all with (L := L). intros α Hα.
  change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
  rewrite <- btyp_to_bskl_open. auto.
Qed.

Lemma guarded_uskl_incl : forall C,
  guarded_utyp C -> guarded_uskl (utyp_to_uskl C).
Proof.
  intros C H; inversion H; subst; simpl;
    [ apply guarded_uskl__unit | apply guarded_uskl__var
    | apply guarded_uskl__arrow; apply lc_utyp_to_uskl; assumption ].
Qed.

Lemma d_tags_skl_incl : forall Ψ C,
  d_tags Ψ C -> d_tags_skl Ψ (utyp_to_uskl C).
Proof.
  intros Ψ C H; induction H; simpl.
  - apply d_tags_skl__unit; assumption.
  - apply d_tags_skl__var; assumption.
  - apply d_tags_skl__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
  - apply d_tags_skl__all_tag with (L := L) (Ψ0 := Ψ0);
      [ | assumption | assumption ].
    intros α Hα. rewrite <- utyp_to_uskl_open_var. auto.
Qed.

Lemma d_wf_uskl_incl_gen : forall Γ C,
  d_wf_utyp Γ C ->
  forall Γ' Δ,
    (forall α, binds α dbind_tvar Γ -> binds α dbind_tvar Γ') ->
    d_wf_uskl Γ' Δ (utyp_to_uskl C).
Proof.
  intros Γ C H; induction H; intros Γ' Δ0 Hvis; simpl.
  - apply d_wf_uskl__unit.
  - apply d_wf_uskl__var. apply Hvis; assumption.
  - apply d_wf_uskl__arrow;
      [ apply IHd_wf_utyp1 | apply IHd_wf_utyp2 ]; exact Hvis.
  - apply d_wf_uskl__all_syn with (L := L). intros α Hα.
    rewrite <- utyp_to_uskl_open_var. apply (H0 α Hα).
    intros β Hb. apply binds_app_iff in Hb. apply binds_app_iff.
    destruct Hb as [ Hb | Hb ]; [ left; exact Hb | right; apply Hvis, Hb ].
  - apply d_wf_uskl__all_tag with (L := L) (ε := ε). intros α Hα.
    rewrite <- utyp_to_uskl_open_var. apply (H0 α Hα).
    intros β Hb. apply binds_app_iff in Hb. apply binds_app_iff.
    destruct Hb as [ Hb | Hb ]; [ left; exact Hb | right; apply Hvis, Hb ].
Qed.

Lemma d_wf_uskl_incl : forall Γ C,
  d_wf_utyp Γ C -> d_wf_uskl Γ empty (utyp_to_uskl C).
Proof.
  intros Γ C H. apply (d_wf_uskl_incl_gen Γ C H Γ empty).
  intros α Hb. exact Hb.
Qed.

Lemma guarded_ityp_inh_paint : forall B,
  is_ityp B -> guarded_btyp B ->
  btyp_to_bskl B = pskl_to_bskl_inh (bskl_to_pskl (btyp_to_bskl B))
  /\ guarded_pskl (bskl_to_pskl (btyp_to_bskl B)).
Proof.
  intros B Hi Hg. split; [ apply inh_paint_bskl; exact Hi | ].
  inversion Hg; subst; simpl;
    [ apply guarded_pskl__unit | apply guarded_pskl__var
    | apply guarded_pskl__arrow; apply lc_pskl_of_lc_btyp; assumption ].
Qed.

Lemma d_consis_refine_ty : forall Ψ Γ C B,
  {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
  {{ (denv_to_aenv Γ) ⨟ empty ⊢ₚₛ (uskl_to_pskl (utyp_to_uskl C)) }}a ->
  {{ (denv_to_aenv Γ) ⨟ empty ⊢ᵣₚ (uskl_to_pskl (utyp_to_uskl C))
     ⊳ (bskl_to_pskl (btyp_to_bskl B)) }}ad.
Proof.
  intros Ψ Γ C B Hc Hwf.
  rewrite bskl_to_pskl_btyp_to_bskl.
  rewrite <- (d_consis_btyp_erase Hc).
  rewrite <- uskl_to_pskl_utyp_to_uskl.
  apply ad_refine_pskl_refl; exact Hwf.
Qed.

Lemma a_wf_pskl_of_d_wf_utyp : forall Γ C,
  d_wf_utyp Γ C ->
  {{ (denv_to_aenv Γ) ⨟ empty ⊢ₚₛ (uskl_to_pskl (utyp_to_uskl C)) }}a.
Proof.
  intros Γ C H.
  exact (a_wf_pskl_of_d_wf_uskl Γ empty (utyp_to_uskl C)
           (d_wf_uskl_incl Γ C H)).
Qed.

Lemma d_consis_join_ty : forall Ψ Γ C B,
  {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
  {{ (denv_to_aenv Γ) ⨟ empty ⊢ₚₛ (uskl_to_pskl (utyp_to_uskl C)) }}a ->
  {{ Ψ ⨟ (denv_to_aenv Γ) ⊢ˢ (utyp_to_uskl C) ∼ᵣ (btyp_to_bskl B) }}ad.
Proof.
  intros Ψ Γ C B Hc Hwf. split.
  - apply d_consis_to_ad; assumption.
  - eapply d_consis_refine_ty; eassumption.
Qed.

Lemma d_sub_to_ad : forall M Ψ Γ C B,
  d_sub M Ψ Γ C B ->
  d_wf_utyp Γ C ->
  ad_pat_sub a_sub_mode_ty M Ψ (denv_to_aenv Γ)
    (utyp_to_uskl C) (btyp_to_bskl B).
Proof.
  intros M Ψ Γ C B H; induction H; intros Hwf; simpl.
  -  apply ad_pat_sub__infer;
      [ assumption
      | eapply d_consis_join_ty;
          [ eassumption | apply a_wf_pskl_of_d_wf_utyp; assumption ]
      | apply is_sskl_of_is_styp; assumption ].
  -
    destruct (guarded_ityp_inh_paint B ltac:(assumption) ltac:(assumption))
      as [ Heq Hgp ].
    rewrite Heq. apply ad_pat_sub__check;
      [ apply guarded_uskl_incl; assumption | exact Hgp | ].
    apply ad_consis_join_inh_intro.
    + rewrite <- Heq. apply d_consis_to_ad; assumption.
    + eapply d_consis_refine_ty;
        [ eassumption | apply a_wf_pskl_of_d_wf_utyp; assumption ].
  -
    apply ad_pat_sub__forall_r with (L := L `union` dom Γ). intros α Hα.
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
    rewrite <- btyp_to_bskl_open.
    apply H0; [ clear - Hα; fsetdec
              | apply (d_wf_utyp_weakening_head ((α ~ dbind_tvar) ++ nil)); assumption ].
  -
    inversion Hwf; subst.
    apply ad_pat_sub__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ eapply d_consis_join_ty;
          [ eassumption | apply a_wf_pskl_of_d_wf_utyp; assumption ]
      | apply IHd_sub; assumption
      | assumption ].
  -
    apply ad_pat_sub__forall_l_tagged with
      (Ψ' := Ψ') (ψ := utyp_to_uskl ph);
      [ assumption | assumption
      |
        rewrite (ftag_utyp_to_uskl (utyp_all_tag ε C)); assumption
      | apply a_tags_sort__ty;
          [ apply is_dskl_utyp_to_uskl; assumption
          | apply d_tags_skl_incl; assumption
          | apply uskl_ghost_free_incl; eapply d_wf_utyp_lc; eassumption ]
      | exact (a_wf_pskl_of_d_wf_uskl Γ empty (utyp_to_uskl ph)
                 (d_wf_uskl_incl Γ ph ltac:(assumption)))
      | rewrite <- utyp_to_uskl_open; apply IHd_sub;
        inversion Hwf; subst; eapply d_wf_utyp_open; eassumption ].
  -
    apply ad_pat_sub__forall_l_untagged with
      (Ψ' := Ψ') (ψ := utyp_to_uskl ph);
      [ assumption | assumption
      | rewrite (ftag_utyp_to_uskl (utyp_all_syn C)); assumption
      | apply a_tags_sort__ty;
          [ apply is_dskl_utyp_to_uskl; assumption
          | apply d_tags_skl_incl; assumption
          | apply uskl_ghost_free_incl; eapply d_wf_utyp_lc; eassumption ]
      | exact (a_wf_pskl_of_d_wf_uskl Γ empty (utyp_to_uskl ph)
                 (d_wf_uskl_incl Γ ph ltac:(assumption)))
      | rewrite <- utyp_to_uskl_open; apply IHd_sub;
        inversion Hwf; subst; eapply d_wf_utyp_open; eassumption ].
Qed.

Lemma d_pat_to_ad : forall M Γ e Q,
  d_pat M Γ e Q -> ad_pat M (denv_to_aenv Γ) e Q.
Proof.
  intros M Γ e Q H; induction H;
    try solve [eauto 5 using ad_pat, d_wf_pskl_to_a, d_wf_ptyp_to_a,
      d_pat_sub_to_ad, d_refine_syn_to_ad].
  eapply ad_pat__var with (b := abind_of_dbind d);
    eauto 3 using binds_denv_to_aenv, d_wf_pskl_to_a, d_pat_sub_to_ad.
  rewrite abind_to_pskl_of_dbind; auto 2.
Qed.

Lemma aenv_tbinds_le_weaken_cons : forall Θ x (b : abind),
  aenv_tbinds_le Θ ((x ~ b) ++ Θ).
Proof. intros Θ x b y c Hc Hy. apply binds_app_3; exact Hy. Qed.

Ltac base_row wftac :=
  unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn;
  rewrite <- utyp_to_uskl_ptyp_to_utyp_syn;
  apply d_sub_to_ad;
    [ eassumption | apply d_wf_utyp_painting_syn; wftac ].

Lemma d_sd_typing_to_ad : forall M Γ e B,
  d_sd_typing M Γ e B ->
  d_wf_denv Γ ->
  {{ (denv_to_aenv Γ) ⊢ᵉ e }}a ->
  ad_sd_typing M (denv_to_aenv Γ) e B.
Proof.
  intros M Γ e B H; induction H; intros Hwf Hwfe.
  -
    apply ad_sd_typing__unit.
    base_row ltac:(apply d_wf_ptyp__unit).
  -
    apply ad_sd_typing__var with (A := A);
      [ apply binds_denv_to_aenv with (d := dbind_typ A); assumption | ].
    base_row ltac:(eapply d_wf_denv_binds_ptyp; eassumption).
  -
    inversion Hwfe as [ | | | | L0 Θ0 e0 Hbody | | ]; subst.
    apply ad_sd_typing__abs with (L := L `union` L0 `union` dom Γ) (A := A);
      [ assumption | apply d_wf_ptyp_to_a; assumption | assumption | ].
    intros x Hx.
    exact (H3 x ltac:(clear - Hx; solve_notin_auto)
             ltac:(apply d_wf_denv__typ;
                     [ exact Hwf | clear - Hx; solve_notin_auto | assumption ])
             ltac:(apply (a_wf_exp_mono
                            (Hbody x ltac:(clear - Hx; solve_notin_auto)));
                   apply aenv_tbinds_le_weaken_cons)).
  -
    apply ad_sd_typing__abs_check_step with (L := L `union` dom Γ).
    intros α Hα.
    exact (H0 α ltac:(clear - Hα; solve_notin_auto)
             ltac:(apply d_wf_denv__tvar;
                     [ exact Hwf | clear - Hα; solve_notin_auto ])
             ltac:(apply (a_wf_exp_mono Hwfe);
                   apply aenv_tbinds_le_weaken_cons)).
  -
    inversion Hwfe as [ | | | | L0 Θ0 e0 Hbody | | ]; subst.
    apply ad_sd_typing__abs_check_base
      with (L := L `union` L0 `union` dom Γ) (A := A);
      [ apply d_wf_ptyp_to_a; assumption | assumption | ].
    intros x Hx.
    exact (H2 x ltac:(clear - Hx; solve_notin_auto)
             ltac:(apply d_wf_denv__typ;
                     [ exact Hwf | clear - Hx; solve_notin_auto | assumption ])
             ltac:(apply (a_wf_exp_mono
                            (Hbody x ltac:(clear - Hx; solve_notin_auto)));
                   apply aenv_tbinds_le_weaken_cons)).
  -
    inversion Hwfe as [ | | Θ0 e0 A0 Hwfa Hwfe0 | | | | ]; subst.
    apply ad_sd_typing__anno with (A := A);
      [ exact Hwfa | apply IHd_sd_typing; assumption | ].
    base_row ltac:(eapply a_wf_ptyp_to_d; [ eassumption | reflexivity ]).
  -
    inversion Hwfe as [ | | | | | L0 Θ0 A0 e0 Hwfa Hbody | ]; subst.

    apply ad_sd_typing__abs_anno
      with (L := L `union` L0 `union` dom Γ)
           (A := btyp_to_ptyp B1) (A' := btyp_to_ptyp B1) (B1 := B1);
      [ assumption | exact Hwfa
      | apply a_tyequiv__refl; eapply d_wf_ptyp_lc; eassumption
      | reflexivity | assumption | ].
    intros x Hx.
    exact (H4 x ltac:(clear - Hx; solve_notin_auto)
             ltac:(apply d_wf_denv__typ;
                     [ exact Hwf | clear - Hx; solve_notin_auto | assumption ])
             ltac:(apply (a_wf_exp_mono
                            (Hbody x ltac:(clear - Hx; solve_notin_auto)));
                   apply aenv_tbinds_le_weaken_cons)).
  -
    apply ad_sd_typing__abs_anno_check_step with (L := L `union` dom Γ).
    intros α Hα.
    exact (H0 α ltac:(clear - Hα; solve_notin_auto)
             ltac:(apply d_wf_denv__tvar;
                     [ exact Hwf | clear - Hα; solve_notin_auto ])
             ltac:(apply (a_wf_exp_mono Hwfe);
                   apply aenv_tbinds_le_weaken_cons)).
  -
    inversion Hwfe as [ | | | | | L0 Θ0 A0 e0 Hwfa Hbody | ]; subst.
    apply ad_sd_typing__abs_anno_check_base
      with (L := L `union` L0 `union` dom Γ) (A := A);
      [ exact Hwfa
      | apply a_tyequiv__refl; eapply d_wf_ptyp_lc; eassumption
      | assumption | ].
    intros x Hx.
    exact (H2 x ltac:(clear - Hx; solve_notin_auto)
             ltac:(apply d_wf_denv__typ;
                     [ exact Hwf | clear - Hx; solve_notin_auto | assumption ])
             ltac:(apply (a_wf_exp_mono
                            (Hbody x ltac:(clear - Hx; solve_notin_auto)));
                   apply aenv_tbinds_le_weaken_cons)).
  -
    inversion Hwfe as [ | | | Θ0 e0 Hwfe0 | | | ]; subst.
    apply ad_sd_typing__freeze with (B := A);
      [ apply IHd_sd_typing; assumption
      | apply a_tyequiv__refl; apply lc_ptyp_of_lc_btyp_syn;
        eapply d_sd_typing_target_lc; eassumption ].
  -
    inversion Hwfe as [ | | | | | | Θ0 e10 e20 Hwf1 Hwf2 ]; subst.
    apply ad_sd_typing__app with (P := P) (A2 := btyp_to_ptyp B1) (B1 := B1);
      [ exact (d_pat_to_ad mode_tc Γ e2 (pskl_to_bskl_syn P) H)
      | eapply d_refine_syn_to_ad; eassumption
      | apply IHd_sd_typing1; assumption
      | apply a_tyequiv__refl; apply lc_ptyp_btyp_to_ptyp;

        match goal with
        | Hf : {{ _ ⊢ˢᵈ[ mode_fn _ ] _ ⦂ (btyp_arrow _ _) }}d |- _ =>
            let Ha := fresh "Ha" in
            assert (Ha : lc_btyp (btyp_arrow B1 B2))
              by (eapply d_sd_typing_target_lc; eassumption);
            inversion Ha; subst; assumption
        end
      | apply IHd_sd_typing2; assumption ].
Qed.
