(** Frost — skeleton/wf lemmas needed by the syntax-directed equivalence.
    RESTART NOTE: this file is the dependency closure of the lemmas that
    prop_syntax_directed.v uses, extracted from the pre-restart development
    (kept in full as prop_skeleton.v.pre-restart-legacy); the skeleton-safety
    machinery is redone later following the paper.  *)

(** Frost — declarative skeleton metatheory for the split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Set Implicit Arguments.

(** * Splitting / inversion lemmas for refinement.

    Only the coloured refinement relation [d_refine_syn] remains; the
    former uncoloured [d_refine] split lemmas were removed with it. *)


(* No [tophole] split lemma: a universal ghost [⫯] now refines by three
   rules (remove / fill-with-∀α / keep), so the output is not uniquely a
   [bskl_tophole].  Invert [d_refine_syn] directly where needed. *)

(** NB the headline lemma "Refinement preserves well-formedness" (the old D4)
    was DELETED upstream (declarative.tex 0dd3488): with the single-[Δ]
    refinement, well-formedness of both sides is a SEPARATE precondition of the
    judgement, not a derived property. *)

(** A well-scoped type's skeleton is a well-formed [pskl].  ([ptyp_to_pskl]
    images are ghost-free, so a scope-coverage premise lets the [∀] case
    route the bound var into [Ψ].) *)
Lemma d_wf_ptyp_ftvar : forall Γ A,
    d_wf_ptyp Γ A ->
    forall α, α `in` ftvar_in_ptyp A -> binds α dbind_tvar Γ.
Proof.
  intros Γ A H. induction H; intros β Hβ; simpl in Hβ.
  - fsetdec.
  - apply singleton_1 in Hβ. subst. assumption.
  - apply union_1 in Hβ. destruct Hβ as [Hβ | Hβ]; auto.
  - pick fresh α for (L `union` ftvar_in_ptyp A `union` dom Γ `union` singleton β).
    assert (HYo : β `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A (ptyp_var_f α))).
    { eapply ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower. eassumption. }
    specialize (H0 α ltac:(auto) β HYo).
    analyze_binds H0.
Qed.

(** Hence a well-formed type's skeleton is a well-formed [pskl] (any scope). *)
Lemma d_wf_pskl_strengthen : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P ->
    forall Γ1 α Γ2, Γ = Γ1 ++ (α ~ dbind_tvar) ++ Γ2 ->
    α `notin` ftvar_in_pskl P ->
    (Γ1 ++ Γ2) ⨟ Ψ ⊢ₚₛ P.
Proof.
  intros Ψ Γ P H. induction H; intros Γ1 α0 Γ2 Heq Hα; subst.
  - apply d_wf_pskl__unit.
  - simpl in Hα. apply d_wf_pskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
    analyze_binds Hb; try (exfalso; fsetdec); auto.
  - simpl in Hα. apply d_wf_pskl__arrow; [ eapply IHd_wf_pskl1 | eapply IHd_wf_pskl2 ]; eauto.
  - simpl in Hα. apply d_wf_pskl__all with (L := L `union` {{α0}}).
    intros β Hβ. eapply (H0 β ltac:(auto) Γ1 α0 Γ2); [ reflexivity | ].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
    simpl in Hup. fsetdec.
  - apply d_wf_pskl__hole.
  - simpl in Hα. apply d_wf_pskl__tophole; [ assumption | eapply IHd_wf_pskl; eauto ].
Qed.

Lemma ftvar_pskl_to_bskl_syn : forall P,
    ftvar_in_bskl (pskl_to_bskl_syn P) = ftvar_in_pskl P.
Proof.
  induction P; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
Qed.

(** [d_pat_consis] strengthening: every tvar LOOKUP goes through the RHS skeleton
    [Q] ([__var] matches [R'=Q'=var α']; [__hole]'s fill lives in [Q = inh P]), so
    conditioning on [α ∉ ftvar Q] suffices.  Forall cases grow [Γ]; recurse with
    [ftvar_in_bskl_open_bskl_wrt_bskl_upper]. *)
Lemma d_refine_syn_strengthen : forall Γ Δi Q Q',
    Γ ⨟ Δi ⊢ᵣ Q ⊳ Q' ->
    forall Γ1 α Γ2, Γ = Γ1 ++ (α ~ dbind_tvar) ++ Γ2 ->
    α `notin` ftvar_in_bskl Q' ->
    (Γ1 ++ Γ2) ⨟ Δi ⊢ᵣ Q ⊳ Q'.
Proof.
  intros Γ Δi Q Q' H. induction H; intros Γ1 α0 Γ2 Heq Hα; subst.
  - apply d_refine_syn__unit.
  - simpl in Hα. apply d_refine_syn__var. destruct H as [HI | Hb];
      [ left; assumption | right ].
    analyze_binds Hb; try (exfalso; fsetdec); auto.
  - simpl in Hα. apply d_refine_syn__arrow;
      [ eapply IHd_refine_syn1 | eapply IHd_refine_syn2 ]; eauto.
  - simpl in Hα. apply d_refine_syn__all with (L := L `union` {{α0}}).
    intros α2 Hα2. eapply (H0 α2 ltac:(auto) Γ1 α0 Γ2); [ reflexivity | ].
    (* [P] is the rule's OWN target binder (d_refine_syn__all /
       __tophole_fill, decl/def_extra.v), auto-bound by [induction H] —
       not this lemma's Q'. *)
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f α2)) as Hup.
    simpl in Hup. fsetdec.
  - apply d_refine_syn__hole. eapply d_wf_pskl_strengthen; eauto.
    rewrite <- ftvar_pskl_to_bskl_syn. assumption.
  - apply d_refine_syn__tophole_remove. eapply IHd_refine_syn; eauto.
  - apply d_refine_syn__tophole_fill with (L := L `union` {{α0}}).
    intros α2 Hα2. eapply (H0 α2 ltac:(auto) ((α2 ~ dbind_tvar) ++ Γ1) α0 Γ2);
      [ simpl_env; reflexivity | ].
    (* [P] is the rule's OWN target binder (d_refine_syn__all /
       __tophole_fill, decl/def_extra.v), auto-bound by [induction H] —
       not this lemma's Q'. *)
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f α2)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in Hα. apply d_refine_syn__tophole_keep; [ assumption | eapply IHd_refine_syn; eauto ].
Qed.

(** The LHS of a consistency / subtyping judgment has no free tvars beyond the
    RHS: every concrete tvar in [R] is matched (via [__var]) to the same tvar in
    [Q]; ghosts/holes in [R] are tvar-free.  Hence [α ∉ ftvar Q ⇒ α ∉ ftvar R],
    which is what makes [d_pat_sub]'s [forall_l] recursion strengthen. *)
Lemma guarded_pskl_subst_unit : forall P α,
    guarded_pskl P -> guarded_pskl (subst_pskl_in_pskl pskl_unit α P).
Proof.
  intros P α H. induction H; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - apply guarded_pskl__arrow; apply subst_pskl_in_pskl_lc_pskl; (assumption || apply lc_pskl_unit).
Qed.

Lemma guarded_uskl_subst_unit : forall R α,
    guarded_uskl R -> guarded_uskl (subst_bskl_in_uskl uskl_unit α R).
Proof.
  intros R α H. induction H; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - apply guarded_uskl__arrow; apply subst_bskl_in_uskl_lc_uskl; (assumption || apply lc_uskl_unit).
Qed.

Lemma d_wf_pskl_subst_unit : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P ->
    forall Γ1 α Γ2, Γ = Γ1 ++ (α ~ dbind_tvar) ++ Γ2 ->
    (Γ1 ++ Γ2) ⨟ Ψ ⊢ₚₛ (subst_pskl_in_pskl pskl_unit α P).
Proof.
  intros Ψ Γ P H. induction H; intros Γ1 α0 Γ2 Heq; subst.
  - apply d_wf_pskl__unit.
  - simpl. destruct_if.
    + apply d_wf_pskl__unit.
    + apply d_wf_pskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
      analyze_binds Hb; auto.
  - simpl. apply d_wf_pskl__arrow; [ eapply IHd_wf_pskl1 | eapply IHd_wf_pskl2 ]; eauto.
  - simpl. apply d_wf_pskl__all with (L := L `union` {{α0}}).
    intros β Hβ. rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      try (apply lc_pskl_unit); try fsetdec.
    eapply (H0 β ltac:(auto) Γ1 α0 Γ2); reflexivity.
  - apply d_wf_pskl__hole.
  - simpl. apply d_wf_pskl__tophole;
      [ apply guarded_pskl_subst_unit; assumption | eapply IHd_wf_pskl; eauto ].
Qed.

Lemma d_wf_uskl_subst_unit : forall Ψ Γ R,
    Γ ⨟ Ψ ⊢ᵤₛ R ->
    forall Γ1 α Γ2, Γ = Γ1 ++ (α ~ dbind_tvar) ++ Γ2 ->
    (Γ1 ++ Γ2) ⨟ Ψ ⊢ᵤₛ (subst_bskl_in_uskl uskl_unit α R).
Proof.
  intros Ψ Γ R H. induction H; intros Γ1 α0 Γ2 Heq; subst.
  - apply d_wf_uskl__unit.
  - simpl. destruct_if.
    + apply d_wf_uskl__unit.
    + apply d_wf_uskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
      analyze_binds Hb; auto.
  - simpl. apply d_wf_uskl__arrow; [ eapply IHd_wf_uskl1 | eapply IHd_wf_uskl2 ]; eauto.
  - simpl. apply d_wf_uskl__all_syn with (L := L `union` {{α0}}).
    intros β Hβ. rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      try (apply lc_uskl_unit); try fsetdec.
    eapply (H0 β ltac:(auto) Γ1 α0 Γ2); reflexivity.
  - simpl. apply d_wf_uskl__all_etag with (L := L `union` {{α0}}).
    intros β Hβ. rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      try (apply lc_uskl_unit); try fsetdec.
    eapply (H0 β ltac:(auto) Γ1 α0 Γ2); reflexivity.
  - apply d_wf_uskl__hole.
  - simpl. apply d_wf_uskl__tophole;
      [ apply guarded_uskl_subst_unit; assumption | eapply IHd_wf_uskl; eauto ].
  - apply d_wf_uskl__holeg.
  - simpl. apply d_wf_uskl__topholeg;
      [ apply guarded_uskl_subst_unit; assumption | eapply IHd_wf_uskl; eauto ].
Qed.

(** [pskl_to_bskl_inh] commutes with the tvar→unit substitution. *)
Lemma pskl_to_bskl_inh_subst_unit : forall P α',
    subst_bskl_in_bskl bskl_unit α' (pskl_to_bskl_inh P)
    = pskl_to_bskl_inh (subst_pskl_in_pskl pskl_unit α' P).
Proof.
  induction P; intros α'; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
  - destruct_if; reflexivity.
Qed.

Lemma is_sskl_subst_unit : forall Q α,
    is_sskl Q -> is_sskl (subst_bskl_in_bskl bskl_unit α Q).
Proof.
  intros Q α H. induction H; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - auto with frost.
  - apply is_sskl__all with (L := L `union` {{α}}). intros β Hβ.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      try (apply lc_bskl_unit); try fsetdec. auto.
  - auto with frost.
  - auto with frost.
Qed.

(** [mod_comp_sk] is preserved under [unit]-substitution: [unit] is [is_sskl]
    and substitution respects the arrow spine. *)
Lemma mod_comp_sk_subst_unit : forall Q m α,
    mod_comp_sk Q m -> mod_comp_sk (subst_bskl_in_bskl bskl_unit α Q) m.
Proof.
  intros Q m α H. induction H; simpl.
  - auto using is_sskl_subst_unit with frost.
  - auto using is_sskl_subst_unit with frost.
  - auto with frost.
Qed.

Lemma is_tskl_subst_unit : forall R α,
    is_tskl R -> is_tskl (subst_bskl_in_uskl uskl_unit α R).
Proof.
  intros R α H. induction H; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - auto with frost.
  - apply is_tskl__all_etag with (L := L `union` {{α}}). intros β Hβ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      try (apply lc_uskl_unit); try fsetdec. auto.
  - auto with frost.
  - auto with frost.
Qed.

Lemma guarded_bskl_subst_unit : forall Q α,
    guarded_bskl Q -> guarded_bskl (subst_bskl_in_bskl bskl_unit α Q).
Proof.
  intros Q α H. induction H; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - apply guarded_bskl__arrow; apply subst_bskl_in_bskl_lc_bskl; (assumption || apply lc_bskl_unit).
Qed.

Lemma d_tags_skl_subst_unit : forall Δ R α,
    d_tags_skl Δ R -> d_tags_skl Δ (subst_bskl_in_uskl uskl_unit α R).
Proof.
  intros Δ R α H. induction H; simpl.
  - apply d_tags_skl__unit; (assumption || fsetdec).
  - destruct_if;
      [ apply d_tags_skl__unit; (assumption || fsetdec)
      | apply d_tags_skl__var; (assumption || fsetdec) ].
  - apply d_tags_skl__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
  - apply d_tags_skl__all_etag with (L := L `union` {{α}}) (Ψ0 := Ψ0); [ | assumption | assumption ]. intros β Hβ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      try (apply lc_uskl_unit); try fsetdec. auto.
  - apply d_tags_skl__holeg; (assumption || fsetdec).
  - apply d_tags_skl__topholeg; assumption.
Qed.

Lemma d_pat_consis_subst_unit : forall Δ Γ R Q,
    Δ ⨟ Γ ⊢ₛ R ∼ Q ->
    forall Γ1 α Γ2, Γ = Γ1 ++ (α ~ dbind_tvar) ++ Γ2 ->
    Δ ⨟ (Γ1 ++ Γ2) ⊢ₛ
      (subst_bskl_in_uskl uskl_unit α R) ∼ (subst_bskl_in_bskl bskl_unit α Q).
Proof.
  intros Δ Γ R Q H. induction H; intros Γ1 α0 Γ2 Heq; subst.
  - apply d_pat_consis__unit; (assumption || fsetdec).
  - simpl. destruct_if.
    + apply d_pat_consis__unit; (assumption || fsetdec).
    + apply d_pat_consis__var; [ (assumption || fsetdec) | ]; match goal with Hb : binds _ _ _ |- _ => analyze_binds Hb end; auto.
  - simpl. eapply d_pat_consis__arrow; [ eapply IHd_pat_consis1 | eapply IHd_pat_consis2 | (eassumption || fsetdec) ]; eauto.
  - simpl. apply d_pat_consis__forall_inh_tagged with (L := L `union` {{α0}}) (Ψ0 := Ψ0). 2: assumption.
    intros α2 Hα2. rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_unit); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_unit); try fsetdec.
    eapply (H0 α2 ltac:(auto) ((α2 ~ dbind_tvar) ++ Γ1) α0 Γ2); simpl_env; reflexivity.
  - simpl. apply d_pat_consis__forall_inh_untagged with (L := L `union` {{α0}}).
    intros α2 Hα2. rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_unit); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_unit); try fsetdec.
    eapply (H0 α2 ltac:(auto) ((α2 ~ dbind_tvar) ++ Γ1) α0 Γ2); simpl_env; reflexivity.
  - simpl. apply d_pat_consis__forall_syn_tagged with (L := L `union` {{α0}}).
    intros α2 Hα2. rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_unit); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_unit); try fsetdec.
    eapply (H0 α2 ltac:(auto) ((α2 ~ dbind_tvar) ++ Γ1) α0 Γ2); simpl_env; reflexivity.
  - simpl. apply d_pat_consis__forall_syn with (L := L `union` {{α0}}).
    intros α2 Hα2. rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_unit); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_unit); try fsetdec.
    eapply (H0 α2 ltac:(auto) ((α2 ~ dbind_tvar) ++ Γ1) α0 Γ2); simpl_env; reflexivity.
  - apply d_pat_consis__ghostg; (assumption || fsetdec).
  - simpl. apply d_pat_consis__topholeg. eapply IHd_pat_consis; eauto.
  - simpl. rewrite pskl_to_bskl_inh_subst_unit. apply d_pat_consis__hole; [ (assumption || fsetdec) | ]; eapply d_wf_pskl_subst_unit; eauto.
  - simpl. apply d_pat_consis__tophole. eapply IHd_pat_consis; eauto.
  - simpl. apply d_pat_consis__tophole_inh with (L := L `union` {{α0}}).
    intros α2 Hα2. rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_unit); try fsetdec.
    change (uskl_tophole (subst_bskl_in_uskl uskl_unit α0 R))
      with (subst_bskl_in_uskl uskl_unit α0 (uskl_tophole R)).
    eapply (H0 α2 ltac:(auto) ((α2 ~ dbind_tvar) ++ Γ1) α0 Γ2); simpl_env; reflexivity.
  - simpl. apply d_pat_consis__tophole_drop. eapply IHd_pat_consis; eauto.
Qed.

Lemma d_pat_sub_subst_unit : forall Δ Γ m R Q,
    Δ ⨟ Γ ⊢ₛ[ m ] R ⩽ Q ->
    forall Γ1 α Γ2, Γ = Γ1 ++ (α ~ dbind_tvar) ++ Γ2 ->
    Δ ⨟ (Γ1 ++ Γ2) ⊢ₛ[ m ]
      (subst_bskl_in_uskl uskl_unit α R) ⩽ (subst_bskl_in_bskl bskl_unit α Q).
Proof.
  intros Δ Γ m R Q H. induction H; intros Γ1 α0 Γ2 Heq; subst.
  - apply d_pat_sub__infer; [ (assumption || fsetdec) | eapply d_pat_consis_subst_unit; eauto | apply is_sskl_subst_unit; assumption ].
  - simpl. apply d_pat_sub__univ_ghost_r;
      [ (assumption || fsetdec)
      | apply guarded_uskl_subst_unit; assumption
      | apply guarded_bskl_subst_unit; assumption
      | apply is_sskl_subst_unit; assumption
      | eapply d_pat_consis_subst_unit; eauto ].
  - simpl. eapply d_pat_sub__arg;
      [ eapply d_pat_consis_subst_unit; eauto | eapply IHd_pat_sub; eauto | (eassumption || fsetdec) ].
  - simpl. eapply d_pat_sub__forall_l_tagged with
      (psi := subst_bskl_in_uskl uskl_unit α0 psi);
      [ assumption | eassumption | apply d_tags_skl_subst_unit; assumption
      | eapply d_wf_uskl_subst_unit; eauto | apply is_tskl_subst_unit; assumption | ].
    rewrite <- subst_bskl_in_uskl_open_uskl_wrt_uskl; try (apply lc_uskl_unit).
    eapply IHd_pat_sub; eauto.
  - simpl. eapply d_pat_sub__forall_l_untagged with
      (psi := subst_bskl_in_uskl uskl_unit α0 psi);
      [ assumption | eassumption | apply d_tags_skl_subst_unit; assumption
      | eapply d_wf_uskl_subst_unit; eauto | apply is_tskl_subst_unit; assumption | ].
    rewrite <- subst_bskl_in_uskl_open_uskl_wrt_uskl; try (apply lc_uskl_unit).
    eapply IHd_pat_sub; eauto.
  - simpl. rewrite pskl_to_bskl_inh_subst_unit. apply d_pat_sub__ghost;
      [ (assumption || fsetdec)
      | eapply d_wf_pskl_subst_unit; eauto
      | rewrite <- pskl_to_bskl_inh_subst_unit; apply mod_comp_sk_subst_unit; assumption ].
  - simpl. apply d_pat_sub__univ_ghost_l; [ assumption | eapply IHd_pat_sub; eauto ].
  - apply d_pat_sub__ghostg; (assumption || fsetdec).
  - simpl. apply d_pat_sub__univ_ghost_lg; [ assumption | eapply IHd_pat_sub; eauto ].
Qed.

(** Consistency reflexivity: a well-scoped synthesised skeleton is consistent with
    its own [uskl]-erasure.  Foundation of the [ti] sub case of the CONSTRUCTION
    path for [d_pat_total] (build [d_pat__sub] via [d_pat_sub__infer]).  Var case
    needs the skeleton well-scoped; holes go via [__hole] (bskl_hole = inh □). *)
Lemma d_wf_ptyp_of_lc_ftvar : forall A Γ,
    lc_ptyp A ->
    (forall α, α `in` ftvar_in_ptyp A -> binds α dbind_tvar Γ) ->
    d_wf_ptyp Γ A.
Proof.
  intros A Γ Hlc. revert Γ. induction Hlc; intros Γ Hcov.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. apply Hcov. simpl. fsetdec.
  - apply d_wf_ptyp__arrow; [ apply IHHlc1 | apply IHHlc2 ];
      intros β Hβ; apply Hcov; simpl; fsetdec.
  - inst_cofinites_for d_wf_ptyp__all. intros α Hα. apply H0. intros β Hβ.
    apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in Hβ. simpl in Hβ.
    apply union_1 in Hβ. destruct Hβ as [Hβ | Hβ].
    + apply singleton_1 in Hβ. subst. simpl_env. auto.
    + apply binds_app_iff. right. apply Hcov. assumption.
Qed.

Lemma d_wf_ptyp_of_btyp_inh : forall A Γ,
    d_wf_btyp Γ (ptyp_to_btyp_inh A) -> d_wf_ptyp Γ A.
Proof.
  intros A Γ H. apply d_wf_ptyp_of_lc_ftvar.
  - apply lc_ptyp_of_lc_btyp_inh. eapply d_wf_btyp_lc; eassumption.
  - intros α Hα. eapply d_wf_btyp_ftvar; [ eassumption | ].
    rewrite ftvar_ptyp_to_btyp_inh. assumption.
Qed.

(** * Skeleton determinism for synthesis (prerequisites for [d_pat_total]).
    [d_consis] preserves the underlying [pskl]; a base term's [mode_ti] type is
    therefore skeleton-determined (sub-[ti] only re-types to a consistent
    variant, same skeleton). *)


Lemma d_wf_ptyp_lc_loc : forall Γ A, d_wf_ptyp Γ A -> lc_ptyp A.
Proof.
  intros Γ A H. induction H.
  - constructor.
  - constructor.
  - constructor; assumption.
  - pick fresh α. apply (lc_ptyp_all_exists α). apply H0. auto.
Qed.

(** A well-formed type's free tvars are all bound in the context. *)
Lemma is_value_subst_var : forall e x y,
    is_value e -> is_value (subst_exp_in_exp (exp_var_f y) x e).
Proof.
  intros e x y H. induction H; simpl;
    [ apply is_value__unit
    | destruct_if;
      apply is_value__var
    | apply is_value__abs | apply is_value__abs_anno
    | apply is_value__anno; assumption ].
Qed.

Lemma d_pat_subst_var : forall m Γ e Q,
    Γ ⊢[ m ] e ⇨ Q ->
    forall x y d, uniq Γ -> binds x d Γ -> binds y d Γ ->
    Γ ⊢[ m ] (subst_exp_in_exp (exp_var_f y) x e) ⇨ Q.
Proof.
  intros m Γ e Q H. induction H; intros x0 y0 d0 Huniq Hbx Hby; simpl.
  - apply d_pat__unit. exact H.
  - (* var *) destruct_if as [Heq | Hne].
    + subst x. assert (d = d0) by (eapply binds_unique; eauto). subst d.
      apply d_pat__var with (d := d0) (P := P); [ exact Hby | exact H0 | exact H1 ].
    + apply d_pat__var with (d := d) (P := P); [ exact H | exact H0 | exact H1 ].
  - (* anno *) apply d_pat__anno; [ exact H | exact H0 ].
  - (* freeze *) apply d_pat__freeze. eapply IHd_pat; eauto.
  - (* abs *) apply d_pat__abs with
      (L := L `union` {{x0}} `union` {{y0}} `union` dom Γ) (P := P);
      [ assumption | assumption | assumption | ].
    intros w Hw. rewrite subst_exp_in_exp_open_exp_wrt_exp_var; try fsetdec; try apply lc_exp_var_f.
    eapply H3; [ fsetdec | apply uniq_push; [ exact Huniq | fsetdec ]
               | apply binds_app_3; exact Hbx | apply binds_app_3; exact Hby ].
  - (* abs_anno *) apply d_pat__abs_anno with
      (L := L `union` {{x0}} `union` {{y0}} `union` dom Γ) (A := A) (B := B);
      [ assumption | assumption | assumption | assumption | ].
    intros w Hw. rewrite subst_exp_in_exp_open_exp_wrt_exp_var; try fsetdec; try apply lc_exp_var_f.
    eapply H4; [ fsetdec | apply uniq_push; [ exact Huniq | fsetdec ]
               | apply binds_app_3; exact Hbx | apply binds_app_3; exact Hby ].
  - (* app *) eapply d_pat__app;
      [ eapply IHd_pat1; eauto | exact H0 | eapply IHd_pat2; eauto ].
  - (* abs_check *) apply d_pat__abs_check with
      (L := L `union` {{x0}} `union` {{y0}} `union` dom Γ).
    intros w Hw. rewrite subst_exp_in_exp_open_exp_wrt_exp_var; try fsetdec; try apply lc_exp_var_f.
    eapply H0; [ fsetdec | apply uniq_push; [ exact Huniq | fsetdec ]
               | apply binds_app_3; exact Hbx | apply binds_app_3; exact Hby ].
  - (* abs_anno_check *) apply d_pat__abs_anno_check with
      (L := L `union` {{x0}} `union` {{y0}} `union` dom Γ) (A := A);
      [ assumption | ].
    intros w Hw. rewrite subst_exp_in_exp_open_exp_wrt_exp_var; try fsetdec; try apply lc_exp_var_f.
    eapply H1; [ fsetdec | apply uniq_push; [ exact Huniq | fsetdec ]
               | apply binds_app_3; exact Hbx | apply binds_app_3; exact Hby ].
Qed.

(** GENERAL variable substitution for typing: substituting [y] for [x] in ANY
    expression preserves [⦂] (same context, [x] and [y] same [typ]-binding). *)
Lemma d_typing_subst_var : forall m Γ e B,
    Γ ⊢[ m ] e ⦂ B ->
    forall x y A', uniq Γ -> binds x (dbind_typ A') Γ -> binds y (dbind_typ A') Γ ->
    Γ ⊢[ m ] (subst_exp_in_exp (exp_var_f y) x e) ⦂ B.
Proof.
  intros m Γ e B H. induction H; intros x0 y0 A' Huniq Hbx Hby; simpl.
  - apply d_typing__unit.
  - (* var *) destruct_if as [Heq | Hne].
    + subst x. assert (dbind_typ A = dbind_typ A') by (eapply binds_unique; eauto).
      match goal with He : dbind_typ _ = dbind_typ _ |- _ => inversion He; subst end.
      apply d_typing__var; exact Hby.
    + apply d_typing__var; exact H.
  - (* anno *) apply d_typing__anno. eapply IHd_typing; eauto.
  - (* sub *) eapply d_typing__sub;
      [ eapply IHd_typing; eauto | exact H0 ].
  - (* freeze *) apply d_typing__freeze. eapply IHd_typing; eauto.
  - (* forall *) apply d_typing__forall with
      (L := L `union` {{x0}} `union` {{y0}} `union` dom Γ);
      [ apply is_value_subst_var; exact H | ].
    intros α Hα. eapply H1; [ fsetdec | apply uniq_push; [ exact Huniq | fsetdec ]
               | apply binds_app_3; exact Hbx | apply binds_app_3; exact Hby ].
  - (* abs (general) *) apply d_typing__abs with
      (L := L `union` {{x0}} `union` {{y0}} `union` dom Γ) (A := A);
      [ assumption | exact H0 | ].
    intros w Hw. rewrite subst_exp_in_exp_open_exp_wrt_exp_var; try fsetdec; try apply lc_exp_var_f.
    eapply H2; [ fsetdec | apply uniq_push; [ exact Huniq | fsetdec ]
               | apply binds_app_3; exact Hbx | apply binds_app_3; exact Hby ].
  - (* abs_anno (general) *) apply d_typing__abs_anno with
      (L := L `union` {{x0}} `union` {{y0}} `union` dom Γ) (A := A) (B1 := B1);
      [ assumption | assumption | exact H1 | ].
    intros w Hw. rewrite subst_exp_in_exp_open_exp_wrt_exp_var; try fsetdec; try apply lc_exp_var_f.
    eapply H3; [ fsetdec | apply uniq_push; [ exact Huniq | fsetdec ]
               | apply binds_app_3; exact Hbx | apply binds_app_3; exact Hby ].
  - (* app *) eapply d_typing__app;
      [ eapply d_pat_subst_var; [ exact H | exact Huniq | exact Hbx | exact Hby ]
      | exact H0 | eapply IHd_typing1; eauto | eapply IHd_typing2; eauto ].
Qed.

(** Tvar STRENGTHENING cascade: drop an UNUSED tvar [α] (one that does not occur
    free in the skeleton/type) from the context.  This is what the [forall] case
    of [d_pat_total] needs: the body is inferred over [(α:tvar)::Γ] for a fresh
    [α ∉ ftvar(e)], so the inferred skeleton is [α]-free and [α] strengthens away.
    Var cases: [α ∉ ftvar] forces the looked-up tvar [≠ α]; cofinite cases use
    [ftvar_in_*_open_*_upper]. *)
