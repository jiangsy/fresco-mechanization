(** Frost — totality + safety of skeleton inference ([d_pat_total],
    [d_pat_safety]).  Split out of [prop_skeleton] so it can use the
    subtyping-transitivity machinery in [prop_general_subsumption]. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_basic.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_weakening.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.decl.prop_general_subsumption.
Require Import src.frost.decl.prop_stability.

Set Implicit Arguments.

(** * Context precision (declarative analog of the paper's [⪯ctx]).
    [Γ'] refines [Γ] if it is [Γ] with some term-bindings [x:typ A] replaced by
    the most-general skeleton binding [x:□].  This is what an [abs] in CHECK mode
    does to the body's context, and is the keystone for the abstraction cases. *)
Inductive dbind_refines : dbind -> dbind -> Prop :=
| dbr_refl : forall d, dbind_refines d d
| dbr_typ_hole : forall A, dbind_refines (dbind_skl pskl_hole) (dbind_typ A).

Inductive ctx_refines : list (atom * dbind) -> list (atom * dbind) -> Prop :=
| ctxr_nil : ctx_refines nil nil
| ctxr_cons : forall x d' d Γ' Γ,
    dbind_refines d' d -> ctx_refines Γ' Γ ->
    ctx_refines ((x ~ d') ++ Γ') ((x ~ d) ++ Γ).

Lemma ctx_refines_refl : forall Γ, ctx_refines Γ Γ.
Proof.
  induction Γ as [ | [x d] Γ IH ]; [ apply ctxr_nil | ].
  apply ctxr_cons; [ apply dbr_refl | exact IH ].
Qed.

(** [ctx_refines] preserves [dom] and tvar bindings. *)
Lemma ctx_refines_dom : forall Γ' Γ, ctx_refines Γ' Γ -> dom Γ' [=] dom Γ.
Proof.
  intros Γ' Γ H. induction H; simpl; [ fsetdec | fsetdec ].
Qed.

Lemma ctx_refines_binds_tvar : forall Γ' Γ X,
    ctx_refines Γ' Γ -> binds X dbind_tvar Γ -> binds X dbind_tvar Γ'.
Proof.
  intros Γ' Γ X H. induction H; intros Hb; [ assumption | ].
  analyze_binds Hb; try (inversion H; subst); auto.
Qed.

(** Well-formedness is preserved under context refinement (tvars are unchanged). *)
Lemma d_wf_ptyp_ctx_refines : forall Γ A,
    d_wf_ptyp Γ A -> forall Γ', ctx_refines Γ' Γ -> d_wf_ptyp Γ' A.
Proof.
  intros Γ A H. induction H; intros Γ' Hcr.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. eapply ctx_refines_binds_tvar; eauto.
  - apply d_wf_ptyp__arrow; eauto.
  - apply d_wf_ptyp__all with (L := L). intros X HX.
    eapply H0; [ exact HX | apply ctxr_cons; [ apply dbr_refl | exact Hcr ] ].
Qed.

(** A binding in [Γ] has a refining binding in any [Γ' ⪯ Γ]. *)
Lemma ctx_refines_binds : forall Γ' Γ x d,
    ctx_refines Γ' Γ -> binds x d Γ ->
    exists d', binds x d' Γ' /\ dbind_refines d' d.
Proof.
  intros Γ' Γ x d H. induction H; intros Hb; [ inversion Hb | ].
  analyze_binds Hb.
  - exists d'. split; [ apply binds_app_iff; left; apply binds_one_iff; auto | assumption ].
  - destruct (IHctx_refines BindsTac) as [d'' [Hb'' Hr'']].
    exists d''. split; [ apply binds_app_iff; right; assumption | assumption ].
Qed.

(** A base term's [mode_ti] type is synthesised ([is_styp]). *)
Lemma d_typing_ti_base_is_styp : forall Γ e B,
    d_wf_denv Γ -> is_base_term e -> d_typing mode_ti Γ e B -> is_styp B.
Proof.
  intros Γ e B Hwf Hbase Hty. remember mode_ti as m eqn:Hm.
  induction Hty; subst; try discriminate; try solve [ inversion Hbase ].
  - apply is_styp__unit.
  - apply is_styp_ptyp_to_btyp_syn. eapply d_wf_ptyp_lc_loc.
    eapply d_wf_denv_binds_typ; eauto.
  - apply is_styp_ptyp_to_btyp_syn. eapply d_wf_ptyp_lc_loc.
    apply d_wf_ptyp_of_btyp_inh. eapply d_typing_wf_btyp; eauto.
  - match goal with Hs : empty ⨟ _ ⊢[ mode_ti ] _ ⊑ _ |- _ =>
      inversion Hs; subst;
      try (exfalso; match goal with Hne : ?mm <> ?mm |- _ =>
                      apply Hne; reflexivity end) end.
    assumption.
Qed.

(** Skeleton determines a synthesised type. *)
Lemma is_styp_skel_inj : forall B1, is_styp B1 ->
    forall C, is_styp C ->
    ptyp_to_pskl (btyp_to_ptyp B1) = ptyp_to_pskl (btyp_to_ptyp C) -> B1 = C.
Proof.
  intros B1 H1. induction H1; intros C HC Hsk; destruct HC; simpl in Hsk;
    try discriminate.
  - reflexivity.
  - inversion Hsk; subst; reflexivity.
  - inversion Hsk. f_equal; [ apply IHis_styp1 | apply IHis_styp2 ]; auto.
  - inversion Hsk. f_equal.
    pick fresh X for (L `union` L0 `union` ftvar_in_btyp B `union` ftvar_in_btyp B0).
    apply open_btyp_wrt_btyp_inj with (Xbt1 := X); [ fsetdec | fsetdec | ].
    eapply H0; [ fsetdec | apply H1; fsetdec | ].
    rewrite ! btyp_to_ptyp_open; cbn [btyp_to_ptyp];
      rewrite ! ptyp_to_pskl_open, H3; reflexivity.
Qed.

(** Principal subsumption: a base term's [mode_ti] type subtypes to every
    [mode_tc] type it checks against (sub case = [is_styp]-skeleton injectivity;
    forall case = [d_sub__forall_r]). *)
Lemma d_typing_base_principal_sub : forall Γ e Bp Bc,
    d_wf_denv Γ -> is_base_term e ->
    d_typing mode_ti Γ e Bp -> d_typing mode_tc Γ e Bc ->
    empty ⨟ Γ ⊢[ mode_tc ] (ptyp_to_utyp_syn Bp) ⊑ Bc.
Proof.
  intros Γ e Bp Bc Hwf Hbase Hti Htc. remember mode_tc as m eqn:Hm.
  revert Bp Hti. induction Htc; intros Bp Hti; subst; try discriminate;
    try solve [ inversion Hbase ].
  - (* sub *)
    assert (Bp = B1) by
      (apply is_styp_skel_inj;
        [ eapply d_typing_ti_base_is_styp; eauto
        | eapply d_typing_ti_base_is_styp; eauto
        | eapply d_typing_ti_skel_det;
          [ eapply d_wf_denv_uniq; eauto | exact Hbase | exact Hti | exact Htc ] ]).
    subst. exact H0.
  - (* forall *) apply d_sub__forall_r with (L := L `union` dom Γ).
    intros X HX. eapply H1;
      [ fsetdec
      | apply d_wf_denv__tvar; [ exact Hwf | fsetdec ]
      | exact Hbase
      | reflexivity
      | apply (d_typing_weakening nil (X ~ dbind_tvar) Γ); exact Hti ].
Qed.

(** ** Totality + safety of skeleton inference ([d_pat_total]).

    The joint invariant carried by the induction (the paper's
    "context-precision for skeleton inference", proofs.tex).  Per mode:
    - [ti]: the inferred skeleton's [pskl] equals the type's [pskl] (synthesis
      is skeleton-determined).
    - [tc]: SAFETY — for every checking type [A], [inh{Q}] fills some colouring
      of [A] (expression-based, the actual safety statement).
    - [fn m']: the inferred skeleton is an arrow whose DOMAIN is forced to
      [inh{skel arg}] (so [d_pat__app] can thread it), and whose codomain
      [Qc] is [safe_skel] for the codomain type — recursively. *)

Fixpoint safe_skel (Γ : list (atom * dbind)) (m : mode) (Q : bskl) (B : btyp)
  : Prop :=
  match m with
  | mode_ti => bskl_to_pskl Q = ptyp_to_pskl (btyp_to_ptyp B)
  | mode_tc =>
      exists B', bskl_to_pskl B' = ptyp_to_pskl (btyp_to_ptyp B)
                 /\ Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳ B'
  | mode_fn m' =>
      exists Barg B0 Qc,
        B = btyp_arrow Barg B0
        /\ Q = bskl_arrow (pskl_to_bskl_inh (ptyp_to_pskl (btyp_to_ptyp Barg))) Qc
        /\ safe_skel Γ m' Qc B0
  end.

Definition gpat (m : mode) (Γ : list (atom * dbind)) (e : exp) (B : btyp)
  : Prop :=
  match m with
  | mode_tc =>
      exists Q, Γ ⊢[ mode_tc ] e ⇨ Q
                /\ (forall A, Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) ->
                       exists B', bskl_to_pskl B' = ptyp_to_pskl A
                         /\ Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳ B')
  | mode_ti =>
      exists Q, Γ ⊢[ mode_ti ] e ⇨ Q
                /\ (forall A, Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_inh A) ->
                       exists B', bskl_to_pskl B' = ptyp_to_pskl A
                         /\ Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳ B')
  | mode_fn _ => exists Q, Γ ⊢[ m ] e ⇨ Q /\ safe_skel Γ m Q B
  end.

(** A type's own skeleton is [hole_safe] for it (concrete refinement-refl). *)
Lemma hole_safe_of_ptyp : forall A,
    lc_ptyp A -> forall L, hole_safe L (ptyp_to_pskl A) A.
Proof.
  intros A H. induction H; intros L; simpl.
  - apply hs_unit.
  - apply hs_var_f.
  - apply hs_arrow; [ apply IHlc_ptyp1 | apply IHlc_ptyp2 ].
  - apply hs_all with (Lc := empty). intros X _.
    rewrite <- ptyp_to_pskl_open. apply H0.
Qed.

(** Base-term [mode_ti] safety: the synthesised skeleton fills every [inh]-type
    the term ti-types to (those types are [is_styp], hence ∀-free here, so the
    concrete refinement [refine_colour_core] applies). *)
Lemma d_pat_base_ti_safe : forall Γ e B,
    d_wf_denv Γ -> is_base_term e -> d_typing mode_ti Γ e B -> gpat mode_ti Γ e B.
Proof.
  intros Γ e B Hwf Hbase Hty.
  destruct (d_pat_ti_base_safe Hwf Hbase Hty) as [Q [HQ [Hsskl [Hftv Hskel]]]].
  exists Q. split; [ exact HQ | ]. intros A HA.
  assert (Hwfa : d_wf_ptyp Γ A)
    by (apply d_wf_ptyp_of_btyp_inh; eapply d_typing_wf_btyp; eauto).
  assert (HQA : bskl_to_pskl Q = ptyp_to_pskl A).
  { rewrite Hskel.
    pose proof (d_typing_ti_skel_det (d_wf_denv_uniq Hwf) Hbase Hty HA) as Hdet.
    rewrite Hdet. rewrite btyp_to_ptyp_ptyp_to_btyp_inh. reflexivity. }
  exists (colour (pskl_to_bskl_inh (bskl_to_pskl Q)) A). split.
  - apply colour_erasure.
  - apply refine_colour_core.
    + eapply d_wf_ptyp_lc_loc; eauto.
    + rewrite HQA. apply hole_safe_of_ptyp. eapply d_wf_ptyp_lc_loc; eauto.
    + intros X HX. right. right. eapply d_wf_ptyp_ftvar; eauto.
Qed.

Lemma d_pat_total : forall m Γ e B,
    Γ ⊢[ m ] e ⦂ B -> d_wf_denv Γ -> gpat m Γ e B.
Proof.
  intros m Γ e B Hty. induction Hty; intros Hwf.
  - (* unit *) apply d_pat_base_ti_safe;
      [ exact Hwf | apply is_base_term__unit | apply d_typing__unit ].
  - (* var *) apply d_pat_base_ti_safe;
      [ exact Hwf | apply is_base_term__var | eapply d_typing__var; eauto ].
  - (* anno *) apply d_pat_base_ti_safe;
      [ exact Hwf | apply is_base_term__anno | apply d_typing__anno; eauto ].
  - (* sub *) destruct m.
    + (* ti *) apply d_pat_base_ti_safe;
        [ exact Hwf | exact H | eapply d_typing__sub; [ exact H | exact Hty | exact H0 ] ].
    + (* tc *) simpl.
      destruct (d_pat_ti_base_safe Hwf H Hty) as [Q1 [HQ1 [Hsskl1 [Hftv1 Hskel1]]]].
      destruct (d_pat_sub_safe_tc Γ (le_n (size_bskl Q1)) Hsskl1 Hftv1)
        as [Q2 [Hsub2 Hghost2]].
      exists Q2. split.
      * eapply d_pat__sub; [ exact H | exact HQ1 | exact Hsub2 ].
      * intros A HA.
        apply (ghost_of_fill (C := btyp_to_ptyp B1)).
        -- apply lc_ptyp_btyp_to_ptyp. eapply d_wf_btyp_lc.
           eapply d_typing_wf_btyp; eauto.
        -- rewrite <- Hskel1. exact Hghost2.
        -- apply d_wf_ptyp_of_btyp_inh. eapply d_typing_wf_btyp; eauto.
        -- exact (d_typing_base_principal_sub Hwf H Hty HA).
    + (* fn *) admit.
  - (* freeze *) destruct (IHHty Hwf) as [Q [HQ Hsafe]].
    exists Q. split.
    + apply d_pat__freeze. exact HQ.
    + intros A HA. inversion HA; subst;
        try (match goal with Hb : is_base_term (exp_freeze _) |- _ => inversion Hb end);
        try (match goal with Hv : is_value (exp_freeze _) |- _ => inversion Hv end);
        apply Hsafe; assumption.
  - (* forall *) admit.
  - (* abs *) admit.
  - (* abs_check *) admit.
  - (* abs_anno *) admit.
  - (* abs_anno_check *) admit.
  - (* app *) admit.
Admitted.

(** Paper "Safety of skeleton inference" (declarative.tex:1950): for a
    well-typed [M] there *exists* an inference [Γ ⊢ti M ⇨ Q] whose [Q] is
    *safe* — it fills *every* checking type [A].

    This is an **existential** over inference derivations, and it holds.
    The paper's WT note (declarative.tex:1956) that declarative inference
    "does not *always* give safe skeletons" is the **universal** statement
    — not every derivation is safe, because inference is non-deterministic
    ([tophole_remove]/[keep]/[fill] are distinct rules; [ForallL] may pick
    a ghost or a monotype) and some choices drop universal ghosts or guess
    monotypes.  Safety only asks for *one* good derivation, which always
    exists (the algorithmic inference is precisely a decision procedure
    that computes such a [Q], and it is sound w.r.t. this declarative
    relation).

    Note: the liberal-[d_pat__abs] gap (an over-specific, ghost-free
    argument skeleton) does NOT affect safety — being existential, safety
    just *picks* a well-behaved derivation (e.g. the unannotated-λ argument
    skeleton [□]), so over-specific inferences are simply not chosen.  In
    particular [freeze (λx.(x:unit))] is not a counterexample: [freeze] is
    not a value, so the term checks only at [unit→unit], which [□→unit]
    fills.

    PAINTING (per the current def — see statement below).  The LHS is
    *inherited* ([inh{P}]) and the target *bidirectional* ([bid{A}]).  This
    is what makes it work: concrete [∀]s in [P] become inh-[∀] (handled by
    [d_refine_syn__all]); ghosts fill via [hole] (any well-formed pskl) /
    [tophole] (universal ghost → syn-[∀] by [tophole_fill]).  Filling a
    ghost to an *inherited* [∀] stays (correctly) banned — the inh-painting
    is on [P], not the target.

    ENGINES (proved): [d_refine_syn_hole_fills] / [d_refine_syn_tophole_hole_fills]
    handle ghosts ([□] / [⫯.□] ⊳ any well-scoped type's syn-skeleton,
    polytypes included).

    REMAINING — the witness: a safe inferable [Q] per well-typed [e] whose
    [inh{Q}] refines every checking type.  Two viable strategies (the
    per-case refinement is discharged by the engines above either way):
    (a) a direct declarative induction on the typing that builds [Q]
        (threading [denv_coh] through λ; the existential IH may well suffice
        with the right invariant); or
    (b) algorithmically — the "looking" relation [a_pat_solution] /
        [a_pat_optimal] (algo/def_question.v:114) computes the skeleton, and
        [a_pat_solution] already *embeds* the declarative inference
        [⌊Θ1⌋ ⊢[M] e ⇨ pskl_to_bskl_syn P1], its [≼]-optimality giving
        fills-every-type; this reduces safety to the Phase-3 algorithmic
        results.
    Still [Admitted] (true) pending the witness. *)
(** Updated to the current paper "Safe Skeleton" definition
    (declarative.tex:1925): [P] is safe for [M] under [Γ] if for every [A]
    with [Γ ⊢tc M ⦂ inh{A}], [inh{P} ⊳ bid{A}] — the inferred skeleton
    *painted inherited* fills to *some bidirectional colouring* of [A].
    Encoding: [inh{P}] = [pskl_to_bskl_inh (bskl_to_pskl Q)] (erase the
    inferred [Q]'s colours, repaint inherited); [bid{A}] = an existential
    [B] with [bskl_to_pskl B = ptyp_to_pskl A] (the refinement output,
    unique by "Refinement determines colours").  The inh-painted LHS is
    what makes this work — concrete [∀]s in [P] become inh-[∀] (handled by
    [d_refine_syn__all]); ghosts fill via [hole]/[tophole]. *)
Theorem d_pat_safety : forall Γ e B0,
    Γ ⊢[ mode_tc ] e ⦂ B0 ->
    d_wf_denv Γ ->
    exists Q, Γ ⊢[ mode_tc ] e ⇨ Q /\
              (forall A, Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) ->
                 exists B, bskl_to_pskl B = ptyp_to_pskl A /\
                   Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳ B).
Proof.
  (* RE-PLAN v3 (the algorithmic-"look" construction — declarative.tex:1957-1981
     Wenhao note: the safe witness is the skeleton the algorithm computes, where
     "the inferred skeletons of arguments are directly passed to the function").

     Decompose into TOTALITY (build the [Q]) + FILL (the per-[A] refinement):
     - [d_pat_total] (induction on [d_typing], MODE-GENERALISED so the [mode_fn]
       IH is available): [d_typing m Γ e B -> exists Q, d_pat m Γ e Q].

       * APP coordination is the crux, and it DISSOLVES here, not via a
         weaken-to-[□]-by-transport.  [d_typing__app] (def_extra.v:742) ALREADY
         carries [e2 ⇨ syn P] and the fill [inh P ⊳ inh(skel A)] as premises
         over the very same [Γ] — REUSE them.  [e1] is consumed in [mode_fn]:
         the function *receives* the (e2-derived) fill output as its arg, so the
         arg is PASSED, never independently re-ghostified.  No determinism / no
         more_ghost coordination needed for the app.

       * ABS_CHECK is the one case needing a ghostified binding: [d_pat__abs_check]
         binds [x:□] and the body must infer for ANY checking arg type, so the
         body's [d_pat] is over [(x:□)::Γ] while its typing is over [(x:typ A)::Γ].
         Generalise [d_pat_total] over a GHOST-CONTEXT relation (each term var
         kept as [skl(skel A)] — via [d_pat_binding_eq], or ghostified to [□]);
         abs_check ghostifies the new λ-var, keeping the app coordination
         consistent (one ghost-context throughout).  [more_ghost] (above) tracks
         the resulting skeleton.

       * FN-mode [abs]: choose [d_pat__abs]'s existential arg = the passed skel
         (so the body is over [x:skl(skel A)] = [x:typ A] by [d_pat_binding_eq],
         IH applies directly).  [forall]: tvar-strengthen the body.  [sub]:
         [d_pat__sub] + [d_pat_sub_infer_ghost].

     - FILL (induction on [d_pat]): base-term leaves close with [ghost_of_fill]
       (Qed, axiom-free); λ/app recurse.  PAINTING caveat to settle at the proof
       assistant: over a ghost-context [e2]'s syn skel gains holes, so the fill
       output gains syn-paintings — check the function (esp. λ via [d_pat__abs]'s
       inh-painted arg) still receives it; var-functions match (syn-arg) directly.

     Then [d_pat_safety] = [d_pat_total] (the [Q]) + FILL.  Still [Admitted]. *)
Admitted.

(** GHOSTIFICATION WITNESS (the mechanism the safety witness relies on).
    A *top-level* [∀] in an annotation's concrete skeleton can be
    generalised to a ghost by [d_pat__sub]: [d_pat_sub__forall_l_untagged]
    instantiates the [∀] with [ψ = □] ([is_tskl □] holds — ghosts ARE
    tagged skeletons), and [d_pat_sub__ghost] then yields [□].  So
    [(e:∀α.α) ⇨tc □], and [□] fills every type ([d_refine_syn_hole_fills]).

    This is why the existential safety is constructive (and why it is NOT
    the algorithm's optimality): the declarative inference is permissive
    enough to pick the fully-ghostified skeleton directly.  No nested-ghost
    problem arises because [d_sub] check-mode is shallow — one-level
    consistency + top-level [forall_l] only, never deep instantiation under
    an arrow — so a term never checks at an instance of a nested covariant
    [∀], and that [∀] need not be ghostified (it stays concrete, matched by
    [d_refine_syn__all] / [__arrow]). *)
