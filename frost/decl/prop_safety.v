(** Frost — totality + safety of skeleton inference ([d_pat_total],
    [d_pat_safety]).  Split out of [prop_skeleton] so it can use the
    subtyping-transitivity machinery in [prop_general_subsumption]. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
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
Require Import src.frost.decl.prop_renaming.
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

(** Forward lookup: a [Γ']-binding refines some [Γ]-binding. *)
Lemma ctx_refines_binds_fwd : forall Γ' Γ x d',
    ctx_refines Γ' Γ -> binds x d' Γ' ->
    exists d, binds x d Γ /\ dbind_refines d' d.
Proof.
  intros Γ' Γ x d' H. induction H; intros Hb; [ inversion Hb | ].
  analyze_binds Hb.
  - exists d. split; [ apply binds_app_iff; left; apply binds_one_iff; auto | assumption ].
  - destruct (IHctx_refines BindsTac) as [d'' [Hb'' Hr'']].
    exists d''. split; [ apply binds_app_iff; right; assumption | assumption ].
Qed.

(** * Strengthening by a NON-tvar binding (no freshness side-condition: a
    non-tvar binding is never looked up, so it strengthens away freely).  This
    is what transports the [abs] body's fill from [(x:□)::Γ'] down to [Γ']. *)
Lemma d_wf_ptyp_strengthen_nontvar : forall Γ1 x d Γ2 A,
    d <> dbind_tvar -> (Γ1 ++ (x ~ d) ++ Γ2) ⊢ₚ A -> (Γ1 ++ Γ2) ⊢ₚ A.
Proof.
  intros Γ1 x d Γ2 A Hd H. remember (Γ1 ++ (x ~ d) ++ Γ2) as Γ eqn:HΓ.
  revert Γ1 HΓ. induction H; intros Γ1 HΓ; subst.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. analyze_binds H; try (exfalso; congruence); auto.
  - apply d_wf_ptyp__arrow; [ eapply IHd_wf_ptyp1 | eapply IHd_wf_ptyp2 ]; eauto.
  - apply d_wf_ptyp__all with (L := L `union` dom (Γ1 ++ Γ2)). intros Y HY.
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Y ltac:(auto) ((Y ~ dbind_tvar) ++ Γ1)); simpl_env; reflexivity.
Qed.

Lemma d_wf_pskl_strengthen_nontvar : forall Γ1 x d Γ2 Ψ P,
    d <> dbind_tvar -> Ψ ⨟ (Γ1 ++ (x ~ d) ++ Γ2) ⊢ₚₛ P -> Ψ ⨟ (Γ1 ++ Γ2) ⊢ₚₛ P.
Proof.
  intros Γ1 x d Γ2 Ψ P Hd H. remember (Γ1 ++ (x ~ d) ++ Γ2) as Γ eqn:HΓ.
  revert Γ1 HΓ. induction H; intros Γ1 HΓ; subst.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
    analyze_binds Hb; try (exfalso; congruence); auto.
  - apply d_wf_pskl__arrow; [ eapply IHd_wf_pskl1 | eapply IHd_wf_pskl2 ]; eauto.
  - apply d_wf_pskl__all with (L := L). intros Y HY. eapply (H0 Y HY Γ1); reflexivity.
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole; [ assumption | eapply IHd_wf_pskl; eauto ].
Qed.

Lemma d_refine_syn_strengthen_nontvar : forall Γ1 x d Γ2 Δs Δi Q P,
    d <> dbind_tvar ->
    (Γ1 ++ (x ~ d) ++ Γ2) ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P ->
    (Γ1 ++ Γ2) ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ1 x d Γ2 Δs Δi Q P Hd H. remember (Γ1 ++ (x ~ d) ++ Γ2) as Γ eqn:HΓ.
  revert Γ1 HΓ. induction H; intros Γ1 HΓ; subst.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [HS | [HI | Hb]];
      [ left; assumption | right; left; assumption | right; right;
        analyze_binds Hb; try (exfalso; congruence); auto ].
  - apply d_refine_syn__arrow; [ eapply IHd_refine_syn1 | eapply IHd_refine_syn2 ]; eauto.
  - apply d_refine_syn__all with (L := L). intros Y HY. eapply (H0 Y HY Γ1); reflexivity.
  - apply d_refine_syn__hole. eapply d_wf_pskl_strengthen_nontvar; eauto.
  - apply d_refine_syn__tophole_remove. eapply IHd_refine_syn; eauto.
  - apply d_refine_syn__tophole_fill with (L := L). intros Y HY. eapply (H0 Y HY Γ1); reflexivity.
  - apply d_refine_syn__tophole_keep; [ assumption | eapply IHd_refine_syn; eauto ].
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
(** A base term's [mode_ti] type is unique: its skeleton is determined
    ([d_typing_ti_primary]) and a synthesised [btyp] is determined by its
    skeleton ([is_styp_skel_inj]). *)
Lemma d_typing_ti_base_unique : forall Γ e B1 B2,
    d_wf_denv Γ -> is_base_term e ->
    d_typing mode_ti Γ e B1 -> d_typing mode_ti Γ e B2 -> B1 = B2.
Proof.
  intros Γ e B1 B2 Hwf Hbase H1 H2.
  apply is_styp_skel_inj;
    [ eapply d_typing_ti_base_is_styp; eauto
    | eapply d_typing_ti_base_is_styp; eauto | ].
  pose proof (d_typing_ti_primary H1) as P1.
  pose proof (d_typing_ti_primary H2) as P2.
  destruct Hbase; simpl in P1, P2.
  - (* unit *) rewrite P1, P2. reflexivity.
  - (* var x *) destruct P1 as [A1 [Hb1 Hs1]]. destruct P2 as [A2 [Hb2 Hs2]].
    assert (dbind_typ A1 = dbind_typ A2) as Ha
      by (eapply binds_unique; [ exact Hb1 | exact Hb2 | eapply d_wf_denv_uniq; eauto ]).
    inversion Ha; subst A2. rewrite Hs1, Hs2. reflexivity.
  - (* anno e A *) rewrite P1, P2. reflexivity.
Qed.

Lemma d_typing_base_principal_sub : forall Γ e Bp Bc,
    d_wf_denv Γ -> is_base_term e ->
    d_typing mode_ti Γ e Bp -> d_typing mode_tc Γ e Bc ->
    empty ⨟ Γ ⊢[ mode_tc ] (ptyp_to_utyp_syn Bp) ⊑ Bc.
Proof.
  intros Γ e Bp Bc Hwf Hbase Htip Htc.
  remember mode_tc as m0 eqn:Hm. revert Bp Hwf Hbase Htip Hm.
  induction Htc; intros Bp Hwf Hbase Htip Hm; try discriminate Hm;
    try solve [ inversion Hbase ].
  - (* sub: the ti-premise type equals [Bp] (base ti uniqueness), then the
       rule's own subtyping IS the goal (same mode as the conclusion). *)
    match goal with Hsub : empty ⨟ _ ⊢[ _ ] _ ⊑ _ |- _ =>
      assert (Bp = ptyp_to_btyp_syn A) as HBp
        by (eapply d_typing_ti_base_unique; [ exact Hwf | exact Hbase | exact Htip | eassumption ]);
      subst Bp; rewrite btyp_to_ptyp_ptyp_to_btyp_syn; exact Hsub end.
  - (* forall: build the ∀ on the right via [d_sub__forall_r]; IH on the body
       with [Bp] weakened to [X :: Γ]. *)
    apply d_sub__forall_r with (L := L `union` dom Γ).
    + change (btyp_all_inh (ptyp_to_btyp_inh A))
        with (ptyp_to_btyp_inh (ptyp_all A)).
      apply is_ityp_paint. eapply d_wf_ptyp_lc. apply d_wf_ptyp_of_btyp_inh.
      eapply d_typing_wf_btyp; [ eapply d_typing__forall with (L := L); eassumption | exact Hwf ].
    + intros X HX.
      match goal with IH : forall _ : atom, _ -> forall _ : btyp, _ |- _ =>
        eapply (IH X ltac:(fsetdec) Bp) end.
      * apply d_wf_denv__tvar; [ exact Hwf | fsetdec ].
      * exact Hbase.
      * rewrite_env (nil ++ (X ~ dbind_tvar) ++ Γ). apply d_typing_weakening. exact Htip.
      * reflexivity.
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

(** Generalized safe-inference predicate (declarative context precision): the
    inference is over [Γ] (possibly carrying [□] for refined vars); the safety
    is quantified over EVERY well-formed [Γt] that [Γ] refines, so a [□]-refined
    inference is safe for the term under any concrete type at that variable. *)
Definition gpat (m : mode) (Γ : list (atom * dbind)) (e : exp) (B : btyp)
  : Prop :=
  match m with
  | mode_fn _ => exists Q, Γ ⊢[ m ] e ⇨ Q /\ safe_skel Γ m Q B
  | _ =>
      exists Q, Γ ⊢[ m ] e ⇨ Q
                /\ (forall Γext Γt A, ctx_weaken Γ Γext -> ctx_refines Γext Γt ->
                       d_wf_denv Γt -> Γt ⊢[ m ] e ⦂ (ptyp_to_btyp_inh A) ->
                       Γext ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳
                         (colour (pskl_to_bskl_inh (bskl_to_pskl Q)) A))
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

(** Fill for a skeleton whose [pskl] matches the checking type [A] (the
    synthesised path: the inh-painted skeleton fills the concrete colouring of
    [A]).  Coverage transfers from [Γt] to [Γ'] since refinement keeps tvars. *)
Lemma gpat_syn_fill : forall Γ' Γt A Q,
    bskl_to_pskl Q = ptyp_to_pskl A ->
    d_wf_ptyp Γt A -> ctx_refines Γ' Γt ->
    Γ' ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳
      (colour (pskl_to_bskl_inh (bskl_to_pskl Q)) A).
Proof.
  intros Γ' Γt A Q Hsk Hwfa Hcr.
  apply refine_colour_core.
  - eapply d_wf_ptyp_lc_loc; eauto.
  - rewrite Hsk. apply hole_safe_of_ptyp. eapply d_wf_ptyp_lc_loc; eauto.
  - intros X HX. right. right.
    eapply ctx_refines_binds_tvar; [ exact Hcr | eapply d_wf_ptyp_ftvar; eauto ].
Qed.

(** Fill for the ghost skeleton [□] (the refined-variable path): [□] fills the
    syn-colouring of any well-formed checking type. *)
Lemma gpat_hole_fill : forall Γ' Γt A,
    d_wf_ptyp Γt A -> ctx_refines Γ' Γt ->
    Γ' ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl bskl_hole)) ⊳
      (colour (pskl_to_bskl_inh (bskl_to_pskl bskl_hole)) A).
Proof.
  intros Γ' Γt A Hwfa Hcr.
  replace (pskl_to_bskl_inh (bskl_to_pskl bskl_hole)) with (@bskl_hole) by reflexivity.
  rewrite colour_hole.
  apply d_refine_syn_hole_fills.
  - eapply d_wf_ptyp_lc_loc; eauto.
  - intros X HX. right.
    eapply ctx_refines_binds_tvar; [ exact Hcr | eapply d_wf_ptyp_ftvar; eauto ].
Qed.

(** Base-term safety under context refinement: [unit]/[var]/[anno].  The inferred
    [Q] is over [Γ'] ([□] for a refined var, else the syn skeleton); its [pskl]
    matches every checking type by [d_typing_ti_primary], and fills via the two
    helpers above. *)
Lemma d_pat_base_safe_gen : forall Γ e B,
    d_wf_denv Γ -> is_base_term e -> d_typing mode_ti Γ e B ->
    forall Γ', ctx_refines Γ' Γ -> gpat mode_ti Γ' e B.
Proof.
  intros Γ e B Hwf Hbase Hty Γ' Hcr.
  pose proof (d_typing_ti_primary Hty) as Hpri.
  destruct Hbase; simpl in Hpri.
  - (* unit *)
    exists bskl_unit. split; [ apply d_pat__unit | ].
    intros Γext Γt A Hcw Hcrt Hwft HA.
    pose proof (d_typing_ti_primary HA) as Hp. simpl in Hp.
    rewrite btyp_to_ptyp_ptyp_to_btyp_inh in Hp.
    eapply gpat_syn_fill;
      [ simpl; rewrite Hp; reflexivity
      | apply d_wf_ptyp_of_btyp_inh; eapply d_typing_wf_btyp; eauto
      | exact Hcrt ].
  - (* var x *)
    destruct Hpri as [A0 [Hbnd Hskel0]].
    destruct (@ctx_refines_binds Γ' Γ x (dbind_typ A0) Hcr Hbnd) as [d' [Hb' Hdr]].
    inversion Hdr; subst.
    + (* kept: x : typ A0 *)
      exists (pskl_to_bskl_syn (ptyp_to_pskl A0)). split.
      * apply d_pat__var with (d := dbind_typ A0); [ exact Hb' | reflexivity ].
      * intros Γext Γt A Hcw Hcrt Hwft HA.
        pose proof (d_typing_ti_primary HA) as Hp. simpl in Hp.
        destruct Hp as [A1 [Hbnd1 Hskel1]].
        rewrite btyp_to_ptyp_ptyp_to_btyp_inh in Hskel1.
        (* x : typ A0 in Γ' ⊆ Γext refines x's Γt-binding ⇒ typ A0, so A1 = A0 *)
        assert (Hb'ext : binds x (dbind_typ A0) Γext)
          by (eapply binds_ctx_weaken; [ exact Hcw | exact Hb' ]).
        destruct (@ctx_refines_binds_fwd Γext Γt x (dbind_typ A0) Hcrt Hb'ext)
          as [dt [Hbt Hdrt]].
        inversion Hdrt; subst.
        assert (dbind_typ A1 = dbind_typ A0) by (eapply binds_unique; [ exact Hbnd1 | exact Hbt | eapply d_wf_denv_uniq; eauto ]).
        match goal with H : dbind_typ _ = dbind_typ _ |- _ => inversion H; subst end.
        eapply gpat_syn_fill;
          [ rewrite bskl_to_pskl_pskl_to_bskl_syn; rewrite Hskel1; reflexivity
          | apply d_wf_ptyp_of_btyp_inh; eapply d_typing_wf_btyp; eauto
          | exact Hcrt ].
    + (* refined: x : □ *)
      exists bskl_hole. split.
      * apply d_pat__var with (d := dbind_skl pskl_hole) (P := pskl_hole);
          [ exact Hb' | reflexivity ].
      * intros Γext Γt A Hcw Hcrt Hwft HA.
        eapply gpat_hole_fill;
          [ apply d_wf_ptyp_of_btyp_inh; eapply d_typing_wf_btyp; eauto | exact Hcrt ].
  - (* anno e A0 *)
    exists (pskl_to_bskl_syn (ptyp_to_pskl A)). split.
    + apply d_pat__anno. eapply d_wf_ptyp_ctx_refines;
        [ eapply d_typing_anno_wf; eauto | exact Hcr ].
    + intros Γext Γt A1 Hcw Hcrt Hwft HA.
      pose proof (d_typing_ti_primary HA) as Hp. simpl in Hp.
      rewrite btyp_to_ptyp_ptyp_to_btyp_inh in Hp.
      eapply gpat_syn_fill;
        [ rewrite bskl_to_pskl_pskl_to_bskl_syn; rewrite Hp; reflexivity
        | apply d_wf_ptyp_of_btyp_inh; eapply d_typing_wf_btyp; eauto
        | exact Hcrt ].
Qed.

(** GENERAL binder rename for typing (mirrors [d_pat_rename]): renaming the
    context binder [x ↦ y] (and [x ↦ y] in the term) preserves [⦂].  The [sub]
    case goes through [d_sub_subst_nontvar] (the subtyping ignores the relabeled
    term binding).  Aligns an abstraction body's premise to a fixed binder. *)
Lemma d_typing_rename : forall m Γ e B,
    Γ ⊢[ m ] e ⦂ B ->
    forall Γ1 x y d Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    x `notin` dom (Γ1 ++ Γ2) ->
    (Γ1 ++ (y ~ d) ++ Γ2) ⊢[ m ] (subst_exp_in_exp (exp_var_f y) x e) ⦂ B.
Proof.
  (* Structural induction on the typing.  Skeletons / types carry no term vars,
     so the relabelling only ever touches term-var lookups; each non-typing
     premise is transported by its own renaming lemma ([d_sub_subst_nontvar],
     [d_pat_rename], [d_refine_syn_rename], [d_wf_ptyp_rename]), and the λ /
     ∀ bodies thread the substitution.  Mirrors [d_pat_rename]. *)
  intros m Γ e B H. induction H; intros Γ1 x0 y0 d0 Γ2 Heq Hd Hnotin; subst.
  - simpl. apply d_typing__unit.
  - (* var *) simpl.
    match goal with |- context [ if ?b then _ else _ ] => destruct b as [Hxeq | Hxne] end.
    + subst x. assert (Hdd : dbind_typ A = d0).
      { apply binds_app_1 in H. destruct H as [Hb1 | Hb2].
        - apply binds_In in Hb1. exfalso. apply Hnotin. rewrite dom_app. fsetdec.
        - apply binds_app_1 in Hb2. destruct Hb2 as [Hb3 | Hb4].
          + apply binds_one_iff in Hb3. destruct Hb3 as [_ Heqd]. exact Heqd.
          + apply binds_In in Hb4. exfalso. apply Hnotin. rewrite dom_app. fsetdec. }
      rewrite <- Hdd. apply d_typing__var. apply binds_app_3; simpl; auto.
    + apply d_typing__var. apply binds_app_1 in H. destruct H as [Hb1 | Hb2].
      * apply binds_app_2; assumption.
      * apply binds_app_1 in Hb2. destruct Hb2 as [Hb3 | Hb4].
        -- apply binds_one_iff in Hb3. destruct Hb3 as [Hxe _]. exfalso. apply Hxne; exact Hxe.
        -- apply binds_app_3; simpl; auto.
  - simpl. apply d_typing__anno. eapply IHd_typing; eauto.
  - simpl. apply d_typing__sub with (A := A);
      [ match goal with Hbe : is_base_term _ |- _ =>
          inversion Hbe; subst; simpl;
          try (match goal with |- context [ if ?b then _ else _ ] => destruct b end);
          constructor end
      | eapply IHd_typing; eauto | eapply d_sub_subst_nontvar; eauto ].
  - simpl. apply d_typing__freeze. eapply IHd_typing; eauto.
  - (* forall: term unchanged under the binder (type opens, not the term) *)
    apply d_typing__forall with (L := L `union` singleton x0 `union` dom (Γ1 ++ Γ2));
      [ apply is_value_subst_var; assumption | ].
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hd | simpl_env in *; fsetdec ].
  - simpl. apply d_typing__abs with (L := L `union` singleton x0 `union` dom (Γ1 ++ Γ2)) (A := A) (B := B);
      [ eapply d_wf_ptyp_rename; eauto | assumption | ].
    intros z Hz. rewrite subst_exp_in_exp_open_exp_wrt_exp_var
      by (solve [ apply lc_exp_var_f | fsetdec ]).
    rewrite_env (((z ~ dbind_typ A) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hd | simpl_env in *; fsetdec ].
  - simpl. apply d_typing__abs_anno with
      (L := L `union` singleton x0 `union` dom (Γ1 ++ Γ2)) (A := btyp_to_ptyp B1) (B1 := B1) (B2 := B2);
      [ eapply d_wf_ptyp_rename; eauto | reflexivity | assumption | ].
    intros z Hz. rewrite subst_exp_in_exp_open_exp_wrt_exp_var
      by (solve [ apply lc_exp_var_f | fsetdec ]).
    rewrite_env (((z ~ dbind_typ (btyp_to_ptyp B1)) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hd | simpl_env in *; fsetdec ].
  - simpl. eapply d_typing__app;
      [ eapply d_pat_rename | eapply d_refine_syn_rename
      | eapply IHd_typing1 | eapply IHd_typing2 ]; eauto.
Qed.

(** The [abs_check] fill (the paper's context-precision lemma for a checked
    λ): given the body's safety over [(x0:□)::Γ'], the universal-ghost arrow
    skeleton [⫯.(□ → inh{Qb})] fills every type the λ checks against — by
    induction on that typing, peeling [∀]s ([tophole_fill]) down to the
    function base ([tophole_remove] + [arrow] + body-safety + strengthening). *)
Lemma abs_check_fill : forall e Qb Γ' L_b,
    (forall x, x `notin` L_b -> forall Γext Γt'' A'',
        ctx_weaken ((x ~ dbind_skl pskl_hole) ++ Γ') Γext -> ctx_refines Γext Γt'' ->
        d_wf_denv Γt'' ->
        Γt'' ⊢[ mode_tc ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ ptyp_to_btyp_inh A'' ->
        Γext ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Qb)) ⊳
          (colour (pskl_to_bskl_inh (bskl_to_pskl Qb)) A'')) ->
    forall Γext0 Γt A',
      ctx_weaken Γ' Γext0 -> ctx_refines Γext0 Γt -> d_wf_denv Γt ->
      Γt ⊢[ mode_tc ] (exp_abs e) ⦂ (ptyp_to_btyp_inh A') ->
      Γext0 ⨟ nil ⨟ nil ⊢ᵣ
        (pskl_to_bskl_inh (bskl_to_pskl (bskl_tophole (bskl_arrow bskl_hole Qb)))) ⊳
        (colour (pskl_to_bskl_inh (bskl_to_pskl (bskl_tophole (bskl_arrow bskl_hole Qb)))) A').
Proof.
  intros e Qb Γ' L_b Hbody Γext0 Γt A' Hcw Hcr Hwf Hty.
  remember (exp_abs e) as ee eqn:Hee.
  remember (ptyp_to_btyp_inh A') as B0 eqn:HB0.
  remember mode_tc as m eqn:Hm.
  revert Γext0 A' Hcw Hcr Hwf Hee HB0 Hm.
  induction Hty; intros Γext0 A'0 Hcw Hcr Hwf Hee HB0 Hm;
    try discriminate Hee;
    try (exfalso; subst;
         match goal with Hb : is_base_term (exp_abs _) |- _ => inversion Hb end).
  - (* forall : A'0 = ∀A, peel one ∀ (tophole_fill + move + IH) *)
    change (btyp_all_inh (ptyp_to_btyp_inh A)) with (ptyp_to_btyp_inh (ptyp_all A)) in HB0.
    apply (f_equal btyp_to_ptyp) in HB0.
    rewrite ! btyp_to_ptyp_ptyp_to_btyp_inh in HB0. subst A'0.
    replace (pskl_to_bskl_inh (bskl_to_pskl (bskl_tophole (bskl_arrow bskl_hole Qb))))
      with (bskl_tophole (bskl_arrow bskl_hole (pskl_to_bskl_inh (bskl_to_pskl Qb)))) by reflexivity.
    replace (colour (bskl_tophole (bskl_arrow bskl_hole (pskl_to_bskl_inh (bskl_to_pskl Qb)))) (ptyp_all A))
      with (bskl_all_syn (colour (bskl_tophole (bskl_arrow bskl_hole (pskl_to_bskl_inh (bskl_to_pskl Qb)))) A))
      by reflexivity.
    apply d_refine_syn__tophole_fill with
      (L := L_b `union` L `union` dom Γ `union` dom Γext0). intros X HX.
    rewrite <- colour_open.
    eapply d_refine_syn_move; [ | apply colour_no_tophole | reflexivity ].
    eapply (H1 X ltac:(fsetdec) Hbody ((X ~ dbind_tvar) ++ Γext0)
              (open_ptyp_wrt_ptyp A (ptyp_var_f X))).
    + eapply ctx_weaken_trans; [ exact Hcw | apply ctx_weaken_app_front ].
    + rewrite_env ((X ~ dbind_tvar) ++ Γext0); rewrite_env ((X ~ dbind_tvar) ++ Γ).
      apply ctxr_cons; [ apply dbr_refl | exact Hcr ].
    + apply d_wf_denv__tvar; [ exact Hwf | fsetdec ].
    + exact Hee.
    + rewrite ptyp_to_btyp_inh_open_var. reflexivity.
    + reflexivity.
  - (* abs : A'0 = arrow A (btyp_to_ptyp B); ⫯ peeled, domain holed, codomain via body-hyp *)
    subst m. injection Hee as Hee'; subst e0.
    match goal with Hsk : skmod_ty _ mode_tc |- _ =>
      inversion Hsk as [ | ? Hia | ]; subst end.
    match goal with Hia : is_ityp (btyp_arrow _ _) |- _ =>
      inversion Hia as [ | | ? ? Hi1 Hi2 | ]; subst end.
    rewrite <- (is_ityp_ptyp_to_btyp_inh Hi2) in HB0.
    change (btyp_arrow (ptyp_to_btyp_inh A) (ptyp_to_btyp_inh (btyp_to_ptyp B)))
      with (ptyp_to_btyp_inh (ptyp_arrow A (btyp_to_ptyp B))) in HB0.
    apply (f_equal btyp_to_ptyp) in HB0.
    rewrite ! btyp_to_ptyp_ptyp_to_btyp_inh in HB0. subst A'0.
    replace (pskl_to_bskl_inh (bskl_to_pskl (bskl_tophole (bskl_arrow bskl_hole Qb))))
      with (bskl_tophole (bskl_arrow bskl_hole (pskl_to_bskl_inh (bskl_to_pskl Qb)))) by reflexivity.
    replace (colour (bskl_tophole (bskl_arrow bskl_hole (pskl_to_bskl_inh (bskl_to_pskl Qb)))) (ptyp_arrow A (btyp_to_ptyp B)))
      with (bskl_arrow (colour bskl_hole A) (colour (pskl_to_bskl_inh (bskl_to_pskl Qb)) (btyp_to_ptyp B)))
      by reflexivity.
    apply d_refine_syn__tophole_remove. apply d_refine_syn__arrow.
    + rewrite colour_hole. apply d_refine_syn_hole_fills.
      * eapply d_wf_ptyp_lc_loc; eauto.
      * intros Y HY. right. eapply ctx_refines_binds_tvar; [ exact Hcr | ].
        eapply d_wf_ptyp_ftvar; [ | exact HY ]. assumption.
    + (* codomain : body-hyp at a fresh x, then strengthen away (x:□) *)
      pick fresh x for (L_b `union` L `union` dom Γ `union` dom Γext0).
      rewrite_env (nil ++ Γext0).
      eapply d_refine_syn_strengthen_nontvar with (x := x) (d := dbind_skl pskl_hole);
        [ discriminate | ].
      simpl.
      eapply (Hbody x ltac:(fsetdec) ((x ~ dbind_skl pskl_hole) ++ Γext0)
                ((x ~ dbind_typ A) ++ Γ) (btyp_to_ptyp B)).
      * apply ctx_weaken_cons; exact Hcw.
      * apply ctxr_cons; [ apply dbr_typ_hole | exact Hcr ].
      * apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ].
      * rewrite (is_ityp_ptyp_to_btyp_inh Hi2).
        match goal with Hbp : forall _ : atom, _ -> _ ⊢[ _ ] _ ⦂ _ |- _ =>
          apply Hbp; fsetdec end.
Qed.

Lemma d_pat_total_gen : forall m Γ e B,
    Γ ⊢[ m ] e ⦂ B -> d_wf_denv Γ ->
    forall Γ', ctx_refines Γ' Γ -> gpat m Γ' e B.
Proof.
  intros m Γ e B Hty. induction Hty; intros Hwf Γ' Hcr.
  - (* unit *) eapply d_pat_base_safe_gen;
      [ exact Hwf | apply is_base_term__unit | apply d_typing__unit | exact Hcr ].
  - (* var *) eapply d_pat_base_safe_gen;
      [ exact Hwf | apply is_base_term__var | eapply d_typing__var; eauto | exact Hcr ].
  - (* anno *) eapply d_pat_base_safe_gen;
      [ exact Hwf | apply is_base_term__anno | apply d_typing__anno; eassumption | exact Hcr ].
  - (* sub *) destruct m.
    + (* ti: subsumed base term still synthesises (skeleton determined) *)
      eapply d_pat_base_safe_gen;
        [ exact Hwf | eassumption | eapply d_typing__sub; eassumption | exact Hcr ].
    + (* tc: SAFETY of a checked, subsumed base term.  All three ingredients
         are now in hand: the FILL side [ghost_of_fill] (prop_skeleton.v, Qed)
         + the inference side [d_pat__sub] + [ghost_of_infer] (Qed) + the
         checking-type inversion [d_typing_base_principal_sub] (Qed above).
         Remaining: the assembly threading [Γ' ⊆ Γext refines Γt] and the
         base-term ti-skeleton shape (always [pskl_to_bskl_syn P']). *)
      admit.
    + (* fn: a subsumed base term in function mode (skeleton is an arrow whose
         domain is forced [inh]); same missing fill-side machinery. *)
      admit.
  - (* freeze: TI [syn A] repainted to TC [inh A]; the [d_pat__freeze]
       inference keeps [syn P], whose safety needs the same ghost fill side
       plus the colour-repaint bookkeeping. *)
    admit.
  - (* forall: a value checked at [∀]; gpat tc needs a skeleton whose inh
       painting fills every [∀]-prefixed checking type (peel ∀ via
       [tophole_fill], recurse). *)
    admit.
  - (* abs: λ in mode [m].  At TC the fill is the (Qed) [abs_check_fill], but
       [d_pat__abs_check] needs the body to infer a SYN/principal skeleton
       [pskl_to_bskl_syn P], whereas the IH ([gpat tc]) only yields the body's
       SAFE (ghostified) skeleton — a distinct, more concrete inference not yet
       available (needs a principal-body-skeleton lemma).  At FN the domain is
       forced [inh]. *)
    admit.
  - (* abs_anno: annotated λ; analogous to [abs] with [d_pat__abs_anno_check]
       / [abs_check_fill] on the annotated domain. *)
    admit.
  - (* app: [d_pat__app] infers the function arrow and threads the refined
       argument; safety follows from the codomain's [safe_skel]. *)
    admit.
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
  intros Γ e B0 Hty Hwf.
  destruct (d_pat_total_gen Hty Hwf (ctx_refines_refl Γ)) as [Q [HQ Hsafe]].
  exists Q. split; [ exact HQ | ].
  intros A HA.
  exists (colour (pskl_to_bskl_inh (bskl_to_pskl Q)) A). split;
    [ apply colour_erasure
    | apply (Hsafe Γ Γ A (ctx_weaken_refl Γ) (ctx_refines_refl Γ) Hwf HA) ].
Qed.

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
