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
Require Import src.frost.decl.prop_syntax_directed.

Set Implicit Arguments.

(** * Context precision (declarative analog of the paper's [⪯ctx]).
    [Γ'] refines [Γ] if it is [Γ] with some term-bindings [x:typ A] replaced by
    the most-general skeleton binding [x:□].  This is what an [abs] in CHECK mode
    does to the body's context, and is the keystone for the abstraction cases. *)
Inductive dbind_refines : dbind -> dbind -> Prop :=
| dbr_refl : forall d, dbind_refines d d
| dbr_typ_hole : forall A, dbind_refines (dbind_skl pskl_hole) (dbind_typ A)
(** A [typ A] binding may also be refined to its *concrete* skeleton painting
    [skl (ptyp_to_pskl A)] — not just the bare hole [□].  This is what an [abs]
    in FUNCTION mode does: the body runs with [x : skl (ptyp_to_pskl A)] so the
    inferred arrow keeps its concrete (polymorphism-preserving) domain, matching
    the algorithmic [a_pat__abs]/[a_split].  [dbind_to_pskl] agrees on the two
    ([typ A ↦ ptyp_to_pskl A] and [skl P ↦ P]), so [d_pat] infers identically. *)
| dbr_typ_skl : forall A, dbind_refines (dbind_skl (ptyp_to_pskl A)) (dbind_typ A).

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

(** [ptyp_to_pskl] never yields the bare hole (it maps every type constructor to
    a non-[pskl_hole] head) — used to prune the spurious [dbr_typ_hole] case when
    inverting a [dbind_refines (skl (ptyp_to_pskl _)) (typ _)]. *)
Lemma ptyp_to_pskl_not_hole : forall A, ptyp_to_pskl A <> pskl_hole.
Proof. destruct A; simpl; discriminate. Qed.

(** A concrete-skeleton refinement [skl (ptyp_to_pskl A) ⪯ typ B] forces the two
    to share a skeleton (only [dbr_typ_skl] can fire; [dbr_typ_hole] is ruled out
    by [ptyp_to_pskl_not_hole], [dbr_refl] by the [skl]/[typ] head clash). *)
Lemma dbind_refines_skl_typ_skel : forall A B,
    dbind_refines (dbind_skl (ptyp_to_pskl A)) (dbind_typ B) ->
    ptyp_to_pskl A = ptyp_to_pskl B.
Proof.
  intros A B H. inversion H; subst.
  - exfalso; match goal with He : pskl_hole = ptyp_to_pskl ?a |- _ =>
      eapply ptyp_to_pskl_not_hole; symmetry; exact He end.
  - congruence.
Qed.

(** The skeleton of a bidirectional type's coercion agrees with the skeleton of
    its erasure (both drop colours structurally). *)
Lemma bskl_to_pskl_btyp_to_bskl : forall B,
    bskl_to_pskl (btyp_to_bskl B) = ptyp_to_pskl (btyp_to_ptyp B).
Proof. induction B; simpl; congruence. Qed.

(** A variable that types in ANY mode is [typ]-bound in the context.  Needed to
    recover a [Γt] binding from a checking derivation whose last rule may be
    [sub], [freeze] (impossible for a bare var), or [forall] (a value checked
    against [∀]) — none of which is directly a [d_typing__var]. *)
Lemma d_typing_var_binds : forall m Γ x B,
    Γ ⊢[ m ] (exp_var_f x) ⦂ B -> exists A, binds x (dbind_typ A) Γ.
Proof.
  intros m Γ x B H. remember (exp_var_f x) as e eqn:He.
  induction H; try discriminate He.
  - (* var *) inversion He; subst. exists A. exact H.
  - (* sub : the [ti] premise is on the same var *) apply IHd_typing; exact He.
  - (* forall : strip the peeled tvar from the body binding *)
    pick fresh X for L.
    match goal with IH : forall X0, X0 `notin` _ -> _ = _ -> _ |- _ =>
      destruct (IH X ltac:(auto) He) as [A0 Hb] end.
    apply binds_cons_1 in Hb.
    destruct Hb as [ [HeqX Hd] | Hb ]; [ discriminate Hd | exists A0; exact Hb ].
Qed.

(** [ctx_refines] preserves [dom] and tvar bindings. *)
Lemma ctx_refines_dom : forall Γ' Γ, ctx_refines Γ' Γ -> dom Γ' [=] dom Γ.
Proof.
  intros Γ' Γ H. induction H; simpl; [ fsetdec | fsetdec ].
Qed.

(** [ctx_refines] up to tvar-insertion on the RIGHT (target).  This is the
    coverage-quantifier relation for the tc [skel_safe] engine: a λ checking
    against a ∀ peels the bound tvar into the context, so the body's checking
    context is a plain refinement of the inference context PLUS the peeled
    tvars.  Since [skel_safe]'s conclusion is context-free, the [crtw_tvar]
    step is absorbed with NO change to the body coverage hypothesis. *)
Inductive ctx_refines_tw : list (atom * dbind) -> list (atom * dbind) -> Prop :=
| crtw_base : forall Γ' Γ, ctx_refines Γ' Γ -> ctx_refines_tw Γ' Γ
| crtw_tvar : forall Γ' Γ X,
    ctx_refines_tw Γ' Γ -> ctx_refines_tw Γ' ((X ~ dbind_tvar) ++ Γ)
| crtw_cons : forall x d' d Γ' Γ,
    dbind_refines d' d -> ctx_refines_tw Γ' Γ ->
    ctx_refines_tw ((x ~ d') ++ Γ') ((x ~ d) ++ Γ).

Lemma ctx_refines_tw_refl : forall Γ, ctx_refines_tw Γ Γ.
Proof. intros; apply crtw_base, ctx_refines_refl. Qed.

(* ===================================================================== *)
(*  tvar-RENAMING for [d_refine_syn] (and onward [d_pat]) — the infra the  *)
(*  [forall] case needs: the inference's fresh tvar [X0] must be α-renamed  *)
(*  to a per-instance-fresh [Y] before transporting it past the (possibly   *)
(*  [X0]-binding) fill context.  Mirrors the [_subst_unit] family but keeps  *)
(*  the binding (relabelled [X0 ↦ Y]) instead of dropping it.                *)
(* ===================================================================== *)

(* coercion / tvar-rename commutes *)
Lemma pskl_to_bskl_syn_subst_var : forall P X Y,
    subst_bskl_in_bskl (bskl_var_f Y) X (pskl_to_bskl_syn P)
    = pskl_to_bskl_syn (subst_pskl_in_pskl (pskl_var_f Y) X P).
Proof.
  induction P; intros X Y; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma guarded_bskl_subst_var : forall Q X Y,
    guarded_bskl Q -> guarded_bskl (subst_bskl_in_bskl (bskl_var_f Y) X Q).
Proof.
  intros Q X Y H. induction H; simpl.
  - apply guarded_bskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; apply guarded_bskl__var.
  - apply guarded_bskl__arrow; apply subst_bskl_in_bskl_lc_bskl; (assumption || apply lc_bskl_var_f).
Qed.

Lemma guarded_pskl_subst_var : forall P X Y,
    guarded_pskl P -> guarded_pskl (subst_pskl_in_pskl (pskl_var_f Y) X P).
Proof.
  intros P X Y H. induction H; simpl.
  - apply guarded_pskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; apply guarded_pskl__var.
  - apply guarded_pskl__arrow; apply subst_pskl_in_pskl_lc_pskl; (assumption || apply lc_pskl_var_f).
Qed.

Lemma d_wf_pskl_rename_tvar : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P ->
    forall Γ1 Γ2 X0 Y, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
    (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⨟ Ψ ⊢ₚₛ (subst_pskl_in_pskl (pskl_var_f Y) X0 P).
Proof.
  intros Ψ Γ P H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst; simpl.
  - apply d_wf_pskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end.
    + apply d_wf_pskl__var. right. simpl_env. auto.
    + apply d_wf_pskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right; analyze_binds Hb ].
  - apply d_wf_pskl__arrow; [ eapply IHd_wf_pskl1 | eapply IHd_wf_pskl2 ]; eauto.
  - apply d_wf_pskl__all
      with (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` {{X0}} `union` {{Y}}).
    intros X HX.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var by (first [ apply lc_pskl_var_f | fsetdec ]).
    eapply (H0 X ltac:(fsetdec) Γ1 Γ2 X0 Y); [ reflexivity | fsetdec ].
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole;
      [ apply guarded_pskl_subst_var; assumption | eapply IHd_wf_pskl; eauto ].
Qed.

Lemma d_refine_syn_rename_tvar : forall Γ Δi Q P,
    Γ ⨟ Δi ⊢ᵣ Q ⊳ P ->
    forall Γ1 Γ2 X0 Y, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
    (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⨟ Δi ⊢ᵣ
      (subst_bskl_in_bskl (bskl_var_f Y) X0 Q) ⊳ (subst_bskl_in_bskl (bskl_var_f Y) X0 P).
Proof.
  intros Γ Δi Q P H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst; simpl.
  - apply d_refine_syn__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end.
    + apply d_refine_syn__var. right. simpl_env. auto.
    + apply d_refine_syn__var. destruct H as [HI | Hb];
        [ left; assumption | right; analyze_binds Hb ].
  - apply d_refine_syn__arrow;
      [ eapply IHd_refine_syn1 | eapply IHd_refine_syn2 ]; eauto.
  - apply d_refine_syn__all
      with (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` {{X0}} `union` {{Y}}).
    intros Z HZ.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var by (first [ apply lc_bskl_var_f | fsetdec ]).
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var by (first [ apply lc_bskl_var_f | fsetdec ]).
    eapply (H0 Z ltac:(fsetdec) Γ1 Γ2 X0 Y); [ reflexivity | fsetdec ].
  - rewrite pskl_to_bskl_syn_subst_var. apply d_refine_syn__hole.
    eapply d_wf_pskl_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
  - apply d_refine_syn__tophole_remove. eapply IHd_refine_syn; eauto.
  - apply d_refine_syn__tophole_fill
      with (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` {{X0}} `union` {{Y}}).
    intros Z HZ. simpl_env in HZ. simpl_env in Hfr.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var by (first [ apply lc_bskl_var_f | fsetdec ]).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ2 X0 Y);
      [ simpl_env; reflexivity | simpl_env; fsetdec ].
  - apply d_refine_syn__tophole_keep;
      [ apply guarded_bskl_subst_var; assumption | eapply IHd_refine_syn; eauto ].
Qed.

(* more coercion / tvar-rename commutes (for [d_pat_rename_tvar]) *)
Lemma pskl_to_bskl_inh_subst_var : forall P X Y,
    subst_bskl_in_bskl (bskl_var_f Y) X (pskl_to_bskl_inh P)
    = pskl_to_bskl_inh (subst_pskl_in_pskl (pskl_var_f Y) X P).
Proof.
  induction P; intros X Y; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma ptyp_to_pskl_subst_var : forall A X Y,
    subst_pskl_in_pskl (pskl_var_f Y) X (ptyp_to_pskl A)
    = ptyp_to_pskl (subst_ptyp_in_ptyp (ptyp_var_f Y) X A).
Proof.
  induction A; intros X Y; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma btyp_to_bskl_subst_var : forall B X Y,
    subst_bskl_in_bskl (bskl_var_f Y) X (btyp_to_bskl B)
    = btyp_to_bskl (subst_btyp_in_btyp (btyp_var_f Y) X B).
Proof.
  induction B; intros X Y; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); try (rewrite IHB; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma ptyp_to_btyp_syn_subst_var : forall A X Y,
    subst_btyp_in_btyp (btyp_var_f Y) X (ptyp_to_btyp_syn A)
    = ptyp_to_btyp_syn (subst_ptyp_in_ptyp (ptyp_var_f Y) X A).
Proof.
  induction A; intros X Y; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma btyp_to_ptyp_subst_var : forall B X Y,
    subst_ptyp_in_ptyp (ptyp_var_f Y) X (btyp_to_ptyp B)
    = btyp_to_ptyp (subst_btyp_in_btyp (btyp_var_f Y) X B).
Proof.
  induction B; intros X Y; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); try (rewrite IHB; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma ptyp_to_btyp_inh_subst_var : forall A X Y,
    subst_btyp_in_btyp (btyp_var_f Y) X (ptyp_to_btyp_inh A)
    = ptyp_to_btyp_inh (subst_ptyp_in_ptyp (ptyp_var_f Y) X A).
Proof.
  induction A; intros X Y; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma ptyp_to_utyp_syn_subst_var : forall A X Y,
    subst_utyp_in_utyp (utyp_var_f Y) X (ptyp_to_utyp_syn A)
    = ptyp_to_utyp_syn (subst_ptyp_in_ptyp (ptyp_var_f Y) X A).
Proof.
  induction A; intros X Y; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma mod_comp_ty_rename_tvar : forall B m X0 Y,
    mod_comp_ty B m -> mod_comp_ty (subst_btyp_in_btyp (btyp_var_f Y) X0 B) m.
Proof.
  intros B m X0 Y H. induction H.
  - apply mod_comp_ty__ti. apply is_styp_rename_tvar. assumption.
  - apply mod_comp_ty__tc. apply is_ityp_rename_tvar. assumption.
  - simpl. apply mod_comp_ty__fn. assumption.
Qed.

Lemma bskl_to_uskl_subst_var : forall Q X Y,
    subst_bskl_in_uskl (uskl_var_f Y) X (bskl_to_uskl Q)
    = bskl_to_uskl (subst_bskl_in_bskl (bskl_var_f Y) X Q).
Proof.
  induction Q; intros X Y; simpl; try reflexivity;
    try (rewrite IHQ1, IHQ2; reflexivity); try (rewrite IHQ; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

(* shape predicates preserved by tvar-rename (subst by a var) *)
Lemma is_sskl_subst_var : forall Q X Y,
    is_sskl Q -> is_sskl (subst_bskl_in_bskl (bskl_var_f Y) X Q).
Proof.
  intros Q X Y H. induction H; simpl.
  - apply is_sskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; apply is_sskl__var.
  - apply is_sskl__arrow; assumption.
  - apply is_sskl__all with (L := L `union` {{X}}). intros Z HZ.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_var_f); try fsetdec. auto.
  - apply is_sskl__hole.
  - apply is_sskl__tophole; assumption.
Qed.

Lemma is_tskl_subst_var : forall R X Y,
    is_tskl R -> is_tskl (subst_bskl_in_uskl (uskl_var_f Y) X R).
Proof.
  intros R X Y H. induction H; simpl.
  - apply is_tskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; apply is_tskl__var.
  - apply is_tskl__arrow; assumption.
  - apply is_tskl__all_etag with (L := L `union` {{X}}). intros Z HZ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_var_f); try fsetdec. auto.
  - apply is_tskl__all_syn with (L := L `union` {{X}}). intros Z HZ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_var_f); try fsetdec. auto.
  - apply is_tskl__holeg.
  - apply is_tskl__topholeg; assumption.
Qed.

Lemma d_tags_skl_subst_var : forall Δ R X Y,
    d_tags_skl Δ R -> d_tags_skl Δ (subst_bskl_in_uskl (uskl_var_f Y) X R).
Proof.
  intros Δ R X Y H. induction H; simpl.
  - apply d_tags_skl__unit; (assumption || fsetdec).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      apply d_tags_skl__var; (assumption || fsetdec).
  - apply d_tags_skl__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
  - apply d_tags_skl__all_etag with (L := L `union` {{X}}) (Ψ0 := Ψ0); [ | assumption | assumption ].
    intros Z HZ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_var_f); try fsetdec. auto.
  - apply d_tags_skl__all_syn with (L := L `union` {{X}}). intros Z HZ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_var_f); try fsetdec. auto.
  - apply d_tags_skl__hole; (assumption || fsetdec).
  - apply d_tags_skl__tophole; assumption.
  - apply d_tags_skl__holeg; (assumption || fsetdec).
  - apply d_tags_skl__topholeg with (Ψ0 := Ψ0); assumption.
Qed.

Lemma guarded_uskl_subst_var : forall R X Y,
    guarded_uskl R -> guarded_uskl (subst_bskl_in_uskl (uskl_var_f Y) X R).
Proof.
  intros R X Y H. induction H; simpl.
  - apply guarded_uskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; apply guarded_uskl__var.
  - apply guarded_uskl__arrow; apply subst_bskl_in_uskl_lc_uskl; (assumption || apply lc_uskl_var_f).
Qed.

Lemma d_wf_uskl_rename_tvar : forall Ψ Γ R,
    Γ ⨟ Ψ ⊢ᵤₛ R ->
    forall Γ1 Γ2 X0 Y, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
    (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⨟ Ψ ⊢ᵤₛ (subst_bskl_in_uskl (uskl_var_f Y) X0 R).
Proof.
  intros Ψ Γ R H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst.
  - apply d_wf_uskl__unit.
  - simpl. match goal with |- context [ if ?b then _ else _ ] => destruct b end.
    + apply d_wf_uskl__var. right. simpl_env. auto.
    + apply d_wf_uskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right; analyze_binds Hb ].
  - simpl. apply d_wf_uskl__arrow; [ eapply IHd_wf_uskl1 | eapply IHd_wf_uskl2 ]; eauto.
  - simpl. apply d_wf_uskl__all_syn
      with (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` {{X0}} `union` {{Y}}).
    intros Z HZ. rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_var_f); try fsetdec.
    eapply (H0 Z ltac:(fsetdec) Γ1 Γ2 X0 Y); [ reflexivity | fsetdec ].
  - simpl. apply d_wf_uskl__all_etag
      with (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` {{X0}} `union` {{Y}}).
    intros Z HZ. rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_var_f); try fsetdec.
    eapply (H0 Z ltac:(fsetdec) Γ1 Γ2 X0 Y); [ reflexivity | fsetdec ].
  - apply d_wf_uskl__hole.
  - simpl. apply d_wf_uskl__tophole;
      [ apply guarded_uskl_subst_var; assumption | eapply IHd_wf_uskl; eauto ].
  - apply d_wf_uskl__holeg.
  - simpl. apply d_wf_uskl__topholeg;
      [ apply guarded_uskl_subst_var; assumption | eapply IHd_wf_uskl; eauto ].
Qed.

Lemma d_pat_consis_rename_tvar : forall Δ Γ R Q,
    Δ ⨟ Γ ⊨ₛ R ≈ Q ->
    forall Γ1 Γ2 X0 Y, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
    Δ ⨟ (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊨ₛ
      (subst_bskl_in_uskl (uskl_var_f Y) X0 R) ≈ (subst_bskl_in_bskl (bskl_var_f Y) X0 Q).
Proof.
  intros Δ Γ R Q H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst.
  - apply d_pat_consis__unit; (assumption || fsetdec).
  - simpl. match goal with |- context [ if ?b then _ else _ ] => destruct b end.
    + apply d_pat_consis__var; [ (assumption || fsetdec) | simpl_env; auto ].
    + apply d_pat_consis__var; [ (assumption || fsetdec)
        | match goal with Hb : binds _ _ (_ ++ _ ~ dbind_tvar ++ _) |- _ => analyze_binds Hb end ].
  - simpl. eapply d_pat_consis__arrow;
      [ eapply (IHd_pat_consis1 Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr ]
      | eapply (IHd_pat_consis2 Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr ]
      | (eassumption || fsetdec) ].
  - simpl. apply d_pat_consis__forall_inh_tagged
      with (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` {{X0}} `union` {{Y}}) (Ψ0 := Ψ0).
    2: assumption.
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_var_f); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_var_f); try fsetdec.
    exact (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ2 X0 Y ltac:(simpl_env; reflexivity) ltac:(simpl_env in *; fsetdec)).
  - simpl. apply d_pat_consis__forall_inh_untagged
      with (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` {{X0}} `union` {{Y}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_var_f); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_var_f); try fsetdec.
    exact (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ2 X0 Y ltac:(simpl_env; reflexivity) ltac:(simpl_env in *; fsetdec)).
  - simpl. apply d_pat_consis__forall_syn_tagged
      with (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` {{X0}} `union` {{Y}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_var_f); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_var_f); try fsetdec.
    exact (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ2 X0 Y ltac:(simpl_env; reflexivity) ltac:(simpl_env in *; fsetdec)).
  - simpl. apply d_pat_consis__forall_syn
      with (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` {{X0}} `union` {{Y}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_var_f); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_var_f); try fsetdec.
    exact (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ2 X0 Y ltac:(simpl_env; reflexivity) ltac:(simpl_env in *; fsetdec)).
  - apply d_pat_consis__ghostg; (assumption || fsetdec).
  - simpl. apply d_pat_consis__topholeg with (Ψ0 := Ψ0);
      [ eapply (IHd_pat_consis Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr ] | eassumption ].
  - simpl. rewrite pskl_to_bskl_inh_subst_var.
    apply d_pat_consis__hole; [ (assumption || fsetdec)
      | eapply d_wf_pskl_rename_tvar; [ eassumption | reflexivity | exact Hfr ] ].
  - simpl. apply d_pat_consis__tophole.
    eapply (IHd_pat_consis Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr ].
  - simpl. apply d_pat_consis__tophole_inh
      with (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` {{X0}} `union` {{Y}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_var_f); try fsetdec.
    exact (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ2 X0 Y
             ltac:(simpl_env; reflexivity) ltac:(simpl_env in *; fsetdec)).
  - simpl. apply d_pat_consis__tophole_drop.
    eapply (IHd_pat_consis Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr ].
Qed.

Lemma d_pat_sub_rename_tvar : forall Δ Γ m R Q,
    Δ ⨟ Γ ⊢ₛ[ m ] R ⊑ Q ->
    forall Γ1 Γ2 X0 Y, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
    Δ ⨟ (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊢ₛ[ m ]
      (subst_bskl_in_uskl (uskl_var_f Y) X0 R) ⊑ (subst_bskl_in_bskl (bskl_var_f Y) X0 Q).
Proof.
  intros Δ Γ m R Q H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst.
  - apply d_pat_sub__infer;
      [ (assumption || fsetdec) | eapply d_pat_consis_rename_tvar; eauto | apply is_sskl_subst_var; assumption ].
  - simpl. apply d_pat_sub__univ_ghost_r;
      [ (assumption || fsetdec) | apply guarded_uskl_subst_var; assumption
      | apply guarded_bskl_subst_var; assumption | apply is_sskl_subst_var; assumption
      | eapply d_pat_consis_rename_tvar; eauto ].
  - simpl. eapply d_pat_sub__arg;
      [ eapply d_pat_consis_rename_tvar; eauto
      | eapply (IHd_pat_sub Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr ]
      | (eassumption || fsetdec) ].
  - simpl. eapply d_pat_sub__forall_l_tagged with (psi := subst_bskl_in_uskl (uskl_var_f Y) X0 psi);
      [ assumption | eassumption | apply d_tags_skl_subst_var; assumption
      | eapply d_wf_uskl_rename_tvar; eauto | apply is_tskl_subst_var; assumption | ].
    rewrite <- subst_bskl_in_uskl_open_uskl_wrt_uskl; try (apply lc_uskl_var_f).
    eapply (IHd_pat_sub Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr ].
  - simpl. eapply d_pat_sub__forall_l_untagged with (psi := subst_bskl_in_uskl (uskl_var_f Y) X0 psi);
      [ assumption | eassumption | apply d_tags_skl_subst_var; assumption
      | eapply d_wf_uskl_rename_tvar; eauto | apply is_tskl_subst_var; assumption | ].
    rewrite <- subst_bskl_in_uskl_open_uskl_wrt_uskl; try (apply lc_uskl_var_f).
    eapply (IHd_pat_sub Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr ].
  - simpl. rewrite pskl_to_bskl_inh_subst_var. apply d_pat_sub__ghost;
      [ (assumption || fsetdec) | eapply d_wf_pskl_rename_tvar; [ eassumption | reflexivity | exact Hfr ] ].
  - simpl. apply d_pat_sub__univ_ghost_l;
      [ assumption | eapply (IHd_pat_sub Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr ] ].
  - apply d_pat_sub__ghostg; (assumption || fsetdec).
  - simpl. apply d_pat_sub__univ_ghost_lg;
      [ assumption | eapply (IHd_pat_sub Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr ] ].
Qed.

(* context-map for the tvar-rename of [d_pat] / [d_typing] (relabel X0↦Y in
   the bindings AFTER X0; bindings before X0 are X0-clean). *)
Definition subst_var_dbind (X0 Y : atom) (d : dbind) : dbind :=
  match d with
  | dbind_tvar => dbind_tvar
  | dbind_typ A => dbind_typ (subst_ptyp_in_ptyp (ptyp_var_f Y) X0 A)
  | dbind_skl P => dbind_skl (subst_pskl_in_pskl (pskl_var_f Y) X0 P)
  end.

Lemma map_subst_var_dbind_cons : forall x d X0 Y Γ1,
    (x ~ subst_var_dbind X0 Y d) ++ map (subst_var_dbind X0 Y) Γ1
    = map (subst_var_dbind X0 Y) ((x ~ d) ++ Γ1).
Proof. intros. simpl_env. reflexivity. Qed.

Lemma same_tvar_map_subst_var : forall X0 Y Γ1 Γ2,
    same_tvar (Γ1 ++ Γ2) (map (subst_var_dbind X0 Y) Γ1 ++ Γ2).
Proof.
  intros X0 Y Γ1 Γ2 X. split; intro Hb; apply binds_app_iff in Hb; apply binds_app_iff;
    destruct Hb as [Hb | Hb].
  - left. change dbind_tvar with (subst_var_dbind X0 Y dbind_tvar). apply binds_map_2. assumption.
  - right. assumption.
  - left. apply binds_map_3 in Hb as [b [Heq Hb']]. destruct b; inversion Heq; subst. assumption.
  - right. assumption.
Qed.

Lemma binds_typ_subst_var_dbind : forall x A X0 Y Γ1 Γ2,
    binds x (dbind_typ A) (Γ1 ++ Γ2) -> tvar_clean X0 Γ2 ->
    binds x (dbind_typ (subst_ptyp_in_ptyp (ptyp_var_f Y) X0 A))
          (map (subst_var_dbind X0 Y) Γ1 ++ (Y ~ dbind_tvar) ++ Γ2).
Proof.
  intros x A X0 Y Γ1 Γ2 Hb [Ht Hs].
  apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
  - apply binds_app_2.
    change (dbind_typ (subst_ptyp_in_ptyp (ptyp_var_f Y) X0 A))
      with (subst_var_dbind X0 Y (dbind_typ A)). apply binds_map_2. assumption.
  - apply binds_app_3. apply binds_app_3.
    rewrite (subst_ptyp_in_ptyp_fresh_eq _ _ _ (Ht _ _ Hb)). assumption.
Qed.

Lemma binds_skl_subst_var_dbind : forall x P X0 Y Γ1 Γ2,
    binds x (dbind_skl P) (Γ1 ++ Γ2) -> tvar_clean X0 Γ2 ->
    binds x (dbind_skl (subst_pskl_in_pskl (pskl_var_f Y) X0 P))
          (map (subst_var_dbind X0 Y) Γ1 ++ (Y ~ dbind_tvar) ++ Γ2).
Proof.
  intros x P X0 Y Γ1 Γ2 Hb [Ht Hs].
  apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
  - apply binds_app_2.
    change (dbind_skl (subst_pskl_in_pskl (pskl_var_f Y) X0 P))
      with (subst_var_dbind X0 Y (dbind_skl P)). apply binds_map_2. assumption.
  - apply binds_app_3. apply binds_app_3.
    rewrite (subst_pskl_in_pskl_fresh_eq _ _ _ (Hs _ _ Hb)). assumption.
Qed.

(** Well-formed skeleton scoping ([ptyp] analogue [d_wf_ptyp_ftvar]). *)
Lemma d_wf_pskl_ftvar : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P ->
    forall X, X `in` ftvar_in_pskl P -> List.In X Ψ \/ binds X dbind_tvar Γ.
Proof.
  intros Ψ Γ P H. induction H; intros Y HY; simpl in HY.
  - fsetdec.
  - apply AtomSetImpl.singleton_1 in HY. subst. assumption.
  - apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY];
      [ apply IHd_wf_pskl1 | apply IHd_wf_pskl2 ]; assumption.
  - pick fresh X for (L `union` ftvar_in_pskl P `union` dom Γ `union` singleton Y).
    assert (HYo : Y `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f X)))
      by (eapply ftvar_in_pskl_open_pskl_wrt_pskl_lower; eassumption).
    specialize (H0 X ltac:(auto) Y HYo).
    destruct H0 as [HIn | HB]; [ | right; assumption ].
    simpl in HIn. destruct HIn as [Heq | HIn]; [ subst Y; solve [ exfalso; fsetdec ] | left; assumption ].
  - fsetdec.
  - apply IHd_wf_pskl in HY. destruct HY as [HIn | HB]; [ inversion HIn | right; exact HB ].
Qed.

(** On a well-formed context with [X ∉ dom], the tvar-substitution [X := W] is
    the identity (no binding's type references an unbound [X]).  This is what
    makes [ctx_refines_tw_rename_tvar] leave the refined bindings untouched. *)
Lemma map_subst_var_dbind_wf : forall Γ,
    d_wf_denv Γ -> forall X W, X `notin` dom Γ ->
    map (subst_var_dbind X W) Γ = Γ.
Proof.
  intros Γ H. induction H; intros X0 W Hnotin; simpl in *.
  - reflexivity.
  - rewrite IHd_wf_denv by fsetdec. reflexivity.
  - rewrite IHd_wf_denv by fsetdec. f_equal. f_equal. simpl. f_equal.
    apply subst_ptyp_in_ptyp_fresh_eq. intro c.
    assert (Hb : binds X0 dbind_tvar Γ) by (eapply d_wf_ptyp_ftvar; [ eassumption | exact c ]).
    apply binds_In in Hb. fsetdec.
  - rewrite IHd_wf_denv by fsetdec. f_equal. f_equal. simpl. f_equal.
    apply subst_pskl_in_pskl_fresh_eq. intro c.
    assert (Hb : List.In X0 (@nil atom) \/ binds X0 dbind_tvar Γ)
      by (eapply d_wf_pskl_ftvar; [ eassumption | exact c ]).
    destruct Hb as [Hc | Hc]; [ inversion Hc | apply binds_In in Hc; fsetdec ].
Qed.

(** [ctx_refines_tw] survives renaming a [ctx_refines_tw]-inserted tvar [X→W]:
    the refined bindings come from [Γ'] (wf, [X∉dom Γ']) so the subst leaves them
    fixed ([map_subst_var_dbind_wf]); only the inserted [X]-tvar is relabelled. *)
Lemma ctx_refines_tw_rename_tvar : forall Γ1 Γ' X W Γ2,
    ctx_refines_tw Γ' (Γ1 ++ (X ~ dbind_tvar) ++ Γ2) ->
    d_wf_denv Γ' -> X `notin` dom Γ' ->
    W `notin` dom (Γ1 ++ (X ~ dbind_tvar) ++ Γ2) ->
    ctx_refines_tw Γ' (map (subst_var_dbind X W) Γ1 ++ (W ~ dbind_tvar) ++ Γ2).
Proof.
  induction Γ1 as [ | [z d] Γ1' IH ]; intros Γ' X W Γ2 Hcr Hwf HXΓ' HW; simpl_env in *.
  - (* Γ1 = nil : front is (X ~ tvar) *)
    inversion Hcr as [ Γ'b Γb Hbase | Γ'v Γv Zv Htw | zc d'c dc Γ'c Γ0c Hdr Htw ]; subst.
    + apply ctx_refines_dom in Hbase. exfalso. simpl in Hbase. fsetdec.
    + apply crtw_tvar. assumption.
    + exfalso. simpl in HXΓ'. fsetdec.
  - (* Γ1 = (z ~ d) :: Γ1' : front is (z ~ d), X in the tail *)
    inversion Hcr as [ Γ'b Γb Hbase | Γ'v Γv Zv Htw | zc d'c dc Γ'c Γ0c Hdr Htw ]; subst.
    + apply ctx_refines_dom in Hbase. exfalso.
      assert (X `in` dom Γ') by (rewrite Hbase; simpl_env; fsetdec). fsetdec.
    + simpl. apply crtw_tvar.
      eapply IH; [ exact Htw | exact Hwf | exact HXΓ' | simpl_env in *; fsetdec ].
    + assert (Hwf0 : d_wf_denv Γ'c) by (inversion Hwf; assumption).
      assert (HXc : X `notin` dom Γ'c) by (simpl in HXΓ'; fsetdec).
      simpl. apply crtw_cons.
      * destruct Hdr as [ dd | AA | AA ].
        -- (* dbr_refl: source = target = dd (a Γ' binding, so X-fixed) *)
           assert (Hsd : subst_var_dbind X W dd = dd).
           { pose proof (@map_subst_var_dbind_wf ((z ~ dd) ++ Γ'c) Hwf X W HXΓ') as Hm.
             simpl in Hm. congruence. }
           rewrite Hsd. apply dbr_refl.
        -- (* dbr_typ_hole: source [□], target [typ AA] — [□] refines anything *)
           simpl. apply dbr_typ_hole.
        -- (* dbr_typ_skl: source [skl (ptyp_to_pskl AA)], target [typ AA].  [AA]
              is X-free (the source [skl] binding is wf in Γ', X∉dom Γ'), so the
              [X→W] subst on the target is the identity and [dbr_typ_skl] applies. *)
           assert (HXAA : X `notin` ftvar_in_ptyp AA).
           { intro Hin. rewrite <- ftvar_ptyp_to_pskl in Hin.
             assert (Hwfp : d_wf_pskl Γ'c nil (ptyp_to_pskl AA))
               by (inversion Hwf; subst; assumption).
             apply (d_wf_pskl_ftvar Hwfp) in Hin.
             destruct Hin as [ Himp | Hb ];
               [ inversion Himp | apply binds_In in Hb; clear - Hb HXc; fsetdec ]. }
           simpl. rewrite subst_ptyp_in_ptyp_fresh_eq by exact HXAA. apply dbr_typ_skl.
      * eapply IH; [ exact Htw | exact Hwf0 | exact HXc | simpl_env in *; fsetdec ].
Qed.

(** [ctx_refines_tw] only grows the domain (inserts tvars). *)
Lemma ctx_refines_tw_dom_sub : forall Γ' Γ, ctx_refines_tw Γ' Γ -> dom Γ' [<=] dom Γ.
Proof.
  intros Γ' Γ H. induction H; simpl.
  - apply ctx_refines_dom in H. fsetdec.
  - fsetdec.
  - fsetdec.
Qed.

(** Relabel a term-variable name [y→x] in a context (types are unchanged — term
    vars never occur in types). *)
Definition rename_var_denv (y x : atom) (Γ : list (atom * dbind)) :=
  List.map (fun p => (if fst p == y then x else fst p, snd p)) Γ.

(** A non-[y] binding survives the term-var relabel. *)
Lemma binds_rename_var : forall z d y xt Γ,
    binds z d Γ -> z <> y -> binds z d (rename_var_denv y xt Γ).
Proof.
  intros z d y xt Γ Hb Hzy. unfold rename_var_denv, binds in *.
  apply (List.in_map (fun p => (if fst p == y then xt else fst p, snd p))) in Hb.
  simpl in Hb. destruct (z == y) as [ Heq | _ ]; [ contradiction | exact Hb ].
Qed.

(** [d_wf_ptyp]/[d_wf_pskl] survive the term-var relabel when [y] is not free in
    the type (which holds when [y] is bound as a non-tvar — types reference only
    tvars). *)
Lemma d_wf_ptyp_relabel_var : forall Γ A,
    d_wf_ptyp Γ A -> forall y xt, y `notin` ftvar_in_ptyp A ->
    d_wf_ptyp (rename_var_denv y xt Γ) A.
Proof.
  intros Γ A H. induction H; intros y0 xt Hy; simpl in Hy.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. apply binds_rename_var; [ assumption | fsetdec ].
  - apply d_wf_ptyp__arrow; [ apply IHd_wf_ptyp1 | apply IHd_wf_ptyp2 ]; fsetdec.
  - apply d_wf_ptyp__all with (L := L `union` {{y0}}). intros X HX.
    replace ((X ~ dbind_tvar) ++ rename_var_denv y0 xt Γ)
      with (rename_var_denv y0 xt ((X ~ dbind_tvar) ++ Γ))
      by (unfold rename_var_denv; simpl; destruct (X == y0); [ fsetdec | reflexivity ]).
    apply H0; [ fsetdec | ].
    intro Hin. apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in Hin. simpl in Hin.
    apply AtomSetImpl.union_1 in Hin. destruct Hin as [Hin | Hin];
      [ apply AtomSetImpl.singleton_1 in Hin; subst; fsetdec | apply Hy; exact Hin ].
Qed.

Lemma d_wf_pskl_relabel_var : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P -> forall y xt, y `notin` ftvar_in_pskl P ->
    (rename_var_denv y xt Γ) ⨟ Ψ ⊢ₚₛ P.
Proof.
  intros Ψ Γ P H. induction H; intros y0 xt Hy; simpl in Hy.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [ HΨ | Hb ]; [ left; assumption | ].
    right. apply binds_rename_var; [ assumption | fsetdec ].
  - apply d_wf_pskl__arrow; [ apply IHd_wf_pskl1 | apply IHd_wf_pskl2 ]; fsetdec.
  - apply d_wf_pskl__all with (L := L `union` {{y0}}). intros X HX.
    replace ((X ~ dbind_tvar) ++ rename_var_denv y0 xt Γ)
      with (rename_var_denv y0 xt ((X ~ dbind_tvar) ++ Γ))
      by (unfold rename_var_denv; simpl; destruct (X == y0); [ fsetdec | reflexivity ]).
    apply H0; [ fsetdec | ].
    intro Hin. apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in Hin. simpl in Hin.
    apply AtomSetImpl.union_1 in Hin. destruct Hin as [Hin | Hin];
      [ apply AtomSetImpl.singleton_1 in Hin; subst; fsetdec | apply Hy; exact Hin ].
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole; [ assumption | apply IHd_wf_pskl; assumption ].
Qed.

(** [ctx_refines_tw] survives relabelling the front bound var [y→x] of [Γ'L]
    (structural: no types touched; [x∉dom Γ] avoids a new clash, [uniq] gives the
    inserted tvars ≠ [y]). *)
Lemma ctx_refines_tw_rename_var : forall Γ'L Γ,
    ctx_refines_tw Γ'L Γ -> forall y dr Γ'r, Γ'L = (y ~ dr) ++ Γ'r ->
    uniq Γ -> forall xt, xt `notin` dom Γ ->
    ctx_refines_tw ((xt ~ dr) ++ Γ'r) (rename_var_denv y xt Γ).
Proof.
  intros Γ'L Γ H. induction H; intros y dr Γ'r Heq Huniq xt Hx; subst.
  - (* crtw_base : ctx_refines ((y~dr)::Γ'r) Γ *)
    inversion H as [ | z0 d0' d0 Γ0' Γ0 Hdr Hcr0 Heqa Heqb ]; subst.
    assert (Hyd : y `notin` dom Γ0) by (inversion Huniq; subst; assumption).
    unfold rename_var_denv. simpl. destruct (y == y) as [ _ | n ]; [ | contradiction n; reflexivity ].
    replace (List.map (fun p => (if fst p == y then xt else fst p, snd p)) Γ0) with Γ0.
    + apply crtw_base. apply ctxr_cons; [ exact Hdr | exact Hcr0 ].
    + clear - Hyd. induction Γ0 as [ | [w dw] Γ0' IHg ]; simpl; [ reflexivity | ].
      destruct (w == y); [ subst; simpl in Hyd; fsetdec | ].
      rewrite <- IHg by (simpl in Hyd; fsetdec). reflexivity.
  - (* crtw_tvar : Γ = (X~tvar)::Γ0 *)
    assert (HZy : X <> y).
    { intro; subst X. inversion Huniq; subst.
      apply ctx_refines_tw_dom_sub in H. simpl in H. fsetdec. }
    unfold rename_var_denv. simpl. destruct (X == y) as [ e | _ ]; [ contradiction | ].
    apply crtw_tvar. eapply IHctx_refines_tw;
      [ reflexivity | inversion Huniq; subst; assumption | simpl in Hx; fsetdec ].
  - (* crtw_cons : ((y~dr)::Γ'r) = ((x0~d')::Γ'0) ⇒ x0=y, front of Γ is (y~d) *)
    injection Heq as Hy Hd Hreq. subst.
    assert (Hyd : y `notin` dom Γ) by (inversion Huniq; subst; assumption).
    unfold rename_var_denv. simpl. destruct (y == y) as [ _ | n ]; [ | contradiction n; reflexivity ].
    replace (List.map (fun p => (if fst p == y then xt else fst p, snd p)) Γ) with Γ.
    + apply crtw_cons; [ assumption | assumption ].
    + clear - Hyd. induction Γ as [ | [w dw] Γ0' IHg ]; simpl; [ reflexivity | ].
      destruct (w == y); [ subst; simpl in Hyd; fsetdec | ].
      rewrite <- IHg by (simpl in Hyd; fsetdec). reflexivity.
Qed.

Lemma dom_rename_var_sub : forall y xt Γ,
    dom (rename_var_denv y xt Γ) [<=] dom Γ `union` {{xt}}.
Proof.
  intros y xt Γ. induction Γ as [ | [w dw] Γ' IH ]; unfold rename_var_denv in *; simpl;
    [ fsetdec | destruct (w == y); simpl; fsetdec ].
Qed.

Lemma rename_var_notin : forall y xt Γ, y `notin` dom Γ -> rename_var_denv y xt Γ = Γ.
Proof.
  intros y xt Γ. induction Γ as [ | [w dw] Γ' IH ]; intros Hy; [ reflexivity | ].
  unfold rename_var_denv in *. simpl in *.
  destruct (w == y) as [ Heq | Hne ]; [ subst; fsetdec | ].
  f_equal. apply IH. fsetdec.
Qed.

Lemma dom_rename_var_notin : forall y xt Γ,
    y `notin` dom Γ -> dom (rename_var_denv y xt Γ) [=] dom Γ.
Proof. intros y xt Γ H. rewrite (@rename_var_notin y xt Γ H). reflexivity. Qed.

(** [d_wf_denv] survives relabelling a non-tvar bound var [y0→xt] ([xt] fresh):
    types reference only tvars, so they are untouched ([d_wf_*_relabel_var]). *)
Lemma d_wf_denv_rename_var : forall Γ,
    d_wf_denv Γ -> forall y0 xt, xt `notin` dom Γ -> ~ binds y0 dbind_tvar Γ ->
    d_wf_denv (rename_var_denv y0 xt Γ).
Proof.
  intros Γ H. induction H; intros y0 xt Hx Hyt; unfold rename_var_denv in *; simpl in *.
  - apply d_wf_denv__nil.
  - (* tvar *)
    destruct (X == y0) as [ Heq | Hne ].
    + subst. exfalso. apply Hyt. unfold binds. simpl. left. reflexivity.
    + apply d_wf_denv__tvar.
      * apply IHd_wf_denv; [ fsetdec | intro Hb; apply Hyt; unfold binds; simpl; right; exact Hb ].
      * pose proof (dom_rename_var_sub y0 xt Γ) as Hsub. fsetdec.
  - (* typ A *)
    assert (Hyf : y0 `notin` ftvar_in_ptyp A).
    { intro c. apply Hyt. unfold binds; simpl; right. eapply d_wf_ptyp_ftvar; [ eassumption | exact c ]. }
    apply d_wf_denv__typ.
    + apply IHd_wf_denv; [ fsetdec | intro Hb; apply Hyt; unfold binds; simpl; right; exact Hb ].
    + destruct (x == y0) as [ Heqx | Hnex ];
      [ subst; pose proof (@dom_rename_var_notin y0 xt Γ ltac:(assumption)) as Hrnd; fsetdec
      | pose proof (dom_rename_var_sub y0 xt Γ) as Hsub; fsetdec ].
    + apply d_wf_ptyp_relabel_var; assumption.
  - (* skl P *)
    assert (Hyf : y0 `notin` ftvar_in_pskl P).
    { intro c. assert (Hdisj : List.In y0 (@nil atom) \/ binds y0 dbind_tvar Γ)
        by (eapply d_wf_pskl_ftvar; [ eassumption | exact c ]).
      destruct Hdisj as [Hc | Hc]; [ inversion Hc | apply Hyt; unfold binds; simpl; right; exact Hc ]. }
    apply d_wf_denv__skl.
    + apply IHd_wf_denv; [ fsetdec | intro Hb; apply Hyt; unfold binds; simpl; right; exact Hb ].
    + destruct (x == y0) as [ Heqx | Hnex ];
      [ subst; pose proof (@dom_rename_var_notin y0 xt Γ ltac:(assumption)) as Hrnd; fsetdec
      | pose proof (dom_rename_var_sub y0 xt Γ) as Hsub; fsetdec ].
    + apply d_wf_pskl_relabel_var; assumption.
Qed.

Lemma d_wf_ptyp_rename_tvar : forall Γ A,
    Γ ⊢ₚ A -> forall Γ1 Γ2 X0 Y, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
    (map (subst_var_dbind X0 Y) Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊢ₚ
      (subst_ptyp_in_ptyp (ptyp_var_f Y) X0 A).
Proof.
  intros Γ A H Γ1 Γ2 X0 Y Heq Hfr. subst Γ.
  apply d_wf_ptyp_of_lc_ftvar.
  - apply subst_ptyp_in_ptyp_lc_ptyp; [ eapply d_wf_ptyp_lc; eassumption | apply lc_ptyp_var_f ].
  - intros Z HZ.
    pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper A (ptyp_var_f Y) X0) as Hup. simpl in Hup.
    destruct (Z == Y).
    + subst Z. apply binds_app_3. simpl_env. auto.
    + assert (HZA : Z `in` ftvar_in_ptyp A) by (clear - HZ Hup n; fsetdec).
      assert (HZne : Z <> X0) by (clear - HZ Hup n; fsetdec).
      assert (Hbnd : binds Z dbind_tvar (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2))
        by (eapply d_wf_ptyp_ftvar; eassumption).
      apply binds_remove_mid in Hbnd; [ | exact HZne ].
      apply binds_app_iff in Hbnd. destruct Hbnd as [Hb | Hb].
      * apply binds_app_2. change dbind_tvar with (subst_var_dbind X0 Y dbind_tvar).
        apply binds_map_2. assumption.
      * apply binds_app_3. apply binds_app_3. assumption.
Qed.

Lemma d_pat_rename_tvar : forall m Γ e Q,
    Γ ⊢[ m ] e ⇨ Q ->
    forall Γ1 Γ2 X0 Y, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) -> tvar_clean X0 Γ2 ->
    (map (subst_var_dbind X0 Y) Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊢[ m ]
      (subst_ptyp_in_exp (ptyp_var_f Y) X0 e) ⇨ (subst_bskl_in_bskl (bskl_var_f Y) X0 Q).
Proof.
  intros m Γ e Q H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr Hclean; subst; simpl.
  - apply d_pat__unit.
  - rewrite pskl_to_bskl_syn_subst_var.
    destruct d as [ | A | P0 ]; simpl in H0.
    + discriminate.
    + injection H0 as H0. subst P. rewrite ptyp_to_pskl_subst_var.
      assert (Hb : binds x (dbind_typ A) (Γ1 ++ Γ2)) by (analyze_binds H).
      eapply d_pat__var; [ apply binds_typ_subst_var_dbind; eassumption | reflexivity ].
    + injection H0 as H0. subst P.
      assert (Hb : binds x (dbind_skl P0) (Γ1 ++ Γ2)) by (analyze_binds H).
      eapply d_pat__var; [ apply binds_skl_subst_var_dbind; eassumption | reflexivity ].
  - rewrite pskl_to_bskl_syn_subst_var. rewrite ptyp_to_pskl_subst_var.
    apply d_pat__anno. eapply d_wf_ptyp_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
  - eapply d_pat__sub.
    + apply is_base_term_subst_ptyp. assumption.
    + rewrite <- pskl_to_bskl_syn_subst_var.
      eapply (IHd_pat Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr | exact Hclean ].
    + rewrite <- pskl_to_bskl_syn_subst_var. rewrite <- bskl_to_uskl_subst_var.
      eapply d_pat_sub_same_tvar;
        [ eapply d_pat_sub_rename_tvar; [ exact H1 | reflexivity | exact Hfr ]
        | apply same_tvar_map_subst_var ].
  - rewrite pskl_to_bskl_syn_subst_var.
    apply d_pat__freeze. rewrite <- pskl_to_bskl_syn_subst_var.
    eapply (IHd_pat Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr | exact Hclean ].
  - rewrite pskl_to_bskl_inh_subst_var.
    apply d_pat__abs with (L := L `union` {{X0}} `union` {{Y}} `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2))
      (P := subst_pskl_in_pskl (pskl_var_f Y) X0 P).
    + assumption.
    + eapply d_wf_pskl_same_tvar;
        [ eapply d_wf_pskl_rename_tvar; [ exact H0 | reflexivity | exact Hfr ]
        | apply same_tvar_map_subst_var ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_var_f | fsetdec ]).
      rewrite_env (((x ~ subst_var_dbind X0 Y (dbind_skl P)) ++ map (subst_var_dbind X0 Y) Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
      rewrite map_subst_var_dbind_cons.
      eapply (H2 x ltac:(fsetdec) ((x ~ dbind_skl P) ++ Γ1) Γ2 X0 Y);
        [ simpl_env; reflexivity | simpl_env in *; fsetdec | exact Hclean ].
  - rewrite btyp_to_bskl_subst_var.
    eapply d_pat__abs_anno with (L := L `union` {{X0}} `union` {{Y}} `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2)).
    + assumption.
    + eapply d_wf_ptyp_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + symmetry. apply btyp_to_ptyp_subst_var.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_var_f | fsetdec ]).
      rewrite_env (((x ~ subst_var_dbind X0 Y (dbind_typ (btyp_to_ptyp B))) ++ map (subst_var_dbind X0 Y) Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
      rewrite map_subst_var_dbind_cons.
      eapply (H3 x ltac:(fsetdec) ((x ~ dbind_typ (btyp_to_ptyp B)) ++ Γ1) Γ2 X0 Y);
        [ simpl_env; reflexivity | simpl_env in *; fsetdec | exact Hclean ].
  - eapply d_pat__app.
    + rewrite <- pskl_to_bskl_syn_subst_var.
      eapply (IHd_pat1 Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr | exact Hclean ].
    + rewrite <- pskl_to_bskl_inh_subst_var.
      eapply d_refine_syn_same_tvar;
        [ eapply d_refine_syn_rename_tvar; [ exact H0 | reflexivity | exact Hfr ]
        | apply same_tvar_map_subst_var ].
    + change (bskl_arrow (subst_bskl_in_bskl (bskl_var_f Y) X0 Q1) (subst_bskl_in_bskl (bskl_var_f Y) X0 Q2))
        with (subst_bskl_in_bskl (bskl_var_f Y) X0 (bskl_arrow Q1 Q2)).
      eapply (IHd_pat2 Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr | exact Hclean ].
  - rewrite pskl_to_bskl_syn_subst_var.
    apply d_pat__abs_check with (L := L `union` {{X0}} `union` {{Y}} `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2))
      (P := subst_pskl_in_pskl (pskl_var_f Y) X0 P).
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_var_f | fsetdec ]).
    rewrite_env (((x ~ subst_var_dbind X0 Y (dbind_skl pskl_hole)) ++ map (subst_var_dbind X0 Y) Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    rewrite map_subst_var_dbind_cons.
    rewrite <- pskl_to_bskl_syn_subst_var.
    eapply (H0 x ltac:(fsetdec) ((x ~ dbind_skl pskl_hole) ++ Γ1) Γ2 X0 Y);
      [ simpl_env; reflexivity | simpl_env in *; fsetdec | exact Hclean ].
  - rewrite btyp_to_bskl_subst_var. rewrite ptyp_to_btyp_syn_subst_var.
    rewrite pskl_to_bskl_syn_subst_var.
    apply d_pat__abs_anno_check with (L := L `union` {{X0}} `union` {{Y}} `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2))
      (A := subst_ptyp_in_ptyp (ptyp_var_f Y) X0 A) (P := subst_pskl_in_pskl (pskl_var_f Y) X0 P).
    + eapply d_wf_ptyp_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_var_f | fsetdec ]).
      rewrite_env (((x ~ subst_var_dbind X0 Y (dbind_typ A)) ++ map (subst_var_dbind X0 Y) Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
      rewrite map_subst_var_dbind_cons.
      rewrite <- pskl_to_bskl_syn_subst_var.
      eapply (H1 x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ1) Γ2 X0 Y);
        [ simpl_env; reflexivity | simpl_env in *; fsetdec | exact Hclean ].
Qed.

(** Term typing is closed under tvar renaming [X0 -> Y].  Mirrors
    [d_pat_rename_tvar]: types/skeletons carry the renamed tvar (so binders are
    mapped through [subst_var_dbind]), and the [sub]/[app] premises are
    transported by [d_sub_rename_tvar] / [d_refine_syn_rename_tvar] /
    [d_pat_rename_tvar] (re-based onto the mapped Γ1 via the [same_tvar]
    congruences, since those judgments ignore term bindings). *)
Lemma d_typing_rename_tvar : forall m Γ e B,
    Γ ⊢[ m ] e ⦂ B ->
    forall Γ1 Γ2 X0 Y, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) -> tvar_clean X0 Γ2 ->
    (map (subst_var_dbind X0 Y) Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊢[ m ]
      (subst_ptyp_in_exp (ptyp_var_f Y) X0 e) ⦂ (subst_btyp_in_btyp (btyp_var_f Y) X0 B).
Proof.
  intros m Γ e B H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr Hclean; subst; simpl.
  - apply d_typing__unit.
  - rewrite ptyp_to_btyp_syn_subst_var. apply d_typing__var.
    assert (Hb : binds x (dbind_typ A) (Γ1 ++ Γ2)) by (analyze_binds H).
    apply binds_typ_subst_var_dbind; [ exact Hb | exact Hclean ].
  - rewrite ptyp_to_btyp_syn_subst_var. apply d_typing__anno.
    rewrite <- ptyp_to_btyp_inh_subst_var.
    eapply (IHd_typing Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr | exact Hclean ].
  - eapply d_typing__sub;
      [ apply is_base_term_subst_ptyp; assumption
      | rewrite <- ptyp_to_btyp_syn_subst_var;
        eapply (IHd_typing Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr | exact Hclean ]
      | rewrite <- ptyp_to_utyp_syn_subst_var;
        eapply d_sub_same_tvar;
          [ eapply d_sub_rename_tvar; [ eassumption | reflexivity | exact Hfr ]
          | apply same_tvar_map_subst_var ] ].
  - rewrite ptyp_to_btyp_inh_subst_var. apply d_typing__freeze.
    rewrite <- ptyp_to_btyp_syn_subst_var.
    eapply (IHd_typing Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr | exact Hclean ].
  - rewrite ptyp_to_btyp_inh_subst_var.
    apply d_typing__forall with
      (L := L `union` {{X0}} `union` {{Y}} `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2))
      (A := subst_ptyp_in_ptyp (ptyp_var_f Y) X0 A).
    + apply is_value_subst_ptyp. assumption.
    + intros Z HZ.
      rewrite <- ptyp_to_btyp_inh_subst_var.
      rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_var_f | fsetdec ]).
      rewrite_env (((Z ~ subst_var_dbind X0 Y dbind_tvar) ++ map (subst_var_dbind X0 Y) Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
      rewrite map_subst_var_dbind_cons.
      match goal with IH : forall _ : atom, _ |- _ =>
        eapply (IH Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ2 X0 Y) end;
        [ simpl_env; reflexivity | simpl_env in *; fsetdec | exact Hclean ].
  - rewrite ptyp_to_btyp_inh_subst_var.
    apply d_typing__abs with
      (L := L `union` {{X0}} `union` {{Y}} `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2))
      (A := subst_ptyp_in_ptyp (ptyp_var_f Y) X0 A) (B := subst_btyp_in_btyp (btyp_var_f Y) X0 B).
    + eapply d_wf_ptyp_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + rewrite <- ptyp_to_btyp_inh_subst_var.
      apply mod_comp_ty_rename_tvar with (B := btyp_arrow (ptyp_to_btyp_inh A) B). assumption.
    + intros z Hz.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_var_f | fsetdec ]).
      rewrite_env (((z ~ subst_var_dbind X0 Y (dbind_typ A)) ++ map (subst_var_dbind X0 Y) Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
      rewrite map_subst_var_dbind_cons.
      match goal with IH : forall _ : atom, _ |- _ =>
        eapply (IH z ltac:(fsetdec) ((z ~ dbind_typ A) ++ Γ1) Γ2 X0 Y) end;
        [ simpl_env; reflexivity | simpl_env in *; fsetdec | exact Hclean ].
  - (* abs_anno: [subst] consumed [btyp_to_ptyp B1 = A], so [A] is now [btyp_to_ptyp B1]. *)
    apply d_typing__abs_anno with
      (L := L `union` {{X0}} `union` {{Y}} `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2))
      (A := subst_ptyp_in_ptyp (ptyp_var_f Y) X0 (btyp_to_ptyp B1))
      (B1 := subst_btyp_in_btyp (btyp_var_f Y) X0 B1) (B2 := subst_btyp_in_btyp (btyp_var_f Y) X0 B2).
    + eapply d_wf_ptyp_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + symmetry. apply btyp_to_ptyp_subst_var.
    + apply mod_comp_ty_rename_tvar with (B := btyp_arrow B1 B2). assumption.
    + intros z Hz.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_var_f | fsetdec ]).
      rewrite_env (((z ~ subst_var_dbind X0 Y (dbind_typ (btyp_to_ptyp B1))) ++ map (subst_var_dbind X0 Y) Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
      rewrite map_subst_var_dbind_cons.
      match goal with IH : forall _ : atom, _ |- _ =>
        eapply (IH z ltac:(fsetdec) ((z ~ dbind_typ (btyp_to_ptyp B1)) ++ Γ1) Γ2 X0 Y) end;
        [ simpl_env; reflexivity | simpl_env in *; fsetdec | exact Hclean ].
  - apply d_typing__app with
      (P := subst_pskl_in_pskl (pskl_var_f Y) X0 P)
      (B1 := subst_btyp_in_btyp (btyp_var_f Y) X0 B1)
      (B2 := subst_btyp_in_btyp (btyp_var_f Y) X0 B2).
    + rewrite <- pskl_to_bskl_syn_subst_var.
      eapply d_pat_rename_tvar; [ eassumption | reflexivity | exact Hfr | exact Hclean ].
    + rewrite <- pskl_to_bskl_inh_subst_var. rewrite <- btyp_to_bskl_subst_var.
      eapply d_refine_syn_same_tvar;
        [ eapply d_refine_syn_rename_tvar; [ eassumption | reflexivity | exact Hfr ]
        | apply same_tvar_map_subst_var ].
    + change (btyp_arrow (subst_btyp_in_btyp (btyp_var_f Y) X0 B1) (subst_btyp_in_btyp (btyp_var_f Y) X0 B2))
        with (subst_btyp_in_btyp (btyp_var_f Y) X0 (btyp_arrow B1 B2)).
      eapply (IHd_typing1 Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr | exact Hclean ].
    + rewrite <- btyp_to_ptyp_subst_var. rewrite <- ptyp_to_btyp_inh_subst_var.
      eapply (IHd_typing2 Γ1 Γ2 X0 Y); [ reflexivity | exact Hfr | exact Hclean ].
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

(** Forward lookup through [ctx_refines_tw] (inserted tvars only add fresh
    names). *)
Lemma ctx_refines_tw_binds_fwd : forall Γ' Γ x d',
    ctx_refines_tw Γ' Γ -> binds x d' Γ' ->
    exists d, binds x d Γ /\ dbind_refines d' d.
Proof.
  intros Γ' Γ x d' H. induction H; intros Hb.
  - eapply ctx_refines_binds_fwd; eauto.
  - destruct (IHctx_refines_tw Hb) as [d [Hbd Hr]].
    exists d. split; [ apply binds_app_3; assumption | assumption ].
  - analyze_binds Hb.
    + exists d. split; [ apply binds_app_iff; left; apply binds_one_iff; auto | assumption ].
    + destruct (IHctx_refines_tw BindsTac) as [d0 [Hbd Hr]].
      exists d0. split; [ apply binds_app_iff; right; assumption | assumption ].
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
    d <> dbind_tvar -> (Γ1 ++ (x ~ d) ++ Γ2) ⨟ Ψ ⊢ₚₛ P -> (Γ1 ++ Γ2) ⨟ Ψ ⊢ₚₛ P.
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

Lemma d_refine_syn_strengthen_nontvar : forall Γ1 x d Γ2 Δi Q P,
    d <> dbind_tvar ->
    (Γ1 ++ (x ~ d) ++ Γ2) ⨟ Δi ⊢ᵣ Q ⊳ P ->
    (Γ1 ++ Γ2) ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ1 x d Γ2 Δi Q P Hd H. remember (Γ1 ++ (x ~ d) ++ Γ2) as Γ eqn:HΓ.
  revert Γ1 HΓ. induction H; intros Γ1 HΓ; subst.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [HI | Hb];
      [ left; assumption | right;
        analyze_binds Hb; try (exfalso; congruence); auto ].
  - apply d_refine_syn__arrow; [ eapply IHd_refine_syn1 | eapply IHd_refine_syn2 ]; eauto.
  - apply d_refine_syn__all with (L := L). intros Y HY. eapply (H0 Y HY Γ1); reflexivity.
  - apply d_refine_syn__hole. eapply d_wf_pskl_strengthen_nontvar; eauto.
  - apply d_refine_syn__tophole_remove. eapply IHd_refine_syn; eauto.
  - apply d_refine_syn__tophole_fill with (L := L). intros Y HY.
    eapply (H0 Y HY ((Y ~ dbind_tvar) ++ Γ1)); simpl_env; reflexivity.
  - apply d_refine_syn__tophole_keep; [ assumption | eapply IHd_refine_syn; eauto ].
Qed.

(** Context-refinement transfer (the safety assembly needs to move a fill /
    skeleton-wf from the concrete checking context [Γt] to the refined
    inference context [Γext]).  Both judgements read [Γ] only through TVAR
    lookups, which [ctx_refines] preserves ([ctx_refines_binds_tvar]). *)
Lemma d_wf_pskl_ctx_refines : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P -> forall Γ', ctx_refines Γ' Γ -> Γ' ⨟ Ψ ⊢ₚₛ P.
Proof.
  intros Ψ Γ P H. induction H; intros Γ' Hcr.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [HΨ | HΓ];
      [ left; assumption | right; eapply ctx_refines_binds_tvar; eauto ].
  - apply d_wf_pskl__arrow; [ apply IHd_wf_pskl1 | apply IHd_wf_pskl2 ]; assumption.
  - apply d_wf_pskl__all with (L := L). intros X HX. apply H0; assumption.
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole; [ assumption | apply IHd_wf_pskl; assumption ].
Qed.

Lemma d_refine_syn_ctx_refines : forall Γ Δi Q P,
    Γ ⨟ Δi ⊢ᵣ Q ⊳ P -> forall Γ', ctx_refines Γ' Γ -> Γ' ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ Δi Q P H. induction H; intros Γ' Hcr.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [HI | HΓ];
      [ left; assumption
      | right; eapply ctx_refines_binds_tvar; eauto ].
  - apply d_refine_syn__arrow; [ apply IHd_refine_syn1 | apply IHd_refine_syn2 ]; assumption.
  - apply d_refine_syn__all with (L := L). intros X HX. apply H0; assumption.
  - apply d_refine_syn__hole. eapply d_wf_pskl_ctx_refines; eauto.
  - apply d_refine_syn__tophole_remove. apply IHd_refine_syn; assumption.
  - apply d_refine_syn__tophole_fill with (L := L). intros X HX.
    apply (H0 X HX ((X ~ dbind_tvar) ++ Γ')). apply ctxr_cons; [ apply dbr_refl | assumption ].
  - apply d_refine_syn__tophole_keep; [ assumption | apply IHd_refine_syn; assumption ].
Qed.

(** Subtyping / consistency / utyp-wf also transfer along [ctx_refines]: they
    read [Γ] only through tvar lookups.  These move the [syn C ⊑ inh A]
    subtyping (extracted from a checking derivation over [Γt]) onto the
    refined fill context [Γext]. *)
Lemma d_wf_utyp_ctx_refines : forall Γ C,
    Γ ⊢ᵤ C -> forall Γ', ctx_refines Γ' Γ -> Γ' ⊢ᵤ C.
Proof.
  intros Γ C H. induction H; intros Γ' Hcr.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var. eapply ctx_refines_binds_tvar; eauto.
  - apply d_wf_utyp__arrow; [ apply IHd_wf_utyp1 | apply IHd_wf_utyp2 ]; assumption.
  - apply d_wf_utyp__all_syn with (L := L). intros X HX.
    apply H0; [ assumption | apply ctxr_cons; [ apply dbr_refl | assumption ] ].
  - apply d_wf_utyp__all_etag with (L := L). intros X HX.
    apply H0; [ assumption | apply ctxr_cons; [ apply dbr_refl | assumption ] ].
Qed.

Lemma d_consis_ctx_refines : forall Ψ Γ C B,
    Ψ ⨟ Γ ⊨ C ≈ B -> forall Γ', ctx_refines Γ' Γ -> Ψ ⨟ Γ' ⊨ C ≈ B.
Proof.
  intros Ψ Γ C B H. induction H; intros Γ' Hcr.
  - apply d_consis__unit; assumption.
  - apply d_consis__var; [ eapply ctx_refines_binds_tvar; eauto | assumption ].
  - eapply d_consis__arrow;
      [ apply IHd_consis1; assumption | apply IHd_consis2; assumption | eassumption ].
  - apply d_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0); [ | eassumption ].
    intros X HX. apply H0; [ assumption | apply ctxr_cons; [ apply dbr_refl | assumption ] ].
  - apply d_consis__forall_inh_untagged with (L := L). intros X HX.
    apply H0; [ assumption | apply ctxr_cons; [ apply dbr_refl | assumption ] ].
  - apply d_consis__forall_syn_tagged with (L := L). intros X HX.
    apply H0; [ assumption | apply ctxr_cons; [ apply dbr_refl | assumption ] ].
  - apply d_consis__forall_syn with (L := L). intros X HX.
    apply H0; [ assumption | apply ctxr_cons; [ apply dbr_refl | assumption ] ].
Qed.

Lemma d_sub_ctx_refines : forall m Ψ Γ C B,
    Ψ ⨟ Γ ⊢[ m ] C ⊑ B -> forall Γ', ctx_refines Γ' Γ -> Ψ ⨟ Γ' ⊢[ m ] C ⊑ B.
Proof.
  intros m Ψ Γ C B H. induction H; intros Γ' Hcr.
  - apply d_sub__infer;
      [ eapply d_consis_ctx_refines; eauto | assumption | assumption ].
  - apply d_sub__check;
      [ assumption | assumption | eapply d_consis_ctx_refines; eauto | assumption ].
  - apply d_sub__forall_r with (L := L); [ assumption | ].
    intros X HX. apply H1; [ assumption | apply ctxr_cons; [ apply dbr_refl | assumption ] ].
  - eapply d_sub__arg;
      [ eapply d_consis_ctx_refines; eauto | apply IHd_sub; assumption | eassumption ].
  - eapply d_sub__forall_l_tagged;
      [ assumption | eassumption | eassumption
      | eapply d_wf_utyp_ctx_refines; eauto | assumption | apply IHd_sub; assumption ].
  - eapply d_sub__forall_l_untagged;
      [ assumption | eassumption | eassumption
      | eapply d_wf_utyp_ctx_refines; eauto | assumption | apply IHd_sub; assumption ].
Qed.

(** [ptyp_to_pskl] is injective on types (no holes): the skeleton determines
    the type. *)
Lemma ptyp_to_pskl_inj : forall A A', ptyp_to_pskl A = ptyp_to_pskl A' -> A = A'.
Proof.
  induction A; intros A' Heq; destruct A'; simpl in Heq; try discriminate;
    try reflexivity.
  - inversion Heq; reflexivity.
  - inversion Heq; reflexivity.
  - inversion Heq. f_equal; [ apply IHA1 | apply IHA2 ]; assumption.
  - inversion Heq. f_equal; apply IHA; assumption.
Qed.

(** SYNTACTIC principal type of a base term: [unit] / the annotation / the
    variable's binding.  Unlike the [ti] typing, this needs NO inner check for
    [anno] (so it never forces a tvar-strengthening), and for the value cases
    it is context-stable. *)
Inductive base_principal : exp -> list (atom * dbind) -> ptyp -> Prop :=
| bp_unit : forall Γ, base_principal exp_unit Γ ptyp_unit
| bp_var  : forall Γ x A, binds x (dbind_typ A) Γ -> base_principal (exp_var_f x) Γ A
| bp_anno : forall Γ e A, base_principal (exp_anno e A) Γ A.

Lemma base_principal_weaken_tvar : forall e Γ C X,
    base_principal e Γ C -> base_principal e ((X ~ dbind_tvar) ++ Γ) C.
Proof.
  intros e Γ C X H. destruct H.
  - apply bp_unit.
  - apply bp_var. apply binds_app_3. assumption.
  - apply bp_anno.
Qed.

(** Base-term checking inversion (subtyping form): a base term checked at [Bc]
    (tc) has its SYNTACTIC principal type [C] subtype to [Bc].  Avoids the
    [anno]-as-value-in-[∀] strengthening obstacle entirely: [C] is an INPUT
    (so the [forall] case fixes it — no existential), and the [sub] case
    relates [C] to the rule's ti type via [d_typing_ti_primary] + skeleton
    injectivity ([ptyp_to_pskl_inj]) — no inner-check production. *)
Lemma d_typing_base_check_sub : forall Γ e C Bc,
    d_wf_denv Γ -> base_principal e Γ C -> d_typing mode_tc Γ e Bc ->
    empty ⨟ Γ ⊢[ mode_tc ] (ptyp_to_utyp_syn C) ⊑ Bc.
Proof.
  intros Γ e C Bc Hwf Hbp Htc.
  remember mode_tc as m0 eqn:Hm. revert C Hwf Hbp Hm.
  induction Htc; intros C Hwf Hbp Hm; try discriminate Hm;
    try solve [ inversion Hbp ].
  - (* sub: ptyp_to_utyp_syn C = ptyp_to_utyp_syn A, then the rule's subtyping *)
    match goal with
    | Hti : d_typing mode_ti _ _ (ptyp_to_btyp_syn ?Aa),
      Hsub : empty ⨟ _ ⊢[ _ ] _ ⊑ _ |- _ =>
        assert (C = Aa) as HCA;
        [ pose proof (d_typing_ti_primary Hti) as Hp;
          inversion Hbp; subst; simpl in Hp;
          [ (* unit *) apply ptyp_to_pskl_inj;
              rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hp; rewrite Hp; reflexivity
          | (* var *) destruct Hp as [A1 [Hb1 Hsk]];
              match goal with Hbnd : binds _ (dbind_typ C) _ |- _ =>
                assert (dbind_typ C = dbind_typ A1)
                  by (eapply binds_unique; [ exact Hbnd | exact Hb1 | eapply d_wf_denv_uniq; eauto ]) end;
              apply ptyp_to_pskl_inj; rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hsk;
              match goal with H : dbind_typ _ = dbind_typ _ |- _ => inversion H; subst end;
              rewrite Hsk; reflexivity
          | (* anno *) apply ptyp_to_pskl_inj;
              rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hp; rewrite Hp; reflexivity ]
        | subst C; assumption ]
    end.
  - (* forall: C fixed → IH directly, then forall_r *)
    apply d_sub__forall_r with (L := L `union` dom Γ).
    + change (btyp_all_inh (ptyp_to_btyp_inh A)) with (ptyp_to_btyp_inh (ptyp_all A)).
      apply is_ityp_paint. eapply d_wf_ptyp_lc. apply d_wf_ptyp_of_btyp_inh.
      eapply d_typing_wf_btyp; [ eapply d_typing__forall with (L := L); eassumption | exact Hwf ].
    + intros X HX.
      match goal with IH : forall _ : atom, _ -> forall _ : ptyp, _ |- _ =>
        eapply (IH X ltac:(fsetdec) C) end.
      * apply d_wf_denv__tvar; [ exact Hwf | fsetdec ].
      * apply base_principal_weaken_tvar; exact Hbp.
      * reflexivity.
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

(** Consistent with the algorithmic [a_pat]/[a_looksub]: an fn skeleton is an
    ARROW whose domain is the concrete (structure-preserving) painting of the
    argument type ([a_pat__abs] emits [pskl_arrow P Q]; [app] needs the concrete
    domain to fill the arg), and whose ti/tc LEAVES are the hole-tolerant
    [skel_safe] (the declarative shadow of [a_looksub]'s absent/vacuous matching
    — this is what legitimately absorbs a [□]-typed result).  Context-free. *)
Fixpoint safe_skel (m : mode) (Q : bskl) (B : btyp) : Prop :=
  match m with
  | mode_ti => skel_safe nil Q (btyp_to_ptyp B)
  | mode_tc => skel_safe nil Q (btyp_to_ptyp B)
  | mode_fn m' =>
      exists Barg B0 Sarg Qc,
        B = btyp_arrow Barg B0
        (* the domain skeleton [Sarg] is whatever the inference produces — the
           inh-painting for a base function ([safe_fn_skel]) or the annotation's
           own colours for an annotated λ ([abs_anno]); either way it is SAFE for
           the domain type (no bare holes hiding polymorphism). *)
        /\ Q = bskl_arrow Sarg Qc
        /\ skel_safe nil (bskl_to_pskl Sarg) (btyp_to_ptyp Barg)
        /\ safe_skel m' Qc B0
  end.

(** Generalized safe-inference predicate (declarative context precision): the
    inference is over [Γ] (possibly carrying [□] for refined vars); the safety
    is quantified over EVERY well-formed [Γt] that [Γ] refines, so a [□]-refined
    inference is safe for the term under any concrete type at that variable. *)
Definition gpat (m : mode) (Γ : list (atom * dbind)) (e : exp) (B : btyp)
  : Prop :=
  match m with
  | mode_fn _ => exists Q, Γ ⊢[ m ] e ⇨ Q /\ safe_skel m Q B
  | mode_ti =>
      (* The TI inference is a SYNTHESISED skeleton ([is_sskl] — the syn-painting
         of its erasure, [is_sskl_syn_roundtrip]); this lets [freeze] lift it via
         [d_pat__freeze].  The safety conjunct is the CONTEXT-FREE [skel_safe]
         over [ctx_refines_tw] (refine + tvar-insertion): [skel_safe nil Q A]
         does not read [Γt], so [abs_check_fill_skel]'s ∀-peel needs no
         Γ-weakening; [refine_colour_skel] recovers the [d_refine_syn] fill at
         the consumer ([d_pat_safety]). *)
      exists Q, Γ ⊢[ mode_ti ] e ⇨ Q /\ is_sskl Q
                /\ (forall Γt A, ctx_refines_tw Γ Γt ->
                       d_wf_denv Γt -> Γt ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) ->
                       skel_safe nil (bskl_to_pskl Q) A)
  | mode_tc =>
      (* The TC inference is also SYNTHESISED ([is_sskl]); same context-free
         [skel_safe]-over-[ctx_refines_tw] conjunct.  This is what makes the λ
         coverage structural: [abs_check_fill_skel] peels a checked [∀] into
         [Γt] via [crtw_tvar] with the body coverage unchanged. *)
      exists Q, Γ ⊢[ mode_tc ] e ⇨ Q /\ is_sskl Q
                /\ (forall Γt A, ctx_refines_tw Γ Γt ->
                       d_wf_denv Γt -> Γt ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) ->
                       skel_safe nil (bskl_to_pskl Q) A)
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

(** Fill for the ghost skeleton [□] (the refined-variable path): [□] fills the
    syn-colouring of any well-formed checking type. *)

(** [skel_safe] twin of [gpat_syn_fill]: a synthesised skeleton whose erasure is
    the type's own [pskl] is [skel_safe] for it (context-free).  Near drop-in for
    [gpat_syn_fill] — same first two args, no [ctx_refines] arg. *)
Lemma gpat_syn_skel : forall Γt A Q,
    bskl_to_pskl Q = ptyp_to_pskl A -> d_wf_ptyp Γt A ->
    skel_safe nil (bskl_to_pskl Q) A.
Proof.
  intros Γt A Q Hsk Hwfa. rewrite Hsk. apply skel_safe_of_ptyp.
  eapply d_wf_ptyp_lc_loc; exact Hwfa.
Qed.

(** [skel_safe] is stable under [X := unit] when [X] is not free in the type
    (the [skel_safe] twin of [d_refine_syn_subst_unit], for the [∀] case). *)
Lemma skel_safe_subst_unit : forall Δ P A,
    skel_safe Δ P A -> forall X,
    X `notin` ftvar_in_ptyp A ->
    skel_safe Δ (subst_pskl_in_pskl pskl_unit X P) A.
Proof.
  induction 1; intros X0 HX0; simpl in HX0 |- *.
  - (* sks_hole *) apply sks_hole. exact H.
  - (* sks_unit *) apply sks_unit.
  - (* sks_var_f *) destruct (X == X0) as [ -> | Hne ];
      [ exfalso; fsetdec | apply sks_var_f ].
  - (* sks_arrow *) apply sks_arrow; [ apply IHskel_safe1 | apply IHskel_safe2 ];
      clear - HX0; fsetdec.
  - (* sks_all *) apply sks_all with (L := L `union` singleton X0). intros X HX.
    replace (open_pskl_wrt_pskl (subst_pskl_in_pskl pskl_unit X0 P0) (pskl_var_f X))
      with (subst_pskl_in_pskl pskl_unit X0 (open_pskl_wrt_pskl P0 (pskl_var_f X))).
    2:{ rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl by apply lc_pskl_unit.
        rewrite (subst_pskl_in_pskl_fresh_eq (pskl_var_f X) pskl_unit X0)
          by (clear - HX; simpl; fsetdec).
        reflexivity. }
    apply H0; [ clear - HX; fsetdec | ].
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A0 (ptyp_var_f X)) as Hsub.
    simpl in Hsub. clear - Hsub HX0 HX. fsetdec.
  - (* sks_top_leaf *) apply sks_top_leaf.
    + exact H.
    + intros Q1 HC. destruct P0 as [ | n | X1 | P1a P1b | P1 | | P1 ];
        simpl in HC; try discriminate HC.
      * destruct (X1 == X0); discriminate HC.
      * exfalso. eapply H0. reflexivity.
    + apply IHskel_safe. exact HX0.
  - (* sks_top_all *) apply sks_top_all with (L := L `union` singleton X0). intros X HX.
    change (pskl_tophole (subst_pskl_in_pskl pskl_unit X0 P0))
      with (subst_pskl_in_pskl pskl_unit X0 (pskl_tophole P0)).
    apply H0; [ clear - HX; fsetdec | ].
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A0 (ptyp_var_f X)) as Hsub.
    simpl in Hsub. clear - Hsub HX0 HX. fsetdec.
Qed.

(** Base-term safety under context refinement: [unit]/[var]/[anno].  The inferred
    [Q] is over [Γ'] ([□] for a refined var, else the syn skeleton); its [pskl]
    matches every checking type by [d_typing_ti_primary], and fills via the two
    helpers above. *)
(** SYN analog of [d_wf_ptyp_of_btyp_inh] (missing in the library): the syn
    painting's well-formedness erases to the underlying type's. *)
Lemma d_wf_ptyp_of_btyp_syn : forall A Γ,
    d_wf_btyp Γ (ptyp_to_btyp_syn A) -> d_wf_ptyp Γ A.
Proof.
  intros A Γ H. apply d_wf_ptyp_of_lc_ftvar.
  - apply lc_ptyp_of_lc_btyp_syn; eapply d_wf_btyp_lc; eassumption.
  - intros X HX. eapply d_wf_btyp_ftvar;
      [ eassumption | rewrite prop_wellformed.ftvar_ptyp_to_btyp_syn; exact HX ].
Qed.

Lemma d_pat_base_safe_gen : forall Γ e B,
    d_wf_denv Γ -> is_base_term e -> d_typing mode_ti Γ e B ->
    forall Γ', ctx_refines Γ' Γ -> gpat mode_ti Γ' e B.
Proof.
  intros Γ e B Hwf Hbase Hty Γ' Hcr.
  pose proof (d_typing_ti_primary Hty) as Hpri.
  destruct Hbase; simpl in Hpri.
  - (* unit *)
    exists bskl_unit. split; [ apply d_pat__unit | split; [ apply is_sskl__unit | ] ].
    intros Γt A Hcrt Hwft HA.
    pose proof (d_typing_ti_primary HA) as Hp. simpl in Hp.
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hp.
    eapply gpat_syn_skel;
      [ simpl; rewrite Hp; reflexivity
      | apply d_wf_ptyp_of_btyp_syn; eapply d_typing_wf_btyp; eauto ].
  - (* var x *)
    destruct Hpri as [A0 [Hbnd Hskel0]].
    destruct (@ctx_refines_binds Γ' Γ x (dbind_typ A0) Hcr Hbnd) as [d' [Hb' Hdr]].
    inversion Hdr; subst.
    + (* kept: x : typ A0 *)
      exists (pskl_to_bskl_syn (ptyp_to_pskl A0)).
      split; [ apply d_pat__var with (d := dbind_typ A0); [ exact Hb' | reflexivity ] | ].
      split; [ apply is_sskl_pskl_to_bskl_syn, lc_pskl_ptyp_to_pskl;
               eapply d_wf_ptyp_lc, d_wf_denv_binds_typ; [ exact Hwf | exact Hbnd ] | ].
      intros Γt A Hcrt Hwft HA.
        pose proof (d_typing_ti_primary HA) as Hp. simpl in Hp.
        destruct Hp as [A1 [Hbnd1 Hskel1]].
        rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hskel1.
        (* x : typ A0 in Γ' refines x's Γt-binding ⇒ typ A0, so A1 = A0 *)
        destruct (@ctx_refines_tw_binds_fwd _ _ x (dbind_typ A0) Hcrt Hb')
          as [dt [Hbt Hdrt]].
        inversion Hdrt; subst.
        assert (dbind_typ A1 = dbind_typ A0) by (eapply binds_unique; [ exact Hbnd1 | exact Hbt | eapply d_wf_denv_uniq; eauto ]).
        match goal with H : dbind_typ _ = dbind_typ _ |- _ => inversion H; subst end.
        eapply gpat_syn_skel;
          [ rewrite bskl_to_pskl_pskl_to_bskl_syn; rewrite Hskel1; reflexivity
          | apply d_wf_ptyp_of_btyp_syn; eapply d_typing_wf_btyp; eauto ].
    + (* refined: x : □ *)
      exists bskl_hole.
      split; [ apply d_pat__var with (d := dbind_skl pskl_hole) (P := pskl_hole);
                 [ exact Hb' | reflexivity ] | ].
      split; [ apply is_sskl__hole | ].
      intros Γt A Hcrt Hwft HA.
        apply skel_safe_hole_nil.
    + (* painted: x : skl (ptyp_to_pskl A0) — concrete-domain refinement.  The
         inference is the SAME syn skeleton [ptyp_to_pskl A0] as the kept case
         (both are the syn painting of [A0]); [dbind_to_pskl] agrees. *)
      exists (pskl_to_bskl_syn (ptyp_to_pskl A0)).
      split; [ apply d_pat__var with (d := dbind_skl (ptyp_to_pskl A0)) (P := ptyp_to_pskl A0);
                 [ exact Hb' | reflexivity ] | ].
      split; [ apply is_sskl_pskl_to_bskl_syn, lc_pskl_ptyp_to_pskl;
               eapply d_wf_ptyp_lc, d_wf_denv_binds_typ; [ exact Hwf | exact Hbnd ] | ].
      intros Γt A Hcrt Hwft HA.
        pose proof (d_typing_ti_primary HA) as Hp. simpl in Hp.
        destruct Hp as [A1 [Hbnd1 Hskel1]].
        rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hskel1.
        destruct (@ctx_refines_tw_binds_fwd _ _ x (dbind_skl (ptyp_to_pskl A0)) Hcrt Hb')
          as [dt [Hbt Hdrt]].
        assert (Hdteq : dbind_typ A1 = dt)
          by (eapply binds_unique; [ exact Hbnd1 | exact Hbt | eapply d_wf_denv_uniq; eauto ]).
        subst dt.
        assert (He : ptyp_to_pskl A0 = ptyp_to_pskl A1)
          by (apply dbind_refines_skl_typ_skel; exact Hdrt).
        eapply gpat_syn_skel;
          [ rewrite bskl_to_pskl_pskl_to_bskl_syn; rewrite Hskel1; exact He
          | apply d_wf_ptyp_of_btyp_syn; eapply d_typing_wf_btyp; eauto ].
  - (* anno e A0 *)
    exists (pskl_to_bskl_syn (ptyp_to_pskl A)).
    split; [ apply d_pat__anno; eapply d_wf_ptyp_ctx_refines;
               [ eapply d_typing_anno_wf; eauto | exact Hcr ] | ].
    split; [ apply is_sskl_pskl_to_bskl_syn, lc_pskl_ptyp_to_pskl;
             eapply d_wf_ptyp_lc; eapply d_typing_anno_wf; eauto | ].
    intros Γt A1 Hcrt Hwft HA.
      pose proof (d_typing_ti_primary HA) as Hp. simpl in Hp.
      rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hp.
      eapply gpat_syn_skel;
        [ rewrite bskl_to_pskl_pskl_to_bskl_syn; rewrite Hp; reflexivity
        | apply d_wf_ptyp_of_btyp_syn; eapply d_typing_wf_btyp; eauto ].
Qed.

(** A type's syn-erasure is consistent with its INH-painting (the domain
    obligation of the [FN]-mode arrow inference, where [safe_skel] forces an
    inh-painted domain).  Monotype parts match structurally; a [∀] uses
    [forall_inh_untagged] ([syn ∀ ≈ inh ∀]). *)
Lemma consis_syn_inh : forall C Γ,
    lc_ptyp C ->
    (forall X, X `in` ftvar_in_ptyp C -> binds X dbind_tvar Γ) ->
    empty ⨟ Γ ⊨ₛ (bskl_to_uskl (pskl_to_bskl_syn (ptyp_to_pskl C)))
                ≈ (pskl_to_bskl_inh (ptyp_to_pskl C)).
Proof.
  intros C Γ Hlc. revert Γ. induction Hlc; intros Γ Hcov; simpl.
  - apply d_pat_consis__unit; fsetdec.
  - apply d_pat_consis__var; [ fsetdec | apply Hcov; simpl; fsetdec ].
  - apply d_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHlc1 | apply IHHlc2 | fsetdec ];
      intros Y HY; apply Hcov; simpl; fsetdec.
  - inst_cofinites_for d_pat_consis__forall_inh_untagged. intros X HX.
    rewrite <- bskl_to_uskl_open. rewrite <- pskl_to_bskl_syn_open.
    rewrite <- pskl_to_bskl_inh_open. rewrite <- ! ptyp_to_pskl_open.
    apply H0.
    intros Y HY. apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY.
    simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + apply AtomSetImpl.singleton_1 in HY. subst. apply binds_app_2. apply binds_one_3; reflexivity.
    + apply binds_app_3. apply Hcov. assumption.
Qed.

(** The syn-erasure of any (lc) utyp's skeleton is a tagged skeleton (every
    forall erases to the synthesised [all_syn], now in [is_tskl]), carries no
    instantiation tags, and is consistent with the inh-painting.  These are the
    three obligations the FN-mode [ForallL] witness [ψ := syn-erase(skel ph)]
    must discharge. *)
Lemma is_tskl_syn_erase : forall C, lc_utyp C ->
    is_tskl (bskl_to_uskl (pskl_to_bskl_syn (utyp_to_pskl C))).
Proof.
  intros C H. induction H; simpl.
  - apply is_tskl__unit.
  - apply is_tskl__var.
  - apply is_tskl__arrow; assumption.
  - inst_cofinites_for is_tskl__all_syn. intros X HX.
    rewrite <- bskl_to_uskl_open, <- pskl_to_bskl_syn_open.
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- utyp_to_pskl_open. auto.
  - inst_cofinites_for is_tskl__all_syn. intros X HX.
    rewrite <- bskl_to_uskl_open, <- pskl_to_bskl_syn_open.
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- utyp_to_pskl_open. auto.
Qed.

Lemma d_tags_skl_syn_erase : forall C, lc_utyp C ->
    d_tags_skl empty (bskl_to_uskl (pskl_to_bskl_syn (utyp_to_pskl C))).
Proof.
  intros C H. induction H; simpl.
  - apply d_tags_skl__unit; fsetdec.
  - apply d_tags_skl__var; fsetdec.
  - apply d_tags_skl__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ assumption | assumption | fsetdec | fsetdec ].
  - inst_cofinites_for d_tags_skl__all_syn. intros X HX.
    rewrite <- bskl_to_uskl_open, <- pskl_to_bskl_syn_open.
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- utyp_to_pskl_open. auto.
  - inst_cofinites_for d_tags_skl__all_syn. intros X HX.
    rewrite <- bskl_to_uskl_open, <- pskl_to_bskl_syn_open.
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- utyp_to_pskl_open. auto.
Qed.

Lemma consis_syn_inh_u : forall C Γ, lc_utyp C ->
    (forall X, X `in` ftvar_in_utyp C -> binds X dbind_tvar Γ) ->
    empty ⨟ Γ ⊨ₛ (bskl_to_uskl (pskl_to_bskl_syn (utyp_to_pskl C)))
                ≈ (pskl_to_bskl_inh (utyp_to_pskl C)).
Proof.
  intros C Γ H. revert Γ. induction H; intros Γ Hcov; simpl.
  - apply d_pat_consis__unit; fsetdec.
  - apply d_pat_consis__var; [ fsetdec | apply Hcov; simpl; fsetdec ].
  - apply d_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHlc_utyp1 | apply IHlc_utyp2 | fsetdec ];
      intros Y HY; apply Hcov; simpl; fsetdec.
  - inst_cofinites_for d_pat_consis__forall_inh_untagged. intros X HX.
    rewrite <- bskl_to_uskl_open, <- pskl_to_bskl_syn_open, <- pskl_to_bskl_inh_open.
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- ! utyp_to_pskl_open.
    apply H0. intros Y HY. apply ftvar_in_utyp_open_utyp_wrt_utyp_upper in HY.
    simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + apply AtomSetImpl.singleton_1 in HY. subst. apply binds_app_2. apply binds_one_3; reflexivity.
    + apply binds_app_3. apply Hcov. assumption.
  - inst_cofinites_for d_pat_consis__forall_inh_untagged. intros X HX.
    rewrite <- bskl_to_uskl_open, <- pskl_to_bskl_syn_open, <- pskl_to_bskl_inh_open.
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- ! utyp_to_pskl_open.
    apply H0. intros Y HY. apply ftvar_in_utyp_open_utyp_wrt_utyp_upper in HY.
    simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + apply AtomSetImpl.singleton_1 in HY. subst. apply binds_app_2. apply binds_one_3; reflexivity.
    + apply binds_app_3. apply Hcov. assumption.
Qed.

(** A type's own (hole-free) skeleton is [hole_safe_u] for it (the
    [ghost_of_fill_gen] invariant for a general utyp LHS). *)
Lemma hole_safe_u_of_utyp : forall C, lc_utyp C ->
    forall L, hole_safe_u L (utyp_to_pskl C) C.
Proof.
  intros C Hlc. induction Hlc; intros L; simpl.
  - apply hsu_unit.
  - apply hsu_var_f.
  - apply hsu_arrow; auto.
  - apply hsu_all_syn with (Lc := empty). intros X HX.
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- utyp_to_pskl_open. auto.
  - apply hsu_all_etag with (Lc := empty). intros X HX.
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- utyp_to_pskl_open. auto.
Qed.

(** The syn-erasure of a (lc) utyp's skeleton is well-formed: its foralls are
    all [all_syn] (the bound var joins the skeleton scope [Ψ]), no holes. *)
Lemma d_wf_uskl_syn_erase : forall C, lc_utyp C ->
    forall Ψ Γ,
      (forall X, X `in` ftvar_in_utyp C -> List.In X Ψ \/ binds X dbind_tvar Γ) ->
      Γ ⨟ Ψ ⊢ᵤₛ (bskl_to_uskl (pskl_to_bskl_syn (utyp_to_pskl C))).
Proof.
  intros C Hlc. induction Hlc; intros Ψ Γ Hcov; simpl.
  - apply d_wf_uskl__unit.
  - apply d_wf_uskl__var. apply Hcov. simpl. fsetdec.
  - apply d_wf_uskl__arrow; [ apply IHHlc1 | apply IHHlc2 ];
      intros Y HY; apply Hcov; simpl; fsetdec.
  - apply d_wf_uskl__all_syn with (L := empty). intros X HX.
    rewrite <- bskl_to_uskl_open, <- pskl_to_bskl_syn_open.
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- utyp_to_pskl_open. apply H0.
    intros Y HY. apply ftvar_in_utyp_open_utyp_wrt_utyp_upper in HY.
    simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + apply AtomSetImpl.singleton_1 in HY. subst. left. simpl. left. reflexivity.
    + destruct (Hcov Y HY) as [HΨ | HΓ]; [ left; simpl; right; exact HΨ | right; exact HΓ ].
  - apply d_wf_uskl__all_syn with (L := empty). intros X HX.
    rewrite <- bskl_to_uskl_open, <- pskl_to_bskl_syn_open.
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- utyp_to_pskl_open. apply H0.
    intros Y HY. apply ftvar_in_utyp_open_utyp_wrt_utyp_upper in HY.
    simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + apply AtomSetImpl.singleton_1 in HY. subst. left. simpl. left. reflexivity.
    + destruct (Hcov Y HY) as [HΨ | HΓ]; [ left; simpl; right; exact HΨ | right; exact HΓ ].
Qed.

Lemma lc_pskl_utyp_to_pskl : forall C, lc_utyp C -> lc_pskl (utyp_to_pskl C).
Proof.
  intros C H. induction H; simpl.
  - apply lc_pskl_unit.
  - apply lc_pskl_var_f.
  - apply lc_pskl_arrow; assumption.
  - pick fresh X. apply (lc_pskl_all_syn_exists X).
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- utyp_to_pskl_open. auto.
  - pick fresh X. apply (lc_pskl_all_syn_exists X).
    change (pskl_var_f X) with (utyp_to_pskl (utyp_var_f X)).
    rewrite <- utyp_to_pskl_open. auto.
Qed.

Lemma ftvar_utyp_to_pskl : forall C, ftvar_in_pskl (utyp_to_pskl C) = ftvar_in_utyp C.
Proof.
  induction C; simpl; try reflexivity;
    try (rewrite IHC1, IHC2; reflexivity); try (rewrite IHC; reflexivity).
Qed.

(** The skeleton syn-erasure commutes with type instantiation. *)
Lemma syn_erase_utyp_open : forall C ph,
    bskl_to_uskl (pskl_to_bskl_syn (utyp_to_pskl (open_utyp_wrt_utyp C ph)))
    = open_uskl_wrt_uskl (bskl_to_uskl (pskl_to_bskl_syn (utyp_to_pskl C)))
                         (bskl_to_uskl (pskl_to_bskl_syn (utyp_to_pskl ph))).
Proof.
  intros C ph.
  unfold open_utyp_wrt_utyp, open_pskl_wrt_pskl, open_bskl_wrt_bskl, open_uskl_wrt_uskl.
  rewrite utyp_to_pskl_open_rec, pskl_to_bskl_syn_open_rec, bskl_to_uskl_open_rec.
  reflexivity.
Qed.

(** Type instantiation preserves well-formedness (open a forall body). *)
Lemma d_wf_utyp_open : forall L Γ C ph,
    (forall X, X `notin` L -> ((X ~ dbind_tvar) ++ Γ) ⊢ᵤ (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    Γ ⊢ᵤ ph ->
    Γ ⊢ᵤ (open_utyp_wrt_utyp C ph).
Proof.
  intros L Γ C ph Hbody Hph.
  pick fresh X for (L `union` ftvar_in_utyp C `union` dom Γ).
  rewrite (subst_utyp_in_utyp_intro X); [ | fsetdec ].
  eapply d_wf_utyp_subst_tvar; [ apply Hbody; fsetdec | exact Hph ].
Qed.

(** Skeleton subtyping respects set-equality of its tag context. *)
Lemma d_pat_sub_eq_tags : forall m Δ Γ R Q,
    Δ ⨟ Γ ⊢ₛ[ m ] R ⊑ Q -> forall Ψ', Δ [=] Ψ' -> Ψ' ⨟ Γ ⊢ₛ[ m ] R ⊑ Q.
Proof.
  intros m Δ Γ R Q H. induction H; intros Δ'' Heq.
  - apply d_pat_sub__infer; [ fsetdec | assumption | assumption ].
  - apply d_pat_sub__univ_ghost_r;
      [ fsetdec | assumption | assumption | assumption | assumption ].
  - eapply d_pat_sub__arg; [ eassumption | eassumption | fsetdec ].
  - (* [Ψ']/[psi] are constructor existentials, NOT fixed by the conclusion —
       a bare eapply leaves them as set-evars and [fsetdec] on [inter ?Ψ' Δ'']
       loops.  Recover the derivation's actual [Ψ']/[psi] from [d_tags_skl]. *)
    match goal with Htags : d_tags_skl ?D ?S |- _ =>
      eapply d_pat_sub__forall_l_tagged with (Ψ' := D) (psi := S) end;
      [ assumption | fsetdec | eassumption | assumption | assumption
      | apply IHd_pat_sub; fsetdec ].
  - match goal with Htags : d_tags_skl ?D ?S |- _ =>
      eapply d_pat_sub__forall_l_untagged with (Ψ' := D) (psi := S) end;
      [ assumption | fsetdec | eassumption | assumption | assumption
      | apply IHd_pat_sub; fsetdec ].
  - apply d_pat_sub__ghost; [ fsetdec | assumption ].
  - apply d_pat_sub__univ_ghost_l; [ assumption | apply IHd_pat_sub; exact Heq ].
  - apply d_pat_sub__ghostg; fsetdec.
  - apply d_pat_sub__univ_ghost_lg; [ assumption | apply IHd_pat_sub; exact Heq ].
Qed.

(** The FN-mode safe skeleton, by recursion over the (general-utyp) subtyping.
    [arg] folds the arrow (domain via [consis_syn_inh_u], codomain by the IH);
    [infer] (TI) gives the syn-painting whose pskl equals the target's
    ([d_consis_skel]); [check]/[forall_r] (TC) ghostify via [ghost_of_fill_gen]
    (general U); [forall_l] instantiates the (synthesised) forall with
    [ψ := syn-erase(skel ph)] — now [is_tskl] — and recurses on the body. *)
Lemma safe_fn_skel : forall m Ψ Γ U B,
    d_wf_utyp Γ U -> d_wf_btyp Γ B ->
    Ψ ⨟ Γ ⊢[ m ] U ⊑ B ->
    exists Q,
      empty ⨟ Γ ⊢ₛ[ m ] (bskl_to_uskl (pskl_to_bskl_syn (utyp_to_pskl U))) ⊑ Q
      /\ safe_skel m Q B.
Proof.
  intros m Ψ Γ U B HwfU HwfB Hsub. revert HwfU HwfB. induction Hsub; intros HwfU HwfB.
  - (* infer (TI) *)
    exists (pskl_to_bskl_syn (utyp_to_pskl C)). split.
    + apply d_pat_sub__infer;
        [ fsetdec
        | apply d_pat_consis_refl;
            [ apply is_sskl_pskl_to_bskl_syn, lc_pskl_utyp_to_pskl, (d_wf_utyp_lc HwfU)
            | intros X HX; rewrite ftvar_pskl_to_bskl_syn, ftvar_utyp_to_pskl in HX;
              eapply d_wf_utyp_ftvar; [ exact HwfU | exact HX ] ]
        | apply is_sskl_pskl_to_bskl_syn, lc_pskl_utyp_to_pskl, (d_wf_utyp_lc HwfU) ].
    + simpl.
      assert (Heq : bskl_to_pskl (pskl_to_bskl_syn (utyp_to_pskl C))
                    = ptyp_to_pskl (btyp_to_ptyp B))
        by (rewrite bskl_to_pskl_pskl_to_bskl_syn; apply (d_consis_skel H)).
      rewrite Heq. apply skel_safe_of_ptyp.
      apply lc_ptyp_btyp_to_ptyp; eapply d_wf_btyp_lc; exact HwfB.
  - (* check (TC) *)
    assert (Hlc : lc_utyp C) by (apply (d_wf_utyp_lc HwfU)).
    destruct (ghost_of_total (le_n (size_pskl (utyp_to_pskl C))) (lc_pskl_utyp_to_pskl Hlc))
      as [Q HQ].
    exists Q. split.
    + eapply (ghost_of_infer HQ (lc_pskl_utyp_to_pskl Hlc));
        [ reflexivity | intros X HX; rewrite ftvar_utyp_to_pskl in HX;
          eapply d_wf_utyp_ftvar; [ exact HwfU | exact HX ] ].
    + simpl.
      assert (Hs : Ψ ⨟ Γ ⊢[ mode_tc ] C ⊑ (ptyp_to_btyp_inh (btyp_to_ptyp B)))
        by (rewrite (is_ityp_ptyp_to_btyp_inh H2); apply d_sub__check; assumption).
      eapply ghost_skel_safe with (A' := btyp_to_ptyp B) (P := utyp_to_pskl C);
        [ exact Hs | reflexivity
        | apply d_wf_ptyp_of_btyp_inh; rewrite (is_ityp_ptyp_to_btyp_inh H2); exact HwfB
        | apply pskl_subsumes_refl | exact HQ | apply hole_safe_u_of_utyp; exact Hlc ].
  - (* forall_r (TC) *)
    assert (Hlc : lc_utyp C) by (apply (d_wf_utyp_lc HwfU)).
    destruct (ghost_of_total (le_n (size_pskl (utyp_to_pskl C))) (lc_pskl_utyp_to_pskl Hlc))
      as [Q HQ].
    exists Q. split.
    + eapply (ghost_of_infer HQ (lc_pskl_utyp_to_pskl Hlc));
        [ reflexivity | intros X HX; rewrite ftvar_utyp_to_pskl in HX;
          eapply d_wf_utyp_ftvar; [ exact HwfU | exact HX ] ].
    + simpl.
      assert (Hs : Ψ ⨟ Γ ⊢[ mode_tc ] C ⊑ (ptyp_to_btyp_inh (btyp_to_ptyp (btyp_all_inh B))))
        by (rewrite (is_ityp_ptyp_to_btyp_inh H); apply d_sub__forall_r with (L := L); assumption).
      eapply ghost_skel_safe with (A' := btyp_to_ptyp (btyp_all_inh B)) (P := utyp_to_pskl C);
        [ exact Hs | reflexivity
        | apply d_wf_ptyp_of_btyp_inh; rewrite (is_ityp_ptyp_to_btyp_inh H); exact HwfB
        | apply pskl_subsumes_refl | exact HQ | apply hole_safe_u_of_utyp; exact Hlc ].
  - (* arg (FN m) *)
    inversion HwfU; subst. inversion HwfB; subst.
    match goal with
    | HC1 : d_wf_utyp Γ C1, HC2 : d_wf_utyp Γ C2,
      HB1w : d_wf_btyp Γ B1, HB2 : d_wf_btyp Γ B2 |- _ =>
      destruct (IHHsub HC2 HB2) as [Qc [HscQc HsafeQc]];
      assert (Hsk1 : utyp_to_pskl C1 = ptyp_to_pskl (btyp_to_ptyp B1)) by (apply (d_consis_skel H));
      exists (bskl_arrow (pskl_to_bskl_inh (utyp_to_pskl C1)) Qc); split;
      [ simpl; eapply d_pat_sub__arg with (Ψ1 := empty) (Ψ2 := empty);
          [ apply consis_syn_inh_u;
              [ apply (d_wf_utyp_lc HC1)
              | intros X HX; eapply d_wf_utyp_ftvar; [ exact HC1 | exact HX ] ]
          | exact HscQc | fsetdec ]
      | simpl; exists B1, B2, (pskl_to_bskl_inh (utyp_to_pskl C1)), Qc;
        split; [ reflexivity
        | split; [ reflexivity
        | split; [ rewrite bskl_to_pskl_pskl_to_bskl_inh, Hsk1;
                   apply skel_safe_of_ptyp; apply lc_ptyp_btyp_to_ptyp;
                   eapply d_wf_btyp_lc; exact HB1w
                 | exact HsafeQc ] ] ] ]
    end.
  - (* forall_l_tagged: the (erased) forall is all_syn; instantiate with syn-erase(skel ph) *)
    assert (Hlcph : lc_utyp ph)
      by (match goal with Hph : Γ ⊢ᵤ ph |- _ => apply (d_wf_utyp_lc Hph) end).
    assert (HwfO : Γ ⊢ᵤ (open_utyp_wrt_utyp C ph)).
    { inversion HwfU; subst.
      match goal with
      | Hbody : forall X, X `notin` _ -> ((X ~ dbind_tvar) ++ Γ) ⊢ᵤ _,
        Hph : Γ ⊢ᵤ ph |- _ => eapply d_wf_utyp_open; [ exact Hbody | exact Hph ]
      end. }
    destruct (IHHsub HwfO HwfB) as [Q [Hsc Hsafe]].
    exists Q. split; [ | exact Hsafe ].
    simpl. eapply d_pat_sub__forall_l_untagged
      with (psi := bskl_to_uskl (pskl_to_bskl_syn (utyp_to_pskl ph))) (Ψ' := empty);
      [ assumption | fsetdec
      | apply d_tags_skl_syn_erase; exact Hlcph
      | eapply d_wf_uskl_syn_erase;
          [ exact Hlcph
          | intros X HX; right;
            match goal with Hph : Γ ⊢ᵤ ph |- _ => eapply d_wf_utyp_ftvar; [ exact Hph | exact HX ] end ]
      | apply is_tskl_syn_erase; exact Hlcph
      | rewrite <- syn_erase_utyp_open;
        match goal with |- _ ⨟ _ ⊢ₛ[ _ ] _ ⊑ _ => idtac end;
        eapply d_pat_sub_eq_tags; [ exact Hsc | fsetdec ] ].
  - (* forall_l_untagged: same *)
    assert (Hlcph : lc_utyp ph)
      by (match goal with Hph : Γ ⊢ᵤ ph |- _ => apply (d_wf_utyp_lc Hph) end).
    assert (HwfO : Γ ⊢ᵤ (open_utyp_wrt_utyp C ph)).
    { inversion HwfU; subst.
      match goal with
      | Hbody : forall X, X `notin` _ -> ((X ~ dbind_tvar) ++ Γ) ⊢ᵤ _,
        Hph : Γ ⊢ᵤ ph |- _ => eapply d_wf_utyp_open; [ exact Hbody | exact Hph ]
      end. }
    destruct (IHHsub HwfO HwfB) as [Q [Hsc Hsafe]].
    exists Q. split; [ | exact Hsafe ].
    simpl. eapply d_pat_sub__forall_l_untagged
      with (psi := bskl_to_uskl (pskl_to_bskl_syn (utyp_to_pskl ph))) (Ψ' := empty);
      [ assumption | fsetdec
      | apply d_tags_skl_syn_erase; exact Hlcph
      | eapply d_wf_uskl_syn_erase;
          [ exact Hlcph
          | intros X HX; right;
            match goal with Hph : Γ ⊢ᵤ ph |- _ => eapply d_wf_utyp_ftvar; [ exact Hph | exact HX ] end ]
      | apply is_tskl_syn_erase; exact Hlcph
      | rewrite <- syn_erase_utyp_open;
        eapply d_pat_sub_eq_tags; [ exact Hsc | fsetdec ] ].
Qed.

(** TC analog of [d_pat_base_safe_gen]: a base term checked in TC mode has a
    GHOSTIFIED safe inference.  Inference = [d_pat__sub] with the ghost
    [ghost_of (skel C) Q] ([ghost_of_infer]); fill = [ghost_of_fill_gen] fed by
    the checking inversion [d_typing_base_check_sub] (moved to [Γext] by
    [d_sub_ctx_refines]).  The refined-variable subcase falls back to the
    bare-hole fill [gpat_hole_fill]. *)
(** A ghostification is a synthesised skeleton (its outputs are
    [bskl_tophole]/[bskl_hole], all [is_sskl]).  Lets the tc safe witnesses
    carry the [is_sskl] component now bundled into [gpat]'s tc case. *)
Lemma is_sskl_ghost_of : forall P Q, ghost_of P Q -> lc_pskl P -> is_sskl Q.
Proof.
  intros P Q H. induction H; intros Hlc.
  - apply is_sskl__tophole, is_sskl__unit.
  - apply is_sskl__tophole, is_sskl__var.
  - inversion Hlc; subst. apply is_sskl__tophole, is_sskl__arrow;
      apply is_sskl_pskl_to_bskl_syn; assumption.
  - apply is_sskl__hole.
  - apply IHghost_of. inversion Hlc; subst; assumption.
  - apply IHghost_of. apply lc_body_pskl_wrt_pskl;
      [ apply lc_body_pskl_all_syn_1; exact Hlc | apply lc_pskl_hole ].
Qed.

Lemma d_pat_base_safe_tc_gen : forall Γ e A,
    d_wf_denv Γ -> is_base_term e -> d_typing mode_ti Γ e (ptyp_to_btyp_syn A) ->
    forall Γ' B, ctx_refines Γ' Γ -> gpat mode_tc Γ' e B.
Proof.
  intros Γ e A Hwf Hbase Hty Γ' B Hcr.
  (* common: the ghost-inference's [cov] premise over [Γ'] for a [C] wf over [Γ] *)
  assert (cov_of : forall C, d_wf_ptyp Γ C ->
            forall X, X `in` ftvar_in_pskl (ptyp_to_pskl C) -> binds X dbind_tvar Γ').
  { intros C HwfC X HX. rewrite ftvar_ptyp_to_pskl in HX.
    eapply ctx_refines_binds_tvar; [ exact Hcr | eapply d_wf_ptyp_ftvar; eauto ]. }
  destruct Hbase.
  - (* unit *)
    destruct (ghost_of_total (le_n (size_pskl (ptyp_to_pskl ptyp_unit)))
                (lc_pskl_ptyp_to_pskl lc_ptyp_unit)) as [Q HQ].
    exists Q. split; [ | split; [ exact (is_sskl_ghost_of HQ (lc_pskl_ptyp_to_pskl lc_ptyp_unit)) | ] ].
    + eapply d_pat__sub with (P := ptyp_to_pskl ptyp_unit); [ apply is_base_term__unit | apply d_pat__unit | ].
      eapply (ghost_of_infer HQ (lc_pskl_ptyp_to_pskl lc_ptyp_unit));
        [ reflexivity | apply cov_of; apply d_wf_ptyp__unit ].
    + intros Γt A1 Hcr2 Hwft HA.
      eapply ghost_skel_safe with (P := ptyp_to_pskl ptyp_unit) (U := ptyp_to_utyp_syn ptyp_unit) (A' := A1);
        [ eapply d_typing_base_check_sub; [ exact Hwft | apply bp_unit | exact HA ]
        | reflexivity
        | apply d_wf_ptyp_of_btyp_inh; eapply d_typing_wf_btyp; [ exact HA | exact Hwft ]
        | rewrite utyp_to_pskl_ptyp_to_utyp_syn; apply pskl_subsumes_refl
        | exact HQ
        | apply hole_safe_u_of_ptyp; apply lc_ptyp_unit ].
  - (* var x *)
    pose proof (d_typing_ti_primary Hty) as Hpri. simpl in Hpri.
    destruct Hpri as [A0 [Hbnd Hsk]].
    assert (HwfA0 : d_wf_ptyp Γ A0)
      by (eapply d_wf_denv_binds_typ; [ exact Hwf | exact Hbnd ]).
    assert (HlcA0 : lc_ptyp A0) by (eapply d_wf_ptyp_lc; exact HwfA0).
    destruct (@ctx_refines_binds Γ' Γ x (dbind_typ A0) Hcr Hbnd) as [d' [Hb' Hdr]].
    inversion Hdr; subst.
    + (* kept: x : typ A0 in Γ' *)
      destruct (ghost_of_total (le_n (size_pskl (ptyp_to_pskl A0)))
                  (lc_pskl_ptyp_to_pskl HlcA0)) as [Q HQ].
      exists Q. split; [ | split; [ exact (is_sskl_ghost_of HQ (lc_pskl_ptyp_to_pskl HlcA0)) | ] ].
      * eapply d_pat__sub with (P := ptyp_to_pskl A0);
          [ apply is_base_term__var
          | apply d_pat__var with (d := dbind_typ A0); [ exact Hb' | reflexivity ] | ].
        eapply (ghost_of_infer HQ (lc_pskl_ptyp_to_pskl HlcA0));
          [ reflexivity | apply cov_of; exact HwfA0 ].
      * intros Γt A1 Hcr2 Hwft HA.
        assert (Hbt : binds x (dbind_typ A0) Γt).
        { destruct (@ctx_refines_tw_binds_fwd _ _ x (dbind_typ A0) Hcr2 Hb')
            as [dt [Hbt Hdrt]]. inversion Hdrt; subst. exact Hbt. }
        eapply ghost_skel_safe with (P := ptyp_to_pskl A0) (U := ptyp_to_utyp_syn A0) (A' := A1);
          [ eapply d_typing_base_check_sub; [ exact Hwft | apply bp_var; exact Hbt | exact HA ]
          | reflexivity
          | apply d_wf_ptyp_of_btyp_inh; eapply d_typing_wf_btyp; [ exact HA | exact Hwft ]
          | rewrite utyp_to_pskl_ptyp_to_utyp_syn; apply pskl_subsumes_refl
          | exact HQ
          | apply hole_safe_u_of_ptyp; exact HlcA0 ].
    + (* refined: x : □ in Γ' — the bare ghost fills everything *)
      exists bskl_hole. split; [ | split; [ apply is_sskl__hole | ] ].
      * eapply d_pat__sub with (P := pskl_hole);
          [ apply is_base_term__var
          | apply d_pat__var with (d := dbind_skl pskl_hole) (P := pskl_hole);
              [ exact Hb' | reflexivity ] | ].
        eapply (ghost_of_infer ghost_of__hole lc_pskl_hole);
          [ reflexivity | intros X HX; simpl in HX; fsetdec ].
      * intros Γt A1 Hcr2 Hwft HA.
        apply skel_safe_hole_nil.
    + (* painted: x : skl (ptyp_to_pskl A0) in Γ' — concrete-domain refinement.
         Same ghost inference [ptyp_to_pskl A0] as the kept case (the skeleton of
         [A0]).  The [Γt] binding is some [typ Ax] with the SAME skeleton
         ([ptyp_to_pskl A0 = ptyp_to_pskl Ax]); run [ghost_skel_safe] at [Ax]. *)
      destruct (ghost_of_total (le_n (size_pskl (ptyp_to_pskl A0)))
                  (lc_pskl_ptyp_to_pskl HlcA0)) as [Q HQ].
      exists Q. split; [ | split; [ exact (is_sskl_ghost_of HQ (lc_pskl_ptyp_to_pskl HlcA0)) | ] ].
      * eapply d_pat__sub with (P := ptyp_to_pskl A0);
          [ apply is_base_term__var
          | apply d_pat__var with (d := dbind_skl (ptyp_to_pskl A0)) (P := ptyp_to_pskl A0);
              [ exact Hb' | reflexivity ] | ].
        eapply (ghost_of_infer HQ (lc_pskl_ptyp_to_pskl HlcA0));
          [ reflexivity | apply cov_of; exact HwfA0 ].
      * intros Γt A1 Hcr2 Hwft HA.
        (* [x] checks in [Γt] ⇒ it is [typ]-bound there; recover that binding. *)
        destruct (d_typing_var_binds HA) as [Ax Hbx].
        assert (HlcAx : lc_ptyp Ax)
          by (eapply d_wf_ptyp_lc, d_wf_denv_binds_typ; [ exact Hwft | exact Hbx ]).
        assert (Heqs : ptyp_to_pskl A0 = ptyp_to_pskl Ax).
        { destruct (@ctx_refines_tw_binds_fwd _ _ x (dbind_skl (ptyp_to_pskl A0)) Hcr2 Hb')
            as [dt [Hbt0 Hdrt]].
          assert (dt = dbind_typ Ax)
            by (eapply binds_unique; [ exact Hbt0 | exact Hbx | eapply d_wf_denv_uniq; eauto ]).
          subst dt. apply dbind_refines_skl_typ_skel; exact Hdrt. }
        eapply ghost_skel_safe with (P := ptyp_to_pskl Ax) (U := ptyp_to_utyp_syn Ax) (A' := A1);
          [ eapply d_typing_base_check_sub; [ exact Hwft | apply bp_var; exact Hbx | exact HA ]
          | reflexivity
          | apply d_wf_ptyp_of_btyp_inh; eapply d_typing_wf_btyp; [ exact HA | exact Hwft ]
          | rewrite utyp_to_pskl_ptyp_to_utyp_syn; apply pskl_subsumes_refl
          | rewrite <- Heqs; exact HQ
          | apply hole_safe_u_of_ptyp; exact HlcAx ].
  - (* anno e0 A0 *)
    assert (HwfA0 : d_wf_ptyp Γ A0) by (eapply d_typing_anno_wf; eauto).
    assert (HlcA0 : lc_ptyp A0) by (eapply d_wf_ptyp_lc; exact HwfA0).
    destruct (ghost_of_total (le_n (size_pskl (ptyp_to_pskl A0)))
                (lc_pskl_ptyp_to_pskl HlcA0)) as [Q HQ].
    exists Q. split; [ | split; [ exact (is_sskl_ghost_of HQ (lc_pskl_ptyp_to_pskl HlcA0)) | ] ].
    + eapply d_pat__sub with (P := ptyp_to_pskl A0);
        [ apply is_base_term__anno
        | apply d_pat__anno; eapply d_wf_ptyp_ctx_refines; [ exact HwfA0 | exact Hcr ] | ].
      eapply (ghost_of_infer HQ (lc_pskl_ptyp_to_pskl HlcA0));
        [ reflexivity | apply cov_of; exact HwfA0 ].
    + intros Γt A1 Hcr2 Hwft HA.
      eapply ghost_skel_safe with (P := ptyp_to_pskl A0) (U := ptyp_to_utyp_syn A0) (A' := A1);
        [ eapply d_typing_base_check_sub; [ exact Hwft | apply bp_anno | exact HA ]
        | reflexivity
        | apply d_wf_ptyp_of_btyp_inh; eapply d_typing_wf_btyp; [ exact HA | exact Hwft ]
        | rewrite utyp_to_pskl_ptyp_to_utyp_syn; apply pskl_subsumes_refl
        | exact HQ
        | apply hole_safe_u_of_ptyp; exact HlcA0 ].
Qed.

Lemma bskl_to_pskl_pskl_to_bskl_inh : forall P, bskl_to_pskl (pskl_to_bskl_inh P) = P.
Proof. induction P; simpl; congruence. Qed.

(** The mode-directed canonical fill of a [□] in FN/TI/TC mode: a refined
    variable infers a [Hole] which, in function mode, must become a SAFE
    concrete arrow.  We exhibit one [P0] whose inherited painting is safe for
    [B] — [skel B] at TI leaves (erasure matches), [pskl_hole] at TC leaves
    (the bare ghost, filled by [d_refine_syn_hole_fills]), arrow at FN nodes.
    The driving [uskl_hole ⊑ inh{P0}] is then one [d_pat_sub__ghost]. *)
Lemma safe_skel_hole_fill : forall m Γ B,
    mod_comp_ty B m -> d_wf_btyp Γ B ->
    exists P0, Γ ⨟ nil ⊢ₚₛ P0 /\ safe_skel m (pskl_to_bskl_inh P0) B.
Proof.
  intros m Γ B Hsk. induction Hsk; intros HwfB.
  - (* ti: is_styp B — paint the whole skeleton (erasure matches) *)
    exists (ptyp_to_pskl (btyp_to_ptyp B)). split.
    + apply d_wf_pskl_of_ptyp;
        [ apply lc_ptyp_btyp_to_ptyp; eapply d_wf_btyp_lc; exact HwfB
        | intros X HX; right; rewrite ftvar_btyp_to_ptyp in HX;
          eapply d_wf_btyp_ftvar; [ exact HwfB | exact HX ] ].
    + simpl. rewrite bskl_to_pskl_pskl_to_bskl_inh. apply skel_safe_of_ptyp.
      apply lc_ptyp_btyp_to_ptyp; eapply d_wf_btyp_lc; exact HwfB.
  - (* tc: is_ityp B — bare hole [□] absorbs the type ([sks_hole]) *)
    exists pskl_hole. split; [ apply d_wf_pskl__hole | ].
    simpl. apply skel_safe_hole_nil.
  - (* fn: arrow — rigid [inh] domain, recurse on the result *)
    inversion HwfB; subst.
    destruct (IHHsk ltac:(assumption)) as [P0' [HwfP0' Hsafe']].
    exists (pskl_arrow (ptyp_to_pskl (btyp_to_ptyp B1)) P0'). split.
    + apply d_wf_pskl__arrow;
        [ apply d_wf_pskl_of_ptyp;
            [ apply lc_ptyp_btyp_to_ptyp;
              match goal with H : Γ ⊢ᵦ B1 |- _ => eapply d_wf_btyp_lc; exact H end
            | intros X HX; right; rewrite ftvar_btyp_to_ptyp in HX;
              match goal with H : Γ ⊢ᵦ B1 |- _ => eapply d_wf_btyp_ftvar; [ exact H | exact HX ] end ]
        | exact HwfP0' ].
    + simpl. exists B1, B2, (pskl_to_bskl_inh (ptyp_to_pskl (btyp_to_ptyp B1))), (pskl_to_bskl_inh P0').
      split; [ reflexivity
      | split; [ reflexivity
      | split; [ rewrite bskl_to_pskl_pskl_to_bskl_inh; apply skel_safe_of_ptyp;
                 apply lc_ptyp_btyp_to_ptyp;
                 match goal with H : Γ ⊢ᵦ B1 |- _ => eapply d_wf_btyp_lc; exact H end
               | exact Hsafe' ] ] ].
Qed.

(** GENERAL binder rename for typing (mirrors [d_pat_rename_var]): renaming the
    context binder [x ↦ y] (and [x ↦ y] in the term) preserves [⦂].  The [sub]
    case goes through [d_sub_rename_var] (the subtyping ignores the relabeled
    term binding).  Aligns an abstraction body's premise to a fixed binder. *)
Lemma d_typing_rename_var : forall m Γ e B,
    Γ ⊢[ m ] e ⦂ B ->
    forall Γ1 x y d Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    x `notin` dom (Γ1 ++ Γ2) ->
    (Γ1 ++ (y ~ d) ++ Γ2) ⊢[ m ] (subst_exp_in_exp (exp_var_f y) x e) ⦂ B.
Proof.
  (* Structural induction on the typing.  Skeletons / types carry no term vars,
     so the relabelling only ever touches term-var lookups; each non-typing
     premise is transported by its own renaming lemma ([d_sub_rename_var],
     [d_pat_rename_var], [d_refine_syn_rename_var], [d_wf_ptyp_rename_var]), and the λ /
     ∀ bodies thread the substitution.  Mirrors [d_pat_rename_var]. *)
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
      | eapply IHd_typing; eauto | eapply d_sub_rename_var; eauto ].
  - simpl. apply d_typing__freeze. eapply IHd_typing; eauto.
  - (* forall: term unchanged under the binder (type opens, not the term) *)
    apply d_typing__forall with (L := L `union` singleton x0 `union` dom (Γ1 ++ Γ2));
      [ apply is_value_subst_var; assumption | ].
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hd | simpl_env in *; fsetdec ].
  - simpl. apply d_typing__abs with (L := L `union` singleton x0 `union` dom (Γ1 ++ Γ2)) (A := A) (B := B);
      [ eapply d_wf_ptyp_rename_var; eauto | assumption | ].
    intros z Hz. rewrite subst_exp_in_exp_open_exp_wrt_exp_var
      by (solve [ apply lc_exp_var_f | fsetdec ]).
    rewrite_env (((z ~ dbind_typ A) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hd | simpl_env in *; fsetdec ].
  - simpl. apply d_typing__abs_anno with
      (L := L `union` singleton x0 `union` dom (Γ1 ++ Γ2)) (A := btyp_to_ptyp B1) (B1 := B1) (B2 := B2);
      [ eapply d_wf_ptyp_rename_var; eauto | reflexivity | assumption | ].
    intros z Hz. rewrite subst_exp_in_exp_open_exp_wrt_exp_var
      by (solve [ apply lc_exp_var_f | fsetdec ]).
    rewrite_env (((z ~ dbind_typ (btyp_to_ptyp B1)) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hd | simpl_env in *; fsetdec ].
  - simpl. eapply d_typing__app;
      [ eapply d_pat_rename_var | eapply d_refine_syn_rename_var
      | eapply IHd_typing1 | eapply IHd_typing2 ]; eauto.
Qed.

(** The [abs_check] fill (the paper's context-precision lemma for a checked
    λ): given the body's safety over [(x0:□)::Γ'], the universal-ghost arrow
    skeleton [⫯.(□ → inh{Qb})] fills every type the λ checks against — by
    induction on that typing, peeling [∀]s ([tophole_fill]) down to the
    function base ([tophole_remove] + [arrow] + body-safety + strengthening). *)
(** The annotation-domain skeleton [btyp_to_bskl (syn A)] erases to [A]'s skeleton. *)
Lemma bskl_to_pskl_btyp_to_bskl_ptyp_to_btyp_syn : forall A,
    bskl_to_pskl (btyp_to_bskl (ptyp_to_btyp_syn A)) = ptyp_to_pskl A.
Proof.
  induction A; simpl; try reflexivity;
    [ rewrite IHA1, IHA2; reflexivity | rewrite IHA; reflexivity ].
Qed.

Lemma btyp_to_bskl_ptyp_to_btyp_syn_eq : forall A,
    btyp_to_bskl (ptyp_to_btyp_syn A) = pskl_to_bskl_syn (ptyp_to_pskl A).
Proof.
  induction A; simpl; try reflexivity;
    [ rewrite IHA1, IHA2; reflexivity | rewrite IHA; reflexivity ].
Qed.

(** STRUCTURAL abs [skel_safe] assembly (the context-free λ [skel_safe] engine
    feeding [d_pat_total_gen]'s abs-tc case).  Induct on the λ CHECKING:
    - [forall] (A' = ∀): [sks_top_all] peels the bound tvar; the IH handles the
      ∀-body typing at [(X:tvar)::Γt], and the peeled [X] is absorbed into the
      outer [ctx_refines_tw] via [crtw_tvar] — the body hypothesis [Hbody] is
      UNCHANGED (skel_safe is context-free).  This is exactly what stranded
      [abs_check_fill_structural]'s [forall] admit.
    - [abs] (A' = arrow): [sks_top_leaf] + [sks_arrow] (domain [sks_hole] at
      [Δ=nil]; codomain from [Hbody] at [(x:typ A)::Γt] via [crtw_cons]). *)
Lemma abs_check_fill_skel : forall e Qb Γ' L_b,
    (forall x, x `notin` L_b -> forall Γt'' A'',
        ctx_refines_tw ((x ~ dbind_skl pskl_hole) ++ Γ') Γt'' -> d_wf_denv Γt'' ->
        Γt'' ⊢[ mode_tc ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ ptyp_to_btyp_inh A'' ->
        skel_safe nil (bskl_to_pskl Qb) A'') ->
    forall Γt A',
      ctx_refines_tw Γ' Γt -> d_wf_denv Γt ->
      Γt ⊢[ mode_tc ] (exp_abs e) ⦂ (ptyp_to_btyp_inh A') ->
      skel_safe nil (pskl_tophole (pskl_arrow pskl_hole (bskl_to_pskl Qb))) A'.
Proof.
  intros e Qb Γ' L_b Hbody Γt A' Hcr Hwf Hty.
  remember (exp_abs e) as ee eqn:Hee.
  remember (ptyp_to_btyp_inh A') as B0 eqn:HB0.
  remember mode_tc as m eqn:Hm.
  revert A' Hcr Hwf Hee HB0 Hm.
  induction Hty; intros A'0 Hcr Hwf Hee HB0 Hm;
    try discriminate Hee;
    try (exfalso; subst;
         match goal with Hb : is_base_term (exp_abs _) |- _ => inversion Hb end).
  - (* forall : A'0 = ∀A *)
    destruct A'0 as [ | n | X | A'a A'b | A0 ]; simpl in HB0; try discriminate.
    injection HB0 as HB0'. apply (f_equal btyp_to_ptyp) in HB0'.
    rewrite ! btyp_to_ptyp_ptyp_to_btyp_inh in HB0'. subst A0.
    apply sks_top_all with (L := L `union` dom Γ). intros Y HY.
    eapply (H1 Y ltac:(fsetdec) Hbody (open_ptyp_wrt_ptyp A (ptyp_var_f Y))).
    + apply crtw_tvar. exact Hcr.
    + apply d_wf_denv__tvar; [ exact Hwf | fsetdec ].
    + exact Hee.
    + rewrite ptyp_to_btyp_inh_open_var. reflexivity.
    + reflexivity.
  - (* abs : A'0 = arrow A (btyp_to_ptyp B) *)
    subst m. injection Hee as Hee'; subst e0.
    match goal with Hsk : mod_comp_ty _ mode_tc |- _ =>
      inversion Hsk as [ | ? Hia | ]; subst end.
    match goal with Hia : is_ityp (btyp_arrow _ _) |- _ =>
      inversion Hia as [ | | ? ? Hi1 Hi2 | ]; subst end.
    rewrite <- (is_ityp_ptyp_to_btyp_inh Hi2) in HB0.
    change (btyp_arrow (ptyp_to_btyp_inh A) (ptyp_to_btyp_inh (btyp_to_ptyp B)))
      with (ptyp_to_btyp_inh (ptyp_arrow A (btyp_to_ptyp B))) in HB0.
    apply (f_equal btyp_to_ptyp) in HB0.
    rewrite ! btyp_to_ptyp_ptyp_to_btyp_inh in HB0. subst A'0.
    apply sks_top_leaf; [ intros ? Hc; discriminate | intros ? Hc; discriminate | ].
    apply sks_arrow.
    + apply sks_hole. intros ? ? HC; inversion HC.
    + pick fresh x for (L_b `union` L `union` dom Γ).
      eapply (Hbody x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ) (btyp_to_ptyp B)).
      * apply crtw_cons; [ apply dbr_typ_hole | exact Hcr ].
      * apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ].
      * rewrite (is_ityp_ptyp_to_btyp_inh Hi2).
        match goal with Hbp : forall _ : atom, _ -> _ ⊢[ _ ] _ ⦂ _ |- _ =>
          apply Hbp; fsetdec end.
Qed.

(** TI-synthesis analog of [abs_check_fill_skel]: a λ that SYNTHESISES an arrow
    ([d_pat__abs] gives [bskl_arrow bskl_hole Qb]).  Simpler — the ti inference
    has no tophole and [is_styp] forces a top-level arrow (no [∀]-peel).  Only
    [d_typing__abs] produces [exp_abs] at [mode_ti]; other cases discriminate on
    the term, the mode, or the [is_base_term] premise. *)
Lemma abs_ti_fill_skel : forall e Qb Γ' L_b,
    (forall x, x `notin` L_b -> forall Γt'' A'',
        ctx_refines_tw ((x ~ dbind_skl pskl_hole) ++ Γ') Γt'' -> d_wf_denv Γt'' ->
        Γt'' ⊢[ mode_ti ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ ptyp_to_btyp_syn A'' ->
        skel_safe nil (bskl_to_pskl Qb) A'') ->
    forall Γt A',
      ctx_refines_tw Γ' Γt -> d_wf_denv Γt ->
      Γt ⊢[ mode_ti ] (exp_abs e) ⦂ (ptyp_to_btyp_syn A') ->
      skel_safe nil (pskl_arrow pskl_hole (bskl_to_pskl Qb)) A'.
Proof.
  intros e Qb Γ' L_b Hbody Γt A' Hcr Hwf Hty.
  remember (exp_abs e) as ee eqn:Hee.
  remember (ptyp_to_btyp_syn A') as B0 eqn:HB0.
  remember mode_ti as m eqn:Hm.
  revert A' Hcr Hwf Hee HB0 Hm.
  induction Hty; intros A'0 Hcr Hwf Hee HB0 Hm;
    try discriminate Hee; try discriminate Hm;
    try (exfalso; subst;
         match goal with Hb : is_base_term (exp_abs _) |- _ => inversion Hb end).
  - (* abs : the only [exp_abs] at [mode_ti] *)
    subst m. injection Hee as Hee'; subst e0.
    destruct A'0 as [ | n | X | A'a A'b | A0 ]; simpl in HB0; try discriminate HB0.
    injection HB0 as HB0a HB0b.
    apply sks_arrow.
    + apply sks_hole. intros ? ? HC; inversion HC.
    + pick fresh x for (L_b `union` L `union` dom Γ).
      eapply (Hbody x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ) A'b).
      * apply crtw_cons; [ apply dbr_typ_hole | exact Hcr ].
      * apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ].
      * rewrite <- HB0b.
        match goal with Hbp : forall _ : atom, _ -> _ ⊢[ _ ] _ ⦂ _ |- _ =>
          apply Hbp; fsetdec end.
Qed.

(** Annotated-λ (TC) analog of [abs_check_fill_skel]: the domain skeleton is the
    ANNOTATION's own pskl ([skel_safe_of_ptyp]) rather than a hole. *)
Lemma abs_anno_check_fill_skel : forall Ann e Qb Γ' L_b,
    lc_ptyp Ann ->
    (forall x, x `notin` L_b -> forall Γt'' A'',
        ctx_refines_tw ((x ~ dbind_typ Ann) ++ Γ') Γt'' -> d_wf_denv Γt'' ->
        Γt'' ⊢[ mode_tc ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ ptyp_to_btyp_inh A'' ->
        skel_safe nil (bskl_to_pskl Qb) A'') ->
    forall Γt A',
      ctx_refines_tw Γ' Γt -> d_wf_denv Γt ->
      Γt ⊢[ mode_tc ] (exp_abs_anno Ann e) ⦂ (ptyp_to_btyp_inh A') ->
      skel_safe nil (pskl_tophole (pskl_arrow (ptyp_to_pskl Ann) (bskl_to_pskl Qb))) A'.
Proof.
  intros Ann e Qb Γ' L_b HlcAnn Hbody Γt A' Hcr Hwf Hty.
  remember (exp_abs_anno Ann e) as ee eqn:Hee.
  remember (ptyp_to_btyp_inh A') as B0 eqn:HB0.
  remember mode_tc as m eqn:Hm.
  revert A' Hcr Hwf Hee HB0 Hm.
  induction Hty; intros A'0 Hcr Hwf Hee HB0 Hm;
    try discriminate Hee;
    try (exfalso; subst;
         match goal with Hb : is_base_term (exp_abs_anno _ _) |- _ => inversion Hb end).
  - (* forall : A'0 = ∀A *)
    destruct A'0 as [ | n | X | A'a A'b | A0 ]; simpl in HB0; try discriminate.
    injection HB0 as HB0'. apply (f_equal btyp_to_ptyp) in HB0'.
    rewrite ! btyp_to_ptyp_ptyp_to_btyp_inh in HB0'. subst A0.
    apply sks_top_all with (L := L `union` dom Γ). intros Y HY.
    eapply (H1 Y ltac:(fsetdec) Hbody (open_ptyp_wrt_ptyp A (ptyp_var_f Y))).
    + apply crtw_tvar. exact Hcr.
    + apply d_wf_denv__tvar; [ exact Hwf | fsetdec ].
    + exact Hee.
    + rewrite ptyp_to_btyp_inh_open_var. reflexivity.
    + reflexivity.
  - (* abs_anno : the ott encoding substitutes [A := btyp_to_ptyp B1], so after
       [subst Ann] the annotation is [btyp_to_ptyp B1] throughout. *)
    subst m. injection Hee as HeeA Hee_e. subst e0. subst Ann.
    match goal with Hsk : mod_comp_ty _ mode_tc |- _ =>
      inversion Hsk as [ | ? Hia | ]; subst end.
    match goal with Hia : is_ityp (btyp_arrow _ _) |- _ =>
      inversion Hia as [ | | ? ? Hi1 Hi2 | ]; subst end.
    rewrite <- (is_ityp_ptyp_to_btyp_inh Hi1) in HB0.
    rewrite <- (is_ityp_ptyp_to_btyp_inh Hi2) in HB0.
    change (btyp_arrow (ptyp_to_btyp_inh (btyp_to_ptyp B1))
                       (ptyp_to_btyp_inh (btyp_to_ptyp B2)))
      with (ptyp_to_btyp_inh (ptyp_arrow (btyp_to_ptyp B1) (btyp_to_ptyp B2))) in HB0.
    apply (f_equal btyp_to_ptyp) in HB0.
    rewrite ! btyp_to_ptyp_ptyp_to_btyp_inh in HB0. subst A'0.
    apply sks_top_leaf; [ intros ? Hc; discriminate | intros ? Hc; discriminate | ].
    apply sks_arrow.
    + apply skel_safe_of_ptyp. exact HlcAnn.
    + pick fresh x for (L_b `union` L `union` dom Γ).
      eapply (Hbody x ltac:(fsetdec) ((x ~ dbind_typ (btyp_to_ptyp B1)) ++ Γ) (btyp_to_ptyp B2)).
      * apply crtw_cons; [ apply dbr_refl | exact Hcr ].
      * apply d_wf_denv__typ; [ exact Hwf | fsetdec | exact H ].
      * rewrite (is_ityp_ptyp_to_btyp_inh Hi2).
        match goal with Hbp : forall _ : atom, _ -> _ ⊢[ _ ] _ ⦂ _ |- _ =>
          apply Hbp; fsetdec end.
Qed.

(** Annotated-λ (TI-synthesis) analog: [d_pat__abs_anno] gives [bskl_arrow
    (btyp_to_bskl B1) Qb]; the domain skeleton is the annotation's pskl. *)
Lemma abs_anno_ti_fill_skel : forall Ann e Qb Γ' L_b,
    lc_ptyp Ann ->
    (forall x, x `notin` L_b -> forall Γt'' A'',
        ctx_refines_tw ((x ~ dbind_typ Ann) ++ Γ') Γt'' -> d_wf_denv Γt'' ->
        Γt'' ⊢[ mode_ti ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ ptyp_to_btyp_syn A'' ->
        skel_safe nil (bskl_to_pskl Qb) A'') ->
    forall Γt A',
      ctx_refines_tw Γ' Γt -> d_wf_denv Γt ->
      Γt ⊢[ mode_ti ] (exp_abs_anno Ann e) ⦂ (ptyp_to_btyp_syn A') ->
      skel_safe nil (pskl_arrow (ptyp_to_pskl Ann) (bskl_to_pskl Qb)) A'.
Proof.
  intros Ann e Qb Γ' L_b HlcAnn Hbody Γt A' Hcr Hwf Hty.
  remember (exp_abs_anno Ann e) as ee eqn:Hee.
  remember (ptyp_to_btyp_syn A') as B0 eqn:HB0.
  remember mode_ti as m eqn:Hm.
  revert A' Hcr Hwf Hee HB0 Hm.
  induction Hty; intros A'0 Hcr Hwf Hee HB0 Hm;
    try discriminate Hee; try discriminate Hm;
    try (exfalso; subst;
         match goal with Hb : is_base_term (exp_abs_anno _ _) |- _ => inversion Hb end).
  - (* abs_anno (ti) *)
    subst m. injection Hee as HeeA Hee_e. subst e0. subst Ann. subst.
    destruct A'0 as [ | n | X | A'a A'b | A0 ]; simpl in HB0; try discriminate HB0.
    injection HB0 as HB0a HB0b.
    apply (f_equal btyp_to_ptyp) in HB0a.
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in HB0a. subst A'a.
    apply sks_arrow.
    + apply skel_safe_of_ptyp. exact HlcAnn.
    + pick fresh x for (L_b `union` L `union` dom Γ).
      eapply (Hbody x ltac:(fsetdec) ((x ~ dbind_typ (btyp_to_ptyp B1)) ++ Γ) A'b).
      * apply crtw_cons; [ apply dbr_refl | exact Hcr ].
      * apply d_wf_denv__typ; [ exact Hwf | fsetdec | exact H ].
      * rewrite <- HB0b.
        match goal with Hbp : forall _ : atom, _ -> _ ⊢[ _ ] _ ⦂ _ |- _ =>
          apply Hbp; fsetdec end.
Qed.


(** ===================================================================== *)
(**  d_look EXTRACTION route (the context-free [a_look] shadow): read a       *)
(**  [hole_safe]/[tophole_safe] out of the typing+inference, then discharge   *)
(**  via the (Qed) [refine_colour_core]/[refine_colour_tophole].  No          *)
(**  [ctx_refines]: the bound var resolves to a hole, ∀-vars live in Δs/Δi.   *)
(** ===================================================================== *)

(** [look_refines Γ1 Γ2]: the body's INFERENCE context [Γ1] vs its TYPING context
    [Γ2].  [Γ2] is a structural refinement of [Γ1] (term bindings painted to
    skeletons/holes) WITH extra ∀-bound tvars interspersed (from the codomain's
    [∀]s).  Kept separate from [ctx_refines] so the wf-transport family is
    untouched: [hole_safe] is context-free, so we only ever look up TERM vars. *)
Inductive look_refines : list (atom * dbind) -> list (atom * dbind) -> Prop :=
| lr_base : forall Γ1 Γ2, ctx_refines Γ1 Γ2 -> look_refines Γ1 Γ2
| lr_tvar : forall X Γ1 Γ2,
    look_refines Γ1 Γ2 -> X `notin` dom Γ2 -> look_refines Γ1 ((X ~ dbind_tvar) ++ Γ2).

(** A NON-tvar binding in the typing context [Γ2] has a refining binding in the
    inference context [Γ1] (the interspersed ∀-vars are skipped). *)
Lemma look_refines_binds : forall Γ1 Γ2 z d,
    look_refines Γ1 Γ2 -> binds z d Γ2 -> d <> dbind_tvar ->
    exists d', binds z d' Γ1 /\ dbind_refines d' d.
Proof.
  intros Γ1 Γ2 z d H. induction H; intros Hb Hnt.
  - eapply ctx_refines_binds; eauto.
  - analyze_binds Hb;
      solve [ exfalso; apply Hnt; reflexivity | apply IHlook_refines; assumption ].
Qed.

(* [hole_safe_Ds_strengthen] DELETED: the Γ∣Δ refactor reverts [hole_safe] to a
   single list (the inherited-var / hole-avoidance scope; [hs_var_f] is now
   unconstrained).  The synthesised ∀-vars live in Γ, not a [Δs] list, so there
   is no var-avoidance scope left to strengthen. *)

(** FN analog of [d_pat_base_safe_tc_gen]: a base term that TI-types to
    [syn A] and is FN-subsumed to [B] has a SAFE function-mode inference.
    Two routes via [d_pat__sub]:
    - unit / kept-var / anno infer the SYN skeleton [pskl_to_bskl_syn(skel A)];
      the safe arrow comes straight from [safe_fn_skel] on the (refined)
      subtyping.
    - a [□]-refined var infers a [Hole]; in FN mode the hole must become a
      concrete arrow, so it fills to [inh{P0}] (one [d_pat_sub__ghost]) with
      [P0] the mode-directed canonical fill of [safe_skel_hole_fill]. *)
Lemma d_pat_base_safe_fn_gen : forall Γ e A m0 B,
    d_wf_denv Γ -> is_base_term e ->
    Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) ->
    empty ⨟ Γ ⊢[ mode_fn m0 ] (ptyp_to_utyp_syn A) ⊑ B ->
    forall Γ', ctx_refines Γ' Γ -> gpat (mode_fn m0) Γ' e B.
Proof.
  intros Γ e A m0 B Hwf Hbase Hty Hsub Γ' Hcr.
  assert (HwfsynB : d_wf_btyp Γ (ptyp_to_btyp_syn A))
    by (eapply d_typing_wf_btyp; [ exact Hty | exact Hwf ]).
  assert (HwfA : d_wf_ptyp Γ A).
  { apply d_wf_ptyp_of_lc_ftvar;
      [ apply lc_ptyp_of_lc_btyp_syn; eapply d_wf_btyp_lc; exact HwfsynB
      | intros X HX; eapply d_wf_btyp_ftvar;
          [ exact HwfsynB | rewrite prop_wellformed.ftvar_ptyp_to_btyp_syn; exact HX ] ]. }
  assert (HwfU : Γ ⊢ᵤ (ptyp_to_utyp_syn A)) by (apply d_wf_utyp_painting_syn; exact HwfA).
  assert (HwfB : d_wf_btyp Γ B) by (eapply d_sub_wf; [ exact Hsub | exact HwfU ]).
  assert (HwfA' : d_wf_ptyp Γ' A) by (eapply d_wf_ptyp_ctx_refines; [ exact HwfA | exact Hcr ]).
  assert (HwfU' : Γ' ⊢ᵤ (ptyp_to_utyp_syn A)) by (apply d_wf_utyp_painting_syn; exact HwfA').
  assert (HwfB' : d_wf_btyp Γ' B).
  { apply d_wf_btyp_of_lc_ftvar;
      [ eapply d_wf_btyp_lc; exact HwfB
      | intros X HX; eapply ctx_refines_binds_tvar;
          [ exact Hcr | eapply d_wf_btyp_ftvar; [ exact HwfB | exact HX ] ] ]. }
  assert (Hsub' : empty ⨟ Γ' ⊢[ mode_fn m0 ] (ptyp_to_utyp_syn A) ⊑ B)
    by (eapply d_sub_ctx_refines; [ exact Hsub | exact Hcr ]).
  destruct (safe_fn_skel HwfU' HwfB' Hsub') as [Qsyn [Hsc Hsafe]].
  rewrite utyp_to_pskl_ptyp_to_utyp_syn in Hsc.
  destruct Hbase.
  - (* unit *)
    pose proof (d_typing_ti_primary Hty) as Hpri. simpl in Hpri.
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hpri.
    exists Qsyn. split; [ | exact Hsafe ].
    eapply d_pat__sub with (P := ptyp_to_pskl A);
      [ apply is_base_term__unit | rewrite Hpri; apply d_pat__unit | exact Hsc ].
  - (* var x *)
    pose proof (d_typing_ti_primary Hty) as Hpri. simpl in Hpri.
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hpri.
    destruct Hpri as [A0 [Hbnd Hpsk]].
    destruct (@ctx_refines_binds Γ' Γ x (dbind_typ A0) Hcr Hbnd) as [d' [Hb' Hdr]].
    inversion Hdr; subst.
    + (* kept: x : typ A0 in Γ' — SYN route *)
      exists Qsyn. split; [ | exact Hsafe ].
      eapply d_pat__sub with (P := ptyp_to_pskl A);
        [ apply is_base_term__var
        | rewrite Hpsk; apply d_pat__var with (d := dbind_typ A0); [ exact Hb' | reflexivity ]
        | exact Hsc ].
    + (* refined: x : □ in Γ' — HOLE fill route *)
      assert (Hskmod : mod_comp_ty B (mode_fn m0)) by (eapply d_sub_skmod; exact Hsub).
      destruct (safe_skel_hole_fill Hskmod HwfB') as [P0 [HwfP0 Hsafe0]].
      exists (pskl_to_bskl_inh P0). split; [ | exact Hsafe0 ].
      eapply d_pat__sub with (P := pskl_hole);
        [ apply is_base_term__var
        | apply d_pat__var with (d := dbind_skl pskl_hole) (P := pskl_hole);
            [ exact Hb' | reflexivity ]
        | change (bskl_to_uskl (pskl_to_bskl_syn pskl_hole)) with uskl_hole;
          apply d_pat_sub__ghost; [ fsetdec | exact HwfP0 ] ].
    + (* painted: x : skl (ptyp_to_pskl A0) in Γ' — same SYN route as kept (the
         concrete skeleton [ptyp_to_pskl A0] is the syn inference of [A0]). *)
      exists Qsyn. split; [ | exact Hsafe ].
      eapply d_pat__sub with (P := ptyp_to_pskl A);
        [ apply is_base_term__var
        | rewrite Hpsk;
          apply d_pat__var with (d := dbind_skl (ptyp_to_pskl A0)) (P := ptyp_to_pskl A0);
            [ exact Hb' | reflexivity ]
        | exact Hsc ].
  - (* anno e0 A0 *)
    pose proof (d_typing_ti_primary Hty) as Hpri. simpl in Hpri.
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hpri.
    assert (HwfA0 : d_wf_ptyp Γ A0) by (eapply d_typing_anno_wf; [ exact Hty | exact Hwf ]).
    exists Qsyn. split; [ | exact Hsafe ].
    eapply d_pat__sub with (P := ptyp_to_pskl A);
      [ apply is_base_term__anno
      | rewrite Hpri; apply d_pat__anno; eapply d_wf_ptyp_ctx_refines; [ exact HwfA0 | exact Hcr ]
      | exact Hsc ].
Qed.

Lemma ptyp_to_btyp_inh_inj : forall A B,
    ptyp_to_btyp_inh A = ptyp_to_btyp_inh B -> A = B.
Proof.
  intros A B H. apply (f_equal btyp_to_ptyp) in H.
  rewrite !btyp_to_ptyp_ptyp_to_btyp_inh in H. exact H.
Qed.

(** Inversion of a frozen term's checking type: [freeze e] checks at [inh A]
    exactly when [e] synthesises [syn A].  The [sub] / [forall] cases are
    impossible ([freeze _] is neither a base term nor a value). *)
Lemma d_typing_freeze_inv : forall Γ e A,
    Γ ⊢[ mode_tc ] (exp_freeze e) ⦂ (ptyp_to_btyp_inh A) ->
    Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A).
Proof.
  intros Γ e A H. inversion H; subst;
    try (match goal with Hb : is_base_term (exp_freeze _) |- _ => inversion Hb end);
    try (match goal with Hv : is_value (exp_freeze _) |- _ => inversion Hv end).
  match goal with
  | Heq : ptyp_to_btyp_inh _ = ptyp_to_btyp_inh _ |- _ =>
      apply ptyp_to_btyp_inh_inj in Heq; subst
  end.
  assumption.
Qed.

(* ===================================================================== *)
(*  INFRA STUBS — expected-to-hold tvar-rename lemmas, delegated.          *)
(*  These are the [d_wf_denv] analog of the rename family already proved   *)
(*  ([d_wf_ptyp_rename_tvar], [d_typing_rename_tvar], etc.): renaming a     *)
(*  bound tvar [X0 ↦ Y] preserves context well-formedness (binders'        *)
(*  carried types are mapped through [subst_var_dbind]).  Used by the       *)
(*  [forall] case of [d_pat_total_gen].  Proof delegated; statement is the  *)
(*  direct map-form analog of [d_wf_ptyp_rename_tvar].                      *)
(* ===================================================================== *)
Lemma d_wf_denv_rename_tvar : forall Γ,
    d_wf_denv Γ ->
    forall Γ1 Γ2 X0 Y, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
    d_wf_denv (map (subst_var_dbind X0 Y) Γ1 ++ (Y ~ dbind_tvar) ++ Γ2).
Proof.
  (* Induction on Γ1 (the prefix before X0); d_wf_denv peels bindings from the
     front, so each step inverts the head binding and recurses on the tail. *)
  intros Γ H Γ1. revert Γ H. induction Γ1 as [ | [x d] Γ1' IH ];
    intros Γ H Γ2 X0 Y Heq Hfr; subst Γ; simpl_env in *.
  - (* Γ1 = nil : the head binding (X0 ~ tvar) is relabelled to (Y ~ tvar). *)
    inversion H; subst.
    apply d_wf_denv__tvar; [ assumption | fsetdec ].
  - (* Γ1 = (x ~ d) :: Γ1' : invert the head binding and recurse on the tail. *)
    inversion H; subst.
    + (* head is a tvar *)
      apply d_wf_denv__tvar.
      * eapply (IH _ ltac:(eassumption) Γ2 X0 Y); [ reflexivity | simpl_env in *; fsetdec ].
      * simpl_env in *; fsetdec.
    + (* head is a term var carrying a type *)
      apply d_wf_denv__typ.
      * eapply (IH _ ltac:(eassumption) Γ2 X0 Y); [ reflexivity | simpl_env in *; fsetdec ].
      * simpl_env in *; fsetdec.
      * eapply d_wf_ptyp_rename_tvar; [ eassumption | reflexivity | simpl_env in *; fsetdec ].
    + (* head is a term var carrying a skeleton *)
      apply d_wf_denv__skl.
      * eapply (IH _ ltac:(eassumption) Γ2 X0 Y); [ reflexivity | simpl_env in *; fsetdec ].
      * simpl_env in *; fsetdec.
      * (* d_wf_pskl_rename_tvar keeps Γ1 un-mapped; re-base via d_wf_pskl_same_tvar. *)
        eapply d_wf_pskl_same_tvar;
          [ eapply d_wf_pskl_rename_tvar; [ eassumption | reflexivity | simpl_env in *; fsetdec ]
          | apply same_tvar_map_subst_var ].
Qed.

(** [d_wf_denv] front term-var rename: the front binding's variable is a
    placeholder (the whole sub-well-formedness lives below it). *)
Lemma d_wf_denv_rename_front : forall x d Γ y,
    d_wf_denv ((x ~ d) ++ Γ) -> y `notin` dom Γ -> d_wf_denv ((y ~ d) ++ Γ).
Proof.
  intros x d Γ y H Hy. inversion H; subst.
  - apply d_wf_denv__tvar; auto.
  - apply d_wf_denv__typ; auto.
  - apply d_wf_denv__skl; auto.
Qed.

(** STRUCTURAL bound-var rename of the [gpat] tc fill — the clean replacement for
    the old erasure-canonicity detour.  Collision-free BY CONSTRUCTION: a
    structural [ctx_refines ((y:□)::Γ') Γt] forces [Γt = (y:d)::Γt0] with [y] ONLY
    at the front and [y ∉ Γt0] (refinement preserves [dom]), so relabelling
    [y → x] cannot collide.  Uses [d_typing_rename_var] + [d_refine_syn_rename_var]
    (refinement reads only tvars, so its rename has no freshness premise). *)
(** [skel_safe] is tvar-equivariant (rename a tvar [Z] to a fresh [W]).  This is
    the ingredient that lets [gpat_skel_rename] handle the name-clash case where
    the fixed bound var collides with a [ctx_refines_tw]-inserted tvar. *)
Lemma skel_safe_rename_tvar : forall Δ P A,
    skel_safe Δ P A -> forall Z W,
    ~ List.In W Δ -> W `notin` ftvar_in_ptyp A ->
    skel_safe (List.map (fun a => if a == Z then W else a) Δ)
              (subst_pskl_in_pskl (pskl_var_f W) Z P)
              (subst_ptyp_in_ptyp (ptyp_var_f W) Z A).
Proof.
  induction 1; intros Z W HWΔ HWA; simpl in *.
  - (* sks_hole *)
    apply sks_hole. intros X HX HInX.
    assert (HXu : X `in` (ftvar_in_ptyp (ptyp_var_f W) `union` remove Z (ftvar_in_ptyp A)))
      by (eapply ftvar_in_ptyp_subst_ptyp_in_ptyp_upper; exact HX).
    simpl in HXu.
    apply List.in_map_iff in HInX. destruct HInX as [a [Ha HaΔ]].
    destruct (a == Z) as [Heqa | Hnea].
    + (* a = Z ⇒ X = W ; both branches contradict *)
      subst a. destruct (Z == Z) as [_ | Hc]; [ | contradiction Hc; reflexivity ].
      subst X.
      destruct (AtomSetImpl.mem Z (ftvar_in_ptyp A)) eqn:Hmem.
      * apply AtomSetImpl.mem_2 in Hmem. exact (H Z Hmem HaΔ).
      * assert (Z `notin` ftvar_in_ptyp A) by (intro c; apply AtomSetImpl.mem_1 in c; congruence).
        rewrite subst_ptyp_in_ptyp_fresh_eq in HX by assumption. exact (HWA HX).
    + (* a ≠ Z ⇒ X = a ∈ Δ, and X ∈ ftvar A ⇒ ~In X Δ *)
      assert (Hxeq : X = a) by (rewrite <- Ha; destruct (a == Z); [ contradiction | reflexivity ]). subst a.
      assert (Hxa : X `in` ftvar_in_ptyp A).
      { apply AtomSetImpl.union_1 in HXu. destruct HXu as [HXu | HXu].
        - apply AtomSetImpl.singleton_1 in HXu. subst X. contradiction (HWΔ HaΔ).
        - eapply AtomSetImpl.remove_3; exact HXu. }
      exact (H X Hxa HaΔ).
  - (* sks_unit *) apply sks_unit.
  - (* sks_var_f *) destruct (X == Z); apply sks_var_f.
  - (* sks_arrow *) apply sks_arrow; [ apply IHskel_safe1 | apply IHskel_safe2 ];
      solve [ assumption | fsetdec ].
  - (* sks_all *) apply sks_all with (L := L `union` {{Z}} `union` {{W}}). intros X HX.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var by (first [ fsetdec | apply lc_pskl_var_f ]).
    rewrite subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var by (first [ fsetdec | apply lc_ptyp_var_f ]).
    replace (X :: List.map (fun a => if a == Z then W else a) Δ)
      with (List.map (fun a => if a == Z then W else a) (X :: Δ))
      by (simpl; destruct (X == Z); [ fsetdec | reflexivity ]).
    apply H0; [ fsetdec | simpl; intro c; destruct c; [ fsetdec | contradiction ] | ].
    intro Hin. apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in Hin. simpl in Hin.
    apply AtomSetImpl.union_1 in Hin. destruct Hin as [Hin | Hin];
      [ apply AtomSetImpl.singleton_1 in Hin; subst; fsetdec | apply HWA; exact Hin ].
  - (* sks_top_leaf *) apply sks_top_leaf.
    + intros A0 Hc. destruct A; simpl in Hc;
        solve [ discriminate | destruct (_ == _); discriminate | eapply H; reflexivity ].
    + intros Q1 Hc. destruct P0; simpl in Hc;
        solve [ discriminate | destruct (_ == _); discriminate | eapply H0; reflexivity ].
    + apply IHskel_safe; assumption.
  - (* sks_top_all *) apply sks_top_all with (L := L `union` {{Z}} `union` {{W}}). intros X HX.
    rewrite subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var by (first [ fsetdec | apply lc_ptyp_var_f ]).
    apply H0; [ fsetdec | assumption | ].
    intro Hin. apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in Hin. simpl in Hin.
    apply AtomSetImpl.union_1 in Hin. destruct Hin as [Hin | Hin];
      [ apply AtomSetImpl.singleton_1 in Hin; subst; fsetdec | apply HWA; exact Hin ].
Qed.


Lemma rename_var_denv_mid : forall Γa y xt d Γb,
    y `notin` dom Γa -> y `notin` dom Γb ->
    rename_var_denv y xt (Γa ++ (y ~ d) ++ Γb) = Γa ++ (xt ~ d) ++ Γb.
Proof.
  induction Γa as [ | [w dw] Γa' IH ]; intros y xt d Γb Ha Hb; simpl_env in *.
  - unfold rename_var_denv. simpl. destruct (y == y) as [ _ | n ]; [ | contradiction n; reflexivity ].
    f_equal. change (List.map (fun p : atom * dbind => (if fst p == y then xt else fst p, snd p)) Γb)
      with (rename_var_denv y xt Γb). apply rename_var_notin. exact Hb.
  - unfold rename_var_denv. simpl. destruct (w == y) as [ Heq | Hne ]; [ subst; simpl in Ha; fsetdec | ].
    f_equal. change (List.map (fun p : atom * dbind => (if fst p == y then xt else fst p, snd p))
                       (Γa' ++ (y ~ d) ++ Γb))
      with (rename_var_denv y xt (Γa' ++ (y ~ d) ++ Γb)).
    apply IH; [ simpl in Ha; fsetdec | exact Hb ].
Qed.

(** The bound-var rename [y→x] of the skel-coverage, in the non-clash case
    [x∉dom Γt]: split [Γt] at [y] ([binds_split]), rename the typing
    ([d_typing_rename_var]) and the context/wf ([ctx_refines_tw_rename_var],
    [d_wf_denv_rename_var]), then apply the [x]-coverage. *)
Lemma gpat_skel_rename_clean : forall (m : mode) (paint : ptyp -> btyp) (db : dbind) e Γ' Q x,
    db <> dbind_tvar ->
    x `notin` (fvar_in_exp e `union` dom Γ') -> d_wf_denv Γ' ->
    (forall Γt A, ctx_refines_tw ((x ~ db) ++ Γ') Γt -> d_wf_denv Γt ->
       Γt ⊢[ m ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ (paint A) ->
       skel_safe nil (bskl_to_pskl Q) A) ->
    forall y, y `notin` (fvar_in_exp e `union` dom Γ') ->
      forall Γt A, ctx_refines_tw ((y ~ db) ++ Γ') Γt -> d_wf_denv Γt ->
        x `notin` dom Γt ->
        Γt ⊢[ m ] (open_exp_wrt_exp e (exp_var_f y)) ⦂ (paint A) ->
        skel_safe nil (bskl_to_pskl Q) A.
Proof.
  intros m paint db e Γ' Q x Hdbntv Hx Hwf' Hcov y Hy Γt A Hcr Hwf Hxt Hty.
  assert (Hby : binds y db ((y ~ db) ++ Γ'))
    by (apply binds_app_iff; left; apply binds_one_iff; auto).
  destruct (@ctx_refines_tw_binds_fwd _ _ _ _ Hcr Hby) as [dt [Hbt Hdrt]].
  assert (Hntv : dt <> dbind_tvar) by (inversion Hdrt; subst; [ exact Hdbntv | discriminate | discriminate ]).
  assert (Huniq : uniq Γt) by (eapply d_wf_denv_uniq; exact Hwf).
  destruct (binds_split _ _ _ _ Hbt) as [Γb [Γa Hsplit]]. subst Γt.
  assert (Hyd : y `notin` dom (Γa ++ Γb)) by solve_uniq.
  assert (Hmid : rename_var_denv y x (Γa ++ (y ~ dt) ++ Γb) = Γa ++ (x ~ dt) ++ Γb)
    by (apply rename_var_denv_mid; solve_uniq).
  assert (Htyx : (Γa ++ (x ~ dt) ++ Γb) ⊢[ m ]
                   (open_exp_wrt_exp e (exp_var_f x)) ⦂ (paint A)).
  { replace (open_exp_wrt_exp e (exp_var_f x))
      with (subst_exp_in_exp (exp_var_f x) y (open_exp_wrt_exp e (exp_var_f y)))
      by (symmetry; apply subst_exp_in_exp_intro; fsetdec).
    eapply d_typing_rename_var with (x := y) (Γ1 := Γa) (Γ2 := Γb);
      [ exact Hty | reflexivity | exact Hntv | exact Hyd ]. }
  eapply Hcov with (Γt := Γa ++ (x ~ dt) ++ Γb).
  - rewrite <- Hmid. eapply ctx_refines_tw_rename_var;
      [ exact Hcr | reflexivity | exact Huniq | exact Hxt ].
  - rewrite <- Hmid. apply d_wf_denv_rename_var; [ exact Hwf | exact Hxt | ].
    intro Hb. assert (Heq : dt = dbind_tvar)
      by (eapply binds_unique; [ exact Hbt | exact Hb | exact Huniq ]).
    apply Hntv; exact Heq.
  - exact Htyx.
Qed.

(** [x → w][w → x] on a type is the identity when [w] is fresh. *)
Lemma ptyp_rename_rename : forall A x w,
    w `notin` ftvar_in_ptyp A ->
    subst_ptyp_in_ptyp (ptyp_var_f x) w (subst_ptyp_in_ptyp (ptyp_var_f w) x A) = A.
Proof.
  induction A as [ | n | X | A1 IHA1 A2 IHA2 | A0 IHA0 ]; intros x w Hw; simpl in Hw |- *.
  - reflexivity.
  - reflexivity.
  - (* var_f *) default_simp.
  - rewrite IHA1 by fsetdec; rewrite IHA2 by fsetdec; reflexivity.
  - rewrite IHA0 by fsetdec; reflexivity.
Qed.

(** [bskl_to_pskl] preserves free type variables (it only erases colours). *)
Lemma ftvar_in_pskl_bskl_to_pskl : forall Q,
    ftvar_in_pskl (bskl_to_pskl Q) [=] ftvar_in_bskl Q.
Proof.
  induction Q; simpl; try reflexivity;
    try (rewrite IHQ1, IHQ2; reflexivity);
    try (rewrite IHQ; reflexivity).
Qed.

(** A suffix of a wf context is wf. *)
Lemma d_wf_denv_app_r : forall Γa Γb,
    d_wf_denv (Γa ++ Γb) -> d_wf_denv Γb.
Proof.
  induction Γa as [ | [z d] Γa' IH ]; intros Γb H; simpl_env in *.
  - exact H.
  - inversion H; subst; apply IH; assumption.
Qed.

(** The tvar in the middle of a wf context is [tvar_clean] for the suffix
    (its suffix bindings predate it, so cannot mention it). *)
Lemma tvar_clean_mid : forall Γa X Γb,
    d_wf_denv (Γa ++ (X ~ dbind_tvar) ++ Γb) -> tvar_clean X Γb.
Proof.
  intros Γa X Γb Hwf.
  assert (Hwfb : d_wf_denv ((X ~ dbind_tvar) ++ Γb))
    by (eapply d_wf_denv_app_r; exact Hwf).
  inversion Hwfb as [ | Γ0 X0 HwfΓb HXdom Heq | | ]; subst.
  split; intros z T Hb.
  - assert (Hwfd : d_wf_ptyp Γb T) by (eapply d_wf_denv_binds_typ; [ exact HwfΓb | exact Hb ]).
    intro Hin. apply (d_wf_ptyp_ftvar Hwfd) in Hin. apply binds_In in Hin. contradiction.
  - assert (Hwfd : Γb ⨟ nil ⊢ₚₛ T) by (eapply d_wf_denv_binds_skl; [ exact HwfΓb | exact Hb ]).
    intro Hin. apply (d_wf_pskl_ftvar Hwfd) in Hin. destruct Hin as [ HImp | Hbtv ];
      [ inversion HImp | apply binds_In in Hbtv; contradiction ].
Qed.

(** The extra names a [ctx_refines_tw] adds beyond its source are all tvars. *)
Lemma ctx_refines_tw_extra_tvar : forall Γs Γt z d,
    ctx_refines_tw Γs Γt -> binds z d Γt -> z `notin` dom Γs -> d = dbind_tvar.
Proof.
  intros Γs Γt z d H. revert z d. induction H; intros z dz Hb Hz.
  - (* crtw_base *) exfalso. apply binds_In in Hb.
    assert (Hdom : dom Γ' [=] dom Γ) by (apply ctx_refines_dom; exact H). fsetdec.
  - (* crtw_tvar : Γt = (X~tvar)::Γ *)
    analyze_binds Hb; try reflexivity;
      eapply IHctx_refines_tw; [ exact BindsTac | exact Hz ].
  - (* crtw_cons : Γs=(x~d')::Γ', Γt=(x~d0)::Γ *)
    simpl_env in Hz. analyze_binds Hb; try (exfalso; fsetdec);
      eapply IHctx_refines_tw; [ exact BindsTac | simpl_env; fsetdec ].
Qed.

(** LN rename of the gpat body coverage from bound var [x] to any fresh [y],
    over [ctx_refines_tw] (which inserts tvars).  The clean case (x ∉ dom Γt)
    is [gpat_skel_rename_clean]; the clash case (x is a tw-inserted tvar in Γt)
    renames that tvar out via the standard tvar-equivariance machinery. *)
Lemma gpat_skel_rename : forall (m : mode) (paint : ptyp -> btyp) (db : dbind),
    (forall A x0 y0, subst_btyp_in_btyp (btyp_var_f y0) x0 (paint A)
                     = paint (subst_ptyp_in_ptyp (ptyp_var_f y0) x0 A)) ->
    db <> dbind_tvar ->
    forall e Γ' Q x,
    x `notin` (fvar_in_exp e `union` ftvar_in_exp e `union` dom Γ') -> d_wf_denv Γ' ->
    (forall y0, y0 `notin` dom Γ' -> d_wf_denv ((y0 ~ db) ++ Γ')) ->
    (forall Γt A, ctx_refines_tw ((x ~ db) ++ Γ') Γt -> d_wf_denv Γt ->
       Γt ⊢[ m ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ (paint A) ->
       skel_safe nil (bskl_to_pskl Q) A) ->
    forall y, y `notin` (fvar_in_exp e `union` ftvar_in_exp e `union` dom Γ') ->
      forall Γt A, ctx_refines_tw ((y ~ db) ++ Γ') Γt -> d_wf_denv Γt ->
        Γt ⊢[ m ] (open_exp_wrt_exp e (exp_var_f y)) ⦂ (paint A) ->
        skel_safe nil (bskl_to_pskl Q) A.
Proof.
  intros m paint db Hpaint Hdbntv e Γ' Q x Hx Hwf' Hdbwf Hcov y Hy Γt A Hcr Hwf Hty.
  destruct (x == y) as [ Hxy | Hxy ].
  { subst y. eapply Hcov; eauto. }
  destruct (AtomSetImpl.mem x (dom Γt)) eqn:Hmem.
  2:{ (* no clash *)
      assert (Hnotin : x `notin` dom Γt)
        by (intro Hc; apply AtomSetImpl.mem_1 in Hc; rewrite Hc in Hmem; discriminate).
      eapply gpat_skel_rename_clean with (m := m) (paint := paint) (db := db)
        (e := e) (Γ' := Γ') (Q := Q) (x := x) (y := y);
        [ exact Hdbntv
        | clear - Hx; fsetdec
        | exact Hwf'
        | intros Γt0 A0 Hcr0 Hwf0 Hty0; eapply Hcov; eauto
        | clear - Hy; fsetdec
        | exact Hcr | exact Hwf | exact Hnotin | exact Hty ]. }
  (* clash: x ∈ dom Γt, x ≠ y ⇒ x is a tw-inserted tvar *)
  apply AtomSetImpl.mem_2 in Hmem.
  apply binds_In_inv in Hmem. destruct Hmem as [dx Hbx].
  assert (Hxsrc : x `notin` dom ((y ~ db) ++ Γ')).
  { simpl_env. clear - Hx Hxy. fsetdec. }
  assert (Hdx : dx = dbind_tvar)
    by (eapply ctx_refines_tw_extra_tvar; [ exact Hcr | exact Hbx | exact Hxsrc ]). subst dx.
  assert (Huniq : uniq Γt) by (eapply d_wf_denv_uniq; exact Hwf).
  destruct (binds_split _ _ _ _ Hbx) as [Γb [Γa Hsplit]]. subst Γt.
  pick fresh w for
    (dom (Γa ++ (x ~ dbind_tvar) ++ Γb) `union` ftvar_in_ptyp A
       `union` singleton x `union` singleton y `union` dom Γ'
       `union` ftvar_in_exp e `union` ftvar_in_bskl Q).
  set (Γt' := map (subst_var_dbind x w) Γa ++ (w ~ dbind_tvar) ++ Γb).
  (* renamed typing *)
  assert (Htyw : Γt' ⊢[ m ] (open_exp_wrt_exp e (exp_var_f y))
                   ⦂ paint (subst_ptyp_in_ptyp (ptyp_var_f w) x A)).
  { unfold Γt'. rewrite <- Hpaint.
    assert (Hfe : x `notin` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f y))).
    { pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f y)) as Hsub.
      simpl in Hsub. clear - Hsub Hx. fsetdec. }
    rewrite <- (subst_ptyp_in_exp_fresh_eq (open_exp_wrt_exp e (exp_var_f y)) (ptyp_var_f w) x Hfe).
    eapply d_typing_rename_tvar with (Γ1 := Γa) (Γ2 := Γb) (X0 := x) (Y := w);
      [ exact Hty | reflexivity | clear - Fr; fsetdec | eapply tvar_clean_mid; exact Hwf ]. }
  (* renamed wf *)
  assert (Hwfw : d_wf_denv Γt').
  { unfold Γt'. eapply d_wf_denv_rename_tvar with (Γ1 := Γa) (Γ2 := Γb) (X0 := x);
      [ exact Hwf | reflexivity | clear - Fr; fsetdec ]. }
  (* renamed ctx_refines_tw *)
  assert (Hcrw : ctx_refines_tw ((y ~ db) ++ Γ') Γt').
  { unfold Γt'.
    assert (Hwfsrc : d_wf_denv ((y ~ db) ++ Γ')).
    { apply Hdbwf; clear - Hy; fsetdec. }
    eapply ctx_refines_tw_rename_tvar;
      [ exact Hcr | exact Hwfsrc | exact Hxsrc | clear - Fr; fsetdec ]. }
  (* x renamed away *)
  assert (Hxnot : x `notin` dom Γt').
  { unfold Γt'. simpl_env.
    assert (HxΓa : x `notin` dom Γa) by solve_uniq.
    assert (HxΓb : x `notin` dom Γb) by solve_uniq.
    clear - HxΓa HxΓb Fr. fsetdec. }
  assert (Hskw : skel_safe nil (bskl_to_pskl Q) (subst_ptyp_in_ptyp (ptyp_var_f w) x A)).
  { eapply gpat_skel_rename_clean with (m := m) (paint := paint) (db := db)
      (e := e) (Γ' := Γ') (Q := Q) (x := x) (y := y);
      [ exact Hdbntv
      | clear - Hx; fsetdec
      | exact Hwf'
      | intros Γt0 A0 Hcr0 Hwf0 Hty0; eapply Hcov; eauto
      | clear - Hy; fsetdec
      | exact Hcrw | exact Hwfw | exact Hxnot | exact Htyw ]. }
  (* rename w → x back (skel_safe is context-free, w ∉ ftvar Q, (A[x→w])[w→x]=A) *)
  assert (Hxnf : x `notin` ftvar_in_ptyp (subst_ptyp_in_ptyp (ptyp_var_f w) x A)).
  { intro Hin. apply ftvar_in_ptyp_subst_ptyp_in_ptyp_upper in Hin. simpl in Hin.
    assert (x <> w) by (clear - Fr; fsetdec). clear - Hin H. fsetdec. }
  pose proof (@skel_safe_rename_tvar nil (bskl_to_pskl Q)
                (subst_ptyp_in_ptyp (ptyp_var_f w) x A) Hskw w x
                ltac:(simpl; auto) Hxnf) as Hback. simpl in Hback.
  rewrite subst_pskl_in_pskl_fresh_eq in Hback
    by (rewrite ftvar_in_pskl_bskl_to_pskl; clear - Fr; fsetdec).
  rewrite ptyp_rename_rename in Hback by (clear - Fr; fsetdec).
  exact Hback.
Qed.

(** [∀]-case coverage transfer: the body-at-fresh-[X] [skel_safe] coverage
    ([Hcov]) yields the [X := unit]-strengthened coverage at [Γ'].  Mirrors
    [gpat_skel_rename]'s clash handling ([X] may be a tw-inserted tvar in [Γt]):
    the non-clash core is [skel_safe_subst_unit] (the [subst_unit] removes [X]),
    the clash is renamed out and back via [skel_safe_rename_tvar]. *)
Lemma skel_safe_forall_cover : forall e Γ' X QX,
    X `notin` (ftvar_in_exp e `union` dom Γ') -> d_wf_denv Γ' ->
    (forall Γt A, ctx_refines_tw ((X ~ dbind_tvar) ++ Γ') Γt -> d_wf_denv Γt ->
       Γt ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) -> skel_safe nil (bskl_to_pskl QX) A) ->
    forall Γt A0, ctx_refines_tw Γ' Γt -> d_wf_denv Γt ->
      Γt ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A0) ->
      skel_safe nil (subst_pskl_in_pskl pskl_unit X (bskl_to_pskl QX)) A0.
Proof.
  intros e Γ' X QX HX Hwf' Hcov Γt A0 Hcr Hwf Hty.
  destruct (AtomSetImpl.mem X (dom Γt)) eqn:Hmem.
  2:{ (* no clash: X ∉ dom Γt *)
      assert (HXnot : X `notin` dom Γt)
        by (intro Hc; apply AtomSetImpl.mem_1 in Hc; rewrite Hc in Hmem; discriminate).
      assert (HXA0 : X `notin` ftvar_in_ptyp A0).
      { intro Hin. rewrite <- ftvar_ptyp_to_btyp_inh in Hin.
        apply d_typing_wf_btyp in Hty; [ | exact Hwf ].
        apply (d_wf_btyp_ftvar Hty) in Hin. apply binds_In in Hin. contradiction. }
      apply skel_safe_subst_unit; [ | exact HXA0 ].
      apply (Hcov ((X ~ dbind_tvar) ++ Γt) A0).
      - apply crtw_cons; [ apply dbr_refl | exact Hcr ].
      - apply d_wf_denv__tvar; [ exact Hwf | exact HXnot ].
      - rewrite_env (nil ++ (X ~ dbind_tvar) ++ Γt). apply d_typing_weakening. exact Hty. }
  (* clash: X ∈ dom Γt ⇒ X is a tw-inserted tvar *)
  apply AtomSetImpl.mem_2 in Hmem. apply binds_In_inv in Hmem. destruct Hmem as [dX HbX].
  assert (HXsrc : X `notin` dom Γ') by (clear - HX; fsetdec).
  assert (HdX : dX = dbind_tvar)
    by (eapply ctx_refines_tw_extra_tvar; [ exact Hcr | exact HbX | exact HXsrc ]). subst dX.
  assert (Huniq : uniq Γt) by (eapply d_wf_denv_uniq; exact Hwf).
  destruct (binds_split _ _ _ _ HbX) as [Γb [Γa Hsplit]]. subst Γt.
  pick fresh W for
    (dom (Γa ++ (X ~ dbind_tvar) ++ Γb) `union` ftvar_in_ptyp A0
       `union` singleton X `union` dom Γ' `union` ftvar_in_exp e
       `union` ftvar_in_bskl QX).
  set (Γt' := map (subst_var_dbind X W) Γa ++ (W ~ dbind_tvar) ++ Γb).
  assert (Hfe : X `notin` ftvar_in_exp e) by (clear - HX; fsetdec).
  assert (Htyw : Γt' ⊢[ mode_tc ] e ⦂ ptyp_to_btyp_inh (subst_ptyp_in_ptyp (ptyp_var_f W) X A0)).
  { unfold Γt'. rewrite <- ptyp_to_btyp_inh_subst_var.
    rewrite <- (subst_ptyp_in_exp_fresh_eq e (ptyp_var_f W) X Hfe).
    eapply d_typing_rename_tvar with (Γ1 := Γa) (Γ2 := Γb) (X0 := X) (Y := W);
      [ exact Hty | reflexivity | clear - Fr; fsetdec | eapply tvar_clean_mid; exact Hwf ]. }
  assert (Hwfw : d_wf_denv Γt').
  { unfold Γt'. eapply d_wf_denv_rename_tvar with (Γ1 := Γa) (Γ2 := Γb) (X0 := X);
      [ exact Hwf | reflexivity | clear - Fr; fsetdec ]. }
  assert (Hcrw : ctx_refines_tw Γ' Γt').
  { unfold Γt'. eapply ctx_refines_tw_rename_tvar;
      [ exact Hcr | exact Hwf' | exact HXsrc | clear - Fr; fsetdec ]. }
  assert (HXnot' : X `notin` dom Γt').
  { unfold Γt'. simpl_env.
    assert (HxΓa : X `notin` dom Γa) by solve_uniq.
    assert (HxΓb : X `notin` dom Γb) by solve_uniq. clear - HxΓa HxΓb Fr. fsetdec. }
  assert (HXA0w : X `notin` ftvar_in_ptyp (subst_ptyp_in_ptyp (ptyp_var_f W) X A0)).
  { intro Hin. apply ftvar_in_ptyp_subst_ptyp_in_ptyp_upper in Hin. simpl in Hin.
    assert (X <> W) by (clear - Fr; fsetdec). clear - Hin H. fsetdec. }
  assert (Hsk : skel_safe nil (subst_pskl_in_pskl pskl_unit X (bskl_to_pskl QX))
                  (subst_ptyp_in_ptyp (ptyp_var_f W) X A0)).
  { apply skel_safe_subst_unit; [ | exact HXA0w ].
    apply (Hcov ((X ~ dbind_tvar) ++ Γt') (subst_ptyp_in_ptyp (ptyp_var_f W) X A0)).
    - apply crtw_cons; [ apply dbr_refl | exact Hcrw ].
    - apply d_wf_denv__tvar; [ exact Hwfw | exact HXnot' ].
    - rewrite_env (nil ++ (X ~ dbind_tvar) ++ Γt'). apply d_typing_weakening. exact Htyw. }
  pose proof (@skel_safe_rename_tvar nil
                (subst_pskl_in_pskl pskl_unit X (bskl_to_pskl QX))
                (subst_ptyp_in_ptyp (ptyp_var_f W) X A0) Hsk W X
                ltac:(simpl; auto) HXA0w) as Hback. simpl in Hback.
  rewrite subst_pskl_in_pskl_fresh_eq in Hback
    by (apply ftvar_in_pskl_subst_pskl_in_pskl_notin;
        [ rewrite ftvar_in_pskl_bskl_to_pskl; clear - Fr; fsetdec | clear; simpl; fsetdec ]).
  rewrite ptyp_rename_rename in Hback by (clear - Fr; fsetdec).
  exact Hback.
Qed.

Lemma bskl_to_pskl_subst_unit : forall Q X,
    subst_pskl_in_pskl pskl_unit X (bskl_to_pskl Q)
    = bskl_to_pskl (subst_bskl_in_bskl bskl_unit X Q).
Proof.
  induction Q; intros X; simpl;
    try reflexivity;
    try (rewrite IHQ; reflexivity);
    try (rewrite IHQ1, IHQ2; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

(** [colour] commutes with the [X := unit] tvar substitution.  By induction on
    the type [A]; the arrow/∀ nodes case-split on [Q]'s (tophole-peeled) head,
    and the syn-default leaves use the painting-substitution commutes. *)
Lemma colour_subst_unit : forall A Q X,
    subst_bskl_in_bskl bskl_unit X (colour Q A)
    = colour (subst_bskl_in_bskl bskl_unit X Q) (subst_ptyp_in_ptyp ptyp_unit X A).
Proof.
  induction A; intros Q X; simpl.
  - reflexivity.
  - reflexivity.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
  - destruct Q; simpl;
      try (rewrite IHA1, IHA2; reflexivity);
      try (rewrite ! pskl_to_bskl_syn_subst_unit, ! ptyp_to_pskl_subst_unit; reflexivity).
    + match goal with |- context [ if ?b then _ else _ ] => destruct b end; simpl;
        rewrite ! pskl_to_bskl_syn_subst_unit, ! ptyp_to_pskl_subst_unit; reflexivity.
    + destruct Q; simpl;
        try (rewrite IHA1, IHA2; reflexivity);
        try (rewrite ! pskl_to_bskl_syn_subst_unit, ! ptyp_to_pskl_subst_unit; reflexivity).
      match goal with |- context [ if ?b then _ else _ ] => destruct b end; simpl;
        rewrite ! pskl_to_bskl_syn_subst_unit, ! ptyp_to_pskl_subst_unit; reflexivity.
  - destruct Q; simpl;
      try (rewrite IHA; reflexivity);
      try (rewrite ! pskl_to_bskl_syn_subst_unit, ! ptyp_to_pskl_subst_unit; reflexivity).
    match goal with |- context [ if ?b then _ else _ ] => destruct b end; simpl;
      rewrite ! pskl_to_bskl_syn_subst_unit, ! ptyp_to_pskl_subst_unit; reflexivity.
Qed.

Lemma d_pat_total_gen : forall m Γ e B,
    Γ ⊢[ m ] e ⦂ B -> d_wf_denv Γ ->
    forall Γ', ctx_refines Γ' Γ -> d_wf_denv Γ' -> gpat m Γ' e B.
Proof.
  intros m Γ e B Hty. induction Hty; intros Hwf Γ' Hcr Hwf'.
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
    + (* tc: SAFETY of a checked, subsumed base term — the ghostified safe
         inference, fully assembled in [d_pat_base_safe_tc_gen]. *)
      eapply d_pat_base_safe_tc_gen; [ exact Hwf | eassumption | eassumption | exact Hcr ].
    + (* fn: a subsumed base term in function mode — SYN route (unit/kept-var/
         anno) via [safe_fn_skel], or the [□]-fill route via [safe_skel_hole_fill],
         assembled in [d_pat_base_safe_fn_gen]. *)
      eapply d_pat_base_safe_fn_gen; [ exact Hwf | eassumption | eassumption | eassumption | exact Hcr ].
  - (* freeze: the inner TI inference is [is_sskl] ⇒ a syn-painting that
       [d_pat__freeze] lifts; safety reuses the IH's (syn-keyed) TI fill after
       inverting the freeze typing back to [Γt ⊢ti e ⦂ syn A1]. *)
    destruct (IHHty Hwf Γ' Hcr Hwf') as [Q0 [Hinf [Hsskl Hfill]]].
    exists Q0. split; [ | split; [ exact Hsskl | ] ].
    + rewrite <- (is_sskl_syn_roundtrip Hsskl). apply d_pat__freeze.
      rewrite (is_sskl_syn_roundtrip Hsskl). exact Hinf.
    + intros Γt A1 Hcrt Hwft HA.
      apply d_typing_freeze_inv in HA.
      exact (Hfill Γt A1 Hcrt Hwft HA).
  - (* forall: a value generalised at [∀].  The skeleton is the same [is_sskl]
       witness as at the body (no [∀] rule in [d_pat]); we read it off the IH at a
       fresh tvar [X] and STRENGTHEN by [X := unit] back to [Γ'].  For the fill:
       the new refinement sends the peeled [X] into [Γ], and the checking type
       [A0] lives in [Γt] (so [X ∉ ftvar A0]), hence [d_refine_syn_subst_unit]
       removes [X] leaving the [colour] of [A0] unchanged. *)
    pick fresh X for (L `union` dom Γ `union` dom Γ' `union` ftvar_in_exp e
                        `union` ftvar_in_denv Γ' `union` ftvar_in_ptyp A).
    pose proof (H1 X ltac:(fsetdec)
                  ltac:(apply d_wf_denv__tvar; [ exact Hwf | fsetdec ])
                  ((X ~ dbind_tvar) ++ Γ')
                  ltac:(apply ctxr_cons; [ apply dbr_refl | exact Hcr ])
                  ltac:(apply d_wf_denv__tvar; [ exact Hwf' | fsetdec ])) as Hgp.
    simpl in Hgp. destruct Hgp as [QX [HinfX [HssklX HfillX]]].
    simpl. exists (subst_bskl_in_bskl bskl_unit X QX). split; [ | split ].
    + (* inference at [Γ'] : strengthen [(X:tvar)::Γ' ⊢ e ⇨ QX] by [X := unit] *)
      pose proof (d_pat_subst_unit _ _ _ _ HinfX nil X Γ'
                    ltac:(reflexivity) ltac:(apply tvar_clean_fresh; fsetdec)) as Hsg.
      simpl in Hsg. rewrite subst_ptyp_in_exp_fresh_eq in Hsg by fsetdec. exact Hsg.
    + (* is_sskl preserved by the substitution *)
      apply is_sskl_subst_unit. exact HssklX.
    + (* skel: strengthen the body-at-[X] coverage by [X := unit] via
         [skel_safe_forall_cover] (context-free; clash of [X] with a tw-inserted
         tvar in [Γt] is renamed out there). *)
      intros Γt A0 Hcrt Hwft HA0.
      rewrite <- bskl_to_pskl_subst_unit.
      apply (@skel_safe_forall_cover e Γ' X QX
               ltac:(clear - Fr; fsetdec) Hwf' HfillX Γt A0 Hcrt Hwft HA0).
  - (* abs: λ in mode [m].  At TC the fill is the (Qed) [abs_check_fill], but
       [d_pat__abs_check] needs the body to infer a SYN/principal skeleton
       [pskl_to_bskl_syn P], whereas the IH ([gpat tc]) only yields the body's
       SAFE (ghostified) skeleton — a distinct, more concrete inference not yet
       available (needs a principal-body-skeleton lemma).  At FN the domain is
       forced [inh]. *)
    destruct m as [ | | m0 ].
    + (* ti: the λ SYNTHESISES [bskl_arrow (inh □) Qb] via [d_pat__abs] (P := □);
         [skel] via [abs_ti_fill_skel] fed by [gpat_skel_rename] at the syn
         painting (the body coverage there is [⦂ syn A]). *)
      pick fresh x0 for
        (L `union` dom Γ `union` dom Γ' `union` fvar_in_exp e `union` ftvar_in_exp e).
      destruct (H2 x0 ltac:(fsetdec)
                  ltac:(apply d_wf_denv__typ;
                          [ exact Hwf | fsetdec
                          | match goal with HA : _ ⊢ₚ _ |- _ => exact HA end ])
                  ((x0 ~ dbind_skl pskl_hole) ++ Γ')
                  ltac:(apply ctxr_cons; [ apply dbr_typ_hole | exact Hcr ])
                  ltac:(apply d_wf_denv__skl; [ exact Hwf' | fsetdec | apply d_wf_pskl__hole ]))
        as [Qb [Hinfb [Hssklb Hfillb]]].
      exists (bskl_arrow (pskl_to_bskl_inh pskl_hole) Qb). split; [ | split ].
      * (* inference: [d_pat__abs] with [P := □] *)
        apply d_pat__abs with
          (L := L `union` {{x0}} `union` dom Γ `union` dom Γ' `union` fvar_in_exp e)
          (P := pskl_hole).
        -- discriminate.
        -- apply d_wf_pskl__hole.
        -- intros x Hx.
           replace (open_exp_wrt_exp e (exp_var_f x))
             with (subst_exp_in_exp (exp_var_f x) x0 (open_exp_wrt_exp e (exp_var_f x0)))
             by (symmetry; apply subst_exp_in_exp_intro; fsetdec).
           eapply d_pat_rename_var with (Γ1 := nil) (x := x0) (d := dbind_skl pskl_hole);
             [ exact Hinfb | reflexivity | discriminate | simpl_env; fsetdec ].
      * (* is_sskl *)
        replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
        apply is_sskl__arrow; [ apply is_sskl__hole | exact Hssklb ].
      * (* skel *)
        intros Γt A1 Hcrt Hwft HA.
        simpl.
        eapply abs_ti_fill_skel with (Qb := Qb) (Γ' := Γ')
          (L_b := L `union` {{x0}} `union` dom Γ `union` dom Γ'
                    `union` fvar_in_exp e `union` ftvar_in_exp e);
          [ | exact Hcrt | exact Hwft | exact HA ].
        intros x Hx.
        eapply gpat_skel_rename with (m := mode_ti) (paint := ptyp_to_btyp_syn)
          (db := dbind_skl pskl_hole) (e := e) (Γ' := Γ') (Q := Qb) (x := x0) (y := x);
          [ apply ptyp_to_btyp_syn_subst_var
          | discriminate
          | clear - Fr; simpl; fsetdec | exact Hwf'
          | intros y0 Hy0; apply d_wf_denv__skl; [ exact Hwf' | exact Hy0 | apply d_wf_pskl__hole ]
          | exact Hfillb | clear - Hx; fsetdec ].
    + (* tc: the body's safe witness is [is_sskl] ⇒ syn-paintable
         ([is_sskl_syn_roundtrip]) ⇒ feeds [d_pat__abs_check]; the fill is the
         (Qed) [abs_check_fill]. *)
      pick fresh x0 for
        (L `union` dom Γ `union` dom Γ' `union` fvar_in_exp e `union` ftvar_in_exp e).
      destruct (H2 x0 ltac:(fsetdec)
                  ltac:(apply d_wf_denv__typ;
                          [ exact Hwf | fsetdec
                          | match goal with HA : _ ⊢ₚ _ |- _ => exact HA end ])
                  ((x0 ~ dbind_skl pskl_hole) ++ Γ')
                  ltac:(apply ctxr_cons; [ apply dbr_typ_hole | exact Hcr ])
                  ltac:(apply d_wf_denv__skl; [ exact Hwf' | fsetdec | apply d_wf_pskl__hole ]))
        as [Qb [Hinfb [Hssklb Hfillb]]].
      exists (bskl_tophole (bskl_arrow bskl_hole Qb)). split; [ | split ].
      * (* inference: body's [is_sskl] witness lifts to a syn body via roundtrip;
           the per-[x] body inference comes from the [x0] one by [d_pat_rename_var]. *)
        rewrite <- (is_sskl_syn_roundtrip Hssklb) at 1.
        apply d_pat__abs_check with
          (L := L `union` {{x0}} `union` dom Γ `union` dom Γ' `union` fvar_in_exp e)
          (P := bskl_to_pskl Qb).
        intros x Hx. rewrite (is_sskl_syn_roundtrip Hssklb).
        replace (open_exp_wrt_exp e (exp_var_f x))
          with (subst_exp_in_exp (exp_var_f x) x0 (open_exp_wrt_exp e (exp_var_f x0)))
          by (symmetry; apply subst_exp_in_exp_intro; fsetdec).
        eapply d_pat_rename_var with (Γ1 := nil) (x := x0) (d := dbind_skl pskl_hole);
          [ exact Hinfb | reflexivity | discriminate | simpl_env; fsetdec ].
      * (* is_sskl *)
        apply is_sskl__tophole, is_sskl__arrow; [ apply is_sskl__hole | exact Hssklb ].
      * (* skel (CONTEXT-FREE): the λ [skel_safe] via [abs_check_fill_skel]
           (which peels a checked [∀] into [Γt] with the body coverage unchanged),
           fed the body coverage [Hfillb] transported from [x0] to any fresh [x]
           by [gpat_skel_rename] (LN bound-var rename over [ctx_refines_tw]).
           Retires [abs_check_fill_structural]'s [forall] admit. *)
        intros Γt A1 Hcrt Hwft HA.
        simpl.
        eapply abs_check_fill_skel with (Qb := Qb) (Γ' := Γ')
          (L_b := L `union` {{x0}} `union` dom Γ `union` dom Γ'
                    `union` fvar_in_exp e `union` ftvar_in_exp e);
          [ | exact Hcrt | exact Hwft | exact HA ].
        intros x Hx.
        eapply gpat_skel_rename with (m := mode_tc) (paint := ptyp_to_btyp_inh)
          (db := dbind_skl pskl_hole) (e := e) (Γ' := Γ') (Q := Qb) (x := x0) (y := x);
          [ apply ptyp_to_btyp_inh_subst_var
          | discriminate
          | clear - Fr; simpl; fsetdec | exact Hwf'
          | intros y0 Hy0; apply d_wf_denv__skl; [ exact Hwf' | exact Hy0 | apply d_wf_pskl__hole ]
          | exact Hfillb | clear - Hx; fsetdec ].
    + (* fn m0: the domain is forced [inh].  Run the body at the CONCRETE domain
         [x0 : skl (ptyp_to_pskl A)] (via [dbr_typ_skl]) so the inferred arrow
         keeps its polymorphism-preserving [inh] domain — matching the
         algorithmic [a_pat__abs]/[a_split].  The codomain safety [safe_skel m0
         Qc B] comes straight from the body [gpat] at [fn], or (at [ti]/[tc])
         from its coverage at the real body context — [mod_comp_ty B m0] paints [B]
         so the raw body typing IS the required painting derivation. *)
      assert (HpA : Γ ⊢ₚ A) by assumption.
      assert (HskB : mod_comp_ty B m0) by (match goal with Hsk : mod_comp_ty _ (mode_fn _) |- _ => inversion Hsk; assumption end).
      assert (HwfPA : Γ' ⨟ nil ⊢ₚₛ (ptyp_to_pskl A)).
      { apply d_wf_pskl_of_ptyp;
          [ eapply d_wf_ptyp_lc; eapply d_wf_ptyp_ctx_refines; [ exact HpA | exact Hcr ]
          | intros X HX; right;
            eapply d_wf_ptyp_ftvar; [ eapply d_wf_ptyp_ctx_refines; [ exact HpA | exact Hcr ] | exact HX ] ]. }
      pick fresh x0 for
        (L `union` dom Γ `union` dom Γ' `union` fvar_in_exp e `union` ftvar_in_exp e).
      assert (Hcrb : ctx_refines ((x0 ~ dbind_skl (ptyp_to_pskl A)) ++ Γ') ((x0 ~ dbind_typ A) ++ Γ))
        by (apply ctxr_cons; [ apply dbr_typ_skl | exact Hcr ]).
      assert (Hwfb : d_wf_denv ((x0 ~ dbind_skl (ptyp_to_pskl A)) ++ Γ'))
        by (apply d_wf_denv__skl; [ exact Hwf' | clear - Fr; fsetdec | exact HwfPA ]).
      assert (Hwftb : d_wf_denv ((x0 ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; [ exact Hwf | clear - Fr; fsetdec | exact HpA ]).
      pose proof (H2 x0 ltac:(clear - Fr; fsetdec) Hwftb
                    ((x0 ~ dbind_skl (ptyp_to_pskl A)) ++ Γ') Hcrb Hwfb) as Hbody.
      assert (Hex : exists Qc,
                 ((x0 ~ dbind_skl (ptyp_to_pskl A)) ++ Γ')
                   ⊢[ m0 ] (open_exp_wrt_exp e (exp_var_f x0)) ⇨ Qc
                 /\ safe_skel m0 Qc B).
      { destruct m0.
        - (* ti : convert coverage at the real body context [(x0:typ A)::Γ] *)
          destruct Hbody as [Qc [Hinf [Hssk Hcov]]].
          assert (Hstyp : is_styp B) by (inversion HskB; assumption).
          exists Qc. split; [ exact Hinf | ]. simpl.
          eapply (Hcov ((x0 ~ dbind_typ A) ++ Γ) (btyp_to_ptyp B));
            [ apply crtw_cons; [ apply dbr_typ_skl | apply crtw_base; exact Hcr ]
            | exact Hwftb
            | rewrite (ptyp_to_btyp_syn_btyp_to_ptyp (is_styp_is_syn Hstyp));
              apply H1; clear - Fr; fsetdec ].
        - (* tc *) destruct Hbody as [Qc [Hinf [Hssk Hcov]]].
          assert (Hityp : is_ityp B) by (inversion HskB; assumption).
          exists Qc. split; [ exact Hinf | ]. simpl.
          eapply (Hcov ((x0 ~ dbind_typ A) ++ Γ) (btyp_to_ptyp B));
            [ apply crtw_cons; [ apply dbr_typ_skl | apply crtw_base; exact Hcr ]
            | exact Hwftb
            | rewrite (is_ityp_ptyp_to_btyp_inh Hityp); apply H1; clear - Fr; fsetdec ].
        - (* fn m0' : the body [gpat] already carries [safe_skel] *)
          exact Hbody. }
      destruct Hex as [Qc [HinfQc HsafeQc]].
      exists (bskl_arrow (pskl_to_bskl_inh (ptyp_to_pskl A)) Qc). split.
      * (* inference: [d_pat__abs] with the CONCRETE domain [P := ptyp_to_pskl A] *)
        apply d_pat__abs with
          (L := L `union` {{x0}} `union` dom Γ `union` dom Γ' `union` fvar_in_exp e)
          (P := ptyp_to_pskl A).
        -- discriminate.
        -- exact HwfPA.
        -- intros x Hx.
           replace (open_exp_wrt_exp e (exp_var_f x))
             with (subst_exp_in_exp (exp_var_f x) x0 (open_exp_wrt_exp e (exp_var_f x0)))
             by (symmetry; apply subst_exp_in_exp_intro; clear - Fr Hx; fsetdec).
           eapply d_pat_rename_var with (Γ1 := nil) (x := x0) (d := dbind_skl (ptyp_to_pskl A));
             [ exact HinfQc | reflexivity | discriminate | simpl_env; clear - Fr; fsetdec ].
      * (* safe_skel (fn m0) : the peeled arrow with concrete [inh] domain *)
        simpl. exists (ptyp_to_btyp_inh A), B, (pskl_to_bskl_inh (ptyp_to_pskl A)), Qc.
        split; [ reflexivity | ].
        split; [ reflexivity | ].
        split; [ rewrite bskl_to_pskl_pskl_to_bskl_inh, btyp_to_ptyp_ptyp_to_btyp_inh;
                 apply skel_safe_of_ptyp; eapply d_wf_ptyp_lc;
                 eapply d_wf_ptyp_ctx_refines; [ exact HpA | exact Hcr ]
               | exact HsafeQc ].
  - (* abs_anno: annotated λ; like [abs] but the domain skeleton is the
       annotation's own pskl ([abs_anno_*_fill_skel]). *)
    destruct m as [ | | m0 ].
    + (* ti: SYNTHESISE [bskl_arrow (btyp_to_bskl B1) Qb]; [is_styp] forces
         [B1 = syn A]. *)
      match goal with Hsk : mod_comp_ty _ mode_ti |- _ =>
        inversion Hsk as [ ? Hsty | | ] end.
      assert (HB1 : B1 = ptyp_to_btyp_syn A)
        by (rewrite <- H0; symmetry; apply ptyp_to_btyp_syn_btyp_to_ptyp;
            apply is_styp_is_syn; eapply is_styp_arrow_l; exact Hsty).
      pick fresh x0 for
        (L `union` dom Γ `union` dom Γ' `union` fvar_in_exp e `union` ftvar_in_exp e).
      destruct (H3 x0 ltac:(fsetdec)
                  ltac:(apply d_wf_denv__typ; [ exact Hwf | fsetdec | exact H ])
                  ((x0 ~ dbind_typ A) ++ Γ')
                  ltac:(apply ctxr_cons; [ apply dbr_refl | exact Hcr ])
                  ltac:(apply d_wf_denv__typ; [ exact Hwf' | fsetdec
                        | eapply d_wf_ptyp_ctx_refines; [ exact H | exact Hcr ] ]))
        as [Qb [Hinfb [Hssklb Hfillb]]].
      exists (bskl_arrow (btyp_to_bskl B1) Qb). split; [ | split ].
      * apply d_pat__abs_anno with (L := L `union` {{x0}} `union` dom Γ
                                          `union` dom Γ' `union` fvar_in_exp e) (B := B1).
        -- discriminate.
        -- eapply d_wf_ptyp_ctx_refines; [ exact H | exact Hcr ].
        -- exact H0.
        -- intros x Hx.
           replace (open_exp_wrt_exp e (exp_var_f x))
             with (subst_exp_in_exp (exp_var_f x) x0 (open_exp_wrt_exp e (exp_var_f x0)))
             by (symmetry; apply subst_exp_in_exp_intro; fsetdec).
           eapply d_pat_rename_var with (Γ1 := nil) (x := x0) (d := dbind_typ A);
             [ exact Hinfb | reflexivity | discriminate | simpl_env; fsetdec ].
      * rewrite HB1, btyp_to_bskl_ptyp_to_btyp_syn_eq.
        apply is_sskl__arrow;
          [ apply is_sskl_pskl_to_bskl_syn, lc_pskl_ptyp_to_pskl;
            eapply d_wf_ptyp_lc_loc; exact H | exact Hssklb ].
      * intros Γt A1 Hcrt Hwft HA.
        simpl. rewrite HB1, bskl_to_pskl_btyp_to_bskl_ptyp_to_btyp_syn.
        eapply abs_anno_ti_fill_skel with (Ann := A) (Qb := Qb) (Γ' := Γ')
          (L_b := L `union` {{x0}} `union` dom Γ `union` dom Γ'
                    `union` fvar_in_exp e `union` ftvar_in_exp e);
          [ eapply d_wf_ptyp_lc_loc; exact H | | exact Hcrt | exact Hwft | exact HA ].
        intros x Hx.
        eapply gpat_skel_rename with (m := mode_ti) (paint := ptyp_to_btyp_syn)
          (db := dbind_typ A) (e := e) (Γ' := Γ') (Q := Qb) (x := x0) (y := x);
          [ apply ptyp_to_btyp_syn_subst_var
          | discriminate
          | clear - Fr; simpl; fsetdec | exact Hwf'
          | intros y0 Hy0; apply d_wf_denv__typ;
              [ exact Hwf' | exact Hy0 | eapply d_wf_ptyp_ctx_refines; [ exact H | exact Hcr ] ]
          | exact Hfillb | clear - Hx; fsetdec ].
    + (* tc *)
      pick fresh x0 for
        (L `union` dom Γ `union` dom Γ' `union` fvar_in_exp e `union` ftvar_in_exp e).
      destruct (H3 x0 ltac:(fsetdec)
                  ltac:(apply d_wf_denv__typ; [ exact Hwf | fsetdec | exact H ])
                  ((x0 ~ dbind_typ A) ++ Γ')
                  ltac:(apply ctxr_cons; [ apply dbr_refl | exact Hcr ])
                  ltac:(apply d_wf_denv__typ; [ exact Hwf' | fsetdec
                        | eapply d_wf_ptyp_ctx_refines; [ exact H | exact Hcr ] ]))
        as [Qb [Hinfb [Hssklb Hfillb]]].
      exists (bskl_tophole (bskl_arrow (btyp_to_bskl (ptyp_to_btyp_syn A)) Qb)).
      split; [ | split ].
      * rewrite <- (is_sskl_syn_roundtrip Hssklb) at 1.
        apply d_pat__abs_anno_check with
          (L := L `union` {{x0}} `union` dom Γ `union` dom Γ' `union` fvar_in_exp e).
        -- eapply d_wf_ptyp_ctx_refines; [ exact H | exact Hcr ].
        -- intros x Hx. rewrite (is_sskl_syn_roundtrip Hssklb).
           replace (open_exp_wrt_exp e (exp_var_f x))
             with (subst_exp_in_exp (exp_var_f x) x0 (open_exp_wrt_exp e (exp_var_f x0)))
             by (symmetry; apply subst_exp_in_exp_intro; fsetdec).
           eapply d_pat_rename_var with (Γ1 := nil) (x := x0) (d := dbind_typ A);
             [ exact Hinfb | reflexivity | discriminate | simpl_env; fsetdec ].
      * apply is_sskl__tophole, is_sskl__arrow; [ | exact Hssklb ].
        rewrite btyp_to_bskl_ptyp_to_btyp_syn_eq.
        apply is_sskl_pskl_to_bskl_syn, lc_pskl_ptyp_to_pskl.
        eapply d_wf_ptyp_lc_loc; exact H.
      * intros Γt A1 Hcrt Hwft HA.
        simpl. rewrite bskl_to_pskl_btyp_to_bskl_ptyp_to_btyp_syn.
        eapply abs_anno_check_fill_skel with (Ann := A) (Qb := Qb) (Γ' := Γ')
          (L_b := L `union` {{x0}} `union` dom Γ `union` dom Γ'
                    `union` fvar_in_exp e `union` ftvar_in_exp e);
          [ eapply d_wf_ptyp_lc_loc; exact H | | exact Hcrt | exact Hwft | exact HA ].
        intros x Hx.
        eapply gpat_skel_rename with (m := mode_tc) (paint := ptyp_to_btyp_inh)
          (db := dbind_typ A) (e := e) (Γ' := Γ') (Q := Qb) (x := x0) (y := x);
          [ apply ptyp_to_btyp_inh_subst_var
          | discriminate
          | clear - Fr; simpl; fsetdec | exact Hwf'
          | intros y0 Hy0; apply d_wf_denv__typ;
              [ exact Hwf' | exact Hy0 | eapply d_wf_ptyp_ctx_refines; [ exact H | exact Hcr ] ]
          | exact Hfillb | clear - Hx; fsetdec ].
    + (* fn m0: the annotation [A] already gives the concrete domain, so the body
         runs at [x0 : typ A] ([dbr_refl]) and the inferred arrow keeps the
         annotation's own domain skeleton [btyp_to_bskl B1] — which is [skel_safe]
         for [B1].  Codomain safety from the body [gpat] as in the [abs] case. *)
      assert (HpA : Γ ⊢ₚ A) by assumption.
      assert (HskB2 : mod_comp_ty B2 m0)
        by (match goal with Hsk : mod_comp_ty (btyp_arrow B1 B2) (mode_fn _) |- _ =>
              inversion Hsk; assumption end).
      assert (HwfA' : d_wf_ptyp Γ' A) by (eapply d_wf_ptyp_ctx_refines; [ exact HpA | exact Hcr ]).
      pick fresh x0 for
        (L `union` dom Γ `union` dom Γ' `union` fvar_in_exp e `union` ftvar_in_exp e).
      assert (Hwftb : d_wf_denv ((x0 ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; [ exact Hwf | clear - Fr; fsetdec | exact HpA ]).
      pose proof (H3 x0 ltac:(clear - Fr; fsetdec) Hwftb
                    ((x0 ~ dbind_typ A) ++ Γ')
                    ltac:(apply ctxr_cons; [ apply dbr_refl | exact Hcr ])
                    ltac:(apply d_wf_denv__typ; [ exact Hwf' | clear - Fr; fsetdec | exact HwfA' ]))
        as Hbody.
      assert (Hex : exists Qc,
                 ((x0 ~ dbind_typ A) ++ Γ') ⊢[ m0 ] (open_exp_wrt_exp e (exp_var_f x0)) ⇨ Qc
                 /\ safe_skel m0 Qc B2).
      { destruct m0.
        - destruct Hbody as [Qc [Hinf [Hssk Hcov]]].
          assert (Hstyp : is_styp B2) by (inversion HskB2; assumption).
          exists Qc. split; [ exact Hinf | ]. simpl.
          eapply (Hcov ((x0 ~ dbind_typ A) ++ Γ) (btyp_to_ptyp B2));
            [ apply crtw_cons; [ apply dbr_refl | apply crtw_base; exact Hcr ]
            | exact Hwftb
            | rewrite (ptyp_to_btyp_syn_btyp_to_ptyp (is_styp_is_syn Hstyp));
              apply H2; clear - Fr; fsetdec ].
        - destruct Hbody as [Qc [Hinf [Hssk Hcov]]].
          assert (Hityp : is_ityp B2) by (inversion HskB2; assumption).
          exists Qc. split; [ exact Hinf | ]. simpl.
          eapply (Hcov ((x0 ~ dbind_typ A) ++ Γ) (btyp_to_ptyp B2));
            [ apply crtw_cons; [ apply dbr_refl | apply crtw_base; exact Hcr ]
            | exact Hwftb
            | rewrite (is_ityp_ptyp_to_btyp_inh Hityp); apply H2; clear - Fr; fsetdec ].
        - exact Hbody. }
      destruct Hex as [Qc [HinfQc HsafeQc]].
      exists (bskl_arrow (btyp_to_bskl B1) Qc). split.
      * apply d_pat__abs_anno with
          (L := L `union` {{x0}} `union` dom Γ `union` dom Γ' `union` fvar_in_exp e) (B := B1).
        -- discriminate.
        -- exact HwfA'.
        -- exact H0.
        -- intros x Hx.
           replace (open_exp_wrt_exp e (exp_var_f x))
             with (subst_exp_in_exp (exp_var_f x) x0 (open_exp_wrt_exp e (exp_var_f x0)))
             by (symmetry; apply subst_exp_in_exp_intro; clear - Fr Hx; fsetdec).
           eapply d_pat_rename_var with (Γ1 := nil) (x := x0) (d := dbind_typ A);
             [ exact HinfQc | reflexivity | discriminate | simpl_env; clear - Fr; fsetdec ].
      * simpl. exists B1, B2, (btyp_to_bskl B1), Qc.
        split; [ reflexivity | ].
        split; [ reflexivity | ].
        split; [ rewrite bskl_to_pskl_btyp_to_bskl; apply skel_safe_of_ptyp;
                 rewrite H0; eapply d_wf_ptyp_lc; exact HpA
               | exact HsafeQc ].
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
                   Γ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳ B).
Proof.
  intros Γ e B0 Hty Hwf.
  destruct (d_pat_total_gen Hty Hwf (ctx_refines_refl Γ) Hwf) as [Q [HQ [_ Hsafe]]].
  exists Q. split; [ exact HQ | ].
  intros A HA.
  exists (colour (pskl_to_bskl_inh (bskl_to_pskl Q)) A). split; [ apply colour_erasure | ].
  (* recover the [d_refine_syn] fill from the context-free [skel_safe] *)
  apply refine_colour_skel.
  - apply (Hsafe Γ A (ctx_refines_tw_refl Γ) Hwf HA).
  - eapply d_wf_ptyp_lc_loc; eapply d_wf_ptyp_of_btyp_inh;
      eapply d_typing_wf_btyp; [ exact HA | exact Hwf ].
  - intros X HX. right.
    eapply d_wf_btyp_ftvar;
      [ eapply d_typing_wf_btyp; [ exact HA | exact Hwf ]
      | rewrite ftvar_ptyp_to_btyp_inh; exact HX ].
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
