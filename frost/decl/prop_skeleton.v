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
Lemma d_wf_pskl_of_ptyp : forall A,
    lc_ptyp A ->
    forall Γ Ψ,
      (forall X, X `in` ftvar_in_ptyp A -> List.In X Ψ \/ binds X dbind_tvar Γ) ->
      Γ ⨟ Ψ ⊢ₚₛ (ptyp_to_pskl A).
Proof.
  intros A Hlc. induction Hlc; intros Γ Ψ Hcov; simpl.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. apply Hcov. simpl. fsetdec.
  - apply d_wf_pskl__arrow;
      [ apply IHHlc1 | apply IHHlc2 ]; intros Y HY; apply Hcov; simpl; fsetdec.
  - inst_cofinites_for d_wf_pskl__all. intros X HX.
    rewrite <- ptyp_to_pskl_open. apply H0. intros Y HY.
    apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY. simpl in HY.
    apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + left. apply AtomSetImpl.singleton_1 in HY. simpl. left. assumption.
    + specialize (Hcov Y HY).
      destruct Hcov as [HΨ | HG]; [ left; simpl; right; assumption | right; assumption ].
Qed.

(** UNIVERSAL FILL ENGINE for [d_pat_safety]: a plain ghost [□] refines to
    *any* well-scoped type's syn-skeleton — INCLUDING polytypes, since the
    [hole] rule fills with any well-formed [pskl] (which may carry concrete
    [∀]s).  This is the "fills every checking type" half of safety, once the
    safe inference is hole-rich.  (NB this corrects the misconception that
    [□] fills only monotypes: it is the [inh]-painted target that blocked
    polytypes, not the fill itself — see [d_pat_safety].) *)
Lemma d_refine_syn_hole_fills : forall A,
    lc_ptyp A ->
    forall Γ Δ,
      (forall X, X `in` ftvar_in_ptyp A -> binds X dbind_tvar Γ) ->
      Γ ⨟ Δ ⊢ᵣ bskl_hole ⊳ (pskl_to_bskl_syn (ptyp_to_pskl A)).
Proof.
  intros A Hlc Γ Δ Hcov.
  apply d_refine_syn__hole. apply d_wf_pskl_of_ptyp with (Ψ := nil);
    [ exact Hlc | intros X HX; right; apply Hcov; assumption ].
Qed.

(** A universal ghost over a hole [⫯.□] also refines any well-scoped type
    (drop the [⫯] via [tophole_remove], then the [□] fills via the engine).
    Together with [d_refine_syn_hole_fills] this is the full fill side of
    safety: a ghost-rich skeleton refines every checking type. *)
Lemma d_refine_syn_tophole_hole_fills : forall A,
    lc_ptyp A ->
    forall Γ Δ,
      (forall X, X `in` ftvar_in_ptyp A -> binds X dbind_tvar Γ) ->
      Γ ⨟ Δ ⊢ᵣ (bskl_tophole bskl_hole) ⊳ (pskl_to_bskl_syn (ptyp_to_pskl A)).
Proof.
  intros A Hlc Γ Δ Hcov.
  apply d_refine_syn__tophole_remove.
  apply d_refine_syn_hole_fills; auto.
Qed.

(** ===================================================================== *)
(**  GHOST-LHS relation [ghc P R] — faithful [ForallL] instantiation.       *)
(** ===================================================================== *)

(** [ghc P R]: [R] is a [uskl] erasure of the synthesised skeleton [P] in
    which every resolved hole [pskl_hole] erases to EITHER the plain
    unresolved hole [uskl_hole] or the universal/ghost hole [uskl_holeg].
    This is exactly the freedom the paper-faithful [ForallL] needs — the
    tagged-skeleton instantiation [ψ] guesses [HoleG] ([uskl_holeg]) for the
    bound variable (plain [Hole] is NOT a tagged skeleton: [is_tskl]
    excludes it), while [P]'s own intrinsic holes stay [uskl_hole].  Both
    erasures are below / consistent with the same [bskl_hole], so the
    ghostification target [Q] is unchanged. *)
Inductive ghc : pskl -> uskl -> Prop :=
| ghc__unit    : ghc pskl_unit uskl_unit
| ghc__var     : forall X, ghc (pskl_var_f X) (uskl_var_f X)
| ghc__arrow   : forall P1 P2 R1 R2,
    ghc P1 R1 -> ghc P2 R2 -> ghc (pskl_arrow P1 P2) (uskl_arrow R1 R2)
| ghc__all     : forall L body R,
    (forall X, X `notin` L ->
       ghc (open_pskl_wrt_pskl body (pskl_var_f X))
           (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    ghc (pskl_all_syn body) (uskl_all_syn R)
| ghc__hole_h  : ghc pskl_hole uskl_hole
| ghc__hole_g  : ghc pskl_hole uskl_holeg
| ghc__tophole : forall P0 R, ghc P0 R -> ghc (pskl_tophole P0) (uskl_tophole R).

#[local] Hint Constructors ghc : core.

(** The exact syn-erasure (every hole plain) is a [ghc]. *)
Lemma ghc_exact : forall P, lc_pskl P -> ghc P (bskl_to_uskl (pskl_to_bskl_syn P)).
Proof.
  intros P H. induction H; simpl; eauto.
  - inst_cofinites_for ghc__all. intros X HX.
    rewrite <- bskl_to_uskl_open. rewrite <- pskl_to_bskl_syn_open. auto.
Qed.

(** [R] is locally closed whenever [P] is. *)
Lemma ghc_lc : forall P R, ghc P R -> lc_pskl P -> lc_uskl R.
Proof.
  intros P R H. induction H; intros Hlc.
  - apply lc_uskl_unit.
  - apply lc_uskl_var_f.
  - inversion Hlc; subst. apply lc_uskl_arrow; [ apply IHghc1 | apply IHghc2 ]; assumption.
  - inversion Hlc; subst. pick fresh X. apply (lc_uskl_all_syn_exists X).
    apply H0; [ fsetdec | auto ].
  - apply lc_uskl_hole.
  - apply lc_uskl_holeg.
  - inversion Hlc; subst. apply lc_uskl_tophole. apply IHghc; assumption.
Qed.

(** [ghc] is preserved by substituting a free var by the ghost pair
    [(pskl_hole, uskl_holeg)] (the two are [ghc]-related — [ghc__hole_g]). *)
Lemma ghc_subst : forall P R X,
    ghc P R ->
    ghc (subst_pskl_in_pskl pskl_hole X P) (subst_bskl_in_uskl uskl_holeg X R).
Proof.
  intros P R X H. induction H; simpl.
  - apply ghc__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      [ apply ghc__hole_g | apply ghc__var ].
  - apply ghc__arrow; assumption.
  - apply ghc__all with (L := L `union` {{X}}). intros Y HY.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var; [ | fsetdec | apply lc_pskl_hole ].
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; [ | fsetdec | apply lc_uskl_holeg ].
    apply H0. fsetdec.
  - apply ghc__hole_h.
  - apply ghc__hole_g.
  - apply ghc__tophole; assumption.
Qed.

(** Opening a [ghc__all] body with the ghost pair stays a [ghc]: the bound
    variable becomes [pskl_hole] on the left, [uskl_holeg] on the right —
    exactly the [ForallL] instantiation with [HoleG]. *)
Lemma ghc_open_holeg : forall L body R,
    (forall X, X `notin` L ->
       ghc (open_pskl_wrt_pskl body (pskl_var_f X))
           (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    ghc (open_pskl_wrt_pskl body pskl_hole) (open_uskl_wrt_uskl R uskl_holeg).
Proof.
  intros L body R H.
  pick fresh X for (L `union` ftvar_in_pskl body `union` ftvar_in_uskl R).
  rewrite (subst_pskl_in_pskl_intro X body); [ | fsetdec ].
  rewrite (subst_bskl_in_uskl_intro X R); [ | fsetdec ].
  apply ghc_subst. apply H. fsetdec.
Qed.

(** CONSISTENCY REFLEXIVITY for a syn-painted skeleton (on [pskl], so it
    covers BOTH hole-free type skeletons AND skeletons carrying ghost holes
    [pskl_hole]/[pskl_tophole]): the [uskl] erasure of a syn-painted skeleton
    is consistent with that skeleton.  This is the foundational brick of the
    inference side — [d_pat_sub__univ_ghost_r] / [__infer] consume an
    [R ≈ Q] to wrap a base term's skeleton core into a (ghost-)bidirectional
    one, and the core that arises AFTER [forall_l] instantiates a top-level
    [∀] with [□] carries exactly such holes.  All tags are empty (no ε-tags):
    [unit]/[var]/[hole] give [nil], [arrow] combines [nil ++ nil], and the
    syn-painting sends each [∀] to [bskl_all_syn] (matched by [__forall_syn]).
    A [pskl_hole] matches [inh{□}] (= [bskl_hole]) via [__hole]. *)
Lemma d_pat_consis_refl_pskl : forall P,
    lc_pskl P ->
    forall Γ,
      (forall X, X `in` ftvar_in_pskl P -> binds X dbind_tvar Γ) ->
      empty ⨟ Γ ⊨ₛ (bskl_to_uskl (pskl_to_bskl_syn P)) ≈ (pskl_to_bskl_syn P).
Proof.
  intros P Hlc. induction Hlc; intros Γ Hcov; simpl.
  - (* unit *) apply d_pat_consis__unit. fsetdec.
  - (* var_f X *) apply d_pat_consis__var; [ fsetdec | apply Hcov; simpl; fsetdec ].
  - (* arrow *) apply d_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHlc1 | apply IHHlc2 | fsetdec ]; intros Y HY; apply Hcov; simpl; fsetdec.
  - (* all_syn: syn-painting → bskl_all_syn, matched by __forall_syn *)
    inst_cofinites_for d_pat_consis__forall_syn. intros X HX.
    rewrite <- bskl_to_uskl_open. rewrite <- pskl_to_bskl_syn_open.
    apply H0. intros Y HY.
    apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in HY. simpl in HY.
    apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + (* Y = X *) apply AtomSetImpl.singleton_1 in HY. subst.
      apply binds_app_2. apply binds_one_3; reflexivity.
    + (* Y ∈ ftvar P *) apply binds_app_3. apply (Hcov Y HY).
  - (* hole: □ ≈ inh{□} = bskl_hole via __hole *)
    change bskl_hole with (pskl_to_bskl_inh pskl_hole).
    apply d_pat_consis__hole; [ fsetdec | apply d_wf_pskl__hole ].
  - (* tophole: ⫯ ≈ ⫯ via __tophole, recurse *)
    apply d_pat_consis__tophole. apply IHHlc. assumption.
Qed.

(** [ghc]-generalised consistency reflexivity: a ghost-LHS [R] of [P] (holes
    plain OR ghost) is consistent with [P]'s syn-painting.  Same as
    [d_pat_consis_refl_pskl] except a [uskl_holeg] hole matches [bskl_hole]
    via [__ghostg] instead of [__hole]. *)
Lemma d_pat_consis_refl_ghc : forall P R,
    ghc P R ->
    lc_pskl P ->
    forall Γ,
      (forall X, X `in` ftvar_in_pskl P -> binds X dbind_tvar Γ) ->
      empty ⨟ Γ ⊨ₛ R ≈ (pskl_to_bskl_syn P).
Proof.
  intros P R H. induction H; intros Hlc Γ Hcov; simpl.
  - apply d_pat_consis__unit. fsetdec.
  - apply d_pat_consis__var; [ fsetdec | apply Hcov; simpl; fsetdec ].
  - inversion Hlc; subst.
    apply d_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHghc1 | apply IHghc2 | fsetdec ]; try assumption;
      intros Y HY; apply Hcov; simpl; fsetdec.
  - (* all *) inversion Hlc; subst.
    inst_cofinites_for d_pat_consis__forall_syn. intros X HX.
    rewrite <- pskl_to_bskl_syn_open.
    apply H0; [ fsetdec | auto | ].
    intros Y HY. apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in HY. simpl in HY.
    apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + apply AtomSetImpl.singleton_1 in HY. subst.
      apply binds_app_2. apply binds_one_3; reflexivity.
    + apply binds_app_3. apply (Hcov Y HY).
  - (* hole_h: □ ≈ inh{□} = bskl_hole via __hole *)
    change bskl_hole with (pskl_to_bskl_inh pskl_hole).
    apply d_pat_consis__hole; [ fsetdec | apply d_wf_pskl__hole ].
  - (* hole_g: ghost □ ≈ bskl_hole via __ghostg *)
    apply d_pat_consis__ghostg. fsetdec.
  - (* tophole *) inversion Hlc; subst.
    apply d_pat_consis__tophole. apply IHghc; assumption.
Qed.

(** Helpers for the ghostified-inference lemma below. *)

(** Opening with the closed ghost [□] preserves skeleton size (both
    [pskl_var_b] and [pskl_hole] have size 1) — gives the size decrease the
    [∀]-prefix recursion needs. *)
Lemma size_pskl_open_hole_rec : forall P k,
    size_pskl (open_pskl_wrt_pskl_rec k pskl_hole P) = size_pskl P.
Proof.
  induction P; intros k; simpl; try reflexivity;
    try (rewrite IHP; reflexivity);
    try (rewrite IHP1, IHP2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma size_pskl_open_hole : forall P,
    size_pskl (open_pskl_wrt_pskl P pskl_hole) = size_pskl P.
Proof. intro P. apply (size_pskl_open_hole_rec P 0). Qed.

(** The syn-painting of any (lc) skeleton is a synthesised bskl. *)
Lemma is_sskl_pskl_to_bskl_syn : forall P,
    lc_pskl P -> is_sskl (pskl_to_bskl_syn P).
Proof.
  intros P H. induction H; simpl; try (constructor; auto; fail).
  - (* all_syn *) inst_cofinites_for is_sskl__all. intros X HX.
    rewrite <- pskl_to_bskl_syn_open. auto.
Qed.

(** BRICK 2 — GHOSTIFICATION as a RELATION [ghost_of P Q]: [Q] is the
    ghost-rich skeleton obtained from skeleton [P] by instantiating each
    leading [∀] with [□] (the [__all] case strips one [∀] by opening its
    body with [□]) and wrapping the resulting core in a universal ghost [⫯]
    (a bare-hole core stays [□]).  Naming [Q] via a relation (rather than an
    existential) lets the FILL side (brick 3) refer to the SAME [Q] the
    inference side produced. *)
Inductive ghost_of : pskl -> bskl -> Prop :=
| ghost_of__unit : ghost_of pskl_unit (bskl_tophole bskl_unit)
| ghost_of__var  : forall X, ghost_of (pskl_var_f X) (bskl_tophole (bskl_var_f X))
| ghost_of__arrow : forall P1 P2,
    ghost_of (pskl_arrow P1 P2)
             (bskl_tophole (bskl_arrow (pskl_to_bskl_syn P1) (pskl_to_bskl_syn P2)))
| ghost_of__hole : ghost_of pskl_hole bskl_hole
| ghost_of__tophole : forall P0 Q,
    ghost_of P0 Q -> ghost_of (pskl_tophole P0) Q
| ghost_of__all : forall body Q,
    ghost_of (open_pskl_wrt_pskl body pskl_hole) Q ->
    ghost_of (pskl_all_syn body) Q.

(** Every (lc) skeleton HAS a ghostification.  Size induction: stripping a
    [∀] opens its body with the closed [□], which preserves size, so the
    recursion is well-founded ([size_pskl_open_hole]). *)
Lemma ghost_of_total : forall n P,
    size_pskl P <= n -> lc_pskl P -> exists Q, ghost_of P Q.
Proof.
  induction n; intros P Hsz Hlc.
  - destruct Hlc; simpl in Hsz; lia.
  - destruct Hlc as [ | X | P1 P2 _ _ | body Hbody | | P0 HP0 ]; simpl in Hsz.
    + exists (bskl_tophole bskl_unit). apply ghost_of__unit.
    + exists (bskl_tophole (bskl_var_f X)). apply ghost_of__var.
    + eexists. apply ghost_of__arrow.
    + destruct (IHn (open_pskl_wrt_pskl body pskl_hole)) as [Q HQ].
      * rewrite size_pskl_open_hole. lia.
      * apply lc_body_pskl_wrt_pskl; [ exact Hbody | apply lc_pskl_hole ].
      * exists Q. apply ghost_of__all. exact HQ.
    + exists bskl_hole. apply ghost_of__hole.
    + destruct (IHn P0) as [Q HQ]; [ lia | exact HP0 | ].
      exists Q. apply ghost_of__tophole. exact HQ.
Qed.

(** INFERENCE side (generalised over the ghost-LHS [ghc P R]): any ghost-LHS
    [R] of [P] subtypes (in [mode_tc]) to any ghostification [Q] of [P].
    Paper-faithful: the [__all] case instantiates [ForallL] with the tagged
    ghost [HoleG] ([psi := uskl_holeg] ∈ [is_tskl]); the bound variable then
    lands as [uskl_holeg] in the body (tracked by [ghc_open_holeg]), matched
    against [bskl_hole] by [GhostG].  Cores go via [univ_ghost_r] +
    [consis_refl_ghc]; a bare hole-h via [__ghost], a bare hole-g via
    [__ghostg]; leading ⫯ dropped by [univ_ghost_l]. *)
Lemma ghost_of_infer_ghc : forall P Q,
    ghost_of P Q ->
    lc_pskl P ->
    forall R, ghc P R ->
    forall Δ Γ,
      Δ [=] empty ->
      (forall X, X `in` ftvar_in_pskl P -> binds X dbind_tvar Γ) ->
      Δ ⨟ Γ ⊢ₛ[ mode_tc ] R ⊑ Q.
Proof.
  intros P Q Hg. induction Hg; intros Hlc R Hghc Δ Γ Hempty Hcov.
  - (* unit *) inversion Hghc; subst. apply d_pat_sub__univ_ghost_r;
      [ exact Hempty | apply guarded_uskl__unit | apply guarded_bskl__unit
      | apply is_sskl__unit | apply d_pat_consis__unit; fsetdec ].
  - (* var *) inversion Hghc; subst. apply d_pat_sub__univ_ghost_r;
      [ exact Hempty | apply guarded_uskl__var | apply guarded_bskl__var | apply is_sskl__var | ].
    apply d_pat_consis__var; [ fsetdec | apply Hcov; simpl; fsetdec ].
  - (* arrow *) inversion Hlc; subst. inversion Hghc; subst.
    apply d_pat_sub__univ_ghost_r.
    + exact Hempty.
    + apply guarded_uskl__arrow; eapply ghc_lc; eauto.
    + apply guarded_bskl__arrow; apply lc_pskl_to_bskl_syn; assumption.
    + apply is_sskl__arrow; apply is_sskl_pskl_to_bskl_syn; assumption.
    + apply (@d_pat_consis_refl_ghc (pskl_arrow P1 P2));
        [ apply ghc__arrow; assumption | apply lc_pskl_arrow; assumption | assumption ].
  - (* hole: R is uskl_hole (Ghost) or uskl_holeg (GhostG) *) inversion Hghc; subst.
    + change bskl_hole with (pskl_to_bskl_inh pskl_hole).
      apply d_pat_sub__ghost;
        [ exact Hempty | apply d_wf_pskl__hole | apply mod_comp_sk__tc; apply is_sskl__hole ].
    + apply d_pat_sub__ghostg; [ exact Hempty | apply mod_comp_sk__tc; apply is_sskl__hole ].
  - (* tophole *) inversion Hlc; subst. inversion Hghc; subst.
    apply d_pat_sub__univ_ghost_l; [ discriminate | ].
    apply IHHg;
      [ assumption | assumption | exact Hempty | intros Y HY; apply Hcov; simpl; assumption ].
  - (* all: forall_l(HoleG) then IH on the instantiated body *)
    inversion Hlc; subst. inversion Hghc; subst.
    eapply d_pat_sub__forall_l_untagged with (Ψ' := empty) (psi := uskl_holeg);
      [ discriminate | fsetdec | apply d_tags_skl__holeg; fsetdec
      | apply d_wf_uskl__holeg | apply is_tskl__holeg | ].
    apply IHHg.
    + apply lc_body_pskl_wrt_pskl; [ apply lc_body_pskl_all_syn_1; exact Hlc | apply lc_pskl_hole ].
    + eapply ghc_open_holeg. eassumption.
    + fsetdec.
    + intros Y HY. apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in HY.
      simpl in HY. apply Hcov. simpl. fsetdec.
Qed.

(** Corollary recovering the original statement: the exact syn-erasure is a
    ghost-LHS ([ghc_exact]), so it subtypes to any ghostification. *)
Lemma ghost_of_infer : forall P Q,
    ghost_of P Q ->
    lc_pskl P ->
    forall Δ Γ,
      Δ [=] empty ->
      (forall X, X `in` ftvar_in_pskl P -> binds X dbind_tvar Γ) ->
      Δ ⨟ Γ ⊢ₛ[ mode_tc ] (bskl_to_uskl (pskl_to_bskl_syn P)) ⊑ Q.
Proof.
  intros P Q Hg Hlc Δ Γ Hempty Hcov.
  eapply ghost_of_infer_ghc;
    [ exact Hg | exact Hlc | apply ghc_exact; exact Hlc | exact Hempty | exact Hcov ].
Qed.

(** Corollary (the existential inference, brick 2's headline). *)
Lemma d_pat_sub_infer_ghost : forall P,
    lc_pskl P ->
    forall Γ,
      (forall X, X `in` ftvar_in_pskl P -> binds X dbind_tvar Γ) ->
      exists Q, empty ⨟ Γ ⊢ₛ[ mode_tc ] (bskl_to_uskl (pskl_to_bskl_syn P)) ⊑ Q.
Proof.
  intros P Hlc Γ Hcov.
  destruct (ghost_of_total (le_n (size_pskl P)) Hlc) as [Q HQ].
  exists Q. apply ghost_of_infer; [ assumption | assumption | fsetdec | assumption ].
Qed.

(** ===================================================================== *)
(** BRICK 3 — FILL SIDE ([ghost_of_fill], below).                          *)
(**
   [ghost_of (ptyp_to_pskl C) Q -> ... empty⨟Γ ⊢[tc] (ptyp_to_utyp_syn C) ⊑
   (ptyp_to_btyp_inh A') -> exists B, bskl_to_pskl B = ptyp_to_pskl A' ∧
   inh{Q} ⊳ B]: the ghost [Q] for a base term's principal type [C] refines a
   colouring of every checking type [A'].  PROVED (Qed, axiom-free) by a
   DETERMINISTIC witness [colour] (B := colour inh{Q} A') + a [d_sub] induction
   ([ghost_of_fill_gen]) carrying [hole_safe_u nil P U]: the [forall_l] [□]/[φ]
   absorption is handled by [hole_safe_u_subst]; the [__check] base by
   [hole_safe_u_transport] (to A') + [refine_colour_core] / [refine_colour_tophole]
   (the ghost's top [⫯]).  (The earlier [more_ghost]-monotonicity plan was
   abandoned in favour of the [colour] witness.) *)


(** ===================================================================== *)
(** PATH (b) INFRASTRUCTURE — tag-erasing [utyp] skeleton + the holed-subsumes
    invariant the [d_sub] induction carries. *)

(** [utyp_to_pskl]: the tag-erased skeleton of a [utyp] (both ∀-colours and
    ε-tags collapse to [pskl_all_syn], as in [utyp_to_btyp]). *)
Fixpoint utyp_to_pskl (C : utyp) : pskl :=
  match C with
  | utyp_unit => pskl_unit
  | utyp_var_b n => pskl_var_b n
  | utyp_var_f X => pskl_var_f X
  | utyp_arrow C1 C2 => pskl_arrow (utyp_to_pskl C1) (utyp_to_pskl C2)
  | utyp_all_syn C0 => pskl_all_syn (utyp_to_pskl C0)
  | utyp_all_etag _ C0 => pskl_all_syn (utyp_to_pskl C0)
  end.

(** The skeleton of a type's syn-painting is the type's skeleton. *)
Lemma utyp_to_pskl_ptyp_to_utyp_syn : forall C,
    utyp_to_pskl (ptyp_to_utyp_syn C) = ptyp_to_pskl C.
Proof. induction C; simpl; try reflexivity; try (rewrite IHC; reflexivity);
  try (rewrite IHC1, IHC2; reflexivity). Qed.

Lemma utyp_to_pskl_open_rec : forall C V k,
    utyp_to_pskl (open_utyp_wrt_utyp_rec k V C) =
    open_pskl_wrt_pskl_rec k (utyp_to_pskl V) (utyp_to_pskl C).
Proof.
  induction C; intros V k; simpl; try reflexivity;
    try (rewrite IHC; reflexivity); try (rewrite IHC1, IHC2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma utyp_to_pskl_open : forall C V,
    utyp_to_pskl (open_utyp_wrt_utyp C V) =
    open_pskl_wrt_pskl (utyp_to_pskl C) (utyp_to_pskl V).
Proof. intros. unfold open_utyp_wrt_utyp, open_pskl_wrt_pskl.
  apply (utyp_to_pskl_open_rec C V 0). Qed.

(** [pskl_subsumes P S]: [P] is [S] with some sub-skeletons replaced by [□].
    The invariant the [d_sub] induction carries — [P] (the skeleton driving
    [ghost_of]/[Q]) is the LHS-skeleton with [forall_l]-instantiated positions
    holed out. *)
Inductive pskl_subsumes : pskl -> pskl -> Prop :=
| pskl_subsumes__hole  : forall S, pskl_subsumes pskl_hole S
| pskl_subsumes__unit  : pskl_subsumes pskl_unit pskl_unit
| pskl_subsumes__var_f : forall X, pskl_subsumes (pskl_var_f X) (pskl_var_f X)
| pskl_subsumes__var_b : forall n, pskl_subsumes (pskl_var_b n) (pskl_var_b n)
| pskl_subsumes__arrow : forall P1 P2 S1 S2,
    pskl_subsumes P1 S1 -> pskl_subsumes P2 S2 ->
    pskl_subsumes (pskl_arrow P1 P2) (pskl_arrow S1 S2)
| pskl_subsumes__all   : forall P S,
    pskl_subsumes P S -> pskl_subsumes (pskl_all_syn P) (pskl_all_syn S)
| pskl_subsumes__tophole : forall P S,
    pskl_subsumes P S -> pskl_subsumes (pskl_tophole P) (pskl_tophole S).

Lemma pskl_subsumes_refl : forall S, pskl_subsumes S S.
Proof. induction S; constructor; assumption. Qed.

(** Subsumption is preserved by opening, where the LHS opens with [□]
    ([□] subsumes anything) and the RHS with the corresponding instantiation. *)
Lemma pskl_subsumes_open_rec : forall P S,
    pskl_subsumes P S ->
    forall V W k, pskl_subsumes V W ->
    pskl_subsumes (open_pskl_wrt_pskl_rec k V P) (open_pskl_wrt_pskl_rec k W S).
Proof.
  intros P S H. induction H; intros V W k Hvw; simpl;
    try (constructor; auto; fail).
  - (* var_b *) destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl;
      [ apply pskl_subsumes__var_b | assumption | apply pskl_subsumes__var_b ].
Qed.


(** A well-formed type is locally closed. *)
Lemma d_wf_ptyp_lc_loc : forall Γ A, d_wf_ptyp Γ A -> lc_ptyp A.
Proof.
  intros Γ A H. induction H.
  - constructor.
  - constructor.
  - constructor; assumption.
  - pick fresh X. apply (lc_ptyp_all_exists X). apply H0. auto.
Qed.

(** A well-formed type's free tvars are all bound in the context. *)
Lemma d_wf_ptyp_ftvar : forall Γ A,
    d_wf_ptyp Γ A ->
    forall X, X `in` ftvar_in_ptyp A -> binds X dbind_tvar Γ.
Proof.
  intros Γ A H. induction H; intros Y HY; simpl in HY.
  - fsetdec.
  - apply AtomSetImpl.singleton_1 in HY. subst. assumption.
  - apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY]; auto.
  - pick fresh X for (L `union` ftvar_in_ptyp A `union` dom Γ `union` singleton Y).
    assert (HYo : Y `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A (ptyp_var_f X))).
    { eapply ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower. eassumption. }
    specialize (H0 X ltac:(auto) Y HYo).
    analyze_binds H0.
Qed.

(** Hence a well-formed type's skeleton is a well-formed [pskl] (any scope). *)
Lemma d_wf_pskl_of_wf_ptyp : forall Γ A,
    d_wf_ptyp Γ A ->
    forall Ψ, Γ ⨟ Ψ ⊢ₚₛ (ptyp_to_pskl A).
Proof.
  intros Γ A H Ψ. apply d_wf_pskl_of_ptyp.
  - eapply d_wf_ptyp_lc_loc; eassumption.
  - intros X HX. right. eapply d_wf_ptyp_ftvar; eassumption.
Qed.

(** The DETERMINISTIC witness colouring [colour Q A]: colour the checking type
    [A] guided by the inferred ghost [Q] — syn where [Q] is a ghost/leaf, inh
    at a nested [∀] that [Q] kept ([bskl_all_inh]), syn at a [∀] the universal
    ghost [⫯] fills.  Recurses on [A] (so it commutes with opening [A], which
    [__forall_r] needs); the single leading [⫯] is peeked (not recursed) to
    stay structural. *)
Fixpoint colour (Q : bskl) (A : ptyp) {struct A} : bskl :=
  match A with
  | ptyp_unit => bskl_unit
  | ptyp_var_b n => bskl_var_b n
  | ptyp_var_f X => bskl_var_f X
  | ptyp_arrow A1 A2 =>
      match (match Q with bskl_tophole Q0 => Q0 | _ => Q end) with
      | bskl_arrow Q1 Q2 => bskl_arrow (colour Q1 A1) (colour Q2 A2)
      | _ => bskl_arrow (pskl_to_bskl_syn (ptyp_to_pskl A1))
                        (pskl_to_bskl_syn (ptyp_to_pskl A2))
      end
  | ptyp_all A0 =>
      match Q with
      | bskl_all_inh Q0 => bskl_all_inh (colour Q0 A0)
      | bskl_tophole Q0 => bskl_all_syn (colour (bskl_tophole Q0) A0)
      | _ => bskl_all_syn (pskl_to_bskl_syn (ptyp_to_pskl A0))
      end
  end.

(** [colour] erases to [A]'s skeleton (independent of [Q]). *)
Lemma colour_erasure : forall A Q,
    bskl_to_pskl (colour Q A) = ptyp_to_pskl A.
Proof.
  induction A; intros Q; simpl; try reflexivity.
  - (* arrow *)
    destruct Q; simpl;
      try (rewrite IHA1, IHA2; reflexivity);
      try (rewrite ! bskl_to_pskl_pskl_to_bskl_syn; reflexivity).
    (* Q = bskl_tophole Q0: peek Q0 *)
    destruct Q; simpl;
      try (rewrite IHA1, IHA2; reflexivity);
      rewrite ! bskl_to_pskl_pskl_to_bskl_syn; reflexivity.
  - (* all *)
    destruct Q; simpl;
      try (rewrite IHA; reflexivity);
      rewrite bskl_to_pskl_pskl_to_bskl_syn; reflexivity.
Qed.

(** [colour] commutes with opening [A] by a fresh tvar (what [__forall_r]
    needs to close the cofinite premise; specialised to a variable so the
    [colour Q V] / [colour Q0 V] divergence at the nested-∀ case vanishes). *)
Lemma colour_open_rec : forall A Q X k,
    colour Q (open_ptyp_wrt_ptyp_rec k (ptyp_var_f X) A) =
    open_bskl_wrt_bskl_rec k (bskl_var_f X) (colour Q A).
Proof.
  induction A; intros Q X k; simpl.
  - reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - reflexivity.
  - (* arrow *)
    destruct Q as [ | ? | ? | qa qb | ? | ? | | q0 ]; simpl;
      try (rewrite IHA1, IHA2; reflexivity);
      try (rewrite !ptyp_to_pskl_open_rec, !pskl_to_bskl_syn_open_rec; reflexivity).
    (* tophole: peek q0 *)
    destruct q0 as [ | | | qa qb | | | | ]; simpl;
      try (rewrite IHA1, IHA2; reflexivity);
      rewrite !ptyp_to_pskl_open_rec, !pskl_to_bskl_syn_open_rec; reflexivity.
  - (* all *)
    destruct Q as [ | ? | ? | ? ? | ? | ? | | ? ]; simpl;
      try (rewrite IHA; reflexivity);
      rewrite !ptyp_to_pskl_open_rec, !pskl_to_bskl_syn_open_rec; reflexivity.
Qed.

Lemma colour_open : forall A Q X,
    colour Q (open_ptyp_wrt_ptyp A (ptyp_var_f X)) =
    open_bskl_wrt_bskl (colour Q A) (bskl_var_f X).
Proof. intros. unfold open_ptyp_wrt_ptyp, open_bskl_wrt_bskl.
  apply colour_open_rec. Qed.

(** [colour] inspects only the guide [Q]'s CONSTRUCTORS, never its leaves, so
    opening the guide leaves [colour] unchanged. *)
Lemma colour_guide_open_rec : forall A Q X k,
    colour (open_bskl_wrt_bskl_rec k (bskl_var_f X) Q) A = colour Q A.
Proof.
  induction A; intros Q X k; simpl; try reflexivity.
  - (* arrow *) destruct Q as [ | n0 | X0 | qa qb | qs | qi | | q0 ]; simpl.
    + reflexivity.
    + destruct (lt_eq_lt_dec n0 k) as [[?|?]|?]; reflexivity.
    + reflexivity.
    + rewrite IHA1, IHA2; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + (* tophole q0: peek *) destruct q0 as [ | n1 | X1 | qa qb | qs | qi | | q1 ]; simpl.
      * reflexivity.
      * destruct (lt_eq_lt_dec n1 k) as [[?|?]|?]; reflexivity.
      * reflexivity.
      * rewrite IHA1, IHA2; reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
  - (* all *) destruct Q as [ | n0 | X0 | qa qb | qs | qi | | q0 ]; simpl.
    + reflexivity.
    + destruct (lt_eq_lt_dec n0 k) as [[?|?]|?]; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + (* all_inh qi *) rewrite IHA; reflexivity.
    + reflexivity.
    + (* tophole q0 *) f_equal.
      change (bskl_tophole (open_bskl_wrt_bskl_rec k (bskl_var_f X) q0))
        with (open_bskl_wrt_bskl_rec k (bskl_var_f X) (bskl_tophole q0)).
      rewrite IHA. reflexivity.
Qed.

Lemma colour_guide_open : forall A Q X,
    colour (open_bskl_wrt_bskl Q (bskl_var_f X)) A = colour Q A.
Proof. intros. unfold open_bskl_wrt_bskl. apply colour_guide_open_rec. Qed.

(** [colour] with a [□] guide is the plain syn-painting. *)
Lemma colour_hole : forall A,
    colour bskl_hole A = pskl_to_bskl_syn (ptyp_to_pskl A).
Proof. induction A; simpl; reflexivity. Qed.

(** A ghostification is always a hole or a universal ghost (top-level shape). *)
Lemma ghost_of_shape : forall P Q,
    ghost_of P Q -> Q = bskl_hole \/ exists Q0, Q = bskl_tophole Q0.
Proof.
  intros P Q H. induction H; eauto.
Qed.

(** [⫯]-free skeletons.  [colour] never emits a [⫯], which is what lets the
    Γ→Δs context-move below go through (a [⫯] would clear the scope). *)
Inductive no_tophole_pskl : pskl -> Prop :=
| nthp_unit  : no_tophole_pskl pskl_unit
| nthp_var_b : forall n, no_tophole_pskl (pskl_var_b n)
| nthp_var_f : forall X, no_tophole_pskl (pskl_var_f X)
| nthp_arrow : forall P1 P2, no_tophole_pskl P1 -> no_tophole_pskl P2 ->
    no_tophole_pskl (pskl_arrow P1 P2)
| nthp_all   : forall P, no_tophole_pskl P -> no_tophole_pskl (pskl_all_syn P)
| nthp_hole  : no_tophole_pskl pskl_hole.

Inductive no_tophole_bskl : bskl -> Prop :=
| nthb_unit  : no_tophole_bskl bskl_unit
| nthb_var_b : forall n, no_tophole_bskl (bskl_var_b n)
| nthb_var_f : forall X, no_tophole_bskl (bskl_var_f X)
| nthb_arrow : forall Q1 Q2, no_tophole_bskl Q1 -> no_tophole_bskl Q2 ->
    no_tophole_bskl (bskl_arrow Q1 Q2)
| nthb_all_syn : forall Q, no_tophole_bskl Q -> no_tophole_bskl (bskl_all_syn Q)
| nthb_all_inh : forall Q, no_tophole_bskl Q -> no_tophole_bskl (bskl_all_inh Q)
| nthb_hole  : no_tophole_bskl bskl_hole.

Lemma no_tophole_pskl_of_ptyp : forall A, no_tophole_pskl (ptyp_to_pskl A).
Proof. induction A; simpl; constructor; assumption. Qed.

Lemma no_tophole_syn : forall P,
    no_tophole_pskl P -> no_tophole_bskl (pskl_to_bskl_syn P).
Proof. intros P H. induction H; simpl; constructor; assumption. Qed.

Lemma colour_no_tophole : forall A Q, no_tophole_bskl (colour Q A).
Proof.
  induction A; intros Q; simpl.
  - constructor.
  - constructor.
  - constructor.
  - (* arrow *) destruct (match Q with bskl_tophole Q0 => Q0 | _ => Q end);
      try (constructor; auto; fail);
      constructor; apply no_tophole_syn; apply no_tophole_pskl_of_ptyp.
  - (* all *) destruct Q;
      try (constructor; apply no_tophole_syn; apply no_tophole_pskl_of_ptyp; fail);
      constructor; auto.
Qed.

Lemma no_tophole_pskl_open_rec : forall P X k,
    no_tophole_pskl P ->
    no_tophole_pskl (open_pskl_wrt_pskl_rec k (pskl_var_f X) P).
Proof.
  intros P X k H. revert k. induction H; intros k; simpl;
    try (constructor; auto; fail).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; constructor.
Qed.

Lemma no_tophole_bskl_open_rec : forall Q X k,
    no_tophole_bskl Q ->
    no_tophole_bskl (open_bskl_wrt_bskl_rec k (bskl_var_f X) Q).
Proof.
  intros Q X k H. revert k. induction H; intros k; simpl;
    try (constructor; auto; fail).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; constructor.
Qed.

Lemma no_tophole_syn_inv : forall P,
    no_tophole_bskl (pskl_to_bskl_syn P) -> no_tophole_pskl P.
Proof.
  induction P; simpl; intros H; try (constructor; fail);
    inversion H; subst; constructor; auto.
Qed.

(** Move a tvar from the type context into the [pskl] scope set [Ψ] (valid
    for [⫯]-free skeletons — a [⫯] would clear [Ψ]). *)
Lemma d_wf_pskl_move : forall Ψ Γ' P,
    Γ' ⨟ Ψ ⊢ₚₛ P ->
    no_tophole_pskl P ->
    forall X Γ, Γ' = (X ~ dbind_tvar) ++ Γ ->
    Γ ⨟ (X :: Ψ) ⊢ₚₛ P.
Proof.
  intros Ψ Γ' P H. induction H; intros Hnt X0 Γ0 HΓ; subst.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [HΨ | Hb].
    + left. simpl. right. assumption.
    + apply binds_app_1 in Hb. destruct Hb as [Hb | Hb].
      * apply binds_one_iff in Hb. destruct Hb as [HX _]. subst.
        left. simpl. left. reflexivity.
      * right. assumption.
  - inversion Hnt; subst. apply d_wf_pskl__arrow; auto.
  - inversion Hnt; subst. inst_cofinites_for d_wf_pskl__all. intros Y HY.
    apply d_wf_pskl_Psi_mono with (Ψ := X0 :: (Y :: Δ)).
    + apply H0; auto. apply no_tophole_pskl_open_rec. assumption.
    + intros Z HZ. simpl in *. tauto.
  - apply d_wf_pskl__hole.
  - inversion Hnt.
Qed.

(** [d_refine_syn_Ds_mono] and [d_refine_syn_move] DELETED: with the single-[Δ]
    refinement the synthesised ∀-vars live in [Γ] (the [tophole_fill] rule
    prepends them directly), so there is no [Δs] to be monotone in, and no
    "move a tvar into [Δs]" step — [ghost_of_fill_gen]'s forall_r case applies
    its IH directly. *)

(** The inh-repaint of a skeleton's erasure preserves free tvars. *)
Lemma ftvar_inh_bskl_to_pskl : forall Q,
    ftvar_in_bskl (pskl_to_bskl_inh (bskl_to_pskl Q)) = ftvar_in_bskl Q.
Proof.
  induction Q; simpl; try reflexivity;
    try (rewrite IHQ1, IHQ2; reflexivity); try (rewrite IHQ; reflexivity).
Qed.

(** The syn-painting preserves free tvars (local copy, used before the
    [ftvar_pskl_to_bskl_syn] defined later). *)
Lemma ftvar_syn_bskl_loc : forall P,
    ftvar_in_bskl (pskl_to_bskl_syn P) = ftvar_in_pskl P.
Proof.
  induction P; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
Qed.

(** A ghostification has the same free tvars as its source skeleton. *)
Lemma ghost_of_ftvar : forall P Q,
    ghost_of P Q -> ftvar_in_bskl Q [<=] ftvar_in_pskl P.
Proof.
  intros P Q H. induction H; simpl.
  - fsetdec.
  - fsetdec.
  - rewrite ! ftvar_syn_bskl_loc. fsetdec.
  - fsetdec.
  - assumption.
  - etransitivity; [ eassumption | ].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper body pskl_hole) as Hub.
    simpl in Hub. fsetdec.
Qed.

(** THE HOLE/Δ INVARIANT.  [hole_safe L P A]: [P] structurally matches the type
    [A] (with holes), and EVERY hole in [P] faces an [A]-subterm whose free vars
    avoid [L] (the enclosing inherited-∀ vars, [Δ]).  Single context now (the
    paper's single-[Δ] refinement): a plain var is unconstrained (the var rule is
    [Δ∨Γ]); only holes must avoid [Δ] (the [hole] rule clears [Δ], filling under
    [Γ]). *)
Inductive hole_safe : list atom -> pskl -> ptyp -> Prop :=
| hs_hole  : forall L A,
    (forall X, X `in` ftvar_in_ptyp A -> ~ List.In X L) -> hole_safe L pskl_hole A
| hs_unit  : forall L, hole_safe L pskl_unit ptyp_unit
| hs_var_f : forall L X, hole_safe L (pskl_var_f X) (ptyp_var_f X)
| hs_var_b : forall L n, hole_safe L (pskl_var_b n) (ptyp_var_b n)
| hs_arrow : forall L P1 P2 A1 A2,
    hole_safe L P1 A1 -> hole_safe L P2 A2 ->
    hole_safe L (pskl_arrow P1 P2) (ptyp_arrow A1 A2)
| hs_all   : forall L Lc P0 A0,
    (forall X, X `notin` Lc ->
       hole_safe (X :: L) (open_pskl_wrt_pskl P0 (pskl_var_f X))
                          (open_ptyp_wrt_ptyp A0 (ptyp_var_f X))) ->
    hole_safe L (pskl_all_syn P0) (ptyp_all A0).

(** CONSISTENCY→REFINEMENT CORE (the heart of [__check]): an [inh]-painted
    [hole_safe] skeleton refines the [colour]ing of its type.  By induction on
    [A]; at a hole, [hs_hole]'s [∉Δ] + the coverage give [binds Γ] (the [hole]
    rule fills under [Γ]); a plain var uses the var rule ([Δ∨Γ]); the ∀ case
    routes the bound var into [Δ]. *)
Lemma refine_colour_core : forall A,
    lc_ptyp A ->
    forall P Γ Δ,
      hole_safe Δ P A ->
      (forall X, X `in` ftvar_in_ptyp A ->
         List.In X Δ \/ binds X dbind_tvar Γ) ->
      Γ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (colour (pskl_to_bskl_inh P) A).
Proof.
  intros A Hlc. induction Hlc; intros P Γ Δ Hhs Hcov.
  - (* unit *) inversion Hhs; subst.
    + replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn_hole_fills;
        [ apply lc_ptyp_unit | intros X HX; simpl in HX; fsetdec ].
    + simpl. apply d_refine_syn__unit.
  - (* var X *) inversion Hhs; subst.
    + replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn_hole_fills.
      * apply lc_ptyp_var_f.
      * intros Y HY. destruct (Hcov Y HY) as [HI | HG];
          [ exfalso; match goal with Hc : forall _ : atom, _ -> ~ List.In _ _ |- _ => eapply Hc; eauto end
          | assumption ].
    + simpl. apply d_refine_syn__var. apply Hcov. simpl. fsetdec.
  - (* arrow *) inversion Hhs; subst.
    + replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn_hole_fills.
      * apply lc_ptyp_arrow; assumption.
      * intros Y HY. destruct (Hcov Y HY) as [HI | HG];
          [ exfalso; match goal with Hc : forall _ : atom, _ -> ~ List.In _ _ |- _ => eapply Hc; eauto end
          | assumption ].
    + simpl. apply d_refine_syn__arrow;
        [ apply IHHlc1 | apply IHHlc2 ]; try assumption;
        intros Y HY; apply Hcov; simpl; fsetdec.
  - (* all *) inversion Hhs; subst.
    + replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn_hole_fills.
      * pick fresh X; apply (lc_ptyp_all_exists X); auto.
      * intros Y HY. destruct (Hcov Y HY) as [HI | HG];
          [ exfalso; match goal with Hc : forall _ : atom, _ -> ~ List.In _ _ |- _ => eapply Hc; eauto end
          | assumption ].
    + simpl. inst_cofinites_for d_refine_syn__all. intros X HX.
      rewrite <- colour_open.
      rewrite <- (colour_guide_open _ (pskl_to_bskl_inh P0) X).
      rewrite <- !pskl_to_bskl_inh_open.
      apply H0; auto.
      intros Y HY. apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY.
      simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
      * apply AtomSetImpl.singleton_1 in HY. subst. left. simpl. left. reflexivity.
      * destruct (Hcov Y HY) as [HI | HG];
          [ left; simpl; right; assumption | right; assumption ].
Qed.

(** [utyp]-level hole-safety, the invariant [ghost_of_fill_gen] carries (since
    [forall_l] changes [P] and the LHS [U] together while keeping the RHS
    [A'] fixed, hole-safety must relate [P] to [U]). *)
Inductive hole_safe_u : list atom -> pskl -> utyp -> Prop :=
| hsu_hole  : forall L C,
    (forall X, X `in` ftvar_in_utyp C -> ~ List.In X L) -> hole_safe_u L pskl_hole C
| hsu_unit  : forall L, hole_safe_u L pskl_unit utyp_unit
| hsu_var_f : forall L X, hole_safe_u L (pskl_var_f X) (utyp_var_f X)
| hsu_var_b : forall L n, hole_safe_u L (pskl_var_b n) (utyp_var_b n)
| hsu_arrow : forall L P1 P2 C1 C2,
    hole_safe_u L P1 C1 -> hole_safe_u L P2 C2 ->
    hole_safe_u L (pskl_arrow P1 P2) (utyp_arrow C1 C2)
| hsu_all_syn : forall L Lc P0 C0,
    (forall X, X `notin` Lc ->
       hole_safe_u (X :: L) (open_pskl_wrt_pskl P0 (pskl_var_f X))
                            (open_utyp_wrt_utyp C0 (utyp_var_f X))) ->
    hole_safe_u L (pskl_all_syn P0) (utyp_all_syn C0)
| hsu_all_etag : forall L Lc e P0 C0,
    (forall X, X `notin` Lc ->
       hole_safe_u (X :: L) (open_pskl_wrt_pskl P0 (pskl_var_f X))
                            (open_utyp_wrt_utyp C0 (utyp_var_f X))) ->
    hole_safe_u L (pskl_all_syn P0) (utyp_all_etag e C0).

(** Anti-monotone in [L] (a smaller forbidden set is a weaker condition). *)
Lemma hole_safe_u_weaken : forall L P C,
    hole_safe_u L P C ->
    forall L', (forall X, List.In X L' -> List.In X L) ->
    hole_safe_u L' P C.
Proof.
  intros L P C H. induction H; intros L' Hsub; try (constructor; auto; fail).
  - apply hsu_hole. intros X HX HInL'. eapply H; eauto.
  - apply hsu_all_syn with (Lc := Lc). intros X HX. apply H0; auto.
    intros Y HY. simpl in HY |- *. destruct HY; [ left; assumption | right; auto ].
  - apply hsu_all_etag with (Lc := Lc). intros X HX. apply H0; auto.
    intros Y HY. simpl in HY |- *. destruct HY; [ left; assumption | right; auto ].
Qed.

(** Substituting [X] with [□] (in [P]) and [φ] (in [C]) preserves hole-safety
    (keeping [L]), provided [φ]'s free vars avoid [L].  [X] is a free param
    (not [L]'s head), so it composes under the [∀] binders. *)
Lemma hole_safe_u_subst : forall L P C,
    hole_safe_u L P C ->
    forall X phi, lc_utyp phi ->
    (forall Y, Y `in` ftvar_in_utyp phi -> ~ List.In Y L) ->
    hole_safe_u L (subst_pskl_in_pskl pskl_hole X P)
                  (subst_utyp_in_utyp phi X C).
Proof.
  intros L P C H. induction H; intros X0 phi Hlcphi Hphi; simpl.
  - (* hole *) apply hsu_hole. intros Y HY HInL.
    apply ftvar_in_utyp_subst_utyp_in_utyp_upper in HY. simpl in HY.
    apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + eapply Hphi; eauto.
    + apply AtomSetImpl.remove_3 in HY. eapply H; eauto.
  - (* unit *) apply hsu_unit.
  - (* var_f X *) destruct (X == X0); subst.
    + apply hsu_hole. intros Y HY. eapply Hphi; eauto.
    + apply hsu_var_f.
  - (* var_b *) apply hsu_var_b.
  - (* arrow *) apply hsu_arrow; [ apply IHhole_safe_u1 | apply IHhole_safe_u2 ]; assumption.
  - (* all_syn *) apply hsu_all_syn with (Lc := Lc \u singleton X0 \u ftvar_in_utyp phi).
    intros Y HY. assert (HYX : X0 <> Y) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var by (try assumption; apply lc_pskl_hole).
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (try assumption).
    eapply H0; [ fsetdec | assumption | ].
    intros Z HZ HZin. simpl in HZin. destruct HZin as [HZeq | HZL].
    * subst Z. assert (Y `notin` ftvar_in_utyp phi) by fsetdec. contradiction.
    * eapply Hphi; eauto.
  - (* all_etag *) apply hsu_all_etag with (Lc := Lc \u singleton X0 \u ftvar_in_utyp phi).
    intros Y HY. assert (HYX : X0 <> Y) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var by (try assumption; apply lc_pskl_hole).
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (try assumption).
    eapply H0; [ fsetdec | assumption | ].
    intros Z HZ HZin. simpl in HZin. destruct HZin as [HZeq | HZL].
    * subst Z. assert (Y `notin` ftvar_in_utyp phi) by fsetdec. contradiction.
    * eapply Hphi; eauto.
Qed.

(** A type's skeleton is hole-safe w.r.t. the type's syn-painting (trivially —
    no holes).  Establishes the [hole_safe_u] invariant at the [ghost_of_fill]
    entry, where [P = ptyp_to_pskl C0]. *)
Lemma hole_safe_u_of_ptyp : forall C0,
    lc_ptyp C0 ->
    forall L, hole_safe_u L (ptyp_to_pskl C0) (ptyp_to_utyp_syn C0).
Proof.
  intros C0 Hlc. induction Hlc; intros L; simpl.
  - apply hsu_unit.
  - apply hsu_var_f.
  - apply hsu_arrow; auto.
  - apply hsu_all_syn with (Lc := empty). intros X HX.
    rewrite <- ptyp_to_pskl_open. rewrite <- (ptyp_to_utyp_syn_open _ (ptyp_var_f X)). auto.
Qed.

Lemma ptyp_to_btyp_inh_open_var : forall A X,
    open_btyp_wrt_btyp (ptyp_to_btyp_inh A) (btyp_var_f X) =
    ptyp_to_btyp_inh (open_ptyp_wrt_ptyp A (ptyp_var_f X)).
Proof.
  intros. unfold open_btyp_wrt_btyp, open_ptyp_wrt_ptyp.
  rewrite ptyp_to_btyp_inh_open_rec. reflexivity.
Qed.

(** Consistency preserves free vars: [A']'s ftvars are among [C]'s. *)
Lemma d_consis_ftvar : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    forall A', B = ptyp_to_btyp_inh A' ->
    ftvar_in_ptyp A' [<=] ftvar_in_utyp C.
Proof.
  intros Δ Γ C B H. induction H; intros A' Heq;
    destruct A'; simpl in Heq; try discriminate; inversion Heq; subst; simpl.
  - fsetdec.
  - fsetdec.
  - specialize (IHd_consis1 A'1 eq_refl). specialize (IHd_consis2 A'2 eq_refl). fsetdec.
  - (* forall_inh_tagged: A' = ptyp_all A'0 *)
    pick fresh X for (L \u ftvar_in_ptyp A' \u ftvar_in_utyp C).
    assert (Hsub : ftvar_in_ptyp (open_ptyp_wrt_ptyp A' (ptyp_var_f X)) [<=]
                   ftvar_in_utyp (open_utyp_wrt_utyp C (utyp_var_f X))).
    { eapply H0; [ auto | ]. rewrite ptyp_to_btyp_inh_open_var. reflexivity. }
    assert (HL : ftvar_in_ptyp A' [<=] ftvar_in_ptyp (open_ptyp_wrt_ptyp A' (ptyp_var_f X)))
      by apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower.
    assert (HU : ftvar_in_utyp (open_utyp_wrt_utyp C (utyp_var_f X)) [<=]
                 AtomSetImpl.union (ftvar_in_utyp (utyp_var_f X)) (ftvar_in_utyp C))
      by apply ftvar_in_utyp_open_utyp_wrt_utyp_upper.
    simpl in HU. fsetdec.
  - (* forall_inh_untagged *)
    pick fresh X for (L \u ftvar_in_ptyp A' \u ftvar_in_utyp C).
    assert (Hsub : ftvar_in_ptyp (open_ptyp_wrt_ptyp A' (ptyp_var_f X)) [<=]
                   ftvar_in_utyp (open_utyp_wrt_utyp C (utyp_var_f X))).
    { eapply H0; [ auto | ]. rewrite ptyp_to_btyp_inh_open_var. reflexivity. }
    assert (HL : ftvar_in_ptyp A' [<=] ftvar_in_ptyp (open_ptyp_wrt_ptyp A' (ptyp_var_f X)))
      by apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower.
    assert (HU : ftvar_in_utyp (open_utyp_wrt_utyp C (utyp_var_f X)) [<=]
                 AtomSetImpl.union (ftvar_in_utyp (utyp_var_f X)) (ftvar_in_utyp C))
      by apply ftvar_in_utyp_open_utyp_wrt_utyp_upper.
    simpl in HU. fsetdec.
Qed.

(** TRANSPORT: hole-safety on the [utyp] [C] transfers to the checking type
    [A'] consistent with it.  This bridges [gen]'s [utyp] invariant
    [hole_safe_u] to the [hole_safe] that [refine_colour_core] consumes. *)
Lemma hole_safe_u_transport : forall La Pa C,
    hole_safe_u La Pa C ->
    forall Δ Γ B A', Δ ⨟ Γ ⊨ C ≈ B -> B = ptyp_to_btyp_inh A' ->
    hole_safe La Pa A'.
Proof.
  intros La Pa C H. induction H; intros Δ Γ B A' Hd Heq.
  - (* hsu_hole *) apply hs_hole. intros Y HY.
    assert (Hsub : ftvar_in_ptyp A' [<=] ftvar_in_utyp C)
      by (eapply d_consis_ftvar; [ exact Hd | exact Heq ]).
    apply H. fsetdec.
  - (* hsu_unit *) revert Heq. inversion Hd; subst; intros Heq.
    destruct A'; simpl in Heq; try discriminate. apply hs_unit.
  - (* hsu_var_f *) revert Heq. inversion Hd; subst; intros Heq.
    destruct A'; simpl in Heq; try discriminate. inversion Heq; subst. apply hs_var_f.
  - (* hsu_var_b *) inversion Hd.
  - (* hsu_arrow *) revert Heq. inversion Hd; subst; intros Heq.
    destruct A'; simpl in Heq; try discriminate. inversion Heq; subst.
    apply hs_arrow; [ eapply IHhole_safe_u1 | eapply IHhole_safe_u2 ]; eauto.
  - (* hsu_all_syn *) revert Heq. inversion Hd; subst; intros Heq;
      destruct A'; simpl in Heq; try discriminate; inversion Heq; subst.
    match goal with Hsc : forall _ : atom, _ -> d_consis _ _ _ _ |- _ =>
      apply hs_all with (Lc := Lc \u L0); intros X HX;
      eapply H0; [ fsetdec | apply Hsc; fsetdec
                 | rewrite ptyp_to_btyp_inh_open_var; reflexivity ] end.
  - (* hsu_all_etag *) revert Heq. inversion Hd; subst; intros Heq;
      destruct A'; simpl in Heq; try discriminate; inversion Heq; subst.
    match goal with Hsc : forall _ : atom, _ -> d_consis _ _ _ _ |- _ =>
      apply hs_all with (Lc := Lc \u L0); intros X HX;
      eapply H0; [ fsetdec | apply Hsc; fsetdec
                 | rewrite ptyp_to_btyp_inh_open_var; reflexivity ] end.
Qed.

(** [tophole_safe P0 A]: a single top ghost [⫯] over a [hole_safe] core [P0],
    against [A].  The [⫯] skips [A]'s leading ∀s ([ths_all], → [__tophole_fill])
    and, at the first non-∀, the core [P0] must be [hole_safe] against that
    ∀-stripped [A] ([ths_leaf], → [__tophole_remove]).  This is exactly the
    shape [bskl_to_pskl Q] takes for a non-□ ghost [Q] (one top [⫯], syn-painted
    — hence [hole_safe], no nested [⫯] — below). *)
Inductive tophole_safe : list atom -> pskl -> ptyp -> Prop :=
| ths_leaf : forall Δ P0 A,
    (forall A0, A <> ptyp_all A0) -> hole_safe Δ P0 A -> tophole_safe Δ P0 A
| ths_all  : forall Δ L P0 A0,
    (* The ∀-var goes into [Γ] (the [tophole_fill] rule), not into [Δ], so [Δ]
       (the inherited context) is unchanged through the peel. *)
    (forall X, X `notin` L ->
       tophole_safe Δ P0 (open_ptyp_wrt_ptyp A0 (ptyp_var_f X))) ->
    tophole_safe Δ P0 (ptyp_all A0).

(** [colour] of a [⫯]-guide against a non-∀ type peeks past the [⫯] (provided
    the peeled guide isn't itself a [⫯]). *)
Lemma colour_tophole_peek : forall A Q0,
    (forall A0, A <> ptyp_all A0) ->
    (forall Q1, Q0 <> bskl_tophole Q1) ->
    colour (bskl_tophole Q0) A = colour Q0 A.
Proof.
  intros A Q0 HnA HnQ. destruct A; simpl; try reflexivity.
  - destruct Q0; simpl; try reflexivity. exfalso; eapply HnQ; reflexivity.
  - exfalso; eapply HnA; reflexivity.
Qed.

(** TOPHOLE refinement: the [⫯]-ghost refines [colour]'s output against [A].
    Leaf (non-∀ [A]): [__tophole_remove] + [refine_colour_core].
    ∀ [A]: [__tophole_fill] (the [⫯] persists into the body, joining [Δs]) +
    recursion on the body. *)
Lemma refine_colour_tophole : forall A,
    lc_ptyp A ->
    forall P0 Γ Δ,
      tophole_safe Δ P0 A ->
      (forall X, X `in` ftvar_in_ptyp A ->
         List.In X Δ \/ binds X dbind_tvar Γ) ->
      Γ ⨟ Δ ⊢ᵣ (bskl_tophole (pskl_to_bskl_inh P0))
               ⊳ (colour (bskl_tophole (pskl_to_bskl_inh P0)) A).
Proof.
  intros A Hlc. induction Hlc; intros P0 Γ Δ Hts Hcov.
  - (* unit *) inversion Hts; subst.
    match goal with Hhs : hole_safe _ P0 ptyp_unit |- _ =>
      assert (Hntp : forall Q1, pskl_to_bskl_inh P0 <> bskl_tophole Q1)
        by (intros Q1; inversion Hhs; subst; simpl; discriminate) end.
    rewrite colour_tophole_peek by (try (intros; discriminate); exact Hntp).
    apply d_refine_syn__tophole_remove.
    apply refine_colour_core; [ apply lc_ptyp_unit | assumption | intros Y HY; simpl in HY; fsetdec ].
  - (* var X *) inversion Hts; subst.
    match goal with Hhs : hole_safe _ P0 (ptyp_var_f _) |- _ =>
      assert (Hntp : forall Q1, pskl_to_bskl_inh P0 <> bskl_tophole Q1)
        by (intros Q1; inversion Hhs; subst; simpl; discriminate) end.
    rewrite colour_tophole_peek by (try (intros; discriminate); exact Hntp).
    apply d_refine_syn__tophole_remove.
    apply refine_colour_core; [ apply lc_ptyp_var_f | assumption | exact Hcov ].
  - (* arrow *) inversion Hts; subst.
    match goal with Hhs : hole_safe _ P0 (ptyp_arrow _ _) |- _ =>
      assert (Hntp : forall Q1, pskl_to_bskl_inh P0 <> bskl_tophole Q1)
        by (intros Q1; inversion Hhs; subst; simpl; discriminate) end.
    rewrite colour_tophole_peek by (try (intros; discriminate); exact Hntp).
    apply d_refine_syn__tophole_remove.
    apply refine_colour_core; [ apply lc_ptyp_arrow; assumption | assumption | exact Hcov ].
  - (* all *) inversion Hts; subst.
    + (* ths_leaf: impossible, A = ptyp_all *)
      match goal with H : forall _ : ptyp, _ |- _ => exfalso; apply (H _ eq_refl) end.
    + (* ths_all: __tophole_fill (the ∀-var joins Γ now) *)
      simpl. inst_cofinites_for d_refine_syn__tophole_fill. intros X HX.
      rewrite <- colour_open.
      eapply (H0 X P0 ((X ~ dbind_tvar) ++ Γ) Δ).
      * match goal with Hb : forall _ : atom, _ -> tophole_safe _ _ _ |- _ => apply Hb; auto end.
      * intros Y HY. apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY.
        simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
        -- apply AtomSetImpl.singleton_1 in HY. subst Y. right.
           apply binds_app_2. apply binds_one_3; reflexivity.
        -- destruct (Hcov Y HY) as [HI | HG];
             [ left; assumption | right; apply binds_app_3; assumption ].
Qed.

(** UNIFIED safe-skeleton predicate merging [hole_safe] (structural) and
    [tophole_safe] (⫯-ghost): a [pskl_tophole] node absorbs a ∀-prefix
    ([sks_top_all]) then matches structurally ([sks_top_leaf]).  This lets an
    arrow CODOMAIN be a [⫯]-ghost (a curried λ), which flat [hole_safe] cannot
    express.  [refine_colour_skel] below is the one tophole-aware refinement
    engine (subsumes [refine_colour_core] + [refine_colour_tophole]). *)
Inductive skel_safe : list atom -> pskl -> ptyp -> Prop :=
| sks_hole  : forall Δ A,
    (forall X, X `in` ftvar_in_ptyp A -> ~ List.In X Δ) -> skel_safe Δ pskl_hole A
| sks_unit  : forall Δ, skel_safe Δ pskl_unit ptyp_unit
| sks_var_f : forall Δ X, skel_safe Δ (pskl_var_f X) (ptyp_var_f X)
| sks_arrow : forall Δ P1 P2 A1 A2,
    skel_safe Δ P1 A1 -> skel_safe Δ P2 A2 ->
    skel_safe Δ (pskl_arrow P1 P2) (ptyp_arrow A1 A2)
| sks_all   : forall Δ L P0 A0,
    (forall X, X `notin` L ->
       skel_safe (X :: Δ) (open_pskl_wrt_pskl P0 (pskl_var_f X))
                          (open_ptyp_wrt_ptyp A0 (ptyp_var_f X))) ->
    skel_safe Δ (pskl_all_syn P0) (ptyp_all A0)
| sks_top_leaf : forall Δ P0 A,
    (forall A0, A <> ptyp_all A0) ->
    (forall Q1, P0 <> pskl_tophole Q1) ->
    skel_safe Δ P0 A ->
    skel_safe Δ (pskl_tophole P0) A
| sks_top_all : forall Δ L P0 A0,
    (forall X, X `notin` L ->
       skel_safe Δ (pskl_tophole P0) (open_ptyp_wrt_ptyp A0 (ptyp_var_f X))) ->
    skel_safe Δ (pskl_tophole P0) (ptyp_all A0).

Lemma refine_colour_skel : forall Δ P A,
    skel_safe Δ P A ->
    lc_ptyp A ->
    forall Γ, (forall X, X `in` ftvar_in_ptyp A -> List.In X Δ \/ binds X dbind_tvar Γ) ->
      Γ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (colour (pskl_to_bskl_inh P) A).
Proof.
  induction 1; intros Hlc Γ Hcov.
  - (* sks_hole *)
    replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
    rewrite colour_hole. apply d_refine_syn_hole_fills; [ exact Hlc | ].
    intros Y HY. destruct (Hcov Y HY) as [HI | HG];
      [ exfalso; eapply H; eauto | assumption ].
  - (* sks_unit *) simpl. apply d_refine_syn__unit.
  - (* sks_var_f *) simpl. apply d_refine_syn__var. apply Hcov. simpl. fsetdec.
  - (* sks_arrow *) simpl. inversion Hlc; subst. apply d_refine_syn__arrow;
      [ apply IHskel_safe1 | apply IHskel_safe2 ]; try assumption;
      intros Y HY; apply Hcov; simpl; fsetdec.
  - (* sks_all *) simpl. inst_cofinites_for d_refine_syn__all. intros X HX.
    rewrite <- colour_open.
    rewrite <- (colour_guide_open _ (pskl_to_bskl_inh P0) X).
    rewrite <- !pskl_to_bskl_inh_open.
    assert (Hlcx : lc_ptyp (open_ptyp_wrt_ptyp A0 (ptyp_var_f X)))
      by (inversion Hlc; subst; eauto).
    apply (H0 X ltac:(fsetdec) Hlcx).
    intros Y HY. apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY.
    simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + apply AtomSetImpl.singleton_1 in HY. subst. left. simpl. left. reflexivity.
    + destruct (Hcov Y HY) as [HI | HG];
        [ left; simpl; right; assumption | right; assumption ].
  - (* sks_top_leaf : ⫯ over non-∀ ⇒ tophole_remove + recurse on P0 *)
    replace (pskl_to_bskl_inh (pskl_tophole P0))
      with (bskl_tophole (pskl_to_bskl_inh P0)) by reflexivity.
    rewrite colour_tophole_peek;
      [ apply d_refine_syn__tophole_remove; apply IHskel_safe; assumption
      | exact H
      | intros Q1 Hc; destruct P0; simpl in Hc; try discriminate;
        exfalso; eapply H0; reflexivity ].
  - (* sks_top_all : ⫯ over ∀ ⇒ tophole_fill (X→Γ) + recurse *)
    replace (pskl_to_bskl_inh (pskl_tophole P0))
      with (bskl_tophole (pskl_to_bskl_inh P0)) by reflexivity.
    replace (colour (bskl_tophole (pskl_to_bskl_inh P0)) (ptyp_all A0))
      with (bskl_all_syn (colour (bskl_tophole (pskl_to_bskl_inh P0)) A0)) by reflexivity.
    let g := gather_atoms in
    apply d_refine_syn__tophole_fill with (L := g).
    intros X HX. rewrite <- colour_open.
    assert (Hlcx : lc_ptyp (open_ptyp_wrt_ptyp A0 (ptyp_var_f X)))
      by (inversion Hlc; subst; eauto).
    apply (H0 X ltac:(fsetdec) Hlcx).
    intros Y HY. apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY.
    simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + apply AtomSetImpl.singleton_1 in HY. subst. right.
      apply binds_app_2, binds_one_3; reflexivity.
    + destruct (Hcov Y HY) as [HI | HG];
        [ left; assumption | right; apply binds_app_3; assumption ].
Qed.

(** A type's own skeleton is [skel_safe] for it (the synthesised/ti leaf: the
    [ti] skeleton IS the type's skeleton). *)
Lemma skel_safe_of_ptyp : forall A,
    lc_ptyp A -> forall L, skel_safe L (ptyp_to_pskl A) A.
Proof.
  intros A H. induction H; intros L; simpl.
  - apply sks_unit.
  - apply sks_var_f.
  - apply sks_arrow; [ apply IHlc_ptyp1 | apply IHlc_ptyp2 ].
  - apply sks_all with (L := empty). intros X _.
    rewrite <- ptyp_to_pskl_open. apply H0.
Qed.

(** BRIDGES old→new: [skel_safe] subsumes [hole_safe] (structural) and
    [tophole_safe] (⫯-ghost).  Lets the existing base-term machinery
    ([hole_safe_u_transport] etc.) feed the unified engine. *)
Lemma hole_safe_skel_safe : forall Δ P A,
    hole_safe Δ P A -> lc_ptyp A -> skel_safe Δ P A.
Proof.
  induction 1; intros Hlc.
  - apply sks_hole. assumption.
  - apply sks_unit.
  - apply sks_var_f.
  - inversion Hlc.
  - inversion Hlc; subst. apply sks_arrow; [ apply IHhole_safe1 | apply IHhole_safe2 ]; assumption.
  - apply sks_all with (L := Lc). intros X HX.
    assert (Hlcx : lc_ptyp (open_ptyp_wrt_ptyp A0 (ptyp_var_f X)))
      by (inversion Hlc; subst; eauto).
    apply (H0 X HX Hlcx).
Qed.

Lemma tophole_safe_skel_safe : forall Δ P0 A,
    tophole_safe Δ P0 A -> lc_ptyp A -> skel_safe Δ (pskl_tophole P0) A.
Proof.
  induction 1; intros Hlc.
  - (* ths_leaf: A ≠ ∀, hole_safe Δ P0 A *)
    apply sks_top_leaf.
    + assumption.
    + intros Q1 Hc; subst P0;
        match goal with Hhs : hole_safe _ (pskl_tophole _) _ |- _ => inversion Hhs end.
    + apply hole_safe_skel_safe; assumption.
  - (* ths_all: A = ∀A0, Δ kept *)
    apply sks_top_all with (L := L). intros X HX.
    assert (Hlcx : lc_ptyp (open_ptyp_wrt_ptyp A0 (ptyp_var_f X)))
      by (inversion Hlc; subst; eauto).
    apply (H0 X HX Hlcx).
Qed.

(** [forall_l] maintenance: from the [hsu_all] body (one [∀] stripped), the
    instantiation [□]/[φ] re-establishes [hole_safe_u] at [nil] for the
    recursion — exactly [subst_intro] + [hole_safe_u_subst] + [weaken]. *)
Lemma hole_safe_u_open_fill : forall L P0 C ph,
    (forall X, X `notin` L ->
       hole_safe_u (X :: nil) (open_pskl_wrt_pskl P0 (pskl_var_f X))
                              (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    lc_utyp ph ->
    hole_safe_u nil (open_pskl_wrt_pskl P0 pskl_hole) (open_utyp_wrt_utyp C ph).
Proof.
  intros L P0 C ph Hbody Hlc.
  pick fresh X for (L \u ftvar_in_pskl P0 \u ftvar_in_utyp C \u ftvar_in_utyp ph).
  rewrite (subst_pskl_in_pskl_intro X P0 pskl_hole) by fsetdec.
  rewrite (subst_utyp_in_utyp_intro X C ph) by fsetdec.
  apply hole_safe_u_weaken with (L := X :: nil); [ | intros Y HY; inversion HY ].
  apply hole_safe_u_subst.
  - apply Hbody. fsetdec.
  - exact Hlc.
  - intros Y HY HIn. simpl in HIn. destruct HIn as [Heq | Hnil];
      [ subst Y; fsetdec | inversion Hnil ].
Qed.

(** A [__check] leaf: the ghost's top [⫯] over [P] refines [colour]'s output
    against the guarded checking type [A'].  Consumes the threaded
    [hole_safe_u nil P C] invariant (via [hole_safe_u_transport] to [A']) and
    feeds [refine_colour_tophole]. *)
Lemma check_leaf : forall Γ P C A' Δ,
    guarded_btyp (ptyp_to_btyp_inh A') ->
    Δ ⨟ Γ ⊨ C ≈ ptyp_to_btyp_inh A' ->
    hole_safe_u nil P C ->
    d_wf_ptyp Γ A' ->
    Γ ⨟ nil ⊢ᵣ (bskl_tophole (pskl_to_bskl_inh P))
                   ⊳ (colour (bskl_tophole (pskl_to_bskl_inh P)) A').
Proof.
  intros Γ P C A' Δ Hgb Hcons Hhsu Hwf.
  assert (Hnall' : forall A0, A' <> ptyp_all A0)
    by (intros A0 Hc; subst A'; inversion Hgb).
  apply refine_colour_tophole.
  - eapply d_wf_ptyp_lc_loc; eauto.
  - apply ths_leaf;
      [ exact Hnall'
      | eapply hole_safe_u_transport; [ exact Hhsu | exact Hcons | reflexivity ] ].
  - intros X HX. right. eapply d_wf_ptyp_ftvar; eauto.
Qed.

(** Generalised fill, by induction on the [d_sub] derivation, carrying the
    [pskl_subsumes] invariant.  KEY: the [forall_l] case (the original
    obstacle) closes cleanly — the invariant is preserved by
    [pskl_subsumes_open_rec] ([□] subsumes the instantiation [φ]'s skeleton)
    with the SAME [Q], so the IH applies; no monotonicity needed.

    STATUS (WIP): the [forall_l] cases (the ORIGINAL obstacle) AND both
    [P = □] subcases are PROVED.  TWO [admit]s remain: [__check]
    (consistency→refinement base) and [__forall_r].  NOTE: [__forall_r] will
    need the existential witness [B] replaced by a DETERMINISTIC colouring
    function of [Q] and [A'] — the cofinite premise gives [B_X] per fresh [X]
    but a plain existential cannot be closed back over [X]; a function
    [colour Q A'] with [colour Q (open A'0 X) = open (colour Q A'0) X] fixes
    it (and threads through [__check] too). *)
(** The uniform [Q = □] subcase of [ghost_of_fill_gen]: the bare ghost fills the
    syn-colouring of any well-formed checking type, independent of the [d_sub]
    derivation. *)
Lemma ghost_fill_hole_case : forall Γ A',
    d_wf_ptyp Γ A' ->
    Γ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl (@bskl_hole)))
                     ⊳ (colour (pskl_to_bskl_inh (bskl_to_pskl bskl_hole)) A').
Proof.
  intros Γ A' Hwf.
  replace (pskl_to_bskl_inh (bskl_to_pskl bskl_hole)) with (@bskl_hole) by reflexivity.
  rewrite colour_hole. apply d_refine_syn_hole_fills.
  - eapply d_wf_ptyp_lc_loc; eauto.
  - intros X HX. eapply d_wf_ptyp_ftvar; eauto.
Qed.

Lemma ghost_of_fill_gen : forall Δ Γ U V,
    Δ ⨟ Γ ⊢[ mode_tc ] U ⊑ V ->
    forall A' P Q,
      V = ptyp_to_btyp_inh A' ->
      d_wf_ptyp Γ A' ->
      pskl_subsumes P (utyp_to_pskl U) ->
      ghost_of P Q ->
      hole_safe_u nil P U ->
      Γ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q))
                       ⊳ (colour (pskl_to_bskl_inh (bskl_to_pskl Q)) A').
Proof.
  intros Δ Γ U V Hsub. remember mode_tc as m eqn:Hm. revert Hm.
  induction Hsub; intros Hm A' P Q Heq Hwfa Hsubs Hg Hhsu; try discriminate Hm.
  - (* check : U guarded, consis U V, V = inh A' *)
    destruct (ghost_of_shape Hg) as [Hqsh | [Q0 Hqsh]]; subst Q.
    + apply ghost_fill_hole_case; assumption.
    + (* Q = ⫯Q0 : P guarded, so bskl_to_pskl Q0 = P; the check leaf closes it *)
      assert (Hbq : bskl_to_pskl Q0 = P).
      { match goal with Hgu : guarded_utyp ?Uu |- _ => inversion Hgu; subst end;
        simpl in Hsubs; inversion Hsubs; subst; inversion Hg; subst; simpl;
        try reflexivity; rewrite ! bskl_to_pskl_pskl_to_bskl_syn; reflexivity. }
      replace (pskl_to_bskl_inh (bskl_to_pskl (bskl_tophole Q0)))
        with (bskl_tophole (pskl_to_bskl_inh (bskl_to_pskl Q0))) by reflexivity.
      rewrite Hbq.
      eapply check_leaf;
        [ rewrite <- Heq; eassumption
        | rewrite <- Heq; eassumption
        | exact Hhsu | exact Hwfa ].
  - (* forall_r : V = btyp_all_inh B = inh (ptyp_all A'0) *)
    destruct A' as [ | n | X | A'a A'b | A'0 ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (ghost_of_shape Hg) as [Hqsh | [Q0 Hqsh]]; subst Q.
    + apply ghost_fill_hole_case; assumption.
    + (* RHS ∀ is filled by a synthesised quantifier ([tophole_fill]) *)
      replace (pskl_to_bskl_inh (bskl_to_pskl (bskl_tophole Q0)))
        with (bskl_tophole (pskl_to_bskl_inh (bskl_to_pskl Q0))) by reflexivity.
      replace (colour (bskl_tophole (pskl_to_bskl_inh (bskl_to_pskl Q0))) (ptyp_all A'0))
        with (bskl_all_syn (colour (bskl_tophole (pskl_to_bskl_inh (bskl_to_pskl Q0))) A'0))
        by reflexivity.
      inversion Hwfa; subst.
      let g := gather_atoms in
      apply d_refine_syn__tophole_fill with (L := g `union` ftvar_in_bskl Q0).
      intros X HX.
      rewrite <- colour_open.
      (* New [tophole_fill] prepends [X] to [Γ] — exactly the IH's context; no move. *)
      match goal with
      | IH : forall _ : atom, _ -> _ -> forall _ _ _ : _, _ |- _ =>
          eapply (IH X ltac:(fsetdec) eq_refl (open_ptyp_wrt_ptyp A'0 (ptyp_var_f X)) P (bskl_tophole Q0))
      end;
        [ rewrite ptyp_to_btyp_inh_open_var; reflexivity
        | match goal with Hb : forall _ : atom, _ -> d_wf_ptyp _ _ |- _ => apply Hb; fsetdec end
        | exact Hsubs | exact Hg | exact Hhsu ].
  - (* forall_l_tagged *)
    destruct (ghost_of_shape Hg) as [Hqsh | [Q0 Hqsh]]; subst Q.
    + apply ghost_fill_hole_case; assumption.
    + simpl in Hsubs. inversion Hsubs; subst.
      * inversion Hg.
      * inversion Hg; subst. inversion Hhsu; subst.
        match goal with Hs0 : pskl_subsumes ?P0 (utyp_to_pskl _) |- _ =>
          eapply (IHHsub eq_refl A' (open_pskl_wrt_pskl P0 pskl_hole) (bskl_tophole Q0)) end;
          [ reflexivity | exact Hwfa
          | rewrite utyp_to_pskl_open; unfold open_pskl_wrt_pskl;
            apply pskl_subsumes_open_rec; [ eassumption | apply pskl_subsumes__hole ]
          | eassumption
          | eapply hole_safe_u_open_fill; [ eassumption | apply is_ttyp_lc; eassumption ] ].
  - (* forall_l_untagged *)
    destruct (ghost_of_shape Hg) as [Hqsh | [Q0 Hqsh]]; subst Q.
    + apply ghost_fill_hole_case; assumption.
    + simpl in Hsubs. inversion Hsubs; subst.
      * inversion Hg.
      * inversion Hg; subst. inversion Hhsu; subst.
        match goal with Hs0 : pskl_subsumes ?P0 (utyp_to_pskl _) |- _ =>
          eapply (IHHsub eq_refl A' (open_pskl_wrt_pskl P0 pskl_hole) (bskl_tophole Q0)) end;
          [ reflexivity | exact Hwfa
          | rewrite utyp_to_pskl_open; unfold open_pskl_wrt_pskl;
            apply pskl_subsumes_open_rec; [ eassumption | apply pskl_subsumes__hole ]
          | eassumption
          | eapply hole_safe_u_open_fill; [ eassumption | apply is_ttyp_lc; eassumption ] ].
Qed.

(** The bare ghost [□] is [skel_safe] for ANY type at [Δ = nil] ([In X nil]
    is [False], so the [sks_hole] scope side-condition is vacuous). *)
Lemma skel_safe_hole_nil : forall A, skel_safe nil pskl_hole A.
Proof. intros A. apply sks_hole. intros X HX HC. inversion HC. Qed.

(** [ghost_of_fill_gen]'s [skel_safe] twin: the ghost [Q] of a base term's
    principal skeleton is [skel_safe] for every checking type [A'] it subsumes
    to.  Same [d_sub] induction + invariants as [ghost_of_fill_gen], but the
    leaves land in [skel_safe] via the [tophole_safe]/[hole_safe] bridges
    ([check] → [ths_leaf] + [tophole_safe_skel_safe]; [forall_r] → [sks_top_all];
    [forall_l] → same IH re-instantiation).  Feeds the context-free
    [refine_colour_skel] so the [∀]-peel needs no [Γ]-weakening. *)
Lemma ghost_skel_safe : forall Δ Γ U V,
    Δ ⨟ Γ ⊢[ mode_tc ] U ⊑ V ->
    forall A' P Q,
      V = ptyp_to_btyp_inh A' ->
      d_wf_ptyp Γ A' ->
      pskl_subsumes P (utyp_to_pskl U) ->
      ghost_of P Q ->
      hole_safe_u nil P U ->
      skel_safe nil (bskl_to_pskl Q) A'.
Proof.
  intros Δ Γ U V Hsub. remember mode_tc as m eqn:Hm. revert Hm.
  induction Hsub; intros Hm A' P Q Heq Hwfa Hsubs Hg Hhsu; try discriminate Hm.
  - (* check : guarded_utyp C, guarded_btyp B, consis C ≈ B, B = inh A' *)
    destruct (ghost_of_shape Hg) as [Hqsh | [Q0 Hqsh]]; subst Q.
    + apply skel_safe_hole_nil.
    + assert (Hbq : bskl_to_pskl Q0 = P).
      { match goal with Hgu : guarded_utyp ?Uu |- _ => inversion Hgu; subst end;
        simpl in Hsubs; inversion Hsubs; subst; inversion Hg; subst; simpl;
        try reflexivity; rewrite ! bskl_to_pskl_pskl_to_bskl_syn; reflexivity. }
      replace (bskl_to_pskl (bskl_tophole Q0))
        with (pskl_tophole (bskl_to_pskl Q0)) by reflexivity.
      rewrite Hbq.
      apply tophole_safe_skel_safe; [ | eapply d_wf_ptyp_lc_loc; eauto ].
      apply ths_leaf.
      * intros A0 Hc; subst A';
          match goal with Hgb : guarded_btyp ?BB |- _ =>
            rewrite Heq in Hgb; inversion Hgb end.
      * eapply hole_safe_u_transport; [ exact Hhsu | eassumption | exact Heq ].
  - (* forall_r : V = inh (∀A'0) *)
    destruct A' as [ | n | X | A'a A'b | A'0 ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (ghost_of_shape Hg) as [Hqsh | [Q0 Hqsh]]; subst Q.
    + apply skel_safe_hole_nil.
    + replace (bskl_to_pskl (bskl_tophole Q0))
        with (pskl_tophole (bskl_to_pskl Q0)) by reflexivity.
      inversion Hwfa; subst.
      let g := gather_atoms in apply sks_top_all with (L := g). intros X HX.
      eapply (H1 X ltac:(fsetdec) eq_refl
                (open_ptyp_wrt_ptyp A'0 (ptyp_var_f X)) P (bskl_tophole Q0)).
      * rewrite ptyp_to_btyp_inh_open_var; reflexivity.
      * match goal with Hb : forall _ : atom, _ -> d_wf_ptyp _ _ |- _ => apply Hb; fsetdec end.
      * exact Hsubs.
      * exact Hg.
      * exact Hhsu.
  - (* forall_l_tagged *)
    destruct (ghost_of_shape Hg) as [Hqsh | [Q0 Hqsh]]; subst Q.
    + apply skel_safe_hole_nil.
    + simpl in Hsubs. inversion Hsubs; subst.
      * inversion Hg.
      * inversion Hg; subst. inversion Hhsu; subst.
        match goal with Hs0 : pskl_subsumes ?P0 (utyp_to_pskl _) |- _ =>
          eapply (IHHsub eq_refl A' (open_pskl_wrt_pskl P0 pskl_hole) (bskl_tophole Q0)) end;
          [ reflexivity | exact Hwfa
          | rewrite utyp_to_pskl_open; unfold open_pskl_wrt_pskl;
            apply pskl_subsumes_open_rec; [ eassumption | apply pskl_subsumes__hole ]
          | eassumption
          | eapply hole_safe_u_open_fill; [ eassumption | apply is_ttyp_lc; eassumption ] ].
  - (* forall_l_untagged *)
    destruct (ghost_of_shape Hg) as [Hqsh | [Q0 Hqsh]]; subst Q.
    + apply skel_safe_hole_nil.
    + simpl in Hsubs. inversion Hsubs; subst.
      * inversion Hg.
      * inversion Hg; subst. inversion Hhsu; subst.
        match goal with Hs0 : pskl_subsumes ?P0 (utyp_to_pskl _) |- _ =>
          eapply (IHHsub eq_refl A' (open_pskl_wrt_pskl P0 pskl_hole) (bskl_tophole Q0)) end;
          [ reflexivity | exact Hwfa
          | rewrite utyp_to_pskl_open; unfold open_pskl_wrt_pskl;
            apply pskl_subsumes_open_rec; [ eassumption | apply pskl_subsumes__hole ]
          | eassumption
          | eapply hole_safe_u_open_fill; [ eassumption | apply is_ttyp_lc; eassumption ] ].
Qed.

(** BRICK 3 GOAL — the fill side, a corollary of [ghost_of_fill_gen]
    (path (b): deterministic witness [colour]).  The ghost [Q] inferred for a
    base term's principal type [C] refines the colouring [colour inh{Q} A'] of
    every checking type [A'] the term subsumes to.  FULLY PROVED (Qed): the
    earlier [__check] and [__forall_r/⫯] admits are closed (via [check_leaf]
    and [tophole_fill] + the deterministic [colour] witness), as is the
    original [forall_l] [φ]/[□] obstacle. *)
Lemma ghost_of_fill : forall C Q Γ A',
    lc_ptyp C ->
    ghost_of (ptyp_to_pskl C) Q ->
    d_wf_ptyp Γ A' ->
    empty ⨟ Γ ⊢[ mode_tc ] (ptyp_to_utyp_syn C) ⊑ (ptyp_to_btyp_inh A') ->
    exists B, bskl_to_pskl B = ptyp_to_pskl A' /\
              Γ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳ B.
Proof.
  intros C Q Γ A' Hlc Hg Hwfa Hsub.
  exists (colour (pskl_to_bskl_inh (bskl_to_pskl Q)) A'). split.
  - apply colour_erasure.
  - eapply ghost_of_fill_gen with (P := ptyp_to_pskl C);
      [ exact Hsub | reflexivity | exact Hwfa | | exact Hg | ].
    + rewrite utyp_to_pskl_ptyp_to_utyp_syn. apply pskl_subsumes_refl.
    + apply hole_safe_u_of_ptyp. exact Hlc.
Qed.


(** * Paper-facing skeleton properties.

    The statements below are native to the new syntax. They remain
    research-level obligations while the main D1/D12 path is being
    re-established. *)

Lemma d_pat_preserves_skel_wf : forall Γ e Q,
    Γ ⊢[ mode_tc ] e ⇨ Q ->
    d_wf_denv Γ ->
    Γ ⨟ nil ⊢ₚₛ Q.
Proof.
  intros Γ e Q H _.
  apply (proj2 d_typing_pat_preserves_wf) with (m := mode_tc) (e := e); auto.
Qed.

(** ===================================================================== *)
(** Binding-replacement invariance (cascade for the [d_pat_safety] λ cases:
    rebind a λ-var [x:typ A ↦ x:skl (skel A)], same [dbind_to_pskl]).  These
    judgements read [Γ] only through TVAR lookups, so changing a term-var's
    binding (to one with the same skeleton view) is invariant. *)

Lemma d_wf_pskl_binding_eq : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P ->
    forall Γ1 x d d' Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 ->
    dbind_to_pskl d = dbind_to_pskl d' ->
    (Γ1 ++ (x ~ d') ++ Γ2) ⨟ Ψ ⊢ₚₛ P.
Proof.
  intros Ψ Γ P H. induction H; intros Γ1 x0 d0 d0' Γ2 Heq Hdd; subst.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
    analyze_binds Hb;
      assert (d0' = dbind_tvar) by (destruct d0'; simpl in Hdd; (reflexivity || discriminate));
      subst d0'; auto.
  - apply d_wf_pskl__arrow; [ eapply IHd_wf_pskl1 | eapply IHd_wf_pskl2 ]; eauto.
  - apply d_wf_pskl__all with (L := L). intros X HX. eapply H0; eauto.
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole; [ assumption | eapply IHd_wf_pskl; eauto ].
Qed.

Lemma d_pat_consis_binding_eq : forall Δ Γ R Q,
    Δ ⨟ Γ ⊨ₛ R ≈ Q ->
    forall Γ1 x d d' Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 ->
    dbind_to_pskl d = dbind_to_pskl d' ->
    Δ ⨟ (Γ1 ++ (x ~ d') ++ Γ2) ⊨ₛ R ≈ Q.
Proof.
  intros Δ Γ R Q H. induction H; intros Γ1 x0 d0 d0' Γ2 Heq Hdd; subst.
  - apply d_pat_consis__unit. assumption.
  - apply d_pat_consis__var; [ assumption | ].
    match goal with Hb : binds _ _ _ |- _ => analyze_binds Hb end;
      assert (d0' = dbind_tvar) by (destruct d0'; simpl in Hdd; (reflexivity || discriminate));
      subst d0'; auto.
  - eapply d_pat_consis__arrow;
      [ eapply IHd_pat_consis1 | eapply IHd_pat_consis2 | eassumption ]; eauto.
  - apply d_pat_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0);
      [ intros Z HZ;
        rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (x0 ~ d0') ++ Γ2);
        eapply (H0 Z HZ ((Z ~ dbind_tvar) ++ Γ1) x0 d0 d0' Γ2); [ simpl_env; reflexivity | exact Hdd ]
      | eassumption ].
  - apply d_pat_consis__forall_inh_untagged with (L := L). intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (x0 ~ d0') ++ Γ2).
    eapply (H0 Z HZ ((Z ~ dbind_tvar) ++ Γ1) x0 d0 d0' Γ2); [ simpl_env; reflexivity | exact Hdd ].
  - apply d_pat_consis__forall_syn_tagged with (L := L). intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (x0 ~ d0') ++ Γ2).
    eapply (H0 Z HZ ((Z ~ dbind_tvar) ++ Γ1) x0 d0 d0' Γ2); [ simpl_env; reflexivity | exact Hdd ].
  - apply d_pat_consis__forall_syn with (L := L). intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (x0 ~ d0') ++ Γ2).
    eapply (H0 Z HZ ((Z ~ dbind_tvar) ++ Γ1) x0 d0 d0' Γ2); [ simpl_env; reflexivity | exact Hdd ].
  - apply d_pat_consis__ghostg. assumption.
  - apply d_pat_consis__topholeg with (Ψ0 := Ψ0);
      [ eapply IHd_pat_consis; eauto | eassumption ].
  - apply d_pat_consis__hole; [ assumption | eapply d_wf_pskl_binding_eq; eauto ].
  - apply d_pat_consis__tophole. eapply IHd_pat_consis; eauto.
  - apply d_pat_consis__tophole_inh with (L := L). intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (x0 ~ d0') ++ Γ2).
    eapply (H0 Z HZ ((Z ~ dbind_tvar) ++ Γ1) x0 d0 d0' Γ2); [ simpl_env; reflexivity | exact Hdd ].
  - apply d_pat_consis__tophole_drop. eapply IHd_pat_consis; eauto.
Qed.

Lemma d_wf_ptyp_binding_eq : forall Γ A,
    Γ ⊢ₚ A ->
    forall Γ1 x d d' Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 ->
    dbind_to_pskl d = dbind_to_pskl d' ->
    (Γ1 ++ (x ~ d') ++ Γ2) ⊢ₚ A.
Proof.
  intros Γ A H. induction H; intros Γ1 x0 d0 d0' Γ2 Heq Hdd; subst.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. analyze_binds H;
      assert (d0' = dbind_tvar) by (destruct d0'; simpl in Hdd; (reflexivity || discriminate));
      subst d0'; auto.
  - apply d_wf_ptyp__arrow; [ eapply IHd_wf_ptyp1 | eapply IHd_wf_ptyp2 ]; eauto.
  - apply d_wf_ptyp__all with (L := L). intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ (x0 ~ d0') ++ Γ2).
    eapply (H0 X HX ((X ~ dbind_tvar) ++ Γ1) x0 d0 d0' Γ2); [ simpl_env; reflexivity | exact Hdd ].
Qed.

Lemma d_wf_uskl_binding_eq : forall Ψ Γ R,
    Γ ⨟ Ψ ⊢ᵤₛ R ->
    forall Γ1 x d d' Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 ->
    dbind_to_pskl d = dbind_to_pskl d' ->
    (Γ1 ++ (x ~ d') ++ Γ2) ⨟ Ψ ⊢ᵤₛ R.
Proof.
  intros Ψ Γ R H. induction H; intros Γ1 x0 d0 d0' Γ2 Heq Hdd; subst.
  - apply d_wf_uskl__unit.
  - apply d_wf_uskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
    analyze_binds Hb;
      assert (d0' = dbind_tvar) by (destruct d0'; simpl in Hdd; (reflexivity || discriminate));
      subst d0'; auto.
  - apply d_wf_uskl__arrow; [ eapply IHd_wf_uskl1 | eapply IHd_wf_uskl2 ]; eauto.
  - apply d_wf_uskl__all_syn with (L := L). intros X HX. eapply H0; eauto.
  - apply d_wf_uskl__all_etag with (L := L). intros X HX. eapply H0; eauto.
  - apply d_wf_uskl__hole.
  - apply d_wf_uskl__tophole; [ assumption | eapply IHd_wf_uskl; eauto ].
  - apply d_wf_uskl__holeg.
  - apply d_wf_uskl__topholeg; [ assumption | eapply IHd_wf_uskl; eauto ].
Qed.

Lemma d_pat_sub_binding_eq : forall Δ Γ m R Q,
    Δ ⨟ Γ ⊢ₛ[ m ] R ⊑ Q ->
    forall Γ1 x d d' Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 ->
    dbind_to_pskl d = dbind_to_pskl d' ->
    Δ ⨟ (Γ1 ++ (x ~ d') ++ Γ2) ⊢ₛ[ m ] R ⊑ Q.
Proof.
  intros Δ Γ m R Q H. induction H; intros Γ1 x0 d0 d0' Γ2 Heq Hdd; subst.
  - apply d_pat_sub__infer; [ assumption | eapply d_pat_consis_binding_eq; eauto | assumption ].
  - apply d_pat_sub__univ_ghost_r; try assumption. eapply d_pat_consis_binding_eq; eauto.
  - eapply d_pat_sub__arg;
      [ eapply d_pat_consis_binding_eq; eauto | eapply IHd_pat_sub; eauto | eassumption ].
  - eapply d_pat_sub__forall_l_tagged;
      [ assumption | eassumption | eassumption | eapply d_wf_uskl_binding_eq; eauto
      | assumption | eapply IHd_pat_sub; eauto ].
  - eapply d_pat_sub__forall_l_untagged;
      [ assumption | eassumption | eassumption | eapply d_wf_uskl_binding_eq; eauto
      | assumption | eapply IHd_pat_sub; eauto ].
  - apply d_pat_sub__ghost; [ assumption | eapply d_wf_pskl_binding_eq; eauto | assumption ].
  - apply d_pat_sub__univ_ghost_l; [ assumption | eapply IHd_pat_sub; eauto ].
  - apply d_pat_sub__ghostg; assumption.
  - apply d_pat_sub__univ_ghost_lg; [ assumption | eapply IHd_pat_sub; eauto ].
Qed.

Lemma d_refine_syn_binding_eq : forall Γ Δi Q P,
    Γ ⨟ Δi ⊢ᵣ Q ⊳ P ->
    forall Γ1 x d d' Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 ->
    dbind_to_pskl d = dbind_to_pskl d' ->
    (Γ1 ++ (x ~ d') ++ Γ2) ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ Δi Q P H. induction H; intros Γ1 x0 d0 d0' Γ2 Heq Hdd; subst.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [HI | Hb];
      [ left; assumption | right ].
    analyze_binds Hb;
      assert (d0' = dbind_tvar) by (destruct d0'; simpl in Hdd; (reflexivity || discriminate));
      subst d0'; auto.
  - apply d_refine_syn__arrow; [ eapply IHd_refine_syn1 | eapply IHd_refine_syn2 ]; eauto.
  - apply d_refine_syn__all with (L := L). intros X HX.
    eapply (H0 X HX Γ1 x0 d0 d0' Γ2); [ reflexivity | exact Hdd ].
  - apply d_refine_syn__hole. eapply d_wf_pskl_binding_eq; eauto.
  - apply d_refine_syn__tophole_remove. eapply IHd_refine_syn; eauto.
  - apply d_refine_syn__tophole_fill with (L := L). intros X HX.
    eapply (H0 X HX ((X ~ dbind_tvar) ++ Γ1) x0 d0 d0' Γ2);
      [ simpl_env; reflexivity | exact Hdd ].
  - apply d_refine_syn__tophole_keep; [ assumption | eapply IHd_refine_syn; eauto ].
Qed.

Lemma d_pat_binding_eq : forall m Γ e Q,
    Γ ⊢[ m ] e ⇨ Q ->
    forall Γ1 x d d' Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 ->
    dbind_to_pskl d = dbind_to_pskl d' ->
    (Γ1 ++ (x ~ d') ++ Γ2) ⊢[ m ] e ⇨ Q.
Proof.
  (* Structural induction on [d_pat]; [Γ] is read only through tvar/binding
     lookups whose [pskl]-view is preserved, so each sub-judgment is rebound by
     its own [binding_eq] lemma.  Mirrors [d_pat_weakening_mid]. *)
  intros m Γ e Q H. induction H; intros Γ1 x0 d0 d0' Γ2 Heq Hdd; subst.
  - apply d_pat__unit.
  - (* var *) analyze_binds H.
    + apply d_pat__var with (d := d);
        [ apply binds_app_iff; left; assumption | assumption ].
    + apply d_pat__var with (d := d0');
        [ apply binds_app_iff; right; apply binds_app_iff; left;
          apply binds_one_iff; auto
        | rewrite <- Hdd; assumption ].
    + apply d_pat__var with (d := d);
        [ apply binds_app_iff; right; apply binds_app_iff; right; assumption
        | assumption ].
  - apply d_pat__anno. eapply d_wf_ptyp_binding_eq; eauto.
  - apply d_pat__sub with (P := P);
      [ assumption | eapply IHd_pat; eauto | eapply d_pat_sub_binding_eq; eauto ].
  - apply d_pat__freeze. eapply IHd_pat; eauto.
  - apply d_pat__abs with (L := L `union` dom (Γ1 ++ (x0 ~ d0') ++ Γ2)) (P := P);
      [ assumption | eapply d_wf_pskl_binding_eq; eauto | assumption | ].
    intros y Hy. rewrite_env (((y ~ dbind_skl P) ++ Γ1) ++ (x0 ~ d0') ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hdd ].
  - apply d_pat__abs_anno with (L := L `union` dom (Γ1 ++ (x0 ~ d0') ++ Γ2)) (B := B);
      [ assumption | eapply d_wf_ptyp_binding_eq; eauto | reflexivity | assumption | ].
    intros y Hy. rewrite_env (((y ~ dbind_typ (btyp_to_ptyp B)) ++ Γ1) ++ (x0 ~ d0') ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hdd ].
  - eapply d_pat__app;
      [ eapply IHd_pat1; eauto | eapply d_refine_syn_binding_eq; eauto
      | eapply IHd_pat2; eauto ].
  - apply d_pat__abs_check with (L := L `union` dom (Γ1 ++ (x0 ~ d0') ++ Γ2)).
    intros y Hy. rewrite_env (((y ~ dbind_skl pskl_hole) ++ Γ1) ++ (x0 ~ d0') ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hdd ].
  - apply d_pat__abs_anno_check with (L := L `union` dom (Γ1 ++ (x0 ~ d0') ++ Γ2)) (A := A);
      [ eapply d_wf_ptyp_binding_eq; eauto | ].
    intros y Hy. rewrite_env (((y ~ dbind_typ A) ++ Γ1) ++ (x0 ~ d0') ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hdd ].
Qed.

(** [more_ghost Q' Q]: [Q'] is [Q] with some sub-skeletons replaced by the plain
    ghost [□].  Backbone of [d_pat_weaken_hole]: rebinding a λ-var to [□]
    ghostifies its uses, so the inferred skeleton becomes [more_ghost] than the
    original. *)
Inductive more_ghost : bskl -> bskl -> Prop :=
| more_ghost__hole  : forall Q, more_ghost bskl_hole Q
| more_ghost__unit  : more_ghost bskl_unit bskl_unit
| more_ghost__var   : forall X, more_ghost (bskl_var_f X) (bskl_var_f X)
| more_ghost__arrow : forall Q1 Q2 R1 R2,
    more_ghost Q1 R1 -> more_ghost Q2 R2 ->
    more_ghost (bskl_arrow Q1 Q2) (bskl_arrow R1 R2)
| more_ghost__all_syn : forall L Q R,
    (forall X, X `notin` L ->
       more_ghost (open_bskl_wrt_bskl Q (bskl_var_f X))
                  (open_bskl_wrt_bskl R (bskl_var_f X))) ->
    more_ghost (bskl_all_syn Q) (bskl_all_syn R)
| more_ghost__all_inh : forall L Q R,
    (forall X, X `notin` L ->
       more_ghost (open_bskl_wrt_bskl Q (bskl_var_f X))
                  (open_bskl_wrt_bskl R (bskl_var_f X))) ->
    more_ghost (bskl_all_inh Q) (bskl_all_inh R)
| more_ghost__tophole : forall Q R,
    more_ghost Q R -> more_ghost (bskl_tophole Q) (bskl_tophole R).

Lemma more_ghost_refl : forall Q, lc_bskl Q -> more_ghost Q Q.
Proof.
  intros Q H. induction H.
  - apply more_ghost__unit.
  - apply more_ghost__var.
  - apply more_ghost__arrow; assumption.
  - apply more_ghost__all_syn with (L := empty). intros X _. auto.
  - apply more_ghost__all_inh with (L := empty). intros X _. auto.
  - apply more_ghost__hole.
  - apply more_ghost__tophole. assumption.
Qed.

(** [ghost_rel Γp Γt]: the [d_pat] context [Γp] is the typing context [Γt] with
    each term var either KEPT (same binding — "a type is a skel" makes
    [d_pat__var] read [dbind_typ A] as [skl(skel A)]) or GHOSTIFIED to [skl □]
    (so the body of a checked-λ infers for any checking arg type).  Backbone of
    the mode-generalised [d_pat_total]. *)
Inductive ghost_rel : list (atom * dbind) -> list (atom * dbind) -> Prop :=
| gr_nil   : ghost_rel nil nil
| gr_keep  : forall Γp Γt x d,
    ghost_rel Γp Γt -> ghost_rel ((x ~ d) ++ Γp) ((x ~ d) ++ Γt)
| gr_ghost : forall Γp Γt x A,
    ghost_rel Γp Γt ->
    ghost_rel ((x ~ dbind_skl pskl_hole) ++ Γp) ((x ~ dbind_typ A) ++ Γt).

Lemma ghost_rel_refl : forall Γ, ghost_rel Γ Γ.
Proof.
  induction Γ as [|[x d] Γ' IH].
  - apply gr_nil.
  - apply gr_keep; assumption.
Qed.

(** A term var typed in [Γt] is bound in [Γp] to *some* binding whose
    [dbind_to_pskl] is defined (its own skel if kept, [□] if ghostified). *)
Lemma ghost_rel_binds_typ : forall Γp Γt x A,
    ghost_rel Γp Γt ->
    binds x (dbind_typ A) Γt ->
    exists d P, binds x d Γp /\ dbind_to_pskl d = Some P.
Proof.
  intros Γp Γt x A Hgr. induction Hgr; intros Hb.
  - analyze_binds Hb.
  - analyze_binds Hb.
    + exists (dbind_typ A), (ptyp_to_pskl A). split; [ auto | reflexivity ].
    + destruct (IHHgr BindsTac) as [d' [P' [Hb' Hd']]].
      exists d', P'. split; [ auto | assumption ].
  - analyze_binds Hb.
    + exists (dbind_skl pskl_hole), pskl_hole. split; [ auto | reflexivity ].
    + destruct (IHHgr BindsTac) as [d' [P' [Hb' Hd']]].
      exists d', P'. split; [ auto | assumption ].
Qed.

(** [ghost_rel] preserves tvar bindings (it only ever changes a term var's
    binding — keep, or [typ A ↦ skl □]). *)
Lemma ghost_rel_binds_tvar : forall Γp Γt X,
    ghost_rel Γp Γt -> binds X dbind_tvar Γt -> binds X dbind_tvar Γp.
Proof.
  intros Γp Γt X Hgr. induction Hgr; intros Hb.
  - analyze_binds Hb.
  - analyze_binds Hb; auto.
  - analyze_binds Hb; auto.
Qed.

(** The [ghost_rel]-invariance cascade: every side-condition judgment in the
    [d_pat] rules reads only tvar bindings, so it transports along [ghost_rel].
    Mirrors the [binding_eq] cascade; var cases via [ghost_rel_binds_tvar],
    Γ-growing cofinite cases via [gr_keep]. *)
Lemma d_wf_pskl_ghost_rel : forall Ψ Γt P,
    Γt ⨟ Ψ ⊢ₚₛ P -> forall Γp, ghost_rel Γp Γt -> Γp ⨟ Ψ ⊢ₚₛ P.
Proof.
  intros Ψ Γt P H. induction H; intros Γp Hgr.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [HΨ | Hb];
      [ left; assumption | right; eapply ghost_rel_binds_tvar; eauto ].
  - apply d_wf_pskl__arrow; [ eapply IHd_wf_pskl1 | eapply IHd_wf_pskl2 ]; eauto.
  - apply d_wf_pskl__all with (L := L). intros X HX. eapply H0; eauto.
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole; [ assumption | eapply IHd_wf_pskl; eauto ].
Qed.

Lemma d_wf_ptyp_ghost_rel : forall Γt A,
    Γt ⊢ₚ A -> forall Γp, ghost_rel Γp Γt -> Γp ⊢ₚ A.
Proof.
  intros Γt A H. induction H; intros Γp Hgr.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. eapply ghost_rel_binds_tvar; eauto.
  - apply d_wf_ptyp__arrow; [ eapply IHd_wf_ptyp1 | eapply IHd_wf_ptyp2 ]; eauto.
  - apply d_wf_ptyp__all with (L := L). intros X HX.
    eapply H0; [ exact HX | apply gr_keep; exact Hgr ].
Qed.

Lemma d_wf_uskl_ghost_rel : forall Ψ Γt R,
    Γt ⨟ Ψ ⊢ᵤₛ R -> forall Γp, ghost_rel Γp Γt -> Γp ⨟ Ψ ⊢ᵤₛ R.
Proof.
  intros Ψ Γt R H. induction H; intros Γp Hgr.
  - apply d_wf_uskl__unit.
  - apply d_wf_uskl__var. destruct H as [HΨ | Hb];
      [ left; assumption | right; eapply ghost_rel_binds_tvar; eauto ].
  - apply d_wf_uskl__arrow; [ eapply IHd_wf_uskl1 | eapply IHd_wf_uskl2 ]; eauto.
  - apply d_wf_uskl__all_syn with (L := L). intros X HX. eapply H0; eauto.
  - apply d_wf_uskl__all_etag with (L := L). intros X HX. eapply H0; eauto.
  - apply d_wf_uskl__hole.
  - apply d_wf_uskl__tophole; [ assumption | eapply IHd_wf_uskl; eauto ].
  - apply d_wf_uskl__holeg.
  - apply d_wf_uskl__topholeg; [ assumption | eapply IHd_wf_uskl; eauto ].
Qed.

Lemma d_pat_consis_ghost_rel : forall Δ Γt R Q,
    Δ ⨟ Γt ⊨ₛ R ≈ Q -> forall Γp, ghost_rel Γp Γt -> Δ ⨟ Γp ⊨ₛ R ≈ Q.
Proof.
  intros Δ Γt R Q H. induction H; intros Γp Hgr.
  - apply d_pat_consis__unit. assumption.
  - apply d_pat_consis__var; [ assumption | eapply ghost_rel_binds_tvar; eauto ].
  - eapply d_pat_consis__arrow;
      [ eapply IHd_pat_consis1 | eapply IHd_pat_consis2 | eassumption ]; eauto.
  - apply d_pat_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0);
      [ intros Z HZ; eapply H0; [ exact HZ | apply gr_keep; exact Hgr ] | eassumption ].
  - apply d_pat_consis__forall_inh_untagged with (L := L). intros Z HZ.
    eapply H0; [ exact HZ | apply gr_keep; exact Hgr ].
  - apply d_pat_consis__forall_syn_tagged with (L := L). intros Z HZ.
    eapply H0; [ exact HZ | apply gr_keep; exact Hgr ].
  - apply d_pat_consis__forall_syn with (L := L). intros Z HZ.
    eapply H0; [ exact HZ | apply gr_keep; exact Hgr ].
  - apply d_pat_consis__ghostg. assumption.
  - apply d_pat_consis__topholeg with (Ψ0 := Ψ0);
      [ eapply IHd_pat_consis; eauto | eassumption ].
  - apply d_pat_consis__hole; [ assumption | eapply d_wf_pskl_ghost_rel; eauto ].
  - apply d_pat_consis__tophole. eapply IHd_pat_consis; eauto.
  - apply d_pat_consis__tophole_inh with (L := L). intros Z HZ.
    eapply H0; [ exact HZ | apply gr_keep; exact Hgr ].
  - apply d_pat_consis__tophole_drop. eapply IHd_pat_consis; eauto.
Qed.

Lemma d_pat_sub_ghost_rel : forall Δ Γt m R Q,
    Δ ⨟ Γt ⊢ₛ[ m ] R ⊑ Q -> forall Γp, ghost_rel Γp Γt -> Δ ⨟ Γp ⊢ₛ[ m ] R ⊑ Q.
Proof.
  intros Δ Γt m R Q H. induction H; intros Γp Hgr.
  - apply d_pat_sub__infer; [ assumption | eapply d_pat_consis_ghost_rel; eauto | assumption ].
  - apply d_pat_sub__univ_ghost_r; try assumption. eapply d_pat_consis_ghost_rel; eauto.
  - eapply d_pat_sub__arg;
      [ eapply d_pat_consis_ghost_rel; eauto | eapply IHd_pat_sub; eauto | eassumption ].
  - eapply d_pat_sub__forall_l_tagged;
      [ assumption | eassumption | eassumption | eapply d_wf_uskl_ghost_rel; eauto
      | assumption | eapply IHd_pat_sub; eauto ].
  - eapply d_pat_sub__forall_l_untagged;
      [ assumption | eassumption | eassumption | eapply d_wf_uskl_ghost_rel; eauto
      | assumption | eapply IHd_pat_sub; eauto ].
  - apply d_pat_sub__ghost; [ assumption | eapply d_wf_pskl_ghost_rel; eauto | assumption ].
  - apply d_pat_sub__univ_ghost_l; [ assumption | eapply IHd_pat_sub; eauto ].
  - apply d_pat_sub__ghostg; assumption.
  - apply d_pat_sub__univ_ghost_lg; [ assumption | eapply IHd_pat_sub; eauto ].
Qed.

Lemma d_refine_syn_ghost_rel : forall Γt Δi Q P,
    Γt ⨟ Δi ⊢ᵣ Q ⊳ P -> forall Γp, ghost_rel Γp Γt -> Γp ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γt Δi Q P H. induction H; intros Γp Hgr.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [HI | Hb];
      [ left; assumption | right; eapply ghost_rel_binds_tvar; eauto ].
  - apply d_refine_syn__arrow; [ eapply IHd_refine_syn1 | eapply IHd_refine_syn2 ]; eauto.
  - apply d_refine_syn__all with (L := L). intros X HX. eapply H0; eauto.
  - apply d_refine_syn__hole. eapply d_wf_pskl_ghost_rel; eauto.
  - apply d_refine_syn__tophole_remove. eapply IHd_refine_syn; eauto.
  - apply d_refine_syn__tophole_fill with (L := L). intros X HX.
    eapply (H0 X HX ((X ~ dbind_tvar) ++ Γp)). apply gr_keep; assumption.
  - apply d_refine_syn__tophole_keep; [ assumption | eapply IHd_refine_syn; eauto ].
Qed.

(** Term-var RENAME cascade: rename a (non-tvar) term binding [x~d ↦ y~d] in the
    context.  Side-condition judgments read only tvar bindings, so the looked-up
    tvar is never the renamed term var ([d <> dbind_tvar] rules out the clash),
    and no freshness on [y] is needed (a tvar found in [Γ1]/[Γ2] stays bound
    after splicing [y~d] into the middle).  Backbone of [d_pat_rename_var], itself
    needed for [d_pat__abs_check]'s cofinite-uniform witness in [d_pat_total]. *)
Lemma d_wf_pskl_rename_var : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P ->
    forall Γ1 x y d Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    (Γ1 ++ (y ~ d) ++ Γ2) ⨟ Ψ ⊢ₚₛ P.
Proof.
  intros Ψ Γ P H. induction H; intros Γ1 x0 y0 d0 Γ2 Heq Hd; subst.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
    analyze_binds Hb; try (exfalso; congruence); auto.
  - apply d_wf_pskl__arrow; [ eapply IHd_wf_pskl1 | eapply IHd_wf_pskl2 ]; eauto.
  - apply d_wf_pskl__all with (L := L). intros X HX. eapply H0; eauto.
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole; [ assumption | eapply IHd_wf_pskl; eauto ].
Qed.

Lemma d_wf_ptyp_rename_var : forall Γ A,
    Γ ⊢ₚ A ->
    forall Γ1 x y d Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    (Γ1 ++ (y ~ d) ++ Γ2) ⊢ₚ A.
Proof.
  intros Γ A H. induction H; intros Γ1 x0 y0 d0 Γ2 Heq Hd; subst.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. analyze_binds H; try (exfalso; congruence); auto.
  - apply d_wf_ptyp__arrow; [ eapply IHd_wf_ptyp1 | eapply IHd_wf_ptyp2 ]; eauto.
  - apply d_wf_ptyp__all with (L := L). intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 X HX ((X ~ dbind_tvar) ++ Γ1) x0 y0 d0 Γ2); [ simpl_env; reflexivity | exact Hd ].
Qed.

Lemma d_wf_uskl_rename_var : forall Ψ Γ R,
    Γ ⨟ Ψ ⊢ᵤₛ R ->
    forall Γ1 x y d Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    (Γ1 ++ (y ~ d) ++ Γ2) ⨟ Ψ ⊢ᵤₛ R.
Proof.
  intros Ψ Γ R H. induction H; intros Γ1 x0 y0 d0 Γ2 Heq Hd; subst.
  - apply d_wf_uskl__unit.
  - apply d_wf_uskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
    analyze_binds Hb; try (exfalso; congruence); auto.
  - apply d_wf_uskl__arrow; [ eapply IHd_wf_uskl1 | eapply IHd_wf_uskl2 ]; eauto.
  - apply d_wf_uskl__all_syn with (L := L). intros X HX. eapply H0; eauto.
  - apply d_wf_uskl__all_etag with (L := L). intros X HX. eapply H0; eauto.
  - apply d_wf_uskl__hole.
  - apply d_wf_uskl__tophole; [ assumption | eapply IHd_wf_uskl; eauto ].
  - apply d_wf_uskl__holeg.
  - apply d_wf_uskl__topholeg; [ assumption | eapply IHd_wf_uskl; eauto ].
Qed.

Lemma d_pat_consis_rename_var : forall Δ Γ R Q,
    Δ ⨟ Γ ⊨ₛ R ≈ Q ->
    forall Γ1 x y d Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    Δ ⨟ (Γ1 ++ (y ~ d) ++ Γ2) ⊨ₛ R ≈ Q.
Proof.
  intros Δ Γ R Q H. induction H; intros Γ1 x0 y0 d0 Γ2 Heq Hd; subst.
  - apply d_pat_consis__unit; (assumption || fsetdec).
  - apply d_pat_consis__var; [ (assumption || fsetdec) | ]; match goal with Hb : binds _ _ _ |- _ => analyze_binds Hb end; try (exfalso; congruence); auto.
  - eapply d_pat_consis__arrow; [ eapply IHd_pat_consis1 | eapply IHd_pat_consis2 | (eassumption || fsetdec) ]; eauto.
  - apply d_pat_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0). 2: assumption. intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 Z HZ ((Z ~ dbind_tvar) ++ Γ1) x0 y0 d0 Γ2); [ simpl_env; reflexivity | exact Hd ].
  - apply d_pat_consis__forall_inh_untagged with (L := L). intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 Z HZ ((Z ~ dbind_tvar) ++ Γ1) x0 y0 d0 Γ2); [ simpl_env; reflexivity | exact Hd ].
  - apply d_pat_consis__forall_syn_tagged with (L := L). intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 Z HZ ((Z ~ dbind_tvar) ++ Γ1) x0 y0 d0 Γ2); [ simpl_env; reflexivity | exact Hd ].
  - apply d_pat_consis__forall_syn with (L := L). intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 Z HZ ((Z ~ dbind_tvar) ++ Γ1) x0 y0 d0 Γ2); [ simpl_env; reflexivity | exact Hd ].
  - apply d_pat_consis__ghostg; (assumption || fsetdec).
  - apply d_pat_consis__topholeg with (Ψ0 := Ψ0);
      [ eapply IHd_pat_consis; eauto | eassumption ].
  - apply d_pat_consis__hole; [ (assumption || fsetdec) | ]; eapply d_wf_pskl_rename_var; eauto.
  - apply d_pat_consis__tophole. eapply IHd_pat_consis; eauto.
  - apply d_pat_consis__tophole_inh with (L := L). intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 Z HZ ((Z ~ dbind_tvar) ++ Γ1) x0 y0 d0 Γ2); [ simpl_env; reflexivity | exact Hd ].
  - apply d_pat_consis__tophole_drop. eapply IHd_pat_consis; eauto.
Qed.

Lemma d_pat_sub_rename_var : forall Δ Γ m R Q,
    Δ ⨟ Γ ⊢ₛ[ m ] R ⊑ Q ->
    forall Γ1 x y d Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    Δ ⨟ (Γ1 ++ (y ~ d) ++ Γ2) ⊢ₛ[ m ] R ⊑ Q.
Proof.
  intros Δ Γ m R Q H. induction H; intros Γ1 x0 y0 d0 Γ2 Heq Hd; subst.
  - apply d_pat_sub__infer; [ (assumption || fsetdec) | eapply d_pat_consis_rename_var; eauto | assumption ].
  - apply d_pat_sub__univ_ghost_r; try assumption. eapply d_pat_consis_rename_var; eauto.
  - eapply d_pat_sub__arg; [ eapply d_pat_consis_rename_var; eauto | eapply IHd_pat_sub; eauto | (eassumption || fsetdec) ].
  - eapply d_pat_sub__forall_l_tagged;
      [ assumption | eassumption | eassumption | eapply d_wf_uskl_rename_var; eauto
      | assumption | eapply IHd_pat_sub; eauto ].
  - eapply d_pat_sub__forall_l_untagged;
      [ assumption | eassumption | eassumption | eapply d_wf_uskl_rename_var; eauto
      | assumption | eapply IHd_pat_sub; eauto ].
  - apply d_pat_sub__ghost; [ (assumption || fsetdec) | eapply d_wf_pskl_rename_var; eauto | assumption ].
  - apply d_pat_sub__univ_ghost_l; [ assumption | eapply IHd_pat_sub; eauto ].
  - apply d_pat_sub__ghostg; (assumption || fsetdec).
  - apply d_pat_sub__univ_ghost_lg; [ assumption | eapply IHd_pat_sub; eauto ].
Qed.

Lemma d_refine_syn_rename_var : forall Γ Δi Q P,
    Γ ⨟ Δi ⊢ᵣ Q ⊳ P ->
    forall Γ1 x y d Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    (Γ1 ++ (y ~ d) ++ Γ2) ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ Δi Q P H. induction H; intros Γ1 x0 y0 d0 Γ2 Heq Hd; subst.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [HI | Hb];
      [ left; assumption | right ].
    analyze_binds Hb; try (exfalso; congruence); auto.
  - apply d_refine_syn__arrow; [ eapply IHd_refine_syn1 | eapply IHd_refine_syn2 ]; eauto.
  - apply d_refine_syn__all with (L := L). intros X HX.
    eapply (H0 X HX Γ1 x0 y0 d0 Γ2); [ reflexivity | exact Hd ].
  - apply d_refine_syn__hole. eapply d_wf_pskl_rename_var; eauto.
  - apply d_refine_syn__tophole_remove. eapply IHd_refine_syn; eauto.
  - apply d_refine_syn__tophole_fill with (L := L). intros X HX.
    eapply (H0 X HX ((X ~ dbind_tvar) ++ Γ1) x0 y0 d0 Γ2);
      [ simpl_env; reflexivity | exact Hd ].
  - apply d_refine_syn__tophole_keep; [ assumption | eapply IHd_refine_syn; eauto ].
Qed.

(** [d_pat] is invariant under renaming a (non-tvar, unshadowed) term var [x ↦ y]
    in the context, substituting [x ↦ y] in the term.  The inferred skeleton [Q]
    is UNCHANGED (skeletons carry no term vars).  This is exactly what makes
    [d_pat__abs_check]'s cofinite-uniform witness work: infer the body at one
    fresh [x], then rename to any other fresh [y] keeping the SAME [Q]. *)
Lemma d_pat_rename_var : forall m Γ e Q,
    Γ ⊢[ m ] e ⇨ Q ->
    forall Γ1 x y d Γ2, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    x `notin` dom (Γ1 ++ Γ2) ->
    (Γ1 ++ (y ~ d) ++ Γ2) ⊢[ m ] (subst_exp_in_exp (exp_var_f y) x e) ⇨ Q.
Proof.
  (* Direct structural induction.  The skeleton [Q] never changes (it carries
     no term vars); each sub-judgment is transported by its own [_rename] lemma,
     and the λ bodies commute the [x↦y] substitution past the opener.  The only
     real content is the [var] case, where [x ∉ dom(Γ1++Γ2)] pins the looked-up
     binding to the relabelled middle one. *)
  intros m Γ e Q H. induction H; intros Γ1 x0 y0 d0 Γ2 Heq Hd Hnotin; subst.
  - simpl. apply d_pat__unit.
  - (* var *) simpl.
    match goal with |- context [ if ?b then _ else _ ] => destruct b as [Heq | Hne] end.
    + (* x = x0: the relabelled var; [Hnotin] forces [d = d0] *)
      subst x. assert (Hdd : d = d0).
      { apply binds_app_1 in H. destruct H as [Hb1 | Hb2].
        - apply binds_In in Hb1. exfalso. apply Hnotin. rewrite dom_app. fsetdec.
        - apply binds_app_1 in Hb2. destruct Hb2 as [Hb3 | Hb4].
          + apply binds_one_iff in Hb3. destruct Hb3 as [_ Heqd]. exact Heqd.
          + apply binds_In in Hb4. exfalso. apply Hnotin. rewrite dom_app. fsetdec. }
      subst d. apply d_pat__var with (d := d0); [ | assumption ].
      apply binds_app_3; simpl; auto.
    + (* x <> x0: binding unchanged *)
      apply d_pat__var with (d := d); [ | assumption ].
      apply binds_app_1 in H. destruct H as [Hb1 | Hb2].
      * apply binds_app_2; assumption.
      * apply binds_app_1 in Hb2. destruct Hb2 as [Hb3 | Hb4].
        -- apply binds_one_iff in Hb3. destruct Hb3 as [Hxe _]. exfalso. apply Hne. exact Hxe.
        -- apply binds_app_3; simpl; auto.
  - simpl. apply d_pat__anno. eapply d_wf_ptyp_rename_var; eauto.
  - simpl. apply d_pat__sub with (P := P);
      [ match goal with Hbe : is_base_term _ |- _ =>
          inversion Hbe; subst; simpl;
          try (match goal with |- context [ if ?b then _ else _ ] => destruct b end);
          constructor end
      | eapply IHd_pat; eauto | eapply d_pat_sub_rename_var; eauto ].
  - simpl. apply d_pat__freeze. eapply IHd_pat; eauto.
  - simpl. apply d_pat__abs with (L := L `union` singleton x0 `union` dom (Γ1 ++ Γ2)) (P := P);
      [ assumption | eapply d_wf_pskl_rename_var; eauto | assumption | ].
    intros z Hz. rewrite subst_exp_in_exp_open_exp_wrt_exp_var
      by (solve [ apply lc_exp_var_f | fsetdec ]).
    rewrite_env (((z ~ dbind_skl P) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hd | simpl_env in *; fsetdec ].
  - simpl. apply d_pat__abs_anno with (L := L `union` singleton x0 `union` dom (Γ1 ++ Γ2)) (B := B);
      [ assumption | eapply d_wf_ptyp_rename_var; eauto | reflexivity | assumption | ].
    intros z Hz. rewrite subst_exp_in_exp_open_exp_wrt_exp_var
      by (solve [ apply lc_exp_var_f | fsetdec ]).
    rewrite_env (((z ~ dbind_typ (btyp_to_ptyp B)) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hd | simpl_env in *; fsetdec ].
  - simpl. eapply d_pat__app;
      [ eapply IHd_pat1 | eapply d_refine_syn_rename_var | eapply IHd_pat2 ]; eauto.
  - simpl. apply d_pat__abs_check with (L := L `union` singleton x0 `union` dom (Γ1 ++ Γ2)).
    intros z Hz. rewrite subst_exp_in_exp_open_exp_wrt_exp_var
      by (solve [ apply lc_exp_var_f | fsetdec ]).
    rewrite_env (((z ~ dbind_skl pskl_hole) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hd | simpl_env in *; fsetdec ].
  - simpl. apply d_pat__abs_anno_check with (L := L `union` singleton x0 `union` dom (Γ1 ++ Γ2)) (A := A);
      [ eapply d_wf_ptyp_rename_var; eauto | ].
    intros z Hz. rewrite subst_exp_in_exp_open_exp_wrt_exp_var
      by (solve [ apply lc_exp_var_f | fsetdec ]).
    rewrite_env (((z ~ dbind_typ A) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    match goal with IH : forall _ : atom, _ -> forall _ _ _ _ _, _ |- _ =>
      eapply IH end; [ fsetdec | simpl_env; reflexivity | exact Hd | simpl_env in *; fsetdec ].
Qed.

(** Substituting one variable for another preserves [is_value] / [is_base_term]
    (the substituted term is itself a variable, so the head shape is kept). *)
Lemma is_value_subst_var : forall e x y,
    is_value e -> is_value (subst_exp_in_exp (exp_var_f y) x e).
Proof.
  intros e x y H. induction H; simpl;
    [ apply is_value__unit
    | match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      apply is_value__var
    | apply is_value__abs | apply is_value__abs_anno
    | apply is_value__anno; assumption ].
Qed.

Lemma is_base_subst_var : forall e x y,
    is_base_term e -> is_base_term (subst_exp_in_exp (exp_var_f y) x e).
Proof.
  intros e x y H. induction H; simpl;
    [ apply is_base_term__unit
    | match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      apply is_base_term__var
    | apply is_base_term__anno ].
Qed.

(** GENERAL variable substitution for skeleton inference: substituting [y] for
    [x] in ANY expression preserves [⇨], provided [x] and [y] have the same
    binding in the (unchanged) context. *)
Lemma d_pat_subst_var : forall m Γ e Q,
    Γ ⊢[ m ] e ⇨ Q ->
    forall x y d, uniq Γ -> binds x d Γ -> binds y d Γ ->
    Γ ⊢[ m ] (subst_exp_in_exp (exp_var_f y) x e) ⇨ Q.
Proof.
  intros m Γ e Q H. induction H; intros x0 y0 d0 Huniq Hbx Hby; simpl.
  - apply d_pat__unit.
  - (* var *) match goal with |- context [ if ?b then _ else _ ] => destruct b as [Heq | Hne] end.
    + subst x. assert (d = d0) by (eapply binds_unique; eauto). subst d.
      apply d_pat__var with (d := d0); [ exact Hby | exact H0 ].
    + apply d_pat__var with (d := d); [ exact H | exact H0 ].
  - (* anno *) apply d_pat__anno. exact H.
  - (* sub *) apply d_pat__sub with (P := P);
      [ apply is_base_subst_var; exact H | eapply IHd_pat; eauto | exact H1 ].
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
    forall x y T, uniq Γ -> binds x (dbind_typ T) Γ -> binds y (dbind_typ T) Γ ->
    Γ ⊢[ m ] (subst_exp_in_exp (exp_var_f y) x e) ⦂ B.
Proof.
  intros m Γ e B H. induction H; intros x0 y0 T Huniq Hbx Hby; simpl.
  - apply d_typing__unit.
  - (* var *) match goal with |- context [ if ?b then _ else _ ] => destruct b as [Heq | Hne] end.
    + subst x. assert (dbind_typ A = dbind_typ T) by (eapply binds_unique; eauto).
      match goal with He : dbind_typ _ = dbind_typ _ |- _ => inversion He; subst end.
      apply d_typing__var; exact Hby.
    + apply d_typing__var; exact H.
  - (* anno *) apply d_typing__anno. eapply IHd_typing; eauto.
  - (* sub *) eapply d_typing__sub;
      [ apply is_base_subst_var; exact H | eapply IHd_typing; eauto | exact H1 ].
  - (* freeze *) apply d_typing__freeze. eapply IHd_typing; eauto.
  - (* forall *) apply d_typing__forall with
      (L := L `union` {{x0}} `union` {{y0}} `union` dom Γ);
      [ apply is_value_subst_var; exact H | ].
    intros X HX. eapply H1; [ fsetdec | apply uniq_push; [ exact Huniq | fsetdec ]
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

(** Tvar STRENGTHENING cascade: drop an UNUSED tvar [X] (one that does not occur
    free in the skeleton/type) from the context.  This is what the [forall] case
    of [d_pat_total] needs: the body is inferred over [(X:tvar)::Γ] for a fresh
    [X ∉ ftvar(e)], so the inferred skeleton is [X]-free and [X] strengthens away.
    Var cases: [X ∉ ftvar] forces the looked-up tvar [≠ X]; cofinite cases use
    [ftvar_in_*_open_*_upper]. *)
Lemma d_wf_ptyp_strengthen : forall Γ A,
    Γ ⊢ₚ A ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    X `notin` ftvar_in_ptyp A ->
    (Γ1 ++ Γ2) ⊢ₚ A.
Proof.
  intros Γ A H. induction H; intros Γ1 X0 Γ2 Heq HX; subst.
  - apply d_wf_ptyp__unit.
  - simpl in HX. apply d_wf_ptyp__var. analyze_binds H; try (exfalso; fsetdec); auto.
  - simpl in HX. apply d_wf_ptyp__arrow; [ eapply IHd_wf_ptyp1 | eapply IHd_wf_ptyp2 ]; eauto.
  - simpl in HX. apply d_wf_ptyp__all with (L := L `union` {{X0}} `union` dom (Γ1 ++ Γ2)).
    intros Y HY. rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Y ltac:(auto) ((Y ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A (ptyp_var_f Y)) as Hup.
    simpl in Hup. fsetdec.
Qed.

Lemma d_wf_pskl_strengthen : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    X `notin` ftvar_in_pskl P ->
    (Γ1 ++ Γ2) ⨟ Ψ ⊢ₚₛ P.
Proof.
  intros Ψ Γ P H. induction H; intros Γ1 X0 Γ2 Heq HX; subst.
  - apply d_wf_pskl__unit.
  - simpl in HX. apply d_wf_pskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
    analyze_binds Hb; try (exfalso; fsetdec); auto.
  - simpl in HX. apply d_wf_pskl__arrow; [ eapply IHd_wf_pskl1 | eapply IHd_wf_pskl2 ]; eauto.
  - simpl in HX. apply d_wf_pskl__all with (L := L `union` {{X0}}).
    intros Y HY. eapply (H0 Y ltac:(auto) Γ1 X0 Γ2); [ reflexivity | ].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f Y)) as Hup.
    simpl in Hup. fsetdec.
  - apply d_wf_pskl__hole.
  - simpl in HX. apply d_wf_pskl__tophole; [ assumption | eapply IHd_wf_pskl; eauto ].
Qed.

Lemma d_wf_uskl_strengthen : forall Ψ Γ R,
    Γ ⨟ Ψ ⊢ᵤₛ R ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    X `notin` ftvar_in_uskl R ->
    (Γ1 ++ Γ2) ⨟ Ψ ⊢ᵤₛ R.
Proof.
  intros Ψ Γ R H. induction H; intros Γ1 X0 Γ2 Heq HX; subst.
  - apply d_wf_uskl__unit.
  - simpl in HX. apply d_wf_uskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
    analyze_binds Hb; try (exfalso; fsetdec); auto.
  - simpl in HX. apply d_wf_uskl__arrow; [ eapply IHd_wf_uskl1 | eapply IHd_wf_uskl2 ]; eauto.
  - simpl in HX. apply d_wf_uskl__all_syn with (L := L `union` {{X0}}).
    intros Y HY. eapply (H0 Y ltac:(auto) Γ1 X0 Γ2); [ reflexivity | ].
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f Y)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in HX. apply d_wf_uskl__all_etag with (L := L `union` {{X0}}).
    intros Y HY. eapply (H0 Y ltac:(auto) Γ1 X0 Γ2); [ reflexivity | ].
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f Y)) as Hup.
    simpl in Hup. fsetdec.
  - apply d_wf_uskl__hole.
  - simpl in HX. apply d_wf_uskl__tophole; [ assumption | eapply IHd_wf_uskl; eauto ].
  - apply d_wf_uskl__holeg.
  - simpl in HX. apply d_wf_uskl__topholeg; [ assumption | eapply IHd_wf_uskl; eauto ].
Qed.

(** Both paintings preserve free tvars (they only repaint quantifiers). *)
Lemma ftvar_pskl_to_bskl_inh : forall P,
    ftvar_in_bskl (pskl_to_bskl_inh P) = ftvar_in_pskl P.
Proof.
  induction P; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
Qed.

Lemma ftvar_pskl_to_bskl_syn : forall P,
    ftvar_in_bskl (pskl_to_bskl_syn P) = ftvar_in_pskl P.
Proof.
  induction P; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
Qed.

(** [d_pat_consis] strengthening: every tvar LOOKUP goes through the RHS skeleton
    [Q] ([__var] matches [R'=Q'=var X']; [__hole]'s fill lives in [Q = inh P]), so
    conditioning on [X ∉ ftvar Q] suffices.  Forall cases grow [Γ]; recurse with
    [ftvar_in_bskl_open_bskl_wrt_bskl_upper]. *)
Lemma d_pat_consis_strengthen : forall Δ Γ R Q,
    Δ ⨟ Γ ⊨ₛ R ≈ Q ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    X `notin` ftvar_in_bskl Q ->
    Δ ⨟ (Γ1 ++ Γ2) ⊨ₛ R ≈ Q.
Proof.
  intros Δ Γ R Q H. induction H; intros Γ1 X0 Γ2 Heq HX; subst.
  - apply d_pat_consis__unit; (assumption || fsetdec).
  - simpl in HX. apply d_pat_consis__var; [ (assumption || fsetdec) | ]; match goal with Hb : binds _ _ _ |- _ => analyze_binds Hb end; try (exfalso; fsetdec); auto.
  - simpl in HX. eapply d_pat_consis__arrow;
      [ eapply IHd_pat_consis1 | eapply IHd_pat_consis2 | (eassumption || fsetdec) ]; eauto.
  - simpl in HX. apply d_pat_consis__forall_inh_tagged with (L := L `union` {{X0}}) (Ψ0 := Ψ0). 2: assumption.
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Z)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in HX. apply d_pat_consis__forall_inh_untagged with (L := L `union` {{X0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Z)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in HX. apply d_pat_consis__forall_syn_tagged with (L := L `union` {{X0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Z)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in HX. apply d_pat_consis__forall_syn with (L := L `union` {{X0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Z)) as Hup.
    simpl in Hup. fsetdec.
  - apply d_pat_consis__ghostg; (assumption || fsetdec).
  - simpl in HX. apply d_pat_consis__topholeg with (Ψ0 := Ψ0);
      [ eapply IHd_pat_consis; eauto | eassumption ].
  - apply d_pat_consis__hole; [ (assumption || fsetdec) | ]; eapply d_wf_pskl_strengthen; eauto.
    rewrite <- ftvar_pskl_to_bskl_inh. assumption.
  - simpl in HX. apply d_pat_consis__tophole. eapply IHd_pat_consis; eauto.
  - simpl in HX. apply d_pat_consis__tophole_inh with (L := L `union` {{X0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Z)) as Hup.
    simpl in Hup. fsetdec.
  - apply d_pat_consis__tophole_drop. eapply IHd_pat_consis; eauto.
Qed.

(** [d_refine_syn] strengthening: lookups go through the OUTPUT [P] ([__var] has
    [Q'=P'=var X']; [__hole]'s fill is on the output), so condition on
    [X ∉ ftvar P].  Forall/tophole-fill grow [Δs]/[Δi] not [Γ]. *)
Lemma d_refine_syn_strengthen : forall Γ Δi Q P,
    Γ ⨟ Δi ⊢ᵣ Q ⊳ P ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    X `notin` ftvar_in_bskl P ->
    (Γ1 ++ Γ2) ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ Δi Q P H. induction H; intros Γ1 X0 Γ2 Heq HX; subst.
  - apply d_refine_syn__unit.
  - simpl in HX. apply d_refine_syn__var. destruct H as [HI | Hb];
      [ left; assumption | right ].
    analyze_binds Hb; try (exfalso; fsetdec); auto.
  - simpl in HX. apply d_refine_syn__arrow;
      [ eapply IHd_refine_syn1 | eapply IHd_refine_syn2 ]; eauto.
  - simpl in HX. apply d_refine_syn__all with (L := L `union` {{X0}}).
    intros Z HZ. eapply (H0 Z ltac:(auto) Γ1 X0 Γ2); [ reflexivity | ].
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f Z)) as Hup.
    simpl in Hup. fsetdec.
  - apply d_refine_syn__hole. eapply d_wf_pskl_strengthen; eauto.
    rewrite <- ftvar_pskl_to_bskl_syn. assumption.
  - apply d_refine_syn__tophole_remove. eapply IHd_refine_syn; eauto.
  - apply d_refine_syn__tophole_fill with (L := L `union` {{X0}}).
    intros Z HZ. eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2);
      [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f Z)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in HX. apply d_refine_syn__tophole_keep; [ assumption | eapply IHd_refine_syn; eauto ].
Qed.

(** The LHS of a consistency / subtyping judgment has no free tvars beyond the
    RHS: every concrete tvar in [R] is matched (via [__var]) to the same tvar in
    [Q]; ghosts/holes in [R] are tvar-free.  Hence [X ∉ ftvar Q ⇒ X ∉ ftvar R],
    which is what makes [d_pat_sub]'s [forall_l] recursion strengthen. *)
Lemma d_pat_consis_ftvar : forall Δ Γ R Q,
    Δ ⨟ Γ ⊨ₛ R ≈ Q -> ftvar_in_uskl R [<=] ftvar_in_bskl Q.
Proof.
  intros Δ Γ R Q H. induction H; simpl; try fsetdec.
  - (* forall_inh_tagged *) pick fresh X for
      (L `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    specialize (H0 X ltac:(auto)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f X)).
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f X)).
    simpl in *. fsetdec.
  - (* forall_inh_untagged *) pick fresh X for
      (L `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    specialize (H0 X ltac:(auto)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f X)).
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f X)).
    simpl in *. fsetdec.
  - (* forall_syn_tagged *) pick fresh X for
      (L `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    specialize (H0 X ltac:(auto)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f X)).
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f X)).
    simpl in *. fsetdec.
  - (* forall_syn *) pick fresh X for
      (L `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    specialize (H0 X ltac:(auto)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f X)).
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f X)).
    simpl in *. fsetdec.
  - (* tophole_inh *) pick fresh X for
      (L `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    specialize (H0 X ltac:(auto)).
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f X)).
    simpl in *. fsetdec.
Qed.

Lemma d_pat_sub_ftvar : forall Δ Γ m R Q,
    Δ ⨟ Γ ⊢ₛ[ m ] R ⊑ Q -> ftvar_in_uskl R [<=] ftvar_in_bskl Q.
Proof.
  intros Δ Γ m R Q H. induction H; simpl.
  - (* infer *) apply d_pat_consis_ftvar in H0. assumption.
  - (* univ_ghost_r *) apply d_pat_consis_ftvar in H3. simpl. fsetdec.
  - (* arg *) apply d_pat_consis_ftvar in H. fsetdec.
  - (* forall_l_tagged *)
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R psi). fsetdec.
  - (* forall_l_untagged *)
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R psi). fsetdec.
  - (* ghost *) fsetdec.
  - (* univ_ghost_l *) fsetdec.
  - (* ghostg *) fsetdec.
  - (* univ_ghost_lg *) fsetdec.
Qed.

(** Tvar→[unit] SUBSTITUTION cascade: replace a fresh tvar [X] by [unit] and drop
    it.  [unit] is guarded / [is_tskl] / well-formed / a valid type, so this is
    CORNER-FREE — it sidesteps both the strengthen corner ([var X] is removable:
    [X↦unit]) and the subst-hole corner ([tophole(var X) ↦ tophole(unit)] stays
    guarded), and keeps tags ([unit] and [var] both carry [nil]).  Applied at the
    [forall] case of [d_pat_total] with an [X]-free derivation, the substitution
    is the identity, so it strengthens away the fresh ∀-var. *)
Lemma guarded_pskl_subst_unit : forall P X,
    guarded_pskl P -> guarded_pskl (subst_pskl_in_pskl pskl_unit X P).
Proof.
  intros P X H. induction H; simpl.
  - apply guarded_pskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      [ apply guarded_pskl__unit | apply guarded_pskl__var ].
  - apply guarded_pskl__arrow; apply subst_pskl_in_pskl_lc_pskl; (assumption || apply lc_pskl_unit).
Qed.

Lemma guarded_uskl_subst_unit : forall R X,
    guarded_uskl R -> guarded_uskl (subst_bskl_in_uskl uskl_unit X R).
Proof.
  intros R X H. induction H; simpl.
  - apply guarded_uskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      [ apply guarded_uskl__unit | apply guarded_uskl__var ].
  - apply guarded_uskl__arrow; apply subst_bskl_in_uskl_lc_uskl; (assumption || apply lc_uskl_unit).
Qed.

Lemma d_wf_pskl_subst_unit : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    (Γ1 ++ Γ2) ⨟ Ψ ⊢ₚₛ (subst_pskl_in_pskl pskl_unit X P).
Proof.
  intros Ψ Γ P H. induction H; intros Γ1 X0 Γ2 Heq; subst.
  - apply d_wf_pskl__unit.
  - simpl. match goal with |- context [ if ?b then _ else _ ] => destruct b end.
    + apply d_wf_pskl__unit.
    + apply d_wf_pskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
      analyze_binds Hb; auto.
  - simpl. apply d_wf_pskl__arrow; [ eapply IHd_wf_pskl1 | eapply IHd_wf_pskl2 ]; eauto.
  - simpl. apply d_wf_pskl__all with (L := L `union` {{X0}}).
    intros Y HY. rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      try (apply lc_pskl_unit); try fsetdec.
    eapply (H0 Y ltac:(auto) Γ1 X0 Γ2); reflexivity.
  - apply d_wf_pskl__hole.
  - simpl. apply d_wf_pskl__tophole;
      [ apply guarded_pskl_subst_unit; assumption | eapply IHd_wf_pskl; eauto ].
Qed.

Lemma d_wf_uskl_subst_unit : forall Ψ Γ R,
    Γ ⨟ Ψ ⊢ᵤₛ R ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    (Γ1 ++ Γ2) ⨟ Ψ ⊢ᵤₛ (subst_bskl_in_uskl uskl_unit X R).
Proof.
  intros Ψ Γ R H. induction H; intros Γ1 X0 Γ2 Heq; subst.
  - apply d_wf_uskl__unit.
  - simpl. match goal with |- context [ if ?b then _ else _ ] => destruct b end.
    + apply d_wf_uskl__unit.
    + apply d_wf_uskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right ].
      analyze_binds Hb; auto.
  - simpl. apply d_wf_uskl__arrow; [ eapply IHd_wf_uskl1 | eapply IHd_wf_uskl2 ]; eauto.
  - simpl. apply d_wf_uskl__all_syn with (L := L `union` {{X0}}).
    intros Y HY. rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      try (apply lc_uskl_unit); try fsetdec.
    eapply (H0 Y ltac:(auto) Γ1 X0 Γ2); reflexivity.
  - simpl. apply d_wf_uskl__all_etag with (L := L `union` {{X0}}).
    intros Y HY. rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      try (apply lc_uskl_unit); try fsetdec.
    eapply (H0 Y ltac:(auto) Γ1 X0 Γ2); reflexivity.
  - apply d_wf_uskl__hole.
  - simpl. apply d_wf_uskl__tophole;
      [ apply guarded_uskl_subst_unit; assumption | eapply IHd_wf_uskl; eauto ].
  - apply d_wf_uskl__holeg.
  - simpl. apply d_wf_uskl__topholeg;
      [ apply guarded_uskl_subst_unit; assumption | eapply IHd_wf_uskl; eauto ].
Qed.

(** [pskl_to_bskl_inh] commutes with the tvar→unit substitution. *)
Lemma pskl_to_bskl_inh_subst_unit : forall P X,
    subst_bskl_in_bskl bskl_unit X (pskl_to_bskl_inh P)
    = pskl_to_bskl_inh (subst_pskl_in_pskl pskl_unit X P).
Proof.
  induction P; intros X; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma is_sskl_subst_unit : forall Q X,
    is_sskl Q -> is_sskl (subst_bskl_in_bskl bskl_unit X Q).
Proof.
  intros Q X H. induction H; simpl.
  - apply is_sskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      [ apply is_sskl__unit | apply is_sskl__var ].
  - apply is_sskl__arrow; assumption.
  - apply is_sskl__all with (L := L `union` {{X}}). intros Y HY.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      try (apply lc_bskl_unit); try fsetdec. auto.
  - apply is_sskl__hole.
  - apply is_sskl__tophole; assumption.
Qed.

(** [mod_comp_sk] is preserved under [unit]-substitution: [unit] is [is_sskl]
    and substitution respects the arrow spine. *)
Lemma mod_comp_sk_subst_unit : forall S m X,
    mod_comp_sk S m -> mod_comp_sk (subst_bskl_in_bskl bskl_unit X S) m.
Proof.
  intros S m X H. induction H; simpl.
  - apply mod_comp_sk__ti; apply is_sskl_subst_unit; assumption.
  - apply mod_comp_sk__tc; apply is_sskl_subst_unit; assumption.
  - apply mod_comp_sk__fn; assumption.
Qed.

Lemma is_tskl_subst_unit : forall R X,
    is_tskl R -> is_tskl (subst_bskl_in_uskl uskl_unit X R).
Proof.
  intros R X H. induction H; simpl.
  - apply is_tskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      [ apply is_tskl__unit | apply is_tskl__var ].
  - apply is_tskl__arrow; assumption.
  - apply is_tskl__all_etag with (L := L `union` {{X}}). intros Y HY.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      try (apply lc_uskl_unit); try fsetdec. auto.
  - apply is_tskl__all_syn with (L := L `union` {{X}}). intros Y HY.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      try (apply lc_uskl_unit); try fsetdec. auto.
  - apply is_tskl__holeg.
  - apply is_tskl__topholeg; assumption.
Qed.

Lemma guarded_bskl_subst_unit : forall Q X,
    guarded_bskl Q -> guarded_bskl (subst_bskl_in_bskl bskl_unit X Q).
Proof.
  intros Q X H. induction H; simpl.
  - apply guarded_bskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      [ apply guarded_bskl__unit | apply guarded_bskl__var ].
  - apply guarded_bskl__arrow; apply subst_bskl_in_bskl_lc_bskl; (assumption || apply lc_bskl_unit).
Qed.

Lemma d_tags_skl_subst_unit : forall Δ R X,
    d_tags_skl Δ R -> d_tags_skl Δ (subst_bskl_in_uskl uskl_unit X R).
Proof.
  intros Δ R X H. induction H; simpl.
  - apply d_tags_skl__unit; (assumption || fsetdec).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      [ apply d_tags_skl__unit; (assumption || fsetdec)
      | apply d_tags_skl__var; (assumption || fsetdec) ].
  - apply d_tags_skl__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
  - apply d_tags_skl__all_etag with (L := L `union` {{X}}) (Ψ0 := Ψ0); [ | assumption | assumption ]. intros Y HY.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      try (apply lc_uskl_unit); try fsetdec. auto.
  - apply d_tags_skl__all_syn with (L := L `union` {{X}}). intros Y HY.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      try (apply lc_uskl_unit); try fsetdec. auto.
  - apply d_tags_skl__hole; (assumption || fsetdec).
  - apply d_tags_skl__tophole; assumption.
  - apply d_tags_skl__holeg; (assumption || fsetdec).
  - apply d_tags_skl__topholeg with (Ψ0 := Ψ0); assumption.
Qed.

Lemma d_pat_consis_subst_unit : forall Δ Γ R Q,
    Δ ⨟ Γ ⊨ₛ R ≈ Q ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    Δ ⨟ (Γ1 ++ Γ2) ⊨ₛ
      (subst_bskl_in_uskl uskl_unit X R) ≈ (subst_bskl_in_bskl bskl_unit X Q).
Proof.
  intros Δ Γ R Q H. induction H; intros Γ1 X0 Γ2 Heq; subst.
  - apply d_pat_consis__unit; (assumption || fsetdec).
  - simpl. match goal with |- context [ if ?b then _ else _ ] => destruct b end.
    + apply d_pat_consis__unit; (assumption || fsetdec).
    + apply d_pat_consis__var; [ (assumption || fsetdec) | ]; match goal with Hb : binds _ _ _ |- _ => analyze_binds Hb end; auto.
  - simpl. eapply d_pat_consis__arrow; [ eapply IHd_pat_consis1 | eapply IHd_pat_consis2 | (eassumption || fsetdec) ]; eauto.
  - simpl. apply d_pat_consis__forall_inh_tagged with (L := L `union` {{X0}}) (Ψ0 := Ψ0). 2: assumption.
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_unit); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_unit); try fsetdec.
    eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2); simpl_env; reflexivity.
  - simpl. apply d_pat_consis__forall_inh_untagged with (L := L `union` {{X0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_unit); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_unit); try fsetdec.
    eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2); simpl_env; reflexivity.
  - simpl. apply d_pat_consis__forall_syn_tagged with (L := L `union` {{X0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_unit); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_unit); try fsetdec.
    eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2); simpl_env; reflexivity.
  - simpl. apply d_pat_consis__forall_syn with (L := L `union` {{X0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var; try (apply lc_uskl_unit); try fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_unit); try fsetdec.
    eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2); simpl_env; reflexivity.
  - apply d_pat_consis__ghostg; (assumption || fsetdec).
  - simpl. apply d_pat_consis__topholeg with (Ψ0 := Ψ0);
      [ eapply IHd_pat_consis; eauto | eassumption ].
  - simpl. rewrite pskl_to_bskl_inh_subst_unit. apply d_pat_consis__hole; [ (assumption || fsetdec) | ]; eapply d_wf_pskl_subst_unit; eauto.
  - simpl. apply d_pat_consis__tophole. eapply IHd_pat_consis; eauto.
  - simpl. apply d_pat_consis__tophole_inh with (L := L `union` {{X0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var; try (apply lc_bskl_unit); try fsetdec.
    change (uskl_tophole (subst_bskl_in_uskl uskl_unit X0 R))
      with (subst_bskl_in_uskl uskl_unit X0 (uskl_tophole R)).
    eapply (H0 Z ltac:(auto) ((Z ~ dbind_tvar) ++ Γ1) X0 Γ2); simpl_env; reflexivity.
  - simpl. apply d_pat_consis__tophole_drop. eapply IHd_pat_consis; eauto.
Qed.

Lemma d_pat_sub_subst_unit : forall Δ Γ m R Q,
    Δ ⨟ Γ ⊢ₛ[ m ] R ⊑ Q ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    Δ ⨟ (Γ1 ++ Γ2) ⊢ₛ[ m ]
      (subst_bskl_in_uskl uskl_unit X R) ⊑ (subst_bskl_in_bskl bskl_unit X Q).
Proof.
  intros Δ Γ m R Q H. induction H; intros Γ1 X0 Γ2 Heq; subst.
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
      (psi := subst_bskl_in_uskl uskl_unit X0 psi);
      [ assumption | eassumption | apply d_tags_skl_subst_unit; assumption
      | eapply d_wf_uskl_subst_unit; eauto | apply is_tskl_subst_unit; assumption | ].
    rewrite <- subst_bskl_in_uskl_open_uskl_wrt_uskl; try (apply lc_uskl_unit).
    eapply IHd_pat_sub; eauto.
  - simpl. eapply d_pat_sub__forall_l_untagged with
      (psi := subst_bskl_in_uskl uskl_unit X0 psi);
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
Lemma d_pat_consis_refl : forall Q Γ,
    is_sskl Q ->
    (forall X, X `in` ftvar_in_bskl Q -> binds X dbind_tvar Γ) ->
    empty ⨟ Γ ⊨ₛ (bskl_to_uskl Q) ≈ Q.
Proof.
  intros Q Γ Hs. generalize dependent Γ. induction Hs; intros Γ Hwf; simpl.
  - apply d_pat_consis__unit; (assumption || fsetdec).
  - apply d_pat_consis__var; [ fsetdec | apply Hwf; simpl; fsetdec ].
  - apply d_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHs1 | apply IHHs2 | fsetdec ]; intros X HX; apply Hwf; simpl; fsetdec.
  - apply d_pat_consis__forall_syn with (L := L `union` dom Γ).
    intros X HX. rewrite <- bskl_to_uskl_open. apply H0; [ fsetdec | ].
    intros Y HY.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper A (bskl_var_f X)) as Hup.
    simpl in Hup. destruct (Y == X).
    + subst. auto.
    + assert (binds Y dbind_tvar Γ) by (apply Hwf; simpl; fsetdec). auto.
  - replace bskl_hole with (pskl_to_bskl_inh pskl_hole) by reflexivity.
    apply d_pat_consis__hole; [ (assumption || fsetdec) | ]; apply d_wf_pskl__hole.
  - apply d_pat_consis__tophole. apply IHHs. intros X HX; apply Hwf; simpl; assumption.
Qed.

(** Opening with [□] preserves size (both a bound var and [□] have size 1). *)
Lemma size_bskl_open_hole_rec : forall Q k,
    size_bskl (open_bskl_wrt_bskl_rec k bskl_hole Q) = size_bskl Q.
Proof.
  induction Q; intro k; simpl;
    try reflexivity;
    try (rewrite IHQ1, IHQ2; reflexivity);
    try (rewrite IHQ; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; simpl; reflexivity.
Qed.

Lemma size_bskl_open_hole : forall Q,
    size_bskl (open_bskl_wrt_bskl Q bskl_hole) = size_bskl Q.
Proof.
  intro Q. apply (size_bskl_open_hole_rec Q 0).
Qed.

(** A synthesised skeleton round-trips through its [pskl]-erasure. *)
Lemma is_sskl_syn_roundtrip : forall Q,
    is_sskl Q -> pskl_to_bskl_syn (bskl_to_pskl Q) = Q.
Proof.
  intros Q H. induction H; simpl;
    try reflexivity;
    try (rewrite IHis_sskl; reflexivity);
    try (rewrite IHis_sskl1, IHis_sskl2; reflexivity).
  - (* all_syn *) f_equal.
    pick fresh X for
      (L `union` ftvar_in_bskl A `union` ftvar_in_bskl (pskl_to_bskl_syn (bskl_to_pskl A))).
    apply open_bskl_wrt_bskl_inj with (Xbs1 := X); [ fsetdec | fsetdec | ].
    rewrite <- pskl_to_bskl_syn_open, <- bskl_to_pskl_open. apply H0. fsetdec.
Qed.

Lemma is_sskl_subst_hole : forall Q X,
    is_sskl Q -> is_sskl (subst_bskl_in_bskl bskl_hole X Q).
Proof.
  intros Q X H. induction H; simpl.
  - apply is_sskl__unit.
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end;
      [ apply is_sskl__hole | apply is_sskl__var ].
  - apply is_sskl__arrow; assumption.
  - apply is_sskl__all with (L := L `union` {{X}}). intros Y HY.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      try (apply lc_bskl_hole); try fsetdec. auto.
  - apply is_sskl__hole.
  - apply is_sskl__tophole; assumption.
Qed.

Lemma is_sskl_lc : forall Q, is_sskl Q -> lc_bskl Q.
Proof.
  intros Q H. induction H.
  - apply lc_bskl_unit.
  - apply lc_bskl_var_f.
  - apply lc_bskl_arrow; assumption.
  - pick fresh X for L. apply (lc_bskl_all_syn_exists X). apply H0; auto.
  - apply lc_bskl_hole.
  - apply lc_bskl_tophole; assumption.
Qed.

Lemma bskl_to_uskl_open_gen : forall A V,
    bskl_to_uskl (open_bskl_wrt_bskl A V) = open_uskl_wrt_uskl (bskl_to_uskl A) (bskl_to_uskl V).
Proof.
  intros. unfold open_bskl_wrt_bskl, open_uskl_wrt_uskl. apply bskl_to_uskl_open_rec.
Qed.

Lemma bskl_to_pskl_open_gen : forall A V,
    bskl_to_pskl (open_bskl_wrt_bskl A V) = open_pskl_wrt_pskl (bskl_to_pskl A) (bskl_to_pskl V).
Proof.
  intros. unfold open_bskl_wrt_bskl, open_pskl_wrt_pskl. apply bskl_to_pskl_open_rec.
Qed.

(** Safe [d_pat_sub] construction at [tc] (size induction): a well-scoped
    synthesised skeleton subtypes to a *safe* checking skeleton — guards wrap in a
    [TopHole] ([univ_ghost_r]); ∀s are stripped by [forall_l] instantiated with a
    GHOST [□] (so the result fills every instantiation), recursing on [open Q0 □]
    (size-decreasing). This is the ghost-instantiation construction; no unit-subst,
    no strengthening corner. *)
Lemma d_pat_sub_safe_tc : forall n Q1 Γ,
    size_bskl Q1 <= n ->
    is_sskl Q1 ->
    (forall X, X `in` ftvar_in_bskl Q1 -> binds X dbind_tvar Γ) ->
    exists Q2, empty ⨟ Γ ⊢ₛ[ mode_tc ] (bskl_to_uskl Q1) ⊑ Q2
               /\ ghost_of (bskl_to_pskl Q1) Q2.
Proof.
  (* Corollary of the (Qed) ghost-instantiation engine: [Q1]'s pskl-erasure has
     a ghostification [Q2] ([ghost_of_total]), and the [tc]-subtyping to it is
     [ghost_of_infer]; [Q1] round-trips through its pskl since it is [is_sskl]. *)
  intros n Q1 Γ Hsz Hsskl Hcov.
  pose proof (lc_bskl_to_pskl _ (is_sskl_lc Hsskl)) as Hlc.
  destruct (ghost_of_total (le_n (size_pskl (bskl_to_pskl Q1))) Hlc) as [Q2 HQ2].
  exists Q2. split; [ | exact HQ2 ].
  rewrite <- (is_sskl_syn_roundtrip Hsskl).
  apply ghost_of_infer; [ exact HQ2 | exact Hlc | fsetdec | ].
  intros X HX. apply Hcov.
  rewrite <- (is_sskl_syn_roundtrip Hsskl), ftvar_pskl_to_bskl_syn. exact HX.
Qed.

(** [d_wf_ptyp] from local closure + scoping (the [ptyp] analogue of
    [d_wf_pskl_of_ptyp]); and the painting inversion needed by the Anno case. *)
Lemma d_wf_ptyp_of_lc_ftvar : forall A Γ,
    lc_ptyp A ->
    (forall X, X `in` ftvar_in_ptyp A -> binds X dbind_tvar Γ) ->
    d_wf_ptyp Γ A.
Proof.
  intros A Γ Hlc. revert Γ. induction Hlc; intros Γ Hcov.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. apply Hcov. simpl. fsetdec.
  - apply d_wf_ptyp__arrow; [ apply IHHlc1 | apply IHHlc2 ];
      intros Y HY; apply Hcov; simpl; fsetdec.
  - inst_cofinites_for d_wf_ptyp__all. intros X HX. apply H0. intros Y HY.
    apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY. simpl in HY.
    apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + apply AtomSetImpl.singleton_1 in HY. subst. simpl_env. auto.
    + apply binds_app_iff. right. apply Hcov. assumption.
Qed.

Lemma d_wf_ptyp_of_btyp_inh : forall A Γ,
    d_wf_btyp Γ (ptyp_to_btyp_inh A) -> d_wf_ptyp Γ A.
Proof.
  intros A Γ H. apply d_wf_ptyp_of_lc_ftvar.
  - apply lc_ptyp_of_lc_btyp_inh. eapply d_wf_btyp_lc; eassumption.
  - intros X HX. eapply d_wf_btyp_ftvar; [ eassumption | ].
    rewrite ftvar_ptyp_to_btyp_inh. assumption.
Qed.

(** * Skeleton determinism for synthesis (prerequisites for [d_pat_total]).
    [d_consis] preserves the underlying [pskl]; a base term's [mode_ti] type is
    therefore skeleton-determined (sub-[ti] only re-types to a consistent
    variant, same skeleton). *)

Lemma utyp_to_pskl_open_fvar : forall C X,
    utyp_to_pskl (open_utyp_wrt_utyp C (utyp_var_f X)) =
    open_pskl_wrt_pskl (utyp_to_pskl C) (pskl_var_f X).
Proof.
  intros. unfold open_utyp_wrt_utyp, open_pskl_wrt_pskl.
  apply (utyp_to_pskl_open_rec C (utyp_var_f X) 0).
Qed.

Lemma btyp_to_ptyp_open_rec : forall B V k,
    btyp_to_ptyp (open_btyp_wrt_btyp_rec k V B) =
    open_ptyp_wrt_ptyp_rec k (btyp_to_ptyp V) (btyp_to_ptyp B).
Proof.
  intros B V. induction B; intros k; simpl; try reflexivity;
    try (rewrite IHB; reflexivity); try (rewrite IHB1, IHB2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma btyp_to_ptyp_open : forall B X,
    btyp_to_ptyp (open_btyp_wrt_btyp B (btyp_var_f X)) =
    open_ptyp_wrt_ptyp (btyp_to_ptyp B) (ptyp_var_f X).
Proof.
  intros. unfold open_btyp_wrt_btyp, open_ptyp_wrt_ptyp.
  apply (btyp_to_ptyp_open_rec B (btyp_var_f X) 0).
Qed.

Lemma d_consis_skel : forall Δ Γ C B,
    d_consis Δ Γ C B -> utyp_to_pskl C = ptyp_to_pskl (btyp_to_ptyp B).
Proof.
  intros Δ Γ C B H. induction H; simpl; try reflexivity;
    try (rewrite IHd_consis1, IHd_consis2; reflexivity).
  all: f_equal;
    pick fresh X for (L `union` ftvar_in_pskl (utyp_to_pskl C)
                        `union` ftvar_in_pskl (ptyp_to_pskl (btyp_to_ptyp B)));
    apply open_pskl_wrt_pskl_inj with (Xps1 := X); [ fsetdec | fsetdec | ];
    rewrite <- utyp_to_pskl_open_fvar, <- ptyp_to_pskl_open, <- btyp_to_ptyp_open;
    apply H0; fsetdec.
Qed.

(** A [mode_ti] derivation pins the skeleton by the term's head form. *)
Lemma d_typing_ti_primary : forall Γ e B,
    d_typing mode_ti Γ e B ->
    match e with
    | exp_unit => ptyp_to_pskl (btyp_to_ptyp B) = pskl_unit
    | exp_var_f x => exists A, binds x (dbind_typ A) Γ
                       /\ ptyp_to_pskl (btyp_to_ptyp B) = ptyp_to_pskl A
    | exp_anno _ A => ptyp_to_pskl (btyp_to_ptyp B) = ptyp_to_pskl A
    | _ => True
    end.
Proof.
  intros Γ e B H. remember mode_ti as m eqn:Hm.
  induction H; subst; try discriminate; try exact I.
  - (* unit *) reflexivity.
  - (* var *) exists A. split; [ assumption | ].
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn. reflexivity.
  - (* anno *) rewrite btyp_to_ptyp_ptyp_to_btyp_syn. reflexivity.
  - (* sub : e is a base term, the ti premise gives [match e ...] in terms of
       [A], and the ti-subsumption ([d_sub__infer], the only ti case) forces
       [ptyp_to_pskl (btyp_to_ptyp B) = ptyp_to_pskl A] via consistency. *)
    inversion H1; subst; try (exfalso; congruence).
    pose proof (d_consis_skel H2) as Hba.
    rewrite utyp_to_pskl_ptyp_to_utyp_syn in Hba.
    (* Hba : ptyp_to_pskl A = ptyp_to_pskl (btyp_to_ptyp B) *)
    specialize (IHd_typing eq_refl).
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in IHd_typing.
    destruct e; simpl in *; try exact I; rewrite <- Hba; exact IHd_typing.
Qed.

(** Base-term [mode_ti] typing is skeleton-deterministic. *)
Lemma d_typing_ti_skel_det : forall Γ e B1 B2,
    uniq Γ -> is_base_term e ->
    d_typing mode_ti Γ e B1 -> d_typing mode_ti Γ e B2 ->
    ptyp_to_pskl (btyp_to_ptyp B1) = ptyp_to_pskl (btyp_to_ptyp B2).
Proof.
  intros Γ e B1 B2 Huniq Hbase H1 H2.
  pose proof (d_typing_ti_primary H1) as P1.
  pose proof (d_typing_ti_primary H2) as P2.
  destruct Hbase; simpl in P1, P2.
  - (* unit *) rewrite P1, P2. reflexivity.
  - (* var *) destruct P1 as [A1 [Hb1 He1]]. destruct P2 as [A2 [Hb2 He2]].
    assert (Heq : dbind_typ A1 = dbind_typ A2) by (eapply binds_unique; eauto).
    inversion Heq; subst. rewrite He1, He2. reflexivity.
  - (* anno *) rewrite P1, P2. reflexivity.
Qed.

Lemma ftvar_ptyp_to_pskl : forall A,
    ftvar_in_pskl (ptyp_to_pskl A) = ftvar_in_ptyp A.
Proof.
  induction A; simpl; try reflexivity;
    try (rewrite IHA; reflexivity); try (rewrite IHA1, IHA2; reflexivity).
Qed.

Lemma lc_pskl_ptyp_to_pskl : forall A,
    lc_ptyp A -> lc_pskl (ptyp_to_pskl A).
Proof.
  intros A H. induction H; simpl.
  - apply lc_pskl_unit.
  - apply lc_pskl_var_f.
  - apply lc_pskl_arrow; assumption.
  - apply lc_pskl_all_syn. intro X.
    rewrite <- ptyp_to_pskl_open. auto.
Qed.

(** The annotation of a well-typed [exp_anno] is well-formed (peeling sub-ti). *)
Lemma d_typing_anno_wf : forall Γ e A B,
    d_typing mode_ti Γ (exp_anno e A) B -> d_wf_denv Γ -> d_wf_ptyp Γ A.
Proof.
  intros Γ e A B H. remember (exp_anno e A) as ea eqn:Heqea.
  remember mode_ti as m eqn:Heqm. revert e A Heqea.
  induction H; intros e0 A0 Heqea Hwf; try discriminate;
    try (inversion Heqea; subst).
  - apply d_wf_ptyp_of_btyp_inh. eapply d_typing_wf_btyp; eauto.
  - eapply IHd_typing; eauto.
Qed.

(** A base term's [mode_ti] inference: a well-scoped synthesised skeleton whose
    [pskl] matches the type (the safe ingredient for the [tc]/[fn] sub cases). *)
Lemma d_pat_ti_base_safe : forall Γ e B,
    d_wf_denv Γ -> is_base_term e -> d_typing mode_ti Γ e B ->
    exists Q, d_pat mode_ti Γ e Q /\ is_sskl Q
      /\ (forall X, X `in` ftvar_in_bskl Q -> binds X dbind_tvar Γ)
      /\ bskl_to_pskl Q = ptyp_to_pskl (btyp_to_ptyp B).
Proof.
  (* The [mode_ti] type is skeleton-pinned by the head ([d_typing_ti_primary]),
     so the synthesised pattern skeleton is read off the binding / annotation
     directly — uniformly across the [sub] re-typing (same pskl). *)
  intros Γ e B Hwf Hbase Hty.
  pose proof (d_typing_ti_primary Hty) as Hpri.
  destruct Hbase; simpl in Hpri.
  - (* unit *) exists bskl_unit.
    repeat split;
      [ apply d_pat__unit | apply is_sskl__unit
      | intros X HX; simpl in HX; fsetdec
      | simpl; rewrite Hpri; reflexivity ].
  - (* var x *) destruct Hpri as [A [Hbnd Hsk]].
    assert (HwfA : d_wf_ptyp Γ A) by (eapply d_wf_denv_binds_typ; eauto).
    exists (pskl_to_bskl_syn (ptyp_to_pskl A)).
    repeat split.
    + apply d_pat__var with (d := dbind_typ A); [ exact Hbnd | reflexivity ].
    + apply is_sskl_pskl_to_bskl_syn, lc_pskl_ptyp_to_pskl. eapply d_wf_ptyp_lc_loc; eauto.
    + intros X HX. rewrite ftvar_pskl_to_bskl_syn, ftvar_ptyp_to_pskl in HX.
      eapply d_wf_ptyp_ftvar; eauto.
    + rewrite bskl_to_pskl_pskl_to_bskl_syn. symmetry; exact Hsk.
  - (* anno e A *) pose proof (d_typing_anno_wf Hty Hwf) as HwfA.
    exists (pskl_to_bskl_syn (ptyp_to_pskl A)).
    repeat split.
    + apply d_pat__anno. exact HwfA.
    + apply is_sskl_pskl_to_bskl_syn, lc_pskl_ptyp_to_pskl. eapply d_wf_ptyp_lc_loc; eauto.
    + intros X HX. rewrite ftvar_pskl_to_bskl_syn, ftvar_ptyp_to_pskl in HX.
      eapply d_wf_ptyp_ftvar; eauto.
    + rewrite bskl_to_pskl_pskl_to_bskl_syn. symmetry; exact Hpri.
Qed.

Lemma d_pat_sub_forall_hole_witness : forall Γ,
  empty ⨟ Γ ⊢ₛ[ mode_tc ]
    (bskl_to_uskl (pskl_to_bskl_syn (ptyp_to_pskl (ptyp_all (ptyp_var_b 0)))))
      ⊑ bskl_hole.
Proof.
  intros Γ. simpl.
  (* Paper-faithful: instantiate the ∀ with the tagged ghost [HoleG]; the
     bound variable becomes [uskl_holeg], matched against [bskl_hole] by
     [GhostG]. *)
  eapply d_pat_sub__forall_l_untagged with (Ψ' := empty) (psi := uskl_holeg).
  - discriminate.
  - fsetdec.
  - apply d_tags_skl__holeg; fsetdec.
  - apply d_wf_uskl__holeg.
  - apply is_tskl__holeg.
  - simpl. apply d_pat_sub__ghostg; [ fsetdec | apply mod_comp_sk__tc; apply is_sskl__hole ].
Qed.
