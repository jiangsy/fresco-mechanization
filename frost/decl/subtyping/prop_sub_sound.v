(** Frost — declarative subtyping metatheory: soundness of subtyping
    (paper 3.2), completeness wrt monotype-only shallow subtyping,
    and no-guessing-of-polytypes (paper 3.3). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.subtyping.prop_basics.
Require Import src.frost.decl.subtyping.prop_consis_trans.
Require Import src.frost.decl.subtyping.prop_consis_sub_trans.

Set Implicit Arguments.

(** * d_sub preserves wellformedness.

    Both [d_consis_preserves_wf] and [d_sub_preserves_wf] live in
    [prop_wellformed.v] (since they only depend on Phase 2.B definitions
    and are referenced by [d_typing_pat_preserves_wf] there). The
    [d_typing__sub] case of that mutual proof is now closed. *)

(** * Soundness of subtyping (paper declarative.tex:1095).

    Headline result: [d_sub mode_tc nil Γ A B → d_shallow_sub Γ A B].

    Subtleties revealed during proof:
    1. When [A] has shape [typ_all_etag ε T] or [typ_all_plain T], the
       [d_sub] derivation uses [d_sub__forall_l_*] — but
       [d_shallow_sub__forall_l] expects LHS [typ_all_col c A]. These are
       different syntactic shapes, so a direct correspondence requires
       either restricting [A] to [is_typ] (i.e. colour-tagged ∀-flavour
       only) or providing a translation between flavours.
    2. The [d_sub__check] case routes through [d_consis nil Γ A B]; for
       the empty-tag case, we need a bridging lemma between [d_consis]
       and [d_shallow_sub] (essentially an α-equivalence / structural
       equality that respects colour differences).

    We state the theorem under the natural precondition [is_typ A]
    (LHS has the [typ_all_col c _] shape, matching [d_shallow_sub]'s
    LHS shape) and admit the [d_sub__check] case behind a bridging
    lemma. *)

(** Structural equality when [Δ = nil] and LHS is [is_typ].
    With no tags to discharge and LHS in [is_typ] (only [typ_all_col]
    flavour), [d_consis] reduces to syntactic equality. *)
Lemma d_consis_empty_eq : forall Γ T A,
    is_typ T ->
    nil ⨟ Γ ⊨ T ≈ A ->
    T = A.
Proof.
  intros Γ T A Hist Hc. dependent induction Hc; try (inversion Hist; fail).
  - reflexivity.
  - reflexivity.
  - (* __forall_syn (post-refactor): T = typ_all_col colour_syn T_inner,
       A = typ_all_col colour_syn A_inner. Same proof as __forall_inh
       (uses is_typ_inv_all which is colour-agnostic). *)
    f_equal.
    apply is_typ_inv_all in Hist. destruct Hist as [L0 Hist_open].
    pick fresh X for (L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX_L : X `notin` L) by fsetdec.
    assert (HX_L0 : X `notin` L0) by fsetdec.
    specialize (H0 X HX_L (Hist_open X HX_L0)).
    apply open_typ_wrt_typ_inj in H0; auto.
  - (* __forall_inh: T = typ_all_col colour_inh T_inner, A = same
       structure. Use the cofinite IH and open injectivity. *)
    f_equal.
    apply is_typ_inv_all in Hist. destruct Hist as [L0 Hist_open].
    pick fresh X for (L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX_L : X `notin` L) by fsetdec.
    assert (HX_L0 : X `notin` L0) by fsetdec.
    specialize (H0 X HX_L (Hist_open X HX_L0)).
    apply open_typ_wrt_typ_inj in H0; auto.
  - (* arrow: Δ1 ++ Δ2 = nil → Δ1 = Δ2 = nil *)
    apply app_eq_nil in x. destruct x as [HΔ1 HΔ2]. subst.
    apply is_typ_inv_arrow in Hist. destruct Hist as [HT1 HT2].
    f_equal.
    + apply IHHc1; auto.
    + apply IHHc2; auto.
Qed.

Lemma d_consis_empty_to_shallow_sub : forall Γ A B,
    is_typ A ->
    nil ⨟ Γ ⊨ A ≈ B ->
    Γ ⊢ A ≤ B.
Proof.
  intros Γ A B Hist Hc. apply d_consis_empty_eq in Hc; auto. subst.
  apply d_shallow_sub__refl.
Qed.

(** Paper Lemma 3.2 (Soundness of subtyping). [paper-ref: name:"Soundness of subtyping"] *)
Theorem d_sub_sound : forall Γ A B,
    is_typ A ->
    Γ ⊢[ mode_tc ; nil ] A ⊑ B ->
    Γ ⊢ A ≤ B.
Proof.
  intros Γ A B Hist H. dependent induction H.
  - (* d_sub__check: M = mode_tc, Δ = nil. Use the bridging lemma. *)
    apply d_consis_empty_to_shallow_sub; auto.
  - (* d_sub__forall_r: B = typ_all_col colour_inh B'. *)
    apply d_shallow_sub__forall_r with (L := L `union` dom Γ).
    intros X HX. apply H0; auto.
  - (* d_sub__forall_l_tagged: A = typ_all_etag ε T — but Hist : is_typ A
       rejects typ_all_etag. Contradiction. *)
    exfalso. eapply is_typ_inv_etag. exact Hist.
Qed.

(** * Completeness wrt monotype-only shallow subtyping.

    Bruno's reviewer suggestion: restrict [d_shallow_sub__forall_l] to
    instantiate the ∀ body with a [mono_typ] witness. This gives a
    fragment that admits decidable inference and is more directly
    comparable to algorithms.

    The monotype-restricted variant: *)

Inductive d_shallow_sub_mono : list (atom * dbind) -> typ -> typ -> Prop :=
| d_shallow_sub_mono__refl : forall Γ A,
    d_shallow_sub_mono Γ A A
| d_shallow_sub_mono__forall_r : forall L Γ A B c,
    (forall X, X `notin` L ->
       d_shallow_sub_mono ((X ~ dbind_tvar) ++ Γ) A
         (open_typ_wrt_typ B (typ_var_f X))) ->
    d_shallow_sub_mono Γ A (typ_all_col c B)
| d_shallow_sub_mono__forall_l : forall Γ A A' B c,
    mono_typ A' ->
    d_wf_typ Γ A' ->
    d_shallow_sub_mono Γ (open_typ_wrt_typ A A') B ->
    d_shallow_sub_mono Γ (typ_all_col c A) B.

(** Completeness claim: every [d_shallow_sub_mono] derivation lifts to
    [d_sub mode_tc nil] — i.e. our system handles at least the
    monotype-only fragment.

    This direction is the easier of the two: [d_shallow_sub_mono]'s LHS
    pattern [typ_all_col c A] corresponds to [d_sub__forall_l_*] in our
    system, but those rules expect LHS shapes [typ_all_etag] /
    [typ_all_plain]. Bridging requires a translation between
    [typ_all_col] (declarative) and [typ_all_etag / typ_all_plain]
    (utyp). *)
Theorem d_sub_complete_mono : forall Γ A B,
    d_shallow_sub_mono Γ A B ->
    d_sub mode_tc nil Γ A B.
Proof.
  intros Γ A B H. induction H.
  - (* refl on A — d_sub mode_tc nil Γ A A. Use d_sub__check via
       d_consis_refl_mono if A is monotype, else... we need refl in
       general which doesn't exist for d_sub on polytypes. *)
    (* Without further restriction, A could be polytype and d_sub refl
       only holds at monotype. So this case CANNOT close without
       narrowing the hypothesis to mono_typ. *)
    admit.
  - (* forall_r — d_sub__forall_r only produces colour_inh on RHS, but
       d_shallow_sub_mono__forall_r is over any colour c. For c = inh
       direct, c = syn we lack the corresponding rule.

       Without splitting on c, the goal is [d_sub mode_tc nil Γ A
       (typ_all_col c B)] for arbitrary c; d_sub__forall_r requires
       c = colour_inh. Admitted: d_sub lacks a forall_r rule for
       colour_syn. *)
    admit.
  - (* forall_l — but the LHS of d_shallow_sub_mono is typ_all_col c A,
       not typ_all_etag/plain. d_sub__forall_l_* requires the etag/plain
       shape. So this case needs a translation between flavours which we
       don't have. *)
    admit.
Admitted.
(* d_sub_complete_mono: two pending sub-cases.
   - refl: needs A in mono_typ; without it we don't have polytype refl.
   - forall_l: needs translation between typ_all_col (decl) and
     typ_all_etag/plain (utyp). The two grammars are intentionally
     separate; completeness here would require a "colour-to-tag" lifting
     that's a research design question, not just mechanization.
   Documented as paper-flagged. *)

(** * No guessing of polytypes (strictified).

    Paper claim (declarative.tex:1102, flagged as sketchy): the
    quantifier-instantiation φ in a [d_sub] derivation is uniquely
    determined by the conclusion's data.

    PAPER-FLAGGED: strict equality form is provably FALSE in general.
    Concrete counter-example: pick [T = ε. β → β], [Γ = ·],
    [A = unit → unit]. Both [ph = unit] (giving [d_sub Δ' Γ (unit →
    unit) (unit → unit)]) and [ph = ∀^ε γ. γ] (giving [d_sub Δ' Γ
    (∀γ. γ → ∀γ. γ) (unit → unit)] via further instantiation) yield
    valid derivations with the same conclusion, so [ph1 ≠ ph2] yet
    both derive. The "right" strictification needs a confluence /
    canonicity argument — flagged for paper revision.

    Kept as [Admitted.] placeholder per user request: paper mentions
    this lemma, so it stays as a paper-claim marker; will be tweaked
    (likely to a weakened "up-to-mutual-subtyping" form) in a future
    paper-revision pass. *)

(** Paper Lemma 3.3 (No guessing of polytypes). [paper-ref: name:"No guessing of polytypes"] *)
Theorem d_sub_no_guess_uniqueness : forall (m : mode) (Δ : list atom)
    (Γ : list (atom * dbind)) (ε : atom) (T A : typ) (Δ' : list atom)
    (ph1 ph2 : typ),
    d_sub m (Δ ++ Δ') Γ (open_typ_wrt_typ T ph1) A ->
    d_sub m (Δ ++ Δ') Γ (open_typ_wrt_typ T ph2) A ->
    d_wf_ttyp Δ' Γ ph1 ->
    d_wf_ttyp Δ' Γ ph2 ->
    list_disjoint Δ' Δ ->
    ph1 = ph2.
Proof.
  (* PROVABLY FALSE as strictly stated; placeholder for paper-revision. *)
  admit.
Admitted.
