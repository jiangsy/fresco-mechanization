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
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.decl.prop_general_subsumption.

Set Implicit Arguments.

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
  | _ => exists Q, Γ ⊢[ m ] e ⇨ Q /\ safe_skel Γ m Q B
  end.

Lemma d_pat_total : forall m Γ e B,
    Γ ⊢[ m ] e ⦂ B -> d_wf_denv Γ -> gpat m Γ e B.
Proof.
  intros m Γ e B Hty. induction Hty; intros Hwf.
  - (* unit *) exists bskl_unit. split.
    + apply d_pat__unit.
    + simpl. reflexivity.
  - (* var *) eexists. split.
    + apply d_pat__var with (d := dbind_typ A); [ assumption | reflexivity ].
    + simpl. rewrite btyp_to_ptyp_ptyp_to_btyp_syn, bskl_to_pskl_pskl_to_bskl_syn.
      reflexivity.
  - (* anno *) eexists. split.
    + apply d_pat__anno. apply d_wf_ptyp_of_btyp_inh.
      eapply d_typing_wf_btyp; eassumption.
    + simpl. rewrite btyp_to_ptyp_ptyp_to_btyp_syn, bskl_to_pskl_pskl_to_bskl_syn.
      reflexivity.
  - (* sub *) destruct m.
    + (* ti *) destruct (IHHty Hwf) as [Q1 [HQ1 HS1]].
      exists Q1. split; [ exact HQ1 | ].
      simpl in HS1 |- *. rewrite HS1.
      match goal with Hsub : empty ⨟ _ ⊢[ mode_ti ] _ ⊑ _ |- _ =>
        inversion Hsub; subst;
        try (exfalso; match goal with Hne : ?mm <> ?mm |- _ =>
                        apply Hne; reflexivity end) end.
      match goal with Hc : empty ⨟ _ ⊨ _ ≈ _ |- _ =>
        apply d_consis_skel in Hc; rewrite utyp_to_pskl_ptyp_to_utyp_syn in Hc;
        exact Hc end.
    + (* tc *) admit.
    + (* fn *) admit.
  - (* freeze *) admit.
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
