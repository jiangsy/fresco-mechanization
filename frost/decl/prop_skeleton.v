(** Frost — declarative skeleton metatheory for the split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
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

(** Refinement preserves well-formedness (paper "Refinement preserves
    well-formedness", declarative.tex).  The two skeleton-scope contexts
    of refinement — [Δs] (syn-quantifier vars) and [Δi] (inh-quantifier
    vars) — collapse, on the colour-erased [pskl] output, into the single
    [d_wf_pskl] scope set [Ψ := Δs ++ Δi] (colours do not affect skeleton
    well-formedness, so both kinds of ∀-bound var live in the one [Ψ]).
    The three-context refinement (which clears [Δs] under a kept [TopHole]
    and [Δi] at [Hole]-fills) is exactly what guarantees the colour-erased
    output is [d_wf_pskl]; with the old "syn var dumped into [Γ]"
    encoding this lemma was false (e.g. [⫯.(□→unit)] refined to
    [∀^syn α.⫯.(α→unit)], which is not well-formed).

    Each [TopHole] / [Hole] rule clears some context, so its premise's
    IH yields wf at a [Ψ] that is a *subset* of the one the conclusion
    needs; we close the gap with [d_wf_pskl_Psi_mono] (monotone in [Ψ]). *)
Lemma d_refine_preserves_wf : forall Γ Δs Δi Q P,
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P ->
    (Δs ++ Δi) ⨟ Γ ⊢ₚₛ (bskl_to_pskl P).
Proof.
  intros Γ Δs Δi Q P H. induction H; simpl.
  - (* unit *) constructor.
  - (* var *) constructor.
    destruct H as [HS | [HI | HG]].
    + left. apply in_or_app; auto.
    + left. apply in_or_app; auto.
    + right; auto.
  - (* arrow *) constructor; auto.
  - (* all (inh): bound var joins Δi; wf Ψ gains it under the binder.
       [d_wf_pskl_Psi_mono] leaves the wf premise first, the [Ψ ⊆ Ψ'] last. *)
    inst_cofinites_for d_wf_pskl__all. intros X HX.
    rewrite <- bskl_to_pskl_open.
    apply d_wf_pskl_Psi_mono with (Ψ := Δs ++ (X :: Δi)); [ apply H0; auto | ].
    intros Y HY. simpl. rewrite in_app_iff in *. simpl in HY |- *. tauto.
  - (* hole: fill is wf with Ψ := Δs; weaken to Δs ++ Δi *)
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    apply d_wf_pskl_Psi_mono with (Ψ := Δs); [ assumption | ].
    intros Y HY. rewrite in_app_iff. tauto.
  - (* tophole_remove: keeps Δs, clears Δi; IH gives Ψ := Δs ++ nil *)
    apply d_wf_pskl_Psi_mono with (Ψ := Δs ++ nil); [ assumption | ].
    intros Y HY. rewrite in_app_iff in *. simpl in HY. tauto.
  - (* tophole_fill: output ∀^syn; body wf with Ψ := (X :: Δs) ++ nil *)
    inst_cofinites_for d_wf_pskl__all. intros X HX.
    rewrite <- bskl_to_pskl_open.
    apply d_wf_pskl_Psi_mono with (Ψ := (X :: Δs) ++ nil); [ apply H0; auto | ].
    intros Y HY. simpl. rewrite in_app_iff in *. simpl in HY |- *. tauto.
  - (* tophole_keep: output ⫯; clears both; guarded + wf-under-nil *)
    apply d_wf_pskl__tophole.
    + apply guarded_bskl_to_pskl; auto.
    + apply d_wf_pskl_Psi_mono with (Ψ := nil ++ nil); [ assumption | ].
      intros Y HY. inversion HY.
Qed.

(** Refinement reflexivity for the inh-painted skeleton of a type.  A
    type's skeleton [ptyp_to_pskl A] has no ghosts, so refinement on it is
    purely structural: it refines to itself, with each ∀ matched by the
    [bskl_all_inh] rule.  Stated with a scope-coverage premise (rather than
    [d_wf_ptyp]) so the [all] case can route the bound var into [Δi] — the
    inherited-quantifier context — which is exactly where the refinement
    [all] rule puts it.  This is the engine for [d_pat_validity]'s base
    cases (inferred skeleton already equal to the type's skeleton). *)
Lemma d_refine_syn_refl_inh : forall A,
    lc_ptyp A ->
    forall Γ Δs Δi,
      (forall X, X `in` ftvar_in_ptyp A ->
         List.In X Δs \/ List.In X Δi \/ binds X dbind_tvar Γ) ->
      Γ ⨟ Δs ⨟ Δi ⊢ᵣ
        (pskl_to_bskl_inh (ptyp_to_pskl A)) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)).
Proof.
  intros A Hlc. induction Hlc; intros Γ Δs Δi Hcov; simpl.
  - (* unit *) apply d_refine_syn__unit.
  - (* var_f X *) apply d_refine_syn__var. apply Hcov. simpl. fsetdec.
  - (* arrow *) apply d_refine_syn__arrow;
      [ apply IHHlc1 | apply IHHlc2 ]; intros Y HY; apply Hcov; simpl; fsetdec.
  - (* all: bound var → Δi, matching the [bskl_all_inh] refine rule *)
    inst_cofinites_for d_refine_syn__all. intros X HX.
    rewrite <- pskl_to_bskl_inh_open. rewrite <- ptyp_to_pskl_open.
    apply H0. intros Y HY.
    apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY. simpl in HY.
    apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + (* Y = X *) right. left. apply AtomSetImpl.singleton_1 in HY. simpl. left. assumption.
    + (* Y ∈ ftvar A *) specialize (Hcov Y HY).
      destruct Hcov as [HS | [HI | HG]];
        [ left; assumption | right; left; simpl; right; assumption | right; right; assumption ].
Qed.

(** A *typing context*: only type/tvar bindings, no ghost-bearing
    skeleton bindings.  (The user's "context has only A, not P" predicate.)
    Every context a [d_typing] derivation actually uses is of this shape. *)
Inductive typ_denv : list (atom * dbind) -> Prop :=
| typ_denv__nil  : typ_denv nil
| typ_denv__tvar : forall Γ X, typ_denv Γ -> typ_denv ((X ~ dbind_tvar) ++ Γ)
| typ_denv__typ  : forall Γ x A, typ_denv Γ -> typ_denv ((x ~ dbind_typ A) ++ Γ).

(** Context coherence between a skeleton-inference context [Γs] and a
    typing context [Γt]: same shape, with each *unannotated*-λ skeleton
    binding [x:P] in [Γs] matched by a type binding [x:A] in [Γt] such that
    the inference skeleton refines the type ([inh{P} ⊳ inh{ptyp A}]).  For
    coerced (ghost-free) bindings this refinement is [refl]; for the λ
    ghost [□] it is "hole refines anything".  This is the invariant that
    lets validity's induction cross a λ where the two judgments bind a
    variable differently ([dbind_skl] vs [dbind_typ]). *)
Inductive denv_coh : list (atom * dbind) -> list (atom * dbind) -> Prop :=
| denv_coh__nil  : denv_coh nil nil
| denv_coh__tvar : forall Γs Γt X,
    denv_coh Γs Γt ->
    denv_coh ((X ~ dbind_tvar) ++ Γs) ((X ~ dbind_tvar) ++ Γt)
| denv_coh__typ  : forall Γs Γt x A,
    denv_coh Γs Γt ->
    denv_coh ((x ~ dbind_typ A) ++ Γs) ((x ~ dbind_typ A) ++ Γt)
| denv_coh__skl  : forall Γs Γt x P A,
    denv_coh Γs Γt ->
    Γt ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)) ->
    denv_coh ((x ~ dbind_skl P) ++ Γs) ((x ~ dbind_typ A) ++ Γt).

(** Coherence is reflexive on pure typing contexts: there the only
    bindings are [tvar]/[typ], matched by themselves. *)
Lemma denv_coh_refl : forall Γ, typ_denv Γ -> denv_coh Γ Γ.
Proof.
  intros Γ H. induction H.
  - apply denv_coh__nil.
  - apply denv_coh__tvar; assumption.
  - apply denv_coh__typ; assumption.
Qed.

(** * Paper-facing skeleton properties.

    The statements below are native to the new syntax. They remain
    research-level obligations while the main D1/D12 path is being
    re-established. *)

Lemma d_pat_preserves_skel_wf : forall Γ e Q,
    Γ ⊢[ mode_tc ] e ⇨ Q ->
    d_wf_denv Γ ->
    nil ⨟ Γ ⊢ₚₛ Q.
Proof.
  intros Γ e Q H _.
  apply (proj2 d_typing_pat_preserves_wf) with (m := mode_tc) (e := e); auto.
Qed.

(** Paper "Validity of skeleton inference" (declarative.tex:1945): a
    well-typed [M] whose skeleton inference is [Γ ⊢tc M ⇨ Q] yields a
    *valid* [Q] — some [A] with [Γ ⊢tc M ⦂ inh{A}] and [Q] fills [inh{A}].

    STATUS: this is FALSE for the current rules (paper AND mech), in BOTH
    modes, because the synthesis-mode λ rule [d_pat__abs] / paper [Abs]
    binds an *arbitrary* argument skeleton.  Two counterexamples:

    - [mode_ti] (direct): [λx.(x:unit) ⇨ti (unit→unit)→unit] (choose arg
      skeleton [unit→unit]; [Anno] does not check the body).  The skeleton
      is ghost-free, so it fills *only* to [(unit→unit)→unit], where the
      term is untypeable — yet it is well-typed (at [unit→unit]).

    - [mode_tc] (via [freeze]): [d_pat__freeze] lifts a *ti*-inference to
      *tc* verbatim, re-exposing the liberal [d_pat__abs].  So
      [freeze (λx.(x:unit)) ⇨tc (unit→unit)→unit], well-typed at
      [unit→unit], same ghost-free dead-end.  (The paper [Freeze] rule,
      declarative.tex:1543, has the identical shape.)

    So [mode_tc] is *necessary* (under [mode_ti] even the non-[freeze] case
    fails) but NOT *sufficient*.  The root cause is that the inferred
    argument skeleton can be over-specific and ghost-free.  Validity holds
    only once [d_pat__abs] is disciplined the way [d_pat__abs_check]
    already is — bind a ghost [□] (or otherwise forbid concrete content in
    the inferred argument skeleton).  That is a rule change to the calculus
    (paper-side), DEFERRED pending discussion.

    Once disciplined, the proof is: induction on the check-mode inference
    under the [denv_coh] context-coherence invariant above (each
    inference-bound skeleton refines the corresponding typing type — [refl]
    for coerced bindings via [d_refine_syn_refl_inh], ghost-refines-anything
    for the λ ghost). *)
Theorem d_pat_validity : forall Γ e Q B,
    Γ ⊢[ mode_tc ] e ⇨ Q ->
    Γ ⊢[ mode_tc ] e ⦂ B ->
    d_wf_denv Γ ->
    exists A, Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) /\
              Γ ⨟ nil ⨟ nil ⊢ᵣ Q ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)).
Proof.
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

    Note: the liberal-[d_pat__abs] gap that falsifies [d_pat_validity]
    (above) does NOT affect safety — being existential, safety just *picks*
    the well-behaved derivation (e.g. the unannotated-λ argument skeleton
    [□] rather than an over-specific one), so the over-specific inferences
    that break validity are simply not chosen.

    Proof deferred: it needs the safe-skeleton *construction* (choose
    ghost-keeping refinements / ghost instantiations), essentially the
    declarative shadow of the algorithm.  See also the coloured-vs-
    uncoloured refinement caveat on [d_pat_validity] above. *)
Theorem d_pat_safety : forall Γ e B,
    Γ ⊢[ mode_tc ] e ⦂ B ->
    d_wf_denv Γ ->
    exists Q, Γ ⊢[ mode_tc ] e ⇨ Q /\
              (forall A, Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) ->
                 Γ ⨟ nil ⨟ nil ⊢ᵣ Q ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A))).
Proof.
Admitted.
