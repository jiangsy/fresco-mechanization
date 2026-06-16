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

(** Paper "Validity of skeleton inference" (declarative.tex): a well-typed
    [M] with inferred skeleton [Γ ⊢ti M ⇨ Q] yields a *valid* skeleton — some
    type [A] with [Γ ⊢tc M : inh A] and [Γ ⊢ inh{Q} ⊳ inh{A}] (the [fill]
    judgment is the coloured refinement [d_refine_syn]).

    PROOF ROADMAP (not a single induction on [d_pat]).  Three obligations:

    1. PAINTING.  As written the refinement is [Q ⊳ inh{A}] with the raw
       (possibly syn-painted) inferred [Q] on the left.  [d_refine_syn] has
       NO rule with [bskl_all_syn] on the left, so this is stuck whenever
       [Q] carries a concrete synthesised quantifier (e.g. an annotation
       [(e : ∀α.A)]).  The faithful, provable statement paints the LHS
       inherited too — matching the *only* consumer of refinement,
       [d_typing__app], which uses [pskl_to_bskl_inh _ ⊳ pskl_to_bskl_inh _].
       I.e. replace the LHS by [pskl_to_bskl_inh (bskl_to_pskl Q)] (this is
       the paper's *uncoloured* [fill], encoded by painting both sides the
       same colour; cf. the WT note at [def_extra.v]).

    2. MUTUAL COMPANION.  [d_pat] and [d_typing] are mutually defined, and
       variables carry DIFFERENT binders in the two: [d_pat__var] reads
       [dbind_skl P], [d_typing__var] reads [dbind_typ A].  So validity must
       be proved by mutual induction with a [d_typing]-side statement, under
       a context-coherence relation linking the [dbind_skl]/[dbind_typ]
       views (a well-typed-skeleton-context invariant).

    3. PER-CASE ENGINE.  With the painting fix, the structural cases close
       with [d_refine_syn_refl_inh] (proved above) — the inh-painted
       skeleton of the witnessed type [A] refines to itself; and
       [d_refine_preserves_wf] handles the well-formedness side.  The [app]
       case threads the argument's skeleton/refinement (the [d_pat__app] /
       [d_typing__app] premises) and is where universal ghosts may be
       dropped (connecting to the safety story below). *)
Theorem d_pat_validity : forall Γ e Q,
    Γ ⊢[ mode_ti ] e ⇨ Q ->
    (exists B, Γ ⊢[ mode_ti ] e ⦂ B) ->
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

    Proof deferred: it needs the safe-skeleton *construction* (choose
    ghost-keeping refinements / ghost instantiations), essentially the
    declarative shadow of the algorithm.  See also the coloured-vs-
    uncoloured refinement caveat on [d_pat_validity] above. *)
Theorem d_pat_safety : forall Γ e,
    (exists B, Γ ⊢[ mode_ti ] e ⦂ B) ->
    d_wf_denv Γ ->
    exists Q, Γ ⊢[ mode_ti ] e ⇨ Q /\
              (forall A, Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) ->
                 Γ ⨟ nil ⨟ nil ⊢ᵣ Q ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A))).
Proof.
Admitted.
