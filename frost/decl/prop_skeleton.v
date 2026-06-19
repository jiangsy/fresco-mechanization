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

(** A well-scoped type's skeleton is a well-formed [pskl].  ([ptyp_to_pskl]
    images are ghost-free, so — as in [d_refine_syn_refl_inh] — a scope
    coverage premise lets the [∀] case route the bound var into [Ψ].) *)
Lemma d_wf_pskl_of_ptyp : forall A,
    lc_ptyp A ->
    forall Γ Ψ,
      (forall X, X `in` ftvar_in_ptyp A -> List.In X Ψ \/ binds X dbind_tvar Γ) ->
      Ψ ⨟ Γ ⊢ₚₛ (ptyp_to_pskl A).
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
    forall Γ Δs Δi,
      (forall X, X `in` ftvar_in_ptyp A -> List.In X Δs \/ binds X dbind_tvar Γ) ->
      Γ ⨟ Δs ⨟ Δi ⊢ᵣ bskl_hole ⊳ (pskl_to_bskl_syn (ptyp_to_pskl A)).
Proof.
  intros A Hlc Γ Δs Δi Hcov.
  apply d_refine_syn__hole. eapply d_wf_pskl_of_ptyp; eassumption.
Qed.

(** Γ-weakening for refinement (local copy — the general
    [d_refine_syn_weakening] lives in [prop_weakening], built later).  Used
    by [denv_coh_lookup] to lift a binding's refinement to the full
    context. *)
Lemma d_refine_syn_wkn : forall Γ1 Γ2 Γ3 Δs Δi Q P,
    (Γ1 ++ Γ3) ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P ->
    (Γ1 ++ Γ2 ++ Γ3) ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ1 Γ2 Γ3 Δs Δi Q P H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst Γ.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var.
    match goal with H : _ \/ _ |- _ => destruct H as [HS | [HI | Hb]] end;
      [ left; assumption | right; left; assumption | right; right; analyze_binds Hb ].
  - apply d_refine_syn__arrow; auto.
  - apply d_refine_syn__all with (L := L `union` dom (Γ1 ++ Γ3)). intros X HX.
    eapply (H0 X ltac:(fsetdec) Γ1 Γ3). reflexivity.
  - apply d_refine_syn__hole. apply d_wf_pskl_weakening. assumption.
  - apply d_refine_syn__tophole_remove; auto.
  - apply d_refine_syn__tophole_fill with (L := L `union` dom (Γ1 ++ Γ3)). intros X HX.
    eapply (H0 X ltac:(fsetdec) Γ1 Γ3). reflexivity.
  - apply d_refine_syn__tophole_keep; [ assumption | auto ].
Qed.

(** A *typing context*: only type/tvar bindings, no ghost-bearing
    skeleton bindings.  (The user's "context has only A, not P" predicate.)
    Every context a [d_typing] derivation actually uses is of this shape. *)
Inductive typ_denv : list (atom * dbind) -> Prop :=
| typ_denv__nil  : typ_denv nil
| typ_denv__tvar : forall Γ X, typ_denv Γ -> typ_denv ((X ~ dbind_tvar) ++ Γ)
| typ_denv__typ  : forall Γ x A, typ_denv Γ -> typ_denv ((x ~ dbind_typ A) ++ Γ).

(** Context coherence between a skeleton-inference context [Γs] and a
    typing context [Γt].  Every term variable is [dbind_skl] in [Γs] (so
    [d_pat__var] applies — inference reads skeletons) and [dbind_typ] in
    [Γt] (so [d_typing__var] applies), linked by a refinement
    [inh{P} ⊳ inh{ptyp A}] (refl for coerced bindings, hole-fills for a λ
    ghost).  This is the bridge a safety/validity induction needs to cross a
    λ where the two judgments bind a variable differently. *)
Inductive denv_coh : list (atom * dbind) -> list (atom * dbind) -> Prop :=
| denv_coh__nil  : denv_coh nil nil
| denv_coh__tvar : forall Γs Γt X,
    denv_coh Γs Γt ->
    denv_coh ((X ~ dbind_tvar) ++ Γs) ((X ~ dbind_tvar) ++ Γt)
| denv_coh__skl  : forall Γs Γt x P A,
    denv_coh Γs Γt ->
    Γt ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)) ->
    denv_coh ((x ~ dbind_skl P) ++ Γs) ((x ~ dbind_typ A) ++ Γt).

(** Lookup: a [dbind_typ A] term-var in [Γt] is matched by some [dbind_skl P]
    in [Γs] whose inh-painting refines [inh{ptyp A}] (weakened to the full
    [Γt]).  This is what discharges the [var] case of safety. *)
Lemma denv_coh_lookup : forall Γs Γt x A,
    denv_coh Γs Γt ->
    binds x (dbind_typ A) Γt ->
    exists P, binds x (dbind_skl P) Γs /\
              Γt ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)).
Proof.
  intros Γs Γt x A Hcoh. induction Hcoh; intros Hb.
  - inversion Hb.
  - (* tvar *) apply binds_app_1 in Hb. destruct Hb as [Hb | Hb].
    + apply binds_one_iff in Hb. destruct Hb as [_ Hd]. inversion Hd.
    + destruct (IHHcoh Hb) as [P [HbP Href]]. exists P. split.
      * apply binds_app_3. exact HbP.
      * rewrite_env (nil ++ (X ~ dbind_tvar) ++ Γt). apply d_refine_syn_wkn. exact Href.
  - (* skl *) apply binds_app_1 in Hb. destruct Hb as [Hb | Hb].
    + apply binds_one_iff in Hb. destruct Hb as [Hx Hd]. inversion Hd. subst.
      exists P. split.
      * apply binds_app_2. apply binds_one_3; auto.
      * rewrite_env (nil ++ (x0 ~ dbind_typ A0) ++ Γt). apply d_refine_syn_wkn. exact H.
    + destruct (IHHcoh Hb) as [P' [HbP' Href']]. exists P'. split.
      * apply binds_app_3. exact HbP'.
      * rewrite_env (nil ++ (x0 ~ dbind_typ A0) ++ Γt). apply d_refine_syn_wkn. exact Href'.
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

    (Painting: the fill target is *syn*-painted, like [d_pat_safety] — the
    faithful encoding of the paper's uncoloured [fill]; filling a ghost to
    an inherited [∀] is deliberately banned.)

    Once disciplined, the proof is: induction on the check-mode inference
    under the [denv_coh] invariant above (each inference-bound skeleton
    refines the corresponding typing type — ghost-refines-anything for the
    λ ghost).  NB a *further* refinement gap surfaces for annotated
    polytypes: a concrete [bskl_all_syn] on the LHS has NO refine rule
    (only [bskl_all_inh] via [__all], plus the ghost rules), so [(e:∀α.B)],
    which infers [bskl_all_syn(…)], cannot even refine to [syn{∀α.B}]
    (refl on a synthesised [∀]).  [d_refine_syn] would need a
    [bskl_all_syn]-LHS rule too. *)
Theorem d_pat_validity : forall Γ e Q B,
    Γ ⊢[ mode_tc ] e ⇨ Q ->
    Γ ⊢[ mode_tc ] e ⦂ B ->
    d_wf_denv Γ ->
    exists A, Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) /\
              Γ ⨟ nil ⨟ nil ⊢ᵣ Q ⊳ (pskl_to_bskl_syn (ptyp_to_pskl A)).
Proof.
(* FALSE for the current rules (see the [freeze (λx.(x:unit))] counterexample
   above); aborted rather than admitted.  Recover by disciplining
   [d_pat__abs] to bind a ghost, then prove via [denv_coh]. *)
Abort.

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

    (The [freeze (λx.(x:unit))] validity counterexample is NOT a safety
    counterexample: [freeze] is not a value, so the term checks only at
    [unit→unit], which [□→unit] fills.)

    PAINTING (per the current def — see statement below).  The LHS is
    *inherited* ([inh{P}]) and the target *bidirectional* ([bid{A}]).  This
    is what makes it work: concrete [∀]s in [P] become inh-[∀] (handled by
    [d_refine_syn__all]); ghosts fill via [hole] (any well-formed pskl) /
    [tophole] (universal ghost → syn-[∀] by [tophole_fill]).  Filling a
    ghost to an *inherited* [∀] stays (correctly) banned — the inh-painting
    is on [P], not the target.

    ENGINES (proved): [d_refine_syn_refl_inh] handles concrete/coerced
    parts ([inh{ptyp A} ⊳ inh{ptyp A}]); [d_refine_syn_hole_fills] handles
    ghosts ([□ ⊳] any well-scoped type's syn-skeleton, polytypes included).

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
  (* Attempted directly: [intros Γ e B0 Hty Hwf; induction Hty] gives 11
     cases.  The [var] case is STUCK: its hypothesis is
     [binds x (dbind_typ A) Γ] (typing binds term-vars as [dbind_typ]), but
     constructing the inference [x ⇨ Q] needs [d_pat__var], which requires
     [binds x (dbind_skl P) Γ] — a [dbind_typ]-bound variable is not
     inferable.  So the single-[Γ] statement cannot be proved by direct
     induction: safety, like [d_pat_validity], must be generalised over
     [denv_coh Γs Γt] (inference context with [dbind_skl] vs typing context
     with [dbind_typ]); the leaves then close with [d_refine_syn_refl_inh] /
     [d_refine_syn_hole_fills].  That generalisation is the remaining work. *)
Admitted.
