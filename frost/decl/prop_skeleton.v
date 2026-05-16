(** Frost — declarative skeleton metatheory (Phase 2.E). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Set Implicit Arguments.

(** d_pat_consis / d_pat_sub preserves_wf lemmas moved to prop_wellformed.v
    so that d_typing_pat_preserves_wf's d_pat__sub case can use them. *)

(** * Task 3 — Splitting / inversion lemmas for d_refine and d_refine_syn.

    Paper Lemma D.4 (Splitting refines). [paper-ref: lemma:split-refine]
    The declarative analogue is inversion of the refinement relations on
    each top-level constructor. *)

Lemma d_refine_arrow_split : forall Ψ Γ P1 P2 Q,
    d_refine Ψ Γ (typ_arrow P1 P2) Q ->
    exists Q1 Q2, Q = typ_arrow Q1 Q2 /\
                  d_refine Ψ Γ P1 Q1 /\
                  d_refine Ψ Γ P2 Q2.
Proof.
  intros Ψ Γ P1 P2 Q H. dependent destruction H. eauto.
Qed.

Lemma d_refine_all_plain_split : forall Ψ Γ P Q,
    d_refine Ψ Γ (typ_all_plain P) Q ->
    exists Q', Q = typ_all_plain Q' /\
               exists L, forall X, X `notin` L ->
                  d_refine (X :: Ψ) Γ
                    (open_typ_wrt_typ P (typ_var_f X))
                    (open_typ_wrt_typ Q' (typ_var_f X)).
Proof.
  intros Ψ Γ P Q H. dependent destruction H. eauto.
Qed.

Lemma d_refine_hole_split : forall Ψ Γ Q,
    d_refine Ψ Γ typ_hole Q ->
    d_wf_skel nil Γ Q.
Proof.
  intros Ψ Γ Q H. dependent destruction H. assumption.
Qed.

Lemma d_refine_tophole_split : forall Ψ Γ P Q,
    d_refine Ψ Γ (typ_tophole P) Q ->
    (exists L Q', Q = typ_all_plain Q' /\
                  (forall X, X `notin` L ->
                     d_refine (X :: Ψ) Γ P (open_typ_wrt_typ Q' (typ_var_f X))))
    \/
    (exists L Q', Q = typ_all_plain (typ_tophole Q') /\
                  guarded_skel Q' /\
                  d_wf_skel nil Γ P /\
                  (forall X, X `notin` L ->
                     d_refine nil Γ P (open_typ_wrt_typ Q' (typ_var_f X)))).
Proof.
  intros Ψ Γ P Q H. dependent destruction H.
  - left. eauto.
  - right. eauto 8.
Qed.

(** Inversion family for [d_refine_syn]. *)

Lemma d_refine_syn_arrow_split : forall Ψ Γ P1 P2 Q,
    d_refine_syn Ψ Γ (typ_arrow P1 P2) Q ->
    exists Q1 Q2, Q = typ_arrow Q1 Q2 /\
                  d_refine_syn Ψ Γ P1 Q1 /\
                  d_refine_syn Ψ Γ P2 Q2.
Proof.
  intros Ψ Γ P1 P2 Q H. dependent destruction H. eauto.
Qed.

Lemma d_refine_syn_all_inh_split : forall Ψ Γ P Q,
    d_refine_syn Ψ Γ (typ_all_col colour_inh P) Q ->
    exists Q', Q = typ_all_col colour_inh Q' /\
               exists L, forall X, X `notin` L ->
                  d_refine_syn (X :: Ψ) Γ
                    (open_typ_wrt_typ P (typ_var_f X))
                    (open_typ_wrt_typ Q' (typ_var_f X)).
Proof.
  intros Ψ Γ P Q H. dependent destruction H. eauto.
Qed.

Lemma d_refine_syn_hole_split : forall Ψ Γ Q,
    d_refine_syn Ψ Γ typ_hole Q ->
    is_syn_skel Q /\ d_wf_skel Ψ Γ Q.
Proof.
  intros Ψ Γ Q H. dependent destruction H. auto.
Qed.

Lemma d_refine_syn_tophole_split : forall Ψ Γ P Q,
    d_refine_syn Ψ Γ (typ_tophole P) Q ->
    (exists L Q', Q = typ_all_col colour_syn Q' /\
                  (forall X, X `notin` L ->
                     d_refine_syn (X :: Ψ) Γ P (open_typ_wrt_typ Q' (typ_var_f X))))
    \/
    (exists L Q', Q = typ_all_col colour_syn (typ_tophole Q') /\
                  guarded_skel Q' /\
                  d_wf_skel nil Γ P /\
                  (forall X, X `notin` L ->
                     d_refine_syn nil Γ P (open_typ_wrt_typ Q' (typ_var_f X)))).
Proof.
  intros Ψ Γ P Q H. dependent destruction H.
  - left. eauto.
  - right. eauto 8.
Qed.

(** * Task 4 — Skeleton wf preservation under d_pat (paper declarative.tex:1970).

    Projection of the mutual lemma [d_typing_pat_preserves_wf] from
    [prop_wellformed.v]. The mutual claim still carries cross-track admits
    ([d_pat__sub], [d_pat__app], the paper-level [abs_check] /
    [abs_anno_check] tensions); this projection inherits them. *)

(** Paper Lemma 3.7 (Preservation of Skeleton Well-formedness). [paper-ref: name:"Preservation of Skeleton Well-formedness"]
    Projection of the mutual [d_typing_pat_preserves_wf] at the
    paper-stated mode (mode_tc). The mutual lemma carries an internal
    mode condition (m = mode_tc ∨ m = mode_ti) to handle sub-derivations;
    this corollary specialises to mode_tc with NO extra premise,
    matching the paper's statement exactly. *)
Lemma d_pat_preserves_skel_wf : forall Γ e P,
    d_pat mode_tc Γ e P ->
    d_wf_denv Γ ->
    d_wf_skel nil Γ P.
Proof.
  intros Γ e P H Hwfd.
  apply (proj2 d_typing_pat_preserves_wf) with (m := mode_tc) (e := e); auto.
Qed.

(** * Task 5 — Validity of skeleton inference (paper declarative.tex:1981).

    Paper restatable lemma: if [M] is well-typed AND skeleton-inferable,
    the inferred skeleton [P] refines an actual type of [M].

    Mechanically the proof would proceed by induction on [d_pat] using:
    - Refinement reflexivity on guarded skeletons (deferred to Phase 3),
    - Inversion of [d_pat_sub] / [d_pat_consis] (Task 3 splits help here
      on the refinement side; the consis-side has the same paper-level
      issue as Task 1's ghost case),
    - Anti-symmetry interaction with [d_typing__sub] (Phase 2.C-adjacent).
    Phase 2.E.5 admit; rationale in PROGRESS.md "Open Admitted". *)

(** Paper Lemma 3.8 (Validity of skeleton inference). [paper-ref: name:"Validity of skeleton inference"] *)
Theorem d_pat_validity : forall m Γ e P,
    d_pat m Γ e P ->
    d_wf_denv Γ ->
    (exists A, d_typing m Γ e A) ->
    (exists B, d_typing m Γ e B /\ d_refine nil Γ P B).
Proof.
  (* Admitted: see comment above. Depends on Phase 3 refinement reflexivity
     and on resolving the d_pat_consis ghost-case narrowing. *)
Admitted.

(** * Task 6 — Safety of skeleton inference (paper declarative.tex:1986).

    Paper restatable lemma (stronger than validity): for ANY well-typed
    [M], there EXISTS a skeleton inference whose result refines EVERY
    type of [M].

    The universal "refines every type" claim relies on a principal-
    skeleton property: the inferred [P] must be a most-precise skeleton
    among those that match any of [M]'s types. The paper's proof
    constructs this principal skeleton by induction on the typing
    derivation; mechanising it would require defining a join operation
    on skeletons under refinement, which sits at the same maturity as
    the deferred algorithmic-side lemmas.
    Phase 2.E.6 admit; see PROGRESS.md. *)

(** Paper Lemma 3.9 (Safety of skeleton inference). [paper-ref: name:"Safety of skeleton inference"] *)
Theorem d_pat_safety : forall m Γ e,
    (exists A, d_typing m Γ e A) ->
    d_wf_denv Γ ->
    exists P, d_pat m Γ e P /\
              (forall B, d_typing m Γ e B -> d_refine nil Γ P B).
Proof.
  (* Admitted: depends on principal-skeleton construction. *)
Admitted.
