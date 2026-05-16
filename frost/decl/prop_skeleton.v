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

(** [d_pat_validity] (paper Lemma 3.8) and [d_pat_safety] (paper
    Lemma 3.9) (REMOVED): these depend on Phase 3 refinement
    reflexivity and on a principal-skeleton construction (a join
    operation on skeletons under refinement) which is not in scope
    for the declarative-properties pass. Removed as unused; future
    work to be added when Phase 3 infrastructure is in place. *)
