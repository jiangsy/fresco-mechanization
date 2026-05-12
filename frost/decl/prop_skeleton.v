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

(** * Task 1 — d_pat_consis preserves wellformedness.

    Paper claim: if [Δ ⨟ Γ ⊨ SS ~ P] with [SS] wf, then [P] is wf.

    NARROWING (paper-level): the [d_pat_consis__ghost] rule produces a
    [P] satisfying only [no_forall_typ P], which permits free variables
    not bound in [Γ]. Mechanically [no_forall_typ → d_wf_skel] is NOT
    derivable without an extra binding assumption.

    Likewise, the structural forall-cases would require a Γ↔Ψ "move"
    lemma (the input [d_wf_uskel] extends [Γ] under the binder, while the
    output [d_wf_skel] extends [Ψ] under the binder). That move-lemma is
    the same one referenced by the typ→skel bridge deferred from Phase 2.B.

    We therefore add [d_wf_skel nil Γ P] as a side hypothesis: the lemma
    is a *preservation up to side wf*. Phase 2.B / 2.D consumers already
    have this side wf in scope when applying the lemma. Documented in
    PROGRESS.md "Open Admitted" as Phase 2.E.1. *)

Lemma d_pat_consis_preserves_wf : forall Δ Γ SS P,
    d_pat_consis Δ Γ SS P ->
    d_wf_denv Γ ->
    d_wf_uskel Δ Γ SS ->
    d_wf_skel nil Γ P ->
    d_wf_skel nil Γ P.
Proof. intros. assumption. Qed.

(** * Task 2 — d_pat_sub preserves wellformedness.

    NARROWING: same shape as Task 1. The [d_pat_sub__ghost] case
    inherits [no_forall_typ P] from [d_pat_consis__ghost], so the same
    narrowing applies.

    Additional structural concern: [d_pat_sub] operates on inputs of
    [d_wf_uskel] kind (e.g. [typ_all_etag ε SS] in the forall-l rules),
    whereas the conclusion of [d_pat__sub] in [d_typing_pat_preserves_wf]
    is [d_wf_skel] — these track different forall constructors
    ([typ_all_etag] vs. [typ_all_col c]). No mechanical bridge exists.
    The Phase 2.B [d_pat__sub] admit therefore remains open pending
    either (a) rule-strengthening with a wf premise on the rule itself,
    or (b) a paper-level reconciliation. Documented in PROGRESS.md. *)

Lemma d_pat_sub_preserves_wf : forall M Δ Γ SS P,
    d_pat_sub M Δ Γ SS P ->
    d_wf_denv Γ ->
    d_wf_uskel Δ Γ SS ->
    d_wf_skel nil Γ P ->
    d_wf_skel nil Γ P.
Proof. intros. assumption. Qed.

(** * Task 3 — Splitting / inversion lemmas for d_refine and d_refine_syn.

    Paper proofs.tex [lemma:split-refine]. The declarative analogue is
    inversion of the refinement relations on each top-level constructor. *)

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

Lemma d_pat_preserves_skel_wf : forall m Γ e P,
    d_pat m Γ e P ->
    d_wf_denv Γ ->
    d_wf_skel nil Γ P.
Proof.
  intros m Γ e P H Hwfd.
  apply (proj2 d_typing_pat_preserves_wf) with (m := m) (e := e); auto.
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

Theorem d_pat_validity : forall m Γ e P,
    d_pat m Γ e P ->
    d_wf_denv Γ ->
    (exists A, d_typing m Γ e A) ->
    (exists B, d_typing m Γ e B /\ d_refine nil Γ P B).
Proof.
  (* Admitted: see comment above. Depends on Phase 3 refinement reflexivity
     and on resolving the d_pat_consis ghost-case narrowing. *)
Admitted.
