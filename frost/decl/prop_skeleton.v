(** Frost — declarative skeleton metatheory for the split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
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

Lemma d_refine_preserves_wf : forall Ψ Γ Q P,
    d_refine_syn Ψ Γ Q P ->
    d_wf_pskl Ψ Γ (bskl_to_pskl P).
Proof.
Admitted.

(** * Paper-facing skeleton properties.

    The statements below are native to the new syntax. They remain
    research-level obligations while the main D1/D12 path is being
    re-established. *)

Lemma d_pat_preserves_skel_wf : forall Γ e Q,
    d_pat mode_tc Γ e Q ->
    d_wf_denv Γ ->
    d_wf_pskl nil Γ Q.
Proof.
  intros Γ e Q H _.
  apply (proj2 d_typing_pat_preserves_wf) with (m := mode_tc) (e := e); auto.
Qed.

(** Paper "Validity of skeleton inference" (declarative.tex): a well-typed
    [M] with inferred skeleton [Γ ⊢ti M ⇨ Q] yields a *valid* skeleton — some
    type [A] with [Γ ⊢tc M : inh A] and [Γ ⊢ inh{Q} ⊳ inh{A}] (the [fill]
    judgment is the coloured refinement [d_refine_syn]).  Proof deferred. *)
Theorem d_pat_validity : forall Γ e Q,
    Γ ⊢[ mode_ti ] e ⇨ Q ->
    (exists B, Γ ⊢[ mode_ti ] e ⦂ B) ->
    d_wf_denv Γ ->
    exists A, Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) /\
              nil ⨟ Γ ⊢ᵣ Q ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)).
Proof.
Admitted.

(** Paper "Safety of skeleton inference" (declarative.tex): a well-typed [M]
    has an inference [Γ ⊢ti M ⇨ Q] whose [Q] is *safe* — it fills *every*
    checking type [A] (and hence is valid).  Proof deferred. *)
Theorem d_pat_safety : forall Γ e,
    (exists B, Γ ⊢[ mode_ti ] e ⦂ B) ->
    d_wf_denv Γ ->
    exists Q, Γ ⊢[ mode_ti ] e ⇨ Q /\
              (forall A, Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) ->
                 nil ⨟ Γ ⊢ᵣ Q ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A))).
Proof.
Admitted.
