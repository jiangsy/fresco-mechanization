(** Declarative judgments in ALGORITHMIC contexts (paper
    app:decl-in-algo-context).

    "All declarative judgements … are naturally extended to algorithmic
    contexts": the rules are the declarative ones with [Γ] replaced by [Θ],
    plus lookup rules that retrieve flexible-variable definitions from [Θ]
    (FlexL/FlexR for consistency, FlexMono for subtyping, two rules for
    refinement).  This file provides the consistency/refinement layer used
    by the soundness lemmas of appendix B (consistency-proofs.tex); the
    subtyping/typing layer follows with appendix C/D.

    Naming: [ad_*] = the [d_*] judgment over an [aenv]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.

Set Implicit Arguments.

(** Monotype embeddings used by the definition-lookup rules. *)
Definition ptyp_to_bskl_syn (A : ptyp) : bskl :=
  pskl_to_bskl_syn (ptyp_to_pskl A).
Definition ptyp_to_uskl_syn (A : ptyp) : uskl :=
  bskl_to_uskl (ptyp_to_bskl_syn A).

(** A type-variable occurrence in [Θ]: rigid, or a flexible declaration /
    definition (an occurrence of a defined [α̂] is still a variable; its
    definition is retrieved by the lookup rules where needed). *)
Definition a_binds_tvar (X : atom) (Θ : aenv) : Prop :=
  binds X abind_tvar Θ \/
  binds X abind_flex_mono Θ \/
  (exists τ, binds X (abind_flex_mono_def τ) Θ).

(* ===================================================================== *)
(*  Skeleton well-formedness over Θ  (decl [Γ ⨟ Δ ⊢ₚₛ P])                *)
(* ===================================================================== *)

Inductive ad_wf_pskl : aenv -> list atom -> pskl -> Prop :=
| ad_wf_pskl__unit : forall Θ Δ,
    ad_wf_pskl Θ Δ pskl_unit
| ad_wf_pskl__var : forall Θ Δ X,
    List.In X Δ \/ a_binds_tvar X Θ ->
    ad_wf_pskl Θ Δ (pskl_var_f X)
| ad_wf_pskl__arrow : forall Θ Δ P1 P2,
    ad_wf_pskl Θ Δ P1 ->
    ad_wf_pskl Θ Δ P2 ->
    ad_wf_pskl Θ Δ (pskl_arrow P1 P2)
| ad_wf_pskl__all : forall L Θ Δ P,
    (forall X, X `notin` L ->
       ad_wf_pskl Θ (X :: Δ) (open_pskl_wrt_pskl P (pskl_var_f X))) ->
    ad_wf_pskl Θ Δ (pskl_all_syn P)
| ad_wf_pskl__hole : forall Θ Δ,
    ad_wf_pskl Θ Δ pskl_hole
| ad_wf_pskl__tophole : forall Θ Δ P,
    guarded_pskl P ->
    ad_wf_pskl Θ nil P ->
    ad_wf_pskl Θ Δ (pskl_tophole P).

(* ===================================================================== *)
(*  Skeleton consistency over Θ  (decl [Ψ ⨟ Γ ⊨ₛ S ≈ Q] + FlexL/FlexR)    *)
(* ===================================================================== *)

Inductive ad_pat_consis : atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_consis__unit : forall Ψ Θ,
    Ψ [=] empty ->
    ad_pat_consis Ψ Θ uskl_unit bskl_unit
| ad_pat_consis__var : forall Ψ Θ X,
    Ψ [=] empty ->
    a_binds_tvar X Θ ->
    ad_pat_consis Ψ Θ (uskl_var_f X) (bskl_var_f X)
| ad_pat_consis__arrow : forall Ψ Ψ1 Ψ2 Θ R1 R2 Q1 Q2,
    ad_pat_consis Ψ1 Θ R1 Q1 ->
    ad_pat_consis Ψ2 Θ R2 Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    ad_pat_consis Ψ Θ (uskl_arrow R1 R2) (bskl_arrow Q1 Q2)
| ad_pat_consis__forall_inh_tagged : forall L Ψ Ψ0 Θ ε R Q,
    (forall X, X `notin` L ->
       ad_pat_consis Ψ0 ((X ~ abind_tvar) ++ Θ)
         (open_uskl_wrt_uskl R (uskl_var_f X))
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ [=] add ε Ψ0 ->
    ad_pat_consis Ψ Θ (uskl_all_etag ε R) (bskl_all_inh Q)
| ad_pat_consis__forall_inh_untagged : forall L Ψ Θ R Q,
    (forall X, X `notin` L ->
       ad_pat_consis Ψ ((X ~ abind_tvar) ++ Θ)
         (open_uskl_wrt_uskl R (uskl_var_f X))
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    ad_pat_consis Ψ Θ (uskl_all_syn R) (bskl_all_inh Q)
| ad_pat_consis__forall_syn_tagged : forall L Ψ Θ ε R Q,
    (forall X, X `notin` L ->
       ad_pat_consis Ψ ((X ~ abind_tvar) ++ Θ)
         (open_uskl_wrt_uskl R (uskl_var_f X))
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    ad_pat_consis Ψ Θ (uskl_all_etag ε R) (bskl_all_syn Q)
| ad_pat_consis__forall_syn : forall L Ψ Θ R Q,
    (forall X, X `notin` L ->
       ad_pat_consis Ψ ((X ~ abind_tvar) ++ Θ)
         (open_uskl_wrt_uskl R (uskl_var_f X))
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    ad_pat_consis Ψ Θ (uskl_all_syn R) (bskl_all_syn Q)
| ad_pat_consis__ghostg : forall Ψ Θ,
    Ψ [=] empty ->
    ad_pat_consis Ψ Θ uskl_holeg bskl_hole
| ad_pat_consis__topholeg : forall Ψ Θ R Q,
    ad_pat_consis Ψ Θ R Q ->
    ad_pat_consis Ψ Θ (uskl_topholeg R) (bskl_tophole Q)
| ad_pat_consis__hole : forall Ψ Θ P,
    Ψ [=] empty ->
    ad_wf_pskl Θ nil P ->
    ad_pat_consis Ψ Θ uskl_hole (pskl_to_bskl_inh P)
| ad_pat_consis__tophole : forall Ψ Θ R Q,
    ad_pat_consis Ψ Θ R Q ->
    ad_pat_consis Ψ Θ (uskl_tophole R) (bskl_tophole Q)
| ad_pat_consis__tophole_inh : forall L Ψ Θ R Q,
    (forall X, X `notin` L ->
       ad_pat_consis Ψ ((X ~ abind_tvar) ++ Θ)
         (uskl_tophole R) (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    ad_pat_consis Ψ Θ (uskl_tophole R) (bskl_all_inh Q)
| ad_pat_consis__tophole_drop : forall Ψ Θ R Q,
    ad_pat_consis Ψ Θ R Q ->
    ad_pat_consis Ψ Θ (uskl_tophole R) Q
(* — new lookup rules (paper eqlab FlexL / FlexR) — *)
| ad_pat_consis__flex_l : forall Ψ Θ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_pat_consis Ψ Θ (ptyp_to_uskl_syn τ) Q ->
    ad_pat_consis Ψ Θ (uskl_var_f α) Q
| ad_pat_consis__flex_r : forall Ψ Θ α τ S,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_pat_consis Ψ Θ S (ptyp_to_bskl_syn τ) ->
    ad_pat_consis Ψ Θ S (bskl_var_f α).

(* ===================================================================== *)
(*  Skeleton refinement over Θ, coloured  (decl [Γ ⨟ Δ ⊢ᵣ Q ⊳ P] + flex)  *)
(* ===================================================================== *)

Inductive ad_refine_syn : aenv -> list atom -> bskl -> bskl -> Prop :=
| ad_refine_syn__unit : forall Θ Δ,
    ad_refine_syn Θ Δ bskl_unit bskl_unit
| ad_refine_syn__var : forall Θ Δ X,
    List.In X Δ \/ a_binds_tvar X Θ ->
    ad_refine_syn Θ Δ (bskl_var_f X) (bskl_var_f X)
| ad_refine_syn__arrow : forall Θ Δ Q1 Q2 P1 P2,
    ad_refine_syn Θ Δ Q1 P1 ->
    ad_refine_syn Θ Δ Q2 P2 ->
    ad_refine_syn Θ Δ (bskl_arrow Q1 Q2) (bskl_arrow P1 P2)
| ad_refine_syn__all : forall L Θ Δ Q P,
    (forall X, X `notin` L ->
       ad_refine_syn Θ (X :: Δ)
         (open_bskl_wrt_bskl Q (bskl_var_f X))
         (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    ad_refine_syn Θ Δ (bskl_all_inh Q) (bskl_all_inh P)
| ad_refine_syn__hole : forall Θ Δ P,
    ad_wf_pskl Θ nil P ->
    ad_refine_syn Θ Δ bskl_hole (pskl_to_bskl_syn P)
| ad_refine_syn__tophole_remove : forall Θ Δ Q P,
    ad_refine_syn Θ Δ Q P ->
    ad_refine_syn Θ Δ (bskl_tophole Q) P
| ad_refine_syn__tophole_fill : forall L Θ Δ Q P,
    (forall X, X `notin` L ->
       ad_refine_syn ((X ~ abind_tvar) ++ Θ) Δ
         (bskl_tophole Q) (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    ad_refine_syn Θ Δ (bskl_tophole Q) (bskl_all_syn P)
| ad_refine_syn__tophole_keep : forall Θ Δ Q P,
    guarded_bskl P ->
    ad_refine_syn Θ Δ Q P ->
    ad_refine_syn Θ Δ (bskl_tophole Q) (bskl_tophole P)
(* — new lookup rules (paper fig:declarative-in-algo-context, refinement) — *)
| ad_refine_syn__flex_l : forall Θ Δ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_refine_syn Θ Δ (ptyp_to_bskl_syn τ) Q ->
    ad_refine_syn Θ Δ (bskl_var_f α) Q
| ad_refine_syn__flex_r : forall Θ Δ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_refine_syn Θ Δ P (ptyp_to_bskl_syn τ) ->
    ad_refine_syn Θ Δ P (bskl_var_f α).

(* ===================================================================== *)
(*  Skeleton refinement over Θ, uncoloured  (decl [Γ ⊢ P ⊳ Q], the paper's *)
(*  colour-ignoring reading of the refinement rules, + flex lookups)       *)
(* ===================================================================== *)

Inductive ad_refine_pskl : aenv -> list atom -> pskl -> pskl -> Prop :=
| ad_refine_pskl__unit : forall Θ Δ,
    ad_refine_pskl Θ Δ pskl_unit pskl_unit
| ad_refine_pskl__var : forall Θ Δ X,
    List.In X Δ \/ a_binds_tvar X Θ ->
    ad_refine_pskl Θ Δ (pskl_var_f X) (pskl_var_f X)
| ad_refine_pskl__arrow : forall Θ Δ P1 P2 Q1 Q2,
    ad_refine_pskl Θ Δ P1 Q1 ->
    ad_refine_pskl Θ Δ P2 Q2 ->
    ad_refine_pskl Θ Δ (pskl_arrow P1 P2) (pskl_arrow Q1 Q2)
| ad_refine_pskl__all : forall L Θ Δ P Q,
    (forall X, X `notin` L ->
       ad_refine_pskl Θ (X :: Δ)
         (open_pskl_wrt_pskl P (pskl_var_f X))
         (open_pskl_wrt_pskl Q (pskl_var_f X))) ->
    ad_refine_pskl Θ Δ (pskl_all_syn P) (pskl_all_syn Q)
| ad_refine_pskl__hole : forall Θ Δ Q,
    ad_wf_pskl Θ nil Q ->
    ad_refine_pskl Θ Δ pskl_hole Q
| ad_refine_pskl__tophole_remove : forall Θ Δ P Q,
    ad_refine_pskl Θ Δ P Q ->
    ad_refine_pskl Θ Δ (pskl_tophole P) Q
| ad_refine_pskl__tophole_fill : forall L Θ Δ P Q,
    (forall X, X `notin` L ->
       ad_refine_pskl ((X ~ abind_tvar) ++ Θ) Δ
         (pskl_tophole P) (open_pskl_wrt_pskl Q (pskl_var_f X))) ->
    ad_refine_pskl Θ Δ (pskl_tophole P) (pskl_all_syn Q)
| ad_refine_pskl__tophole_keep : forall Θ Δ P Q,
    guarded_pskl Q ->
    ad_refine_pskl Θ Δ P Q ->
    ad_refine_pskl Θ Δ (pskl_tophole P) (pskl_tophole Q)
| ad_refine_pskl__flex_l : forall Θ Δ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_refine_pskl Θ Δ (ptyp_to_pskl τ) Q ->
    ad_refine_pskl Θ Δ (pskl_var_f α) Q
| ad_refine_pskl__flex_r : forall Θ Δ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_refine_pskl Θ Δ P (ptyp_to_pskl τ) ->
    ad_refine_pskl Θ Δ P (pskl_var_f α).
