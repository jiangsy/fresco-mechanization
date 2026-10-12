(** Fresco — index of the mechanized results.

    This file lists, for each theorem and lemma of the paper, the Rocq
    statement that mechanizes it.  Every entry is a [Check] of the result
    at its paper-level type, followed by [Print Assumptions], so that the
    build itself verifies both the statement and its axiom status: every
    assumption report must read "Closed under the global context".

    External well-formedness premises are those the paper states in prose
    ("all inputs are well-formed") rather than in its rules; the Rocq
    statements carry them as explicit hypotheses.

    Notation
      Γ / Θ  declarative / algorithmic context      Ξ  suffix (fresh block)
      Δ      skeleton ∀-scope (atom set)            κ, ζ  metasubstitutions
      Ψ      solved-tag context (atom set)
      A B C  ptyp, btyp, utyp                       P Q R  pskl, bskl, uskl
      κ ∷ Θ₀ ⊑ Θ  information increase              Θ₀ ⊴ Θ₁  its relational form
      ∼ consistency   ⩽ subtyping   ⦂ a term's type / skeleton (at any mode)
      ⊳ refinement    ⊑ᵖ partial precision   ≡ᵗ/≡ˢ/≡ᵘ equivalence
      ⪯ᶜᵗˣ context precision

    Judgement delimiters: the brace pair names the system, and each pair is
    its own notation scope (see fresco/notations.v).
      [{{ … }}d]   declarative ([d_*], over Γ)
      [{{ … }}ad]  declarative over algorithmic contexts ([ad_*], over Θ)
      [{{ … }}a]   algorithmic ([a_*], with output context [⊣ Θ'])
      [{{ … }}da]  ε-tagged decorated ([a_consistag] / [a_subtag])
    The turnstile's superscript selects the sort or copy: bare for types,
    [⊢ˢ] skeletons, [⊢ᵉ] expressions, [⊢ˢᵈ] syntax-directed typing.  Its
    subscript selects the relation where a system has several at one sort:
    [⊢ᵣ]/[⊢ᵣₚ] refinement, [⊢ₚᵣ] precision, [⊢ₛ]/[⊢ₑ] the solve layer, and
    [⊢ₚ]/[⊢ᵦ]/[⊢ᵤ]/[⊢ₚₛ]/[⊢ᵤₛ] well-formedness.  [{{ ⊢ Θ }}a] is context
    well-formedness.  [⦂] is used at every mode. *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.def_typing.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_syntax_directed.
Require Import src.fresco.decl.prop_general_subsumption.
Require Import src.fresco.decl.prop_stability.
Require Import src.fresco.decl.prop_shallow.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.deco_algo.prop_soundness_sub.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_precise.
Require Import src.fresco.algo.subtyping.prop_completeness_solve_eq_var.
Require Import src.fresco.algo.subtyping.prop_completeness_lookeq_solve.
Require Import src.fresco.algo.subtyping.prop_completeness_solve_sub_var.
Require Import src.fresco.algo.subtyping.prop_completeness_looksub_solve.
Require Import src.fresco.algo.subtyping.prop_completeness_extract.
Require Import src.fresco.algo.subtyping.prop_completeness_sub.
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.typing.prop_soundness_typing.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo_decl.prop_ctx_precision.
Require Import src.fresco.algo.typing.prop_completeness_pat.
Require Import src.fresco.algo.typing.prop_completeness_typing.
Require Import src.fresco.algo.typing.prop_typing_closed.
Require Import src.fresco.algo_decl.prop_conservativity.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.typing.def_typing.
Require Import src.fresco.ext_algo.typing.prop_typing.
Require Import src.fresco.ext_algo.typing.def_typing_impl.
Require Import src.fresco.ext_algo.prop_run_corollaries.

(* Lemma B.1 (Soundness of syntax-directed rules) *)
Check d_sd_typing_sound :
  forall M Γ e B, {{ Γ ⊢ˢᵈ[ M ] e ⦂ B }}d -> {{ Γ ⊢[ M ] e ⦂ B }}d.
Print Assumptions d_sd_typing_sound.

(* Lemma B.2 (Completeness of syntax-directed rules) *)
Check d_sd_typing_complete :
  forall M Γ e B, {{ Γ ⊢[ M ] e ⦂ B }}d -> d_wf_denv Γ -> {{ Γ ⊢ˢᵈ[ M ] e ⦂ B }}d.
Print Assumptions d_sd_typing_complete.

(* General subsumption *)
Check d_sd_typing_general_subsumption :
  forall Γ e A B m,
  d_wf_denv Γ ->
  {{ Γ ⊢ˢᵈ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) }}d ->
  {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
  {{ Γ ⊢ˢᵈ[ m ] e ⦂ B }}d.
Print Assumptions d_sd_typing_general_subsumption.

(* General subsumption, for the declarative typing judgement *)
Check d_typing_general_subsumption :
  forall Γ e A B m,
  {{ Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) }}d ->
  {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
  {{ Γ ⊢[ m ] e ⦂ B }}d.
Print Assumptions d_typing_general_subsumption.

(* Lemma C.6 (Soundness of consistency) *)
Check a_consis_sound :
  forall Θ0 P0 P P' Θ1,
  {{ Θ0 ⊢[ P0 ] P ∼ P' ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  Θ0 ⊴ Θ1 /\
  (exists Qt, bskl_to_pskl Qt = P' /\
     {{ empty ⨟ Θ1 ⊢ˢ (pskl_to_uskl P) ∼ Qt }}ad /\
     {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad) /\
  {{ Θ1 ⨟ empty ⊢ᵣₚ P ⊳ P' }}ad.
Print Assumptions a_consis_sound.

(* Lemma C.7 (Completeness and optimality of consistency) *)
Check a_consis_complete.
Print Assumptions a_consis_complete.

(* Theorem 4.5 (Soundness of subtyping) *)
Check a_sub_sound :
  forall NM M P0 Θ0 P P' Θ1,
  {{ Θ0 ⊢[ NM | M | P0 ] P ⩽ P' ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt,
    bskl_to_pskl Qt = P' /\
    ({{ empty ⨟ Θ1 ⊢ˢ[ NM | M ] (pskl_to_uskl P) ⩽ Qt }}ad) /\
    {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad.
Print Assumptions a_sub_sound.

(* Theorem 4.6 (Completeness and optimality of subtyping) *)
Check a_sub_complete.
Print Assumptions a_sub_complete.

(* Lemma E.14 (Stability of subtyping under more precise substitution) *)
Check ad_pat_sub_precise_upre_fuel.
Print Assumptions ad_pat_sub_precise_upre_fuel.

(* Lemma F.6 (Completeness of consistency constraint collection and solving for variables) *)
Check a_solve_eq_complete_var.
Print Assumptions a_solve_eq_complete_var.

(* Lemma F.5 (Completeness of consistency constraint collection and solving) *)
Check a_lookeq_solve_complete.
Print Assumptions a_lookeq_solve_complete.

(* Lemma E.15 (Completeness of constraint collection and solving for variables) *)
Check a_solve_sub_complete_var.
Print Assumptions a_solve_sub_complete_var.

(* Lemma E.16 (Completeness of constraint collection and solving) *)
Check a_looksub_solve_complete.
Print Assumptions a_looksub_solve_complete.

(* Lemma E.17 (Look completeness) *)
Check a_extract_complete.
Print Assumptions a_extract_complete.

(* Theorem C.2 (Soundness of skeleton inference) *)
Check a_pat_sound :
  forall m Θ0 P0 e P Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ P ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat m P0 ->
  {{ Θ0 ⊢ᵉ e }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt, bskl_to_pskl Qt = P /\
    ({{ Θ1 ⊢ˢ[ m ] e ⦂ Qt }}ad) /\
    ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad).
Print Assumptions a_pat_sound.

(* Theorem 4.2 (Soundness of type inference) *)
Check a_typing_sound :
  forall m Θ0 P0 e A Θ1,
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ A ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat m P0 ->
  {{ Θ0 ⊢ᵉ e }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  exists Bt, btyp_to_ptyp Bt = A /\
    ({{ Θ1 ⊢ˢᵈ[ m ] e ⦂ Bt }}ad) /\
    ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ (btyp_to_bskl Bt) }}ad).
Print Assumptions a_typing_sound.

(* Theorem 4.2 (Soundness of type inference), closed programs, inference mode *)
Check a_typing_sound_infer :
  forall e A Θ1,
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_ti ; pskl_ghost ] e ⦂ A ⊣ Θ1 }}a ->
  nil ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  ({{ Θ1 ⨟ empty ⊢ᵣ bskl_ghost ⊳ (btyp_to_bskl (ptyp_to_btyp_syn A)) }}ad) /\
  exists ζ, ζ ∷ Θ1 ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ A)) }}d) /\
    ({{ nil ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ A)) }}d).
Print Assumptions a_typing_sound_infer.

(* Theorem 4.2 (Soundness of type inference), closed programs, checking mode *)
Check a_typing_sound_check :
  forall e A0 A Θ1,
  {{ nil ⊢ᵉ e }}a ->
  a_wf_ptyp nil A0 ->
  {{ nil ⊢[ mode_tc ; (ptyp_to_pskl A0) ] e ⦂ A ⊣ Θ1 }}a ->
  nil ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl A0))
     ⊳ (btyp_to_bskl (ptyp_to_btyp_inh A)) }}ad) /\
  exists ζ, ζ ∷ Θ1 ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ (ptyp_to_btyp_inh (msubst_ptyp ζ A)) }}d) /\
    ({{ nil ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh (msubst_ptyp ζ A)) }}d).
Print Assumptions a_typing_sound_check.

(* Theorem C.3 (Completeness and optimality of skeleton inference) *)
Check a_pat_complete :
  forall e M Θ0 P0 κ Θ Q,
    {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    a_sk_mode_compat M P0 ->
    κ ∷ Θ0 ⊑ Θ ->
    (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
    lc_exp e ->
    {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
    exists P1 Θ1,
      {{ Θ0 ⊢ˢ[ M ; P0 ] e ⦂ P1 ⊣ Θ1 }}a /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl ζ P1) ⊑ (bskl_to_pskl Q) }}ad).
Print Assumptions a_pat_complete.

(* Theorem 4.3 (Completeness and optimality of type inference) *)
Check a_typing_complete :
  forall e M Θ0 P0 κ Θ B,
    {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    a_ty_mode_compat M P0 ->
    κ ∷ Θ0 ⊑ Θ ->
    (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
    {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
    exists A1 Θ1,
      {{ Θ0 ⊢[ M ; P0 ] e ⦂ A1 ⊣ Θ1 }}a /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           {{ Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a).
Print Assumptions a_typing_complete.

(* Theorem 4.3 (Completeness of type inference), closed programs, inference mode *)
Check a_typing_complete_infer :
  forall e (B : btyp),
  {{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ B }}ad ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_ghost ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_infer.

(* Theorem 4.3 (Completeness of type inference), closed programs, checking mode *)
Check a_typing_complete_check :
  forall e (B : btyp),
  {{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ B }}ad ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_check.

(* Theorem 4.3, closed programs, over syntax-directed typing, inference mode *)
Check a_typing_complete_sd_infer :
  forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_ghost ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_sd_infer.

(* Theorem 4.3, closed programs, over syntax-directed typing, checking mode *)
Check a_typing_complete_sd_check :
  forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_sd_check.

(* Theorem 4.3, closed programs, over declarative typing, inference mode *)
Check a_typing_complete_decl_infer :
  forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_ghost ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_decl_infer.

(* Theorem 4.3, closed programs, over declarative typing, checking mode *)
Check a_typing_complete_decl_check :
  forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_tc ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_decl_check.

(* Lemma D.4 (Precision extends skeleton subtyping) *)
Check ad_precise_extends_pat_sub.
Print Assumptions ad_precise_extends_pat_sub.

(* Lemma D.7 (Context precision preserves skeleton inference) *)
Check ad_ctx_precise_pat :
  forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θ', {{ Θ' ⪯ᶜᵗˣ Θ }}ad -> {{ ⊢ Θ }}a -> {{ ⊢ Θ' }}a -> {{ Θ' ⊢ˢ[ M ] e ⦂ Q }}ad.
Print Assumptions ad_ctx_precise_pat.

(* Consistency-subtyping transitivity *)
Check d_consis_sub_trans :
  forall M Δb Γ C B,
  {{ Δb ⨟ Γ ⊢[ M ] C ⩽ B }}d ->
  Δb [=] empty ->
  forall B_A C' Δt,
  C = btyp_to_utyp_syn B_A ->
  is_styp B_A ->
  {{ Δt ⨟ Γ ⊢ C' ∼ B_A }}d ->
  exists Δ, Δb [<=] Δ /\ {{ Δ ⨟ Γ ⊢[ M ] C' ⩽ B }}d.
Print Assumptions d_consis_sub_trans.

(* Order irrelevance of arguments *)
Check d_typing_order_irrel :
  forall Γ m n x y args args' A B',
  d_wf_denv Γ ->
  Permutation args args' ->
  binds x (dbind_typ (ptyp_forall_prefix n (curry_ptyp args A))) Γ ->
  binds y (dbind_typ (ptyp_forall_prefix n (curry_ptyp args' A))) Γ ->
  {{ Γ ⊢[ m ] (curry_exp (exp_var_f x) args) ⦂ B' }}d ->
  {{ Γ ⊢[ m ] (curry_exp (exp_var_f y) args') ⦂ B' }}d.
Print Assumptions d_typing_order_irrel.

(* Checking-mode subtyping subsumes shallow monotype subtyping *)
Check d_shallow_sub_complete :
  forall Γ A A',
  {{ Γ ⊢ A ≤ A' }}d ->
  {{ empty ⨟ Γ ⊢[ mode_tc ] (ptyp_to_utyp_syn A) ⩽ (ptyp_to_btyp_inh A') }}d.
Print Assumptions d_shallow_sub_complete.

(* Only polytypes need annotation *)
Check mono_lambda_anno_redundant :
  forall m Γ A e B2,
  mono_ptyp A ->
  {{ Γ ⊢[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B2) }}d ->
  {{ Γ ⊢[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B2) }}d.
Print Assumptions mono_lambda_anno_redundant.

(* Decidability of type inference *)
Check e_typing_dec_init :
  forall m P0 e,
  lc_pskl P0 -> lc_exp e ->
  sumbool (e_typable (entry_supply P0 e) m nil P0 e)
          (~ e_typable (entry_supply P0 e) m nil P0 e).
Print Assumptions e_typing_dec_init.

(* Decidability of type inference: the certified inference function *)
Check fresco_infer :
  forall e, {{ nil ⊢ᵉ e }}d ->
  sumor
    (sig (fun r : typing_result =>
       e_typing_run (entry_supply pskl_ghost e) mode_ti nil pskl_ghost e
         = Some r /\
       exists ζ, ζ ∷ (ty_ctx r) ⊑ nil /\
         {{ nil ⊢[ mode_ti ]
            e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ (ty_out r))) }}d))
    (~ exists B : btyp, {{ nil ⊢[ mode_ti ] e ⦂ B }}d).
Print Assumptions fresco_infer.
