(** TAG-HYGIENIC FUEL MIRROR of [ad_pat_sub] (completeness-only).

    [ad_pat_sub_g] refines [ad_pat_sub_n] (def_decl_algo_sub.v) in two ways,
    both forced by precision-substitution
    (docs/DESIGN-completeness-subtyping.md §5.4):

    1. TAG HYGIENE.  The paper's ForallL side condition [fresh Ψ'] means the
       instantiation's tags are GLOBALLY fresh; the [_n] mirror renders it
       only as freshness from the tag context, which does not survive the
       Arrow split (a tag can leave the context on one branch while the
       subject still carries it on the other), and precision-substitution
       is FALSE over such derivations.  Both ForallL rules therefore also
       require the instantiation's tags fresh from the SUBJECT's syntactic
       tags ([ftag_in_uskl], def_tags.v).

    2. FUEL DISCIPLINE.  Precision-substitution must be fuel-PRESERVING
       (the completeness ForallL case applies its induction hypothesis to
       the substituted premise, subtyping-proofs.tex:3416-3429), but the
       ghostier subject may carry extra [⊤◇]-wrappers (UnivGhostL steps)
       or fold flexible definitions (FlexMono steps) that the original
       derivation does not have.  So: leaves conclude at ANY fuel,
       UnivGhostL/UnivGhostLG/FlexMono are NON-incrementing, and only
       Arrow/ForallR/ForallL increment — which is all the completeness
       measure needs (its ForallL premise still strictly decreases; the
       non-incrementing rules recurse on structural sub-derivations, so
       the main induction uses lex(fuel, derivation)).

    Bridges ([_g] erasure to the plain judgment; the renaming-based
    freshening [_n → _g]) live in prop_sub_complete.v / are deferred —
    see the DESIGN doc. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_tags.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.

Set Implicit Arguments.

Inductive ad_pat_sub_g :
  nat -> a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub_g__infer : forall n NM Ψ Θ R Q,                  (* Infer *)
    Ψ [=] empty ->
    empty ⨟ Θ ⊢ₛᵃ R ∼ Q ->
    is_sskl Q ->
    ad_pat_sub_g n NM mode_ti Ψ Θ R Q
| ad_pat_sub_g__check : forall n Ψ Θ T B,                     (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    Ψ ⨟ Θ ⊢ₛᵃ T ∼ (pskl_to_bskl_inh B) ->
    ad_pat_sub_g n a_sub_mode_ty mode_tc Ψ Θ T (pskl_to_bskl_inh B)
| ad_pat_sub_g__forall_r : forall n L Ψ Θ T B,               (* ForallR (TY) *)
    (forall α, α `notin` L ->
       ad_pat_sub_g n a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ)
         T (open_bskl_wrt_bskl B (bskl_var_f α))) ->
    ad_pat_sub_g (S n) a_sub_mode_ty mode_tc Ψ Θ T (bskl_all_inh B)
| ad_pat_sub_g__univ_ghost_r : forall n Ψ Θ R Q,             (* UnivGhostR (SK) *)
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    empty ⨟ Θ ⊢ₛᵃ R ∼ Q ->
    ad_pat_sub_g n a_sub_mode_sk mode_tc Ψ Θ R (bskl_tophole Q)
| ad_pat_sub_g__arrow : forall n NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2, (* Arrow *)
    Ψ1 ⨟ Θ ⊢ₛᵃ R1 ∼ Q1 ->
    ad_pat_sub_g n NM M Ψ2 Θ R2 Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    ad_pat_sub_g (S n) NM (mode_fn M) Ψ Θ (uskl_arrow R1 R2) (bskl_arrow Q1 Q2)
| ad_pat_sub_g__forall_l_tagged : forall n NM Ψ Ψ' Θ M ε R ψ Q, (* ForallL, δ=ε *)
    M <> mode_ti ->
    AtomSetImpl.inter Ψ' Ψ [=] empty ->
    AtomSetImpl.inter Ψ' (ftag_in_uskl (uskl_all_etag ε R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_g n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_g (S n) NM M Ψ Θ (uskl_all_etag ε R) Q
| ad_pat_sub_g__forall_l_untagged : forall n NM Ψ Ψ' Θ M R ψ Q, (* ForallL, δ=· *)
    M <> mode_ti ->
    AtomSetImpl.inter Ψ' Ψ [=] empty ->
    AtomSetImpl.inter Ψ' (ftag_in_uskl (uskl_all_syn R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_g n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_g (S n) NM M Ψ Θ (uskl_all_syn R) Q
| ad_pat_sub_g__ghost : forall n Ψ Θ M P,                     (* Ghost (SK) *)
    Ψ [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ P ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ uskl_hole (pskl_to_bskl_inh P)
| ad_pat_sub_g__ghostg : forall n Ψ Θ M,                      (* GhostG (SK) *)
    Ψ [=] empty ->
    mod_comp_sk bskl_hole M ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ uskl_holeg bskl_hole
| ad_pat_sub_g__univ_ghost_l : forall n Ψ Θ M R Q,           (* UnivGhostL (SK) *)
    M <> mode_ti ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ (uskl_tophole R) Q
| ad_pat_sub_g__univ_ghost_lg : forall n Ψ Θ M R Q,          (* UnivGhostLG (SK) *)
    M <> mode_ti ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ (uskl_topholeg R) Q
| ad_pat_sub_g__flex_mono : forall n NM Ψ Θ M α τ Q,          (* FlexMono *)
    binds α (abind_flex_mono_def τ) Θ ->
    ad_pat_sub_g n NM (mode_fn M) Ψ Θ (ptyp_to_uskl_syn τ) Q ->
    ad_pat_sub_g n NM (mode_fn M) Ψ Θ (uskl_var_f α) Q.
