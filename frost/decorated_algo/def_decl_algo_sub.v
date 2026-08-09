(** DECLARATIVE SUBTYPING IN ALGORITHMIC CONTEXTS + PARTIAL PRECISION.

    The two judgments the subtyping soundness/completeness proofs are stated
    against (docs/DESIGN-subtyping.md §1.2, D1/D4):

    - [ad_pat_sub]: the paper's all-in-one declarative subtyping
      [typsub^N_M[Ψ] Θ ⊢ syn R ⩽ bid Q] (fig:decl-subtyping-all,
      full-decl-spec.tex:33-121) transplanted to algorithmic contexts, with
      the single flexible-variable rule the paper adds there — [FlexMono]
      (fig:declarative-in-algo-context, full-algo-spec.tex:170-176; LHS
      flexible in FUNCTION mode only; targets' flexibles are reached through
      the consistency premises' own FlexR).  The transplant mirrors the
      SETTLED formulations of the mech's [d_pat_sub] (decl/def_extra.v:479 —
      the WT-reviewed skeleton side: [is_sskl]/guardedness on
      Infer/UnivGhostR, [mod_comp_sk] on Ghost/GhostG, the scope premise on
      ForallL) and, for the TY-only rules Check/ForallR absent from
      [d_pat_sub], the fused appendix figure directly.  The N-indexed tag
      premise of ForallL is [a_tags_sort] (def_decorated.v:96), exactly as in
      the decorated algorithmic system [a_subtag].

    - [ad_partial_precise]: partial precision [Θ ⨟ Δ ⊢ᵃᵈ P ⊑ᵖ[Ψ] ψ]
      (subtyping-proofs.tex:1561-1637), the completeness-only refinement of
      precision: quantifiers of ψ whose tags are NOT in Ψ may be matched by
      ghosts in P.  Its definition "corresponds one to one to the definition
      of refinement in algorithmic contexts" (tex:1552-1554), so it mirrors
      [ad_refine_pskl] (def_decl_algo.v:198) — including the placements the
      mech settled there for the paper's external wf side conditions
      (docs/WF-SIDE-CONDITIONS.md): the var rule carries the
      [Δ ∨ a_binds_tvar] visibility disjunction, the ∀-rule extends only Δ
      (the rigid binder is picked cofinitely), tophole_fill extends Θ.
      Targets ψ are decorated skeletons, so their quantifiers are always
      tagged ([uskl_all_etag]; [is_tskl] has no [all_syn] constructor) and
      their ghosts dotted — the subject-hole rule is the only rule matching
      a dotted ghost. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decorated.

Set Implicit Arguments.

(* ===================================================================== *)
(*  All-in-one declarative subtyping over Θ                               *)
(*  [Ψ ⨟ Θ ⊢ᵃᵈ[ N | M ] R ⩽ Q]  (fig:decl-subtyping-all + FlexMono)       *)
(* ===================================================================== *)

Reserved Notation "Ψ ⨟ Θ ⊢ᵃᵈ[ NM | M ] R ⩽ Q"
  (at level 75, Θ at level 74, NM at level 0, M at level 0,
   R at level 74, Q at level 74, no associativity).

Inductive ad_pat_sub :
  a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub__infer : forall NM Ψ Θ R Q,                      (* Infer *)
    Ψ [=] empty ->
    empty ⨟ Θ ⊢ᵃᵈ R ∼ Q ->
    is_sskl Q ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ NM | mode_ti ] R ⩽ Q
| ad_pat_sub__check : forall Ψ Θ T B,                         (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    Ψ ⨟ Θ ⊢ᵃᵈ T ∼ (pskl_to_bskl_inh B) ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ a_sub_mode_ty | mode_tc ] T ⩽ (pskl_to_bskl_inh B)
| ad_pat_sub__forall_r : forall L Ψ Θ T B,                    (* ForallR (TY) *)
    (forall α, α `notin` L ->
       Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ᵃᵈ[ a_sub_mode_ty | mode_tc ]
         T ⩽ (open_bskl_wrt_bskl B (bskl_var_f α))) ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ a_sub_mode_ty | mode_tc ] T ⩽ (bskl_all_inh B)
| ad_pat_sub__univ_ghost_r : forall Ψ Θ R Q,                  (* UnivGhostR (SK) *)
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    empty ⨟ Θ ⊢ᵃᵈ R ∼ Q ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ a_sub_mode_sk | mode_tc ] R ⩽ (bskl_tophole Q)
| ad_pat_sub__arrow : forall NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2,      (* Arrow *)
    Ψ1 ⨟ Θ ⊢ᵃᵈ R1 ∼ Q1 ->
    Ψ2 ⨟ Θ ⊢ᵃᵈ[ NM | M ] R2 ⩽ Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ NM | mode_fn M ] (uskl_arrow R1 R2) ⩽ (bskl_arrow Q1 Q2)
| ad_pat_sub__forall_l_tagged : forall NM Ψ Ψ' Θ M ε R ψ Q,   (* ForallL, β1=ε *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    (Ψ `union` Ψ') ⨟ Θ ⊢ᵃᵈ[ NM | M ] (open_uskl_wrt_uskl R ψ) ⩽ Q ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ NM | M ] (uskl_all_etag ε R) ⩽ Q
| ad_pat_sub__forall_l_untagged : forall NM Ψ Ψ' Θ M R ψ Q,   (* ForallL, β1=· *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    (Ψ `union` Ψ') ⨟ Θ ⊢ᵃᵈ[ NM | M ] (open_uskl_wrt_uskl R ψ) ⩽ Q ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ NM | M ] (uskl_all_syn R) ⩽ Q
| ad_pat_sub__ghost : forall Ψ Θ M P,                         (* Ghost (SK) *)
    Ψ [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ P ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ a_sub_mode_sk | M ] uskl_hole ⩽ (pskl_to_bskl_inh P)
| ad_pat_sub__ghostg : forall Ψ Θ M,                          (* GhostG (SK) *)
    Ψ [=] empty ->
    mod_comp_sk bskl_hole M ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ a_sub_mode_sk | M ] uskl_holeg ⩽ bskl_hole
| ad_pat_sub__univ_ghost_l : forall Ψ Θ M R Q,                (* UnivGhostL (SK) *)
    M <> mode_ti ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ a_sub_mode_sk | M ] R ⩽ Q ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ a_sub_mode_sk | M ] (uskl_tophole R) ⩽ Q
| ad_pat_sub__univ_ghost_lg : forall Ψ Θ M R Q,               (* UnivGhostLG (SK) *)
    M <> mode_ti ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ a_sub_mode_sk | M ] R ⩽ Q ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ a_sub_mode_sk | M ] (uskl_topholeg R) ⩽ Q
(* — the algorithmic-context lookup rule (fig:declarative-in-algo-context) — *)
| ad_pat_sub__flex_mono : forall NM Ψ Θ M α τ Q,              (* FlexMono *)
    binds α (abind_flex_mono_def τ) Θ ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ NM | mode_fn M ] (ptyp_to_uskl_syn τ) ⩽ Q ->
    Ψ ⨟ Θ ⊢ᵃᵈ[ NM | mode_fn M ] (uskl_var_f α) ⩽ Q
where "Ψ ⨟ Θ ⊢ᵃᵈ[ NM | M ] R ⩽ Q" :=
  (ad_pat_sub NM M Ψ Θ R Q) : type_scope.

(* ===================================================================== *)
(*  Fuel-indexed mirror of [ad_pat_sub]  (completeness measure).           *)
(*                                                                         *)
(*  The completeness induction is on the HEIGHT of the declarative         *)
(*  subtyping derivation (subtyping-proofs.tex:3082-3085), and its ForallL *)
(*  case applies the IH to a derivation PRODUCED BY precision-substitution *)
(*  — not a structural sub-derivation — so plain induction on [ad_pat_sub] *)
(*  gives no IH there.  [ad_pat_sub] is in [Prop], so we cannot extract a  *)
(*  structural [nat] size; instead we mirror it with an explicit fuel [n]. *)
(*                                                                         *)
(*  This is a SEPARATE inductive (not a re-indexing of [ad_pat_sub]) so it *)
(*  does not cascade into the finished, Qed soundness proofs.  Bridges     *)
(*  [ad_pat_sub_of_n] / [ad_pat_sub_to_n] / [ad_pat_sub_n_mono] live in    *)
(*  [prop_sub_complete.v].  Each rule has AT MOST ONE recursive            *)
(*  [ad_pat_sub] premise (the [a_consis]/[a_tags_sort]/refinement premises *)
(*  are other judgments), so a single fuel = the derivation height.  Rules *)
(*  conclude at [S n] with their recursive premise at [n]; leaves take any *)
(*  [n].  See docs/DESIGN-completeness-subtyping.md §2.                     *)
(* ===================================================================== *)

Inductive ad_pat_sub_n :
  nat -> a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub_n__infer : forall n NM Ψ Θ R Q,                  (* Infer *)
    Ψ [=] empty ->
    empty ⨟ Θ ⊢ᵃᵈ R ∼ Q ->
    is_sskl Q ->
    ad_pat_sub_n (S n) NM mode_ti Ψ Θ R Q
| ad_pat_sub_n__check : forall n Ψ Θ T B,                     (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    Ψ ⨟ Θ ⊢ᵃᵈ T ∼ (pskl_to_bskl_inh B) ->
    ad_pat_sub_n (S n) a_sub_mode_ty mode_tc Ψ Θ T (pskl_to_bskl_inh B)
| ad_pat_sub_n__forall_r : forall n L Ψ Θ T B,               (* ForallR (TY) *)
    (forall α, α `notin` L ->
       ad_pat_sub_n n a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ)
         T (open_bskl_wrt_bskl B (bskl_var_f α))) ->
    ad_pat_sub_n (S n) a_sub_mode_ty mode_tc Ψ Θ T (bskl_all_inh B)
| ad_pat_sub_n__univ_ghost_r : forall n Ψ Θ R Q,             (* UnivGhostR (SK) *)
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    empty ⨟ Θ ⊢ᵃᵈ R ∼ Q ->
    ad_pat_sub_n (S n) a_sub_mode_sk mode_tc Ψ Θ R (bskl_tophole Q)
| ad_pat_sub_n__arrow : forall n NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2, (* Arrow *)
    Ψ1 ⨟ Θ ⊢ᵃᵈ R1 ∼ Q1 ->
    ad_pat_sub_n n NM M Ψ2 Θ R2 Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    ad_pat_sub_n (S n) NM (mode_fn M) Ψ Θ (uskl_arrow R1 R2) (bskl_arrow Q1 Q2)
| ad_pat_sub_n__forall_l_tagged : forall n NM Ψ Ψ' Θ M ε R ψ Q, (* ForallL, β1=ε *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_n n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_n (S n) NM M Ψ Θ (uskl_all_etag ε R) Q
| ad_pat_sub_n__forall_l_untagged : forall n NM Ψ Ψ' Θ M R ψ Q, (* ForallL, β1=· *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_n n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_n (S n) NM M Ψ Θ (uskl_all_syn R) Q
| ad_pat_sub_n__ghost : forall n Ψ Θ M P,                     (* Ghost (SK) *)
    Ψ [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ P ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    ad_pat_sub_n (S n) a_sub_mode_sk M Ψ Θ uskl_hole (pskl_to_bskl_inh P)
| ad_pat_sub_n__ghostg : forall n Ψ Θ M,                      (* GhostG (SK) *)
    Ψ [=] empty ->
    mod_comp_sk bskl_hole M ->
    ad_pat_sub_n (S n) a_sub_mode_sk M Ψ Θ uskl_holeg bskl_hole
| ad_pat_sub_n__univ_ghost_l : forall n Ψ Θ M R Q,           (* UnivGhostL (SK) *)
    M <> mode_ti ->
    ad_pat_sub_n n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_n (S n) a_sub_mode_sk M Ψ Θ (uskl_tophole R) Q
| ad_pat_sub_n__univ_ghost_lg : forall n Ψ Θ M R Q,          (* UnivGhostLG (SK) *)
    M <> mode_ti ->
    ad_pat_sub_n n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_n (S n) a_sub_mode_sk M Ψ Θ (uskl_topholeg R) Q
| ad_pat_sub_n__flex_mono : forall n NM Ψ Θ M α τ Q,          (* FlexMono *)
    binds α (abind_flex_mono_def τ) Θ ->
    ad_pat_sub_n n NM (mode_fn M) Ψ Θ (ptyp_to_uskl_syn τ) Q ->
    ad_pat_sub_n (S n) NM (mode_fn M) Ψ Θ (uskl_var_f α) Q.

(* ===================================================================== *)
(*  Partial precision  [Θ ⨟ Δ ⊢ᵃᵈ P ⊑ᵖ[ Ψ ] ψ]                              *)
(*  (subtyping-proofs.tex:1561-1637; the ad_refine_pskl mirror with tags) *)
(* ===================================================================== *)

Reserved Notation "Θ ⨟ Δ ⊢ᵃᵈ P ⊑ᵖ[ Ψ ] ψ"
  (at level 75, Δ at level 74, P at level 74, Ψ at level 0, ψ at level 74,
   no associativity).

Inductive ad_partial_precise :
  aenv -> atoms -> atoms -> pskl -> uskl -> Prop :=
| ad_ppre__unit : forall Θ Δ Ψ,
    Ψ [=] empty ->
    Θ ⨟ Δ ⊢ᵃᵈ pskl_unit ⊑ᵖ[ Ψ ] uskl_unit
| ad_ppre__var : forall Θ Δ Ψ α,
    Ψ [=] empty ->
    α `in` Δ \/ a_binds_tvar α Θ ->
    Θ ⨟ Δ ⊢ᵃᵈ (pskl_var_f α) ⊑ᵖ[ Ψ ] (uskl_var_f α)
| ad_ppre__arrow : forall Θ Δ Ψ Ψ1 Ψ2 P1 P2 ψ1 ψ2,
    Θ ⨟ Δ ⊢ᵃᵈ P1 ⊑ᵖ[ Ψ1 ] ψ1 ->
    Θ ⨟ Δ ⊢ᵃᵈ P2 ⊑ᵖ[ Ψ2 ] ψ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    Θ ⨟ Δ ⊢ᵃᵈ (pskl_arrow P1 P2) ⊑ᵖ[ Ψ ] (uskl_arrow ψ1 ψ2)
| ad_ppre__forall : forall L Θ Δ Ψ Ψ0 ε P ψ,
    (forall α, α `notin` L ->
       Θ ⨟ (add α Δ) ⊢ᵃᵈ (open_pskl_wrt_pskl P (pskl_var_f α))
         ⊑ᵖ[ Ψ0 ] (open_uskl_wrt_uskl ψ (uskl_var_f α))) ->
    Ψ [=] add ε Ψ0 ->
    Θ ⨟ Δ ⊢ᵃᵈ (pskl_all_syn P) ⊑ᵖ[ Ψ ] (uskl_all_etag ε ψ)
| ad_ppre__hole : forall Θ Δ Ψ ψ,
    Ψ [=] empty ->
    Δ ∩ ftvar_in_uskl ψ [=] empty ->
    Θ ⨟ Δ ⊢ᵃᵈ pskl_hole ⊑ᵖ[ Ψ ] ψ
| ad_ppre__tophole_remove : forall Θ Δ Ψ P ψ,
    Θ ⨟ Δ ⊢ᵃᵈ P ⊑ᵖ[ Ψ ] ψ ->
    Θ ⨟ Δ ⊢ᵃᵈ (pskl_tophole P) ⊑ᵖ[ Ψ ] ψ
| ad_ppre__tophole_fill : forall L Θ Δ Ψ P ψ,
    (forall α, α `notin` L ->
       ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵃᵈ (pskl_tophole P)
         ⊑ᵖ[ Ψ ] (open_uskl_wrt_uskl ψ (uskl_var_f α))) ->
    forall ε,
    Θ ⨟ Δ ⊢ᵃᵈ (pskl_tophole P) ⊑ᵖ[ Ψ ] (uskl_all_etag ε ψ)
| ad_ppre__tophole_keep : forall Θ Δ Ψ P ψ,
    Θ ⨟ Δ ⊢ᵃᵈ P ⊑ᵖ[ Ψ ] ψ ->
    Θ ⨟ Δ ⊢ᵃᵈ (pskl_tophole P) ⊑ᵖ[ Ψ ] (uskl_topholeg ψ)
(* — flexible-variable lookups (fig:declarative-in-algo-context style) — *)
| ad_ppre__flex_l : forall Θ Δ Ψ α τ ψ,
    binds α (abind_flex_mono_def τ) Θ ->
    Θ ⨟ Δ ⊢ᵃᵈ (ptyp_to_pskl τ) ⊑ᵖ[ Ψ ] ψ ->
    Θ ⨟ Δ ⊢ᵃᵈ (pskl_var_f α) ⊑ᵖ[ Ψ ] ψ
| ad_ppre__flex_r : forall Θ Δ Ψ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    Θ ⨟ Δ ⊢ᵃᵈ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) ->
    Θ ⨟ Δ ⊢ᵃᵈ P ⊑ᵖ[ Ψ ] (uskl_var_f α)
where "Θ ⨟ Δ ⊢ᵃᵈ P ⊑ᵖ[ Ψ ] ψ" :=
  (ad_partial_precise Θ Δ Ψ P ψ) : type_scope.
