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
      SETTLED formulations of the mech's [d_pat_sub] (decl/def_rules.v —
      [is_sskl]/guardedness on Infer/UnivGhostR, [mod_comp_sk] on
      Ghost/GhostG, the scope premise on ForallL) and, for the TY-only rules
      Check/ForallR absent from [d_pat_sub], the fused appendix figure
      directly.  The N-indexed tag premise of ForallL is [a_tags_sort]
      (deco_algo/def_decorated.v), exactly as in
      the decorated algorithmic system [a_subtag].

    - [ad_partial_precise]: partial precision [{{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[Ψ] ψ }}ad]
      (subtyping-proofs.tex:1561-1637), the completeness-only refinement of
      precision: quantifiers of ψ whose tags are NOT in Ψ may be matched by
      ghosts in P.  Its definition "corresponds one to one to the definition
      of refinement in algorithmic contexts" (tex:1552-1554), so it mirrors
      [ad_refine_pskl] (def_consis_refine.v) rule for rule: no scoping
      premises (well-formedness is a presupposition), the ∀-rule extends both
      Θ and Δ, univ_ghost_fill extends Θ.
      Targets ψ are decorated skeletons, so their quantifiers are always
      tagged ([uskl_all_tag]; [is_dskl] has no [all_syn] constructor) and
      their ghosts dotted — the subject-ghost rule is the only rule matching
      a dotted ghost. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope fresco_ad_scope.

(* ===================================================================== *)
(*  All-in-one declarative subtyping over Θ                               *)
(*  [{{ Ψ ⨟ Θ ⊢ˢ[ N | M ] R ⩽ Q }}ad]  (fig:decl-subtyping-all + FlexMono) *)
(* ===================================================================== *)

Reserved Notation "{{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad"
  (at level 0, Θ at level 74, NM at level 0, M at level 0, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Θ  ⊢ˢ[  NM  |  M  ]  R  ⩽  Q  '}}ad'").

Inductive ad_pat_sub :
  a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub__infer : forall NM Ψ Θ R Q,                      (* Infer *)
    Ψ [=] empty ->
    {{ empty ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
    is_sskl Q ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_ti ] R ⩽ Q }}ad
| ad_pat_sub__check : forall Ψ Θ T B,                         (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    {{ Ψ ⨟ Θ ⊢ˢ T ∼ᵣ (pskl_to_bskl_inh B) }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_ty | mode_tc ] T ⩽ (pskl_to_bskl_inh B) }}ad
| ad_pat_sub__forall_r : forall L Ψ Θ T B,                    (* ForallR (TY) *)
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ[ a_sub_mode_ty | mode_tc ]
         T ⩽ (open_bskl_wrt_bskl B (bskl_var_f α)) }}ad) ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_ty | mode_tc ] T ⩽ (bskl_all_inh B) }}ad
| ad_pat_sub__univ_ghost_r : forall Ψ Θ R Q,                  (* UnivGhostR (SK) *)
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    {{ empty ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | mode_tc ] R ⩽ (bskl_univ_ghost Q) }}ad
| ad_pat_sub__arrow : forall NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2,      (* Arrow *)
    (* the DOMAIN premise is itself a consistency leaf, hence a join *)
    {{ Ψ1 ⨟ Θ ⊢ˢ R1 ∼ᵣ Q1 }}ad ->
    {{ Ψ2 ⨟ Θ ⊢ˢ[ NM | M ] R2 ⩽ Q2 }}ad ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_fn M ] (uskl_arrow R1 R2) ⩽ (bskl_arrow Q1 Q2) }}ad
| ad_pat_sub__forall_l_tagged : forall NM Ψ Ψ' Θ M ε R ψ Q,   (* ForallL, β1=ε *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_tag ε R)) [=] empty ->  (* GLOBAL freshness *)
    a_tags_sort NM Ψ' ψ ->
    {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a ->
    {{ (Ψ `union` Ψ') ⨟ Θ ⊢ˢ[ NM | M ] (open_uskl_wrt_uskl R ψ) ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] (uskl_all_tag ε R) ⩽ Q }}ad
| ad_pat_sub__forall_l_untagged : forall NM Ψ Ψ' Θ M R ψ Q,   (* ForallL, β1=· *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_syn R)) [=] empty ->     (* GLOBAL freshness *)
    a_tags_sort NM Ψ' ψ ->
    {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a ->
    {{ (Ψ `union` Ψ') ⨟ Θ ⊢ˢ[ NM | M ] (open_uskl_wrt_uskl R ψ) ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] (uskl_all_syn R) ⩽ Q }}ad
| ad_pat_sub__ghost : forall Ψ Θ M P,                         (* Ghost (SK) *)
    (* Paper [Ghost]: no premise on the fill, as [d_pat_sub__ghost] and
       [ad_pat_consis__ghost].  docs/WF-SIDE-CONDITIONS.md §2a. *)
    Ψ [=] empty ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] uskl_ghost ⩽ (pskl_to_bskl_inh P) }}ad
| ad_pat_sub__ghostg : forall Ψ Θ M,                          (* GhostG (SK) *)
    Ψ [=] empty ->
    mod_comp_sk bskl_ghost M ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] uskl_dot_ghost ⩽ bskl_ghost }}ad
| ad_pat_sub__univ_ghost_l : forall Ψ Θ M R Q,                (* UnivGhostL (SK) *)
    M <> mode_ti ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] R ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] (uskl_univ_ghost R) ⩽ Q }}ad
| ad_pat_sub__univ_ghost_lg : forall Ψ Θ M R Q,               (* UnivGhostLG (SK) *)
    M <> mode_ti ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] R ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] (uskl_dot_univ_ghost R) ⩽ Q }}ad
(* — the algorithmic-context lookup rule (fig:declarative-in-algo-context) — *)
| ad_pat_sub__flex_mono : forall NM Ψ Θ M α τ Q,              (* FlexMono *)
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_fn M ] (ptyp_to_uskl_syn τ) ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_fn M ] (uskl_var_f α) ⩽ Q }}ad
where "{{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad" :=
  (ad_pat_sub NM M Ψ Θ R Q) : fresco_ad_scope.

(* ⚙ There is deliberately no non-hygienic fuel mirror ([ad_pat_sub_n]):
   nothing consumed one.  The completeness measure is [ad_pat_sub_fuel] below;
   a second mirror would have to be bridged to [ad_pat_sub] all over again. *)

(** [ad_pat_sub_fuel] is [ad_pat_sub] with the completeness measure made
    visible: it differs in the FUEL discipline only.  Tag hygiene (ForallL's
    [fresh Ψ'] read GLOBALLY — fresh from the subject's own tags too, since
    the context-local reading does not survive the Arrow split and
    precision-substitution is FALSE without it; docs/PAPER-GAPS.md) and the
    leaf presupposition are carried by [ad_pat_sub] itself.

    FUEL DISCIPLINE.  Precision-substitution must be fuel-PRESERVING
       (the completeness ForallL case applies its induction hypothesis to
       the substituted premise, subtyping-proofs.tex:3416-3429), but the
       ghostier subject may carry extra [∀◇]-wrappers (UnivGhostL steps)
       or fold flexible definitions (FlexMono steps) that the original
       derivation does not have.  So: leaves conclude at ANY fuel,
       UnivGhostL/UnivGhostLG/FlexMono are NON-incrementing, and only
       Arrow/ForallR/ForallL increment — which is all the completeness
       measure needs (its ForallL premise still strictly decreases; the
       non-incrementing rules recurse on structural sub-derivations, so
       the main induction uses lex(fuel, derivation)).

    ⭐ THE TWO RELATIONS ARE INTERDERIVABLE: [ad_pat_sub_of_fuel]
    (prop_ctx_mono.v) and [ad_pat_sub_to_fuel] (algo/subtyping/prop_soundness_subtag.v),
    unconditional at either sort over any Θ — the fuel is the derivation's
    height.  This relation appears NOWHERE outside the completeness proof:
    every rule and every other statement in the tree uses [ad_pat_sub]. *)

(* ===================================================================== *)
(*  [ad_pat_sub_fuel] (completeness-only, P7's join): [ad_pat_sub] + FUEL.   *)
(*                                                                        *)
(*  ⭐ The four CONSISTENCY-LEAF rows — [__infer], [__check],              *)
(*  [__univ_ghost_r] and [__arrow]'s DOMAIN — carry the SUBJECT's         *)
(*  refinement into the leaf's counterpart (for [UnivGhostR], into the    *)
(*  STRIPPED counterpart [Q], not [∀◇.Q]), exactly as [ad_pat_sub] does.  *)
(*                                                                        *)
(*  WHY.  thm:complete-subtyping needs, at each leaf, exactly the third   *)
(*  solution condition of the AUGMENTED thm:complete-consistency          *)
(*  (consistency-proofs.tex:2230-2242) for the consistency subproblem it  *)
(*  invokes there — and that condition is NOT derivable from the paper's  *)
(*  two subtyping-solution conditions (the capture configuration          *)
(*  [(P0=◇, P=∀X.◇, Q=∀X.X)] passes both).  Stating it at the ROOT        *)
(*  instead — as one [{{ … ⊢ᵣₚ κ⌊S⌋ˢ ⊳ ⌊Q⌋ }}ad] premise on the theorem — is       *)
(*  WRONG: refinement is a lockstep relation, so a root condition         *)
(*  excludes every solution whose sides disagree at a head through       *)
(*  ForallL / ForallR / UnivGhostR, i.e. instantiation and               *)
(*  generalisation themselves (machine-checked:                          *)
(*  cex/cex_p7_univ_ghost_r_vacuous.v, cex/cex_p7_third_premise_forall.v).*)
(*  The ghost leaves [__ghost] / [__ghostg] need no condition: they do    *)
(*  not invoke consistency completeness, and their subject's refinement   *)
(*  is derivable from the rule's own wf premise.                          *)
(*                                                                        *)
(* ===================================================================== *)

Inductive ad_pat_sub_fuel :
  nat -> a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub_fuel__infer : forall n NM Ψ Θ R Q,                 (* Infer *)
    Ψ [=] empty ->
    {{ empty ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
    is_sskl Q ->
    ad_pat_sub_fuel n NM mode_ti Ψ Θ R Q
| ad_pat_sub_fuel__check : forall n Ψ Θ T B,                    (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    {{ Ψ ⨟ Θ ⊢ˢ T ∼ᵣ (pskl_to_bskl_inh B) }}ad ->
    ad_pat_sub_fuel n a_sub_mode_ty mode_tc Ψ Θ T (pskl_to_bskl_inh B)
| ad_pat_sub_fuel__forall_r : forall n L Ψ Θ T B,              (* ForallR (TY) *)
    (forall α, α `notin` L ->
       ad_pat_sub_fuel n a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ)
         T (open_bskl_wrt_bskl B (bskl_var_f α))) ->
    ad_pat_sub_fuel (S n) a_sub_mode_ty mode_tc Ψ Θ T (bskl_all_inh B)
| ad_pat_sub_fuel__univ_ghost_r : forall n Ψ Θ R Q,            (* UnivGhostR (SK) *)
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    {{ empty ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
    ad_pat_sub_fuel n a_sub_mode_sk mode_tc Ψ Θ R (bskl_univ_ghost Q)
| ad_pat_sub_fuel__arrow : forall n NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2, (* Arrow *)
    (* the DOMAIN premise is itself a consistency leaf — Sub-Arrow invokes
       thm:complete-consistency on it (:3334), so it carries the same
       subject-refinement data as [__infer] *)
    {{ Ψ1 ⨟ Θ ⊢ˢ R1 ∼ᵣ Q1 }}ad ->
    ad_pat_sub_fuel n NM M Ψ2 Θ R2 Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    ad_pat_sub_fuel (S n) NM (mode_fn M) Ψ Θ (uskl_arrow R1 R2) (bskl_arrow Q1 Q2)
| ad_pat_sub_fuel__forall_l_tagged : forall n NM Ψ Ψ' Θ M ε R ψ Q, (* ForallL, β1=ε *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_tag ε R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a ->
    ad_pat_sub_fuel n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_fuel (S n) NM M Ψ Θ (uskl_all_tag ε R) Q
| ad_pat_sub_fuel__forall_l_untagged : forall n NM Ψ Ψ' Θ M R ψ Q, (* ForallL, β1=· *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_syn R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a ->
    ad_pat_sub_fuel n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_fuel (S n) NM M Ψ Θ (uskl_all_syn R) Q
| ad_pat_sub_fuel__ghost : forall n Ψ Θ M P,                    (* Ghost (SK) *)
    (* no fill premise, as [ad_pat_sub__ghost] *)
    Ψ [=] empty ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ uskl_ghost (pskl_to_bskl_inh P)
| ad_pat_sub_fuel__ghostg : forall n Ψ Θ M,                     (* GhostG (SK) *)
    Ψ [=] empty ->
    mod_comp_sk bskl_ghost M ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ uskl_dot_ghost bskl_ghost
| ad_pat_sub_fuel__univ_ghost_l : forall n Ψ Θ M R Q,          (* UnivGhostL (SK) *)
    M <> mode_ti ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ (uskl_univ_ghost R) Q
| ad_pat_sub_fuel__univ_ghost_lg : forall n Ψ Θ M R Q,         (* UnivGhostLG (SK) *)
    M <> mode_ti ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ (uskl_dot_univ_ghost R) Q
| ad_pat_sub_fuel__flex_mono : forall n NM Ψ Θ M α τ Q,         (* FlexMono *)
    binds α (abind_flex_mono_def τ) Θ ->
    ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ (ptyp_to_uskl_syn τ) Q ->
    ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ (uskl_var_f α) Q.

(* ⚙ There is no existentially-fuelled [ad_pat_sub_v]: [ad_pat] /
   [ad_sd_typing] embed [ad_pat_sub] directly, which the two bridges above
   make interderivable with the fuelled relation. *)

(* ===================================================================== *)
(*  Partial precision  [{{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad]                       *)
(*  (subtyping-proofs.tex:1561-1637; the ad_refine_pskl mirror with tags) *)
(* ===================================================================== *)

(* The paper's partial-precision rules, rule for rule: like the refinement
   relations it mirrors, it carries no scoping premises (well-formedness is
   the paper's presupposition, carried as a hypothesis by the lemmas that
   need it), and its [∀] row extends both [Θ] and [Δ]. *)

Reserved Notation "{{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad"
  (at level 0, Δ at level 74, P at level 74, Ψ at level 0, ψ at level 74,
   format "'{{'  Θ  ⨟  Δ  ⊢ˢ  P  ⊑ᵖ[  Ψ  ]  ψ  '}}ad'").

Inductive ad_partial_precise :
  aenv -> atoms -> atoms -> pskl -> uskl -> Prop :=
| ad_ppre__unit : forall Θ Δ Ψ,
    Ψ [=] empty ->
    {{ Θ ⨟ Δ ⊢ˢ pskl_unit ⊑ᵖ[ Ψ ] uskl_unit }}ad
| ad_ppre__var : forall Θ Δ Ψ α,
    Ψ [=] empty ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_var_f α) ⊑ᵖ[ Ψ ] (uskl_var_f α) }}ad
| ad_ppre__arrow : forall Θ Δ Ψ Ψ1 Ψ2 P1 P2 ψ1 ψ2,
    {{ Θ ⨟ Δ ⊢ˢ P1 ⊑ᵖ[ Ψ1 ] ψ1 }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ P2 ⊑ᵖ[ Ψ2 ] ψ2 }}ad ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_arrow P1 P2) ⊑ᵖ[ Ψ ] (uskl_arrow ψ1 ψ2) }}ad
| ad_ppre__forall : forall L Θ Δ Ψ Ψ0 ε P ψ,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ˢ
         (open_pskl_wrt_pskl P (pskl_var_f α))
         ⊑ᵖ[ Ψ0 ] (open_uskl_wrt_uskl ψ (uskl_var_f α)) }}ad) ->
    Ψ [=] add ε Ψ0 ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_all_syn P) ⊑ᵖ[ Ψ ] (uskl_all_tag ε ψ) }}ad
| ad_ppre__ghost : forall Θ Δ Ψ ψ,
    Ψ [=] empty ->
    Δ ∩ ftvar_in_uskl ψ [=] empty ->
    {{ Θ ⨟ Δ ⊢ˢ pskl_ghost ⊑ᵖ[ Ψ ] ψ }}ad
| ad_ppre__univ_ghost_remove : forall Θ Δ Ψ P ψ,
    {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_univ_ghost P) ⊑ᵖ[ Ψ ] ψ }}ad
| ad_ppre__univ_ghost_fill : forall L Θ Δ Ψ P ψ,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ (pskl_univ_ghost P)
         ⊑ᵖ[ Ψ ] (open_uskl_wrt_uskl ψ (uskl_var_f α)) }}ad) ->
    forall ε,
    {{ Θ ⨟ Δ ⊢ˢ (pskl_univ_ghost P) ⊑ᵖ[ Ψ ] (uskl_all_tag ε ψ) }}ad
| ad_ppre__univ_ghost_keep : forall Θ Δ Ψ P ψ,
    {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_univ_ghost P) ⊑ᵖ[ Ψ ] (uskl_dot_univ_ghost ψ) }}ad
(* — flexible-variable lookups (fig:declarative-in-algo-context style) — *)
| ad_ppre__flex_l : forall Θ Δ Ψ α τ ψ,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τ) ⊑ᵖ[ Ψ ] ψ }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_var_f α) ⊑ᵖ[ Ψ ] ψ }}ad
| ad_ppre__flex_r : forall Θ Δ Ψ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (uskl_var_f α) }}ad
where "{{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad" :=
  (ad_partial_precise Θ Δ Ψ P ψ) : fresco_ad_scope.
