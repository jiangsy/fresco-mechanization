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
Require Import Coq.micromega.Lia.
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

(* ⚙ RESTART NOTE (2026-08-11) — [ad_pat_sub_n], the NON-hygienic fuel mirror,
   and its five bridge lemmas ([ad_pat_sub_of_n] / [_n_succ] / [_n_mono] /
   [_n_rename_tvar] / [ad_pat_sub_to_n], ~230 lines in
   algo/sub/prop_completeness_sub_precise.v §P5a) were DELETED: NOTHING in the
   tree consumed any of them.  §1 of the completeness skeleton named [_n] as
   the measure, but the development settled on the TAG-HYGIENIC fuel
   [ad_pat_sub_g] (algo/sub/prop_completeness_sub_gen.v §1) and never came
   back, so [_n] was scaffolding that outlived its plan.
   To re-derive: copy [ad_pat_sub_g] (def_decl_algo_sub.v) with the
   ORIGINAL fuel discipline — every rule increments, leaves conclude at
   [S n] — and drop its two [ftag_in_uskl] premises.  ⚠️ But check first
   whether [_g] serves: the completeness track's measure is [_g]'s fuel, and
   a second mirror has to be bridged to [ad_pat_sub] all over again. *)

(* ===================================================================== *)
(*  TAG-HYGIENIC FUEL MIRRORS of [ad_pat_sub]  (completeness-only)        *)
(* ===================================================================== *)

(** ⚙ MERGED IN 2026-08-11 from [def_decl_algo_sub.v].  The two files
    were one topic — the paper's all-in-one subtyping box and the mirrors
    the completeness proof measures it by — split only because the mirrors
    arrived later.  The split cost nothing to keep and nothing to remove:
    the [_hyg] file's dependencies were this file's plus [Lia].

    TAG-HYGIENIC FUEL MIRROR of [ad_pat_sub].

    [ad_pat_sub_g] refines [ad_pat_sub] in two ways, both forced by
    precision-substitution (docs/DESIGN-completeness-subtyping.md §5.4):

    1. TAG HYGIENE.  The paper's ForallL side condition [fresh Ψ'] means the
       instantiation's tags are GLOBALLY fresh; [ad_pat_sub] — like its
       declarative originals [d_sub] / [d_pat_sub] — renders it only as
       freshness from the tag context, which does not survive the Arrow split
       (a tag can leave the context on one branch while the subject still
       carries it on the other), and precision-substitution is FALSE over such
       derivations.  Both ForallL rules therefore also require the
       instantiation's tags fresh from the SUBJECT's syntactic tags
       ([ftag_in_uskl], def_extra.v).
       ⚠️ MOVING THIS PREMISE ONTO [d_sub] — so that all four judgments read
       [fresh Ψ'] the same way — is NOT bookkeeping, and was tried and backed
       out on 2026-08-11: it relocates the obligation into Phase 2's
       [d_consis_sub_trans_mid] (CST, decl/prop_general_subsumption.v), whose
       ForallL case transports a derivation along [utyp_tag_refines], where
       the subject GAINS tags — so the hygiene has to be re-established for a
       strictly bigger tag set, which needs the ε-tag freshening the
       development does not have.  Details in docs/PAPER-GAPS.md.

    2.     FUEL DISCIPLINE.  Precision-substitution must be fuel-PRESERVING
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

    The erasure [_g → ad_pat_sub] is [ad_pat_sub_g_of] below.  ⚠️ The
    renaming-based freshening in the other direction ([ad_pat_sub] → [_g], and
    equally [d_sub] → [_g], which is what a COMPLETENESS corollary over the
    declarative system would need) is still owed — see §1's note and
    docs/HANDOFF-closed-corollaries-declarative.md. *)

Inductive ad_pat_sub_g :
  nat -> a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub_g__infer : forall n NM Ψ Θ R Q,                  (* Infer *)
    Ψ [=] empty ->
    empty ⨟ Θ ⊢ᵃᵈ R ∼ Q ->
    is_sskl Q ->
    ad_pat_sub_g n NM mode_ti Ψ Θ R Q
| ad_pat_sub_g__check : forall n Ψ Θ T B,                     (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    Ψ ⨟ Θ ⊢ᵃᵈ T ∼ (pskl_to_bskl_inh B) ->
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
    empty ⨟ Θ ⊢ᵃᵈ R ∼ Q ->
    ad_pat_sub_g n a_sub_mode_sk mode_tc Ψ Θ R (bskl_tophole Q)
| ad_pat_sub_g__arrow : forall n NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2, (* Arrow *)
    Ψ1 ⨟ Θ ⊢ᵃᵈ R1 ∼ Q1 ->
    ad_pat_sub_g n NM M Ψ2 Θ R2 Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    ad_pat_sub_g (S n) NM (mode_fn M) Ψ Θ (uskl_arrow R1 R2) (bskl_arrow Q1 Q2)
| ad_pat_sub_g__forall_l_tagged : forall n NM Ψ Ψ' Θ M ε R ψ Q, (* ForallL, β1=ε *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_etag ε R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_g n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_g (S n) NM M Ψ Θ (uskl_all_etag ε R) Q
| ad_pat_sub_g__forall_l_untagged : forall n NM Ψ Ψ' Θ M R ψ Q, (* ForallL, β1=· *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_syn R)) [=] empty ->
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

(* ===================================================================== *)
(*  LEAF-VALID variant [ad_pat_sub_gv] (completeness-only, P7's join).     *)
(*                                                                        *)
(*  Same rules as [ad_pat_sub_g], except the three CONSISTENCY-LEAF rows  *)
(*  — [__infer], [__check], [__univ_ghost_r] — additionally carry the     *)
(*  SUBJECT's refinement into the leaf's counterpart (for [UnivGhostR],   *)
(*  into the STRIPPED counterpart [Q], not [∀◇.Q]).                       *)
(*                                                                        *)
(*  WHY.  thm:complete-subtyping needs, at each leaf, exactly the third   *)
(*  solution condition of the AUGMENTED thm:complete-consistency          *)
(*  (consistency-proofs.tex:2230-2242) for the consistency subproblem it  *)
(*  invokes there — and that condition is NOT derivable from the paper's  *)
(*  two subtyping-solution conditions (the capture configuration          *)
(*  [(P0=◇, P=∀X.◇, Q=∀X.X)] passes both).  Stating it at the ROOT        *)
(*  instead — as one [⊢ᵣₚᵃᵈ κ⌊S⌋ˢ ⊳ ⌊Q⌋] premise on the theorem — is       *)
(*  WRONG: refinement is a lockstep relation, so a root condition         *)
(*  excludes every solution whose sides disagree at a head through       *)
(*  ForallL / ForallR / UnivGhostR, i.e. instantiation and               *)
(*  generalisation themselves (machine-checked:                          *)
(*  cex/cex_p7_univ_ghost_r_vacuous.v, cex/cex_p7_third_premise_forall.v).*)
(*  The ghost leaves [__ghost] / [__ghostg] need no condition: they do    *)
(*  not invoke consistency completeness, and their subject's refinement   *)
(*  is derivable from the rule's own wf premise.                          *)
(*                                                                        *)
(*  [ad_pat_sub_gv_forget] recovers the plain mirror wherever leaf data   *)
(*  is not needed (in particular for every P5/P6 invocation).             *)
(* ===================================================================== *)

Inductive ad_pat_sub_gv :
  nat -> a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub_gv__infer : forall n NM Ψ Θ R Q,                 (* Infer *)
    Ψ [=] empty ->
    empty ⨟ Θ ⊢ᵃᵈ R ∼ Q ->
    is_sskl Q ->
    Θ ⨟ empty ⊢ᵣₚᵃᵈ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) ->
    ad_pat_sub_gv n NM mode_ti Ψ Θ R Q
| ad_pat_sub_gv__check : forall n Ψ Θ T B,                    (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    Ψ ⨟ Θ ⊢ᵃᵈ T ∼ (pskl_to_bskl_inh B) ->
    Θ ⨟ empty ⊢ᵣₚᵃᵈ ⌊ T ⌋ˢ ⊳ B ->
    ad_pat_sub_gv n a_sub_mode_ty mode_tc Ψ Θ T (pskl_to_bskl_inh B)
| ad_pat_sub_gv__forall_r : forall n L Ψ Θ T B,              (* ForallR (TY) *)
    (forall α, α `notin` L ->
       ad_pat_sub_gv n a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ)
         T (open_bskl_wrt_bskl B (bskl_var_f α))) ->
    ad_pat_sub_gv (S n) a_sub_mode_ty mode_tc Ψ Θ T (bskl_all_inh B)
| ad_pat_sub_gv__univ_ghost_r : forall n Ψ Θ R Q,            (* UnivGhostR (SK) *)
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    empty ⨟ Θ ⊢ᵃᵈ R ∼ Q ->
    Θ ⨟ empty ⊢ᵣₚᵃᵈ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) ->
    ad_pat_sub_gv n a_sub_mode_sk mode_tc Ψ Θ R (bskl_tophole Q)
| ad_pat_sub_gv__arrow : forall n NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2, (* Arrow *)
    Ψ1 ⨟ Θ ⊢ᵃᵈ R1 ∼ Q1 ->
    (* the DOMAIN premise is itself a consistency leaf — Sub-Arrow invokes
       thm:complete-consistency on it (:3334), so it carries the same
       subject-refinement data as [__infer] *)
    Θ ⨟ empty ⊢ᵣₚᵃᵈ ⌊ R1 ⌋ˢ ⊳ (bskl_to_pskl Q1) ->
    ad_pat_sub_gv n NM M Ψ2 Θ R2 Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    ad_pat_sub_gv (S n) NM (mode_fn M) Ψ Θ (uskl_arrow R1 R2) (bskl_arrow Q1 Q2)
| ad_pat_sub_gv__forall_l_tagged : forall n NM Ψ Ψ' Θ M ε R ψ Q, (* ForallL, β1=ε *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_etag ε R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_gv n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_gv (S n) NM M Ψ Θ (uskl_all_etag ε R) Q
| ad_pat_sub_gv__forall_l_untagged : forall n NM Ψ Ψ' Θ M R ψ Q, (* ForallL, β1=· *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_syn R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_gv n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_gv (S n) NM M Ψ Θ (uskl_all_syn R) Q
| ad_pat_sub_gv__ghost : forall n Ψ Θ M P,                    (* Ghost (SK) *)
    Ψ [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ P ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ uskl_hole (pskl_to_bskl_inh P)
| ad_pat_sub_gv__ghostg : forall n Ψ Θ M,                     (* GhostG (SK) *)
    Ψ [=] empty ->
    mod_comp_sk bskl_hole M ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ uskl_holeg bskl_hole
| ad_pat_sub_gv__univ_ghost_l : forall n Ψ Θ M R Q,          (* UnivGhostL (SK) *)
    M <> mode_ti ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ (uskl_tophole R) Q
| ad_pat_sub_gv__univ_ghost_lg : forall n Ψ Θ M R Q,         (* UnivGhostLG (SK) *)
    M <> mode_ti ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ (uskl_topholeg R) Q
| ad_pat_sub_gv__flex_mono : forall n NM Ψ Θ M α τ Q,         (* FlexMono *)
    binds α (abind_flex_mono_def τ) Θ ->
    ad_pat_sub_gv n NM (mode_fn M) Ψ Θ (ptyp_to_uskl_syn τ) Q ->
    ad_pat_sub_gv n NM (mode_fn M) Ψ Θ (uskl_var_f α) Q.

(** Forgetting the leaf data recovers the plain hygienic mirror. *)
Lemma ad_pat_sub_gv_forget : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  ad_pat_sub_g n NM M Ψ Θ R Q.
Proof.
  intros * H; induction H; eauto using ad_pat_sub_g.
Qed.

(* ===================================================================== *)
(*  The three ERASURES + fuel monotonicity.                               *)
(*                                                                        *)
(*  ⚙ [ad_pat_sub_g_of] and [ad_pat_sub_gv_fuel_weaken] are HERE, not with *)
(*  the completeness files: the SOUNDNESS side has to CONCLUDE [_gv]       *)
(*  ([ad_pat] / [ad_sd_typing] embed the leaf-valid join, so               *)
(*  thm:complete-skeleton/type-inference can consume it), and              *)
(*  algo/prop_soundness_sub.v sits BEFORE both of them in the dependency   *)
(*  order.  Both are plain inductions over the mirrors and need nothing    *)
(*  this file does not already import.                                     *)
(* ===================================================================== *)

(** Erase hygiene + fuel: a hygienic derivation is a plain one. *)
Lemma ad_pat_sub_g_of : forall n NM M Ψ Θ R Q,
  ad_pat_sub_g n NM M Ψ Θ R Q ->
  Ψ ⨟ Θ ⊢ᵃᵈ[ NM | M ] R ⩽ Q.
Proof.
  intros n NM M Ψ Θ R Q H. induction H.
  - eapply ad_pat_sub__infer; eauto.
  - eapply ad_pat_sub__check; eauto.
  - eapply ad_pat_sub__forall_r; eauto.
  - eapply ad_pat_sub__univ_ghost_r; eauto.
  - eapply ad_pat_sub__arrow; eauto.
  - eapply ad_pat_sub__forall_l_tagged; eauto.
  - eapply ad_pat_sub__forall_l_untagged; eauto.
  - eapply ad_pat_sub__ghost; eauto.
  - eapply ad_pat_sub__ghostg; eauto.
  - eapply ad_pat_sub__univ_ghost_l; eauto.
  - eapply ad_pat_sub__univ_ghost_lg; eauto.
  - eapply ad_pat_sub__flex_mono; eauto.
Qed.

(** Fuel monotonicity for the leaf-valid hygienic join.  The fuel is the
    declarative derivation's HEIGHT, so a derivation of height [n] is also
    one of every larger height.  Needed because the permutation below
    returns the family at whatever height the extraction yields, while
    [a_sub_complete_forall_r] wants it at exactly [n] for a conclusion at
    [S n]. *)
Lemma ad_pat_sub_gv_fuel_weaken : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  forall m, n <= m -> ad_pat_sub_gv m NM M Ψ Θ R Q.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; intros m Hle;
    try solve [ econstructor; eauto ].
  - (* forall_r : the conclusion's fuel is [S n] *)
    destruct m as [ | m' ]; [ lia | ].
    apply ad_pat_sub_gv__forall_r with (L := L).
    intros α Hα. apply H0; [ exact Hα | lia ].
  - (* arrow *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_gv__arrow;
      [ exact H | exact H0 | apply IHad_pat_sub_gv; lia | assumption ].
  - (* forall_l_tagged *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_gv__forall_l_tagged;
      [ eassumption | eassumption | eassumption | eassumption | eassumption
      | apply IHad_pat_sub_gv; lia ].
  - (* forall_l_untagged *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_gv__forall_l_untagged;
      [ eassumption | eassumption | eassumption | eassumption | eassumption
      | apply IHad_pat_sub_gv; lia ].
Qed.

(** The composite erasure the [ad_pat] / [ad_sd_typing] consumers want:
    a leaf-valid join IS a plain declarative subtyping derivation. *)
Lemma ad_pat_sub_of_gv : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  Ψ ⨟ Θ ⊢ᵃᵈ[ NM | M ] R ⩽ Q.
Proof. intros * H. exact (ad_pat_sub_g_of (ad_pat_sub_gv_forget H)). Qed.

(** ⭐ THE LEAF-VALID JOIN WITH THE FUEL FORGOTTEN — what the
    declarative-in-algo judgements [ad_pat] / [ad_sd_typing] embed in their
    base rows (hand-off §6.2).  The fuel is an artefact of the completeness
    measure, so it has no business in a judgement's premise; what those rules
    must carry is the LEAF DATUM, which the capture configuration shows is not
    recoverable from a plain join (cex/cex_ad_pat_join_not_leaf_valid.v).

    ⚙ No notation, deliberately: like [ad_pat_sub_g] / [_gv] / [_n], this is a
    mech-internal variant of the paper's box, not a paper judgement. *)
Definition ad_pat_sub_v (NM : a_sub_mode) (M : mode) (Ψ : atoms)
    (Θ : aenv) (R : uskl) (Q : bskl) : Prop :=
  exists n, ad_pat_sub_gv n NM M Ψ Θ R Q.

(** A leaf-valid join IS a plain declarative subtyping derivation. *)
Lemma ad_pat_sub_of_v : forall NM M Ψ Θ R Q,
  ad_pat_sub_v NM M Ψ Θ R Q ->
  Ψ ⨟ Θ ⊢ᵃᵈ[ NM | M ] R ⩽ Q.
Proof. intros * [n H]. exact (ad_pat_sub_of_gv H). Qed.

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
