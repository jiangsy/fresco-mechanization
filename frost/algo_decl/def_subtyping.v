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

    - [ad_partial_precise]: partial precision [{{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[Ψ] ψ }}ad]
      (subtyping-proofs.tex:1561-1637), the completeness-only refinement of
      precision: quantifiers of ψ whose tags are NOT in Ψ may be matched by
      ghosts in P.  Its definition "corresponds one to one to the definition
      of refinement in algorithmic contexts" (tex:1552-1554), so it mirrors
      [ad_refine_pskl] (def_consis_refine.v:198) — including the placements the
      mech settled there for the paper's external wf side conditions
      (docs/WF-SIDE-CONDITIONS.md): the var rule carries the
      [Δ ∨ a_binds_tvar] visibility disjunction, the ∀-rule extends only Δ
      (the rigid binder is picked cofinitely), tophole_fill extends Θ.
      Targets ψ are decorated skeletons, so their quantifiers are always
      tagged ([uskl_all_tag]; [is_tskl] has no [all_syn] constructor) and
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
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.deco_algo.def_decorated.

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope frost_ad_scope.

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
    {{ empty ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    is_sskl Q ->
    (* ⭐ [paper-gap] THE PRESUPPOSITION OF SKELETON CONSISTENCY at this leaf
       (declarative.tex:2074), the same premise [d_pat_sub] carries.  Added
       2026-08-12: until then only the mirror [ad_pat_sub_fuel] had it, so the
       plain relation and its declarative twin disagreed and the bridge had to
       run through the mirror.  It is NOT derivable from the consistency
       premise (cex/cex_ad_pat_join_not_leaf_valid.v). *)
    {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_ti ] R ⩽ Q }}ad
| ad_pat_sub__check : forall Ψ Θ T B,                         (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    {{ Ψ ⨟ Θ ⊢ˢ T ∼ (pskl_to_bskl_inh B) }}ad ->
    {{ Θ ⨟ empty ⊢ᵣₚ ⌊ T ⌋ˢ ⊳ B }}ad ->
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
    {{ empty ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | mode_tc ] R ⩽ (bskl_tophole Q) }}ad
| ad_pat_sub__arrow : forall NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2,      (* Arrow *)
    {{ Ψ1 ⨟ Θ ⊢ˢ R1 ∼ Q1 }}ad ->
    (* the DOMAIN premise is itself a consistency leaf *)
    {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R1 ⌋ˢ ⊳ (bskl_to_pskl Q1) }}ad ->
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
    Ψ [=] empty ->
    {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] uskl_hole ⩽ (pskl_to_bskl_inh P) }}ad
| ad_pat_sub__ghostg : forall Ψ Θ M,                          (* GhostG (SK) *)
    Ψ [=] empty ->
    mod_comp_sk bskl_hole M ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] uskl_holeg ⩽ bskl_hole }}ad
| ad_pat_sub__univ_ghost_l : forall Ψ Θ M R Q,                (* UnivGhostL (SK) *)
    M <> mode_ti ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] R ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] (uskl_tophole R) ⩽ Q }}ad
| ad_pat_sub__univ_ghost_lg : forall Ψ Θ M R Q,               (* UnivGhostLG (SK) *)
    M <> mode_ti ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] R ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] (uskl_topholeg R) ⩽ Q }}ad
(* — the algorithmic-context lookup rule (fig:declarative-in-algo-context) — *)
| ad_pat_sub__flex_mono : forall NM Ψ Θ M α τ Q,              (* FlexMono *)
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_fn M ] (ptyp_to_uskl_syn τ) ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_fn M ] (uskl_var_f α) ⩽ Q }}ad
where "{{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad" :=
  (ad_pat_sub NM M Ψ Θ R Q) : frost_ad_scope.

(* ⚙ RESTART NOTE (2026-08-11) — [ad_pat_sub_n], the NON-hygienic fuel mirror,
   and its five bridge lemmas ([ad_pat_sub_of_n] / [_n_succ] / [_n_mono] /
   [_n_rename_tvar] / [ad_pat_sub_to_n], ~230 lines in
   algo/sub/prop_completeness_sub_precise.v §P5a) were DELETED: NOTHING in the
   tree consumed any of them.  §1 of the completeness skeleton named [_n] as
   the measure, but the development settled on the TAG-HYGIENIC fuel
   [ad_pat_sub_fuel] (algo/sub/prop_completeness_sub_gen.v §1) and never came
   back, so [_n] was scaffolding that outlived its plan.
   To re-derive: copy [ad_pat_sub_fuel] (below) with the ORIGINAL fuel discipline
   — every rule increments, leaves conclude at [S n].  ⚙ 2026-08-11: there is
   nothing else to drop — [ad_pat_sub] now carries the [ftag_in_uskl] hygiene
   itself, so "[_n] = non-hygienic mirror" no longer names a difference.
   ⚠️ And check first whether [_gv] serves: the completeness track's measure is
   [_gv]'s fuel, and a second mirror has to be bridged to [ad_pat_sub] all over
   again — a lesson paid for twice, since [ad_pat_sub_g] was exactly such a
   second mirror and was retired 2026-08-12. *)

(* ===================================================================== *)
(*  THE TAG-HYGIENIC, LEAF-VALID FUEL MIRROR of [ad_pat_sub]              *)
(*  (completeness-only)                                                   *)
(* ===================================================================== *)

(** ⚙ MERGED IN 2026-08-11 from [def_subtyping.v].  The two files
    were one topic — the paper's all-in-one subtyping box and the mirror
    the completeness proof measures it by — split only because the mirror
    arrived later.  The split cost nothing to keep and nothing to remove:
    the [_hyg] file's dependencies were this file's plus [Lia].

    [ad_pat_sub_fuel] refines [ad_pat_sub] in ONE way — the FUEL discipline.
    It used to refine it in three; the other two, TAG HYGIENE and the LEAF
    PRESUPPOSITION, are now shared.

    ⭐ 2026-08-11: THE HYGIENE IS NO LONGER A DIFFERENCE.  The paper's ForallL
    side condition [fresh Ψ'] means the instantiation's tags are GLOBALLY
    fresh — fresh from the SUBJECT's own tags too, not just from the tag
    context — because the context-local reading does not survive the Arrow
    split (a tag can leave the context on one branch while the subject still
    carries it on the other), and precision-substitution is FALSE over such
    derivations (docs/DESIGN-completeness-subtyping.md §5.2/§5.4).  That
    premise now sits on [d_sub], [d_pat_sub] AND [ad_pat_sub] as well, so all
    four judgments read the word the same way and a completeness statement over
    the DECLARATIVE system can reach this mirror.  The one place it cost real
    work was Phase 2's [d_consis_sub_trans_mid] (CST,
    decl/prop_general_subsumption.v), whose ForallL case transports along
    [utyp_tag_refines], where the subject GAINS tags; the repair is the
    tags-bound twin [d_sub_tagsin] + wholesale freshening in
    decl/prop_tag_swap.v §4-§5.  Details in docs/PAPER-GAPS.md.

    ⭐⭐ 2026-08-12: NOR IS THE LEAF PRESUPPOSITION.  [ad_pat_sub]'s own
    consistency-leaf rows carry it now, so the SECOND mirror this file used to
    declare — [ad_pat_sub_g], the same fuel with the leaf data forgotten — is
    gone, together with [ad_pat_sub_fuel_forget] and the ~20 [_g]-flavoured
    lemmas that duplicated their [_gv] twins.  What kept [_g] alive was P7's
    two ForallL rows, which reshape the join's subject along [≡ᵘ] before
    handing it to the look layer; the leaf data survive that reshaping by
    [ad_refine_pskl_tyequiv_source] (algo/sub/prop_completeness_sub_precise.v),
    which is what let the mirror go.

    1.     FUEL DISCIPLINE.  Precision-substitution must be fuel-PRESERVING
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

    The erasure [_fuel -> ad_pat_sub] is [ad_pat_sub_of_fuel]
    (prop_sub_mirrors.v).  ⚠️ The other direction ([ad_pat_sub] -> [_gv],
    which is what a COMPLETENESS corollary over the declarative system would
    need) is still owed — but it is now purely a FUEL question: hygiene and
    the leaf datum are both already there.  See
    docs/HANDOFF-closed-corollaries-declarative.md. *)

(* ===================================================================== *)
(*  [ad_pat_sub_fuel] (completeness-only, P7's join): [ad_pat_sub] + FUEL.   *)
(*                                                                        *)
(*  ⭐ The four CONSISTENCY-LEAF rows — [__infer], [__check],              *)
(*  [__univ_ghost_r] and [__arrow]'s DOMAIN — carry the SUBJECT's         *)
(*  refinement into the leaf's counterpart (for [UnivGhostR], into the    *)
(*  STRIPPED counterpart [Q], not [∀◇.Q]).  Since 2026-08-12 that is NOT  *)
(*  a difference from [ad_pat_sub]: the plain relation carries the same   *)
(*  premise, which is why this is the only mirror left.  The paragraph    *)
(*  below is why the premise exists at all.                               *)
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
    {{ empty ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    is_sskl Q ->
    {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad ->
    ad_pat_sub_fuel n NM mode_ti Ψ Θ R Q
| ad_pat_sub_fuel__check : forall n Ψ Θ T B,                    (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    {{ Ψ ⨟ Θ ⊢ˢ T ∼ (pskl_to_bskl_inh B) }}ad ->
    {{ Θ ⨟ empty ⊢ᵣₚ ⌊ T ⌋ˢ ⊳ B }}ad ->
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
    {{ empty ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad ->
    ad_pat_sub_fuel n a_sub_mode_sk mode_tc Ψ Θ R (bskl_tophole Q)
| ad_pat_sub_fuel__arrow : forall n NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2, (* Arrow *)
    {{ Ψ1 ⨟ Θ ⊢ˢ R1 ∼ Q1 }}ad ->
    (* the DOMAIN premise is itself a consistency leaf — Sub-Arrow invokes
       thm:complete-consistency on it (:3334), so it carries the same
       subject-refinement data as [__infer] *)
    {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R1 ⌋ˢ ⊳ (bskl_to_pskl Q1) }}ad ->
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
    Ψ [=] empty ->
    {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ uskl_hole (pskl_to_bskl_inh P)
| ad_pat_sub_fuel__ghostg : forall n Ψ Θ M,                     (* GhostG (SK) *)
    Ψ [=] empty ->
    mod_comp_sk bskl_hole M ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ uskl_holeg bskl_hole
| ad_pat_sub_fuel__univ_ghost_l : forall n Ψ Θ M R Q,          (* UnivGhostL (SK) *)
    M <> mode_ti ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ (uskl_tophole R) Q
| ad_pat_sub_fuel__univ_ghost_lg : forall n Ψ Θ M R Q,         (* UnivGhostLG (SK) *)
    M <> mode_ti ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ (uskl_topholeg R) Q
| ad_pat_sub_fuel__flex_mono : forall n NM Ψ Θ M α τ Q,         (* FlexMono *)
    binds α (abind_flex_mono_def τ) Θ ->
    ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ (ptyp_to_uskl_syn τ) Q ->
    ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ (uskl_var_f α) Q.

(* ⚙ RESTART NOTE (2026-08-12) — [ad_pat_sub_v], the fuel EXISTENTIALLY
   CLOSED ([exists n, ad_pat_sub_fuel n …]), was deleted.  It existed so that
   [ad_pat] / [ad_sd_typing] could embed the leaf-valid join without naming a
   fuel in their rules — the fuel is the completeness measure's artefact, not
   part of the specification.  Both halves of that reason are gone: since
   [ad_pat_sub] carries the leaf presupposition itself, and
   [ad_pat_sub_to_fuel] / [ad_pat_sub_of_fuel] make the two relations
   INTERDERIVABLE, those rules embed [ad_pat_sub] — the paper's own relation —
   directly.  So the tree has exactly two: [ad_pat_sub] in every rule and every
   statement, and [ad_pat_sub_fuel] inside the subtyping-completeness proof,
   where the measure actually lives. *)

(* ===================================================================== *)
(*  Partial precision  [{{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad]                       *)
(*  (subtyping-proofs.tex:1561-1637; the ad_refine_pskl mirror with tags) *)
(* ===================================================================== *)

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
    α `in` Δ \/ a_binds_tvar α Θ ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_var_f α) ⊑ᵖ[ Ψ ] (uskl_var_f α) }}ad
| ad_ppre__arrow : forall Θ Δ Ψ Ψ1 Ψ2 P1 P2 ψ1 ψ2,
    {{ Θ ⨟ Δ ⊢ˢ P1 ⊑ᵖ[ Ψ1 ] ψ1 }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ P2 ⊑ᵖ[ Ψ2 ] ψ2 }}ad ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_arrow P1 P2) ⊑ᵖ[ Ψ ] (uskl_arrow ψ1 ψ2) }}ad
| ad_ppre__forall : forall L Θ Δ Ψ Ψ0 ε P ψ,
    (forall α, α `notin` L ->
       {{ Θ ⨟ (add α Δ) ⊢ˢ (open_pskl_wrt_pskl P (pskl_var_f α))
         ⊑ᵖ[ Ψ0 ] (open_uskl_wrt_uskl ψ (uskl_var_f α)) }}ad) ->
    Ψ [=] add ε Ψ0 ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_all_syn P) ⊑ᵖ[ Ψ ] (uskl_all_tag ε ψ) }}ad
| ad_ppre__hole : forall Θ Δ Ψ ψ,
    Ψ [=] empty ->
    Δ ∩ ftvar_in_uskl ψ [=] empty ->
    {{ Θ ⨟ Δ ⊢ˢ pskl_hole ⊑ᵖ[ Ψ ] ψ }}ad
| ad_ppre__tophole_remove : forall Θ Δ Ψ P ψ,
    {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_tophole P) ⊑ᵖ[ Ψ ] ψ }}ad
| ad_ppre__tophole_fill : forall L Θ Δ Ψ P ψ,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ (pskl_tophole P)
         ⊑ᵖ[ Ψ ] (open_uskl_wrt_uskl ψ (uskl_var_f α)) }}ad) ->
    forall ε,
    {{ Θ ⨟ Δ ⊢ˢ (pskl_tophole P) ⊑ᵖ[ Ψ ] (uskl_all_tag ε ψ) }}ad
| ad_ppre__tophole_keep : forall Θ Δ Ψ P ψ,
    {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_tophole P) ⊑ᵖ[ Ψ ] (uskl_topholeg ψ) }}ad
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
  (ad_partial_precise Θ Δ Ψ P ψ) : frost_ad_scope.
