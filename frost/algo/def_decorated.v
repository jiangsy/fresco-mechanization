(** Decorated algorithmic judgments (paper appendices/decorated-algosub.tex).

    The decorated system re-runs the algorithmic subtyping/consistency over
    UNRESOLVED skeletons [S : uskl] (tagged quantifiers + dotted ghosts,
    extended with flexible variables), threading the tag context [Ψ] exactly
    as the declarative judgments do.  It is the bridge for the soundness
    proofs: ordinary run ⇒ decorated run ⇒ declarative derivation. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Erasure  ⌊S⌋ : uskl → pskl  (decorated-algosub.tex:27-38)             *)
(*  Homomorphic; non-trivial cases: ∀^δ ↦ ∀, HoleG ↦ □, TopHoleG ↦ ⊤.     *)
(* ===================================================================== *)

Fixpoint uskl_to_pskl (S : uskl) : pskl :=
  match S with
  | uskl_unit => pskl_unit
  | uskl_var_b n => pskl_var_b n
  | uskl_var_f X => pskl_var_f X
  | uskl_arrow S1 S2 => pskl_arrow (uskl_to_pskl S1) (uskl_to_pskl S2)
  | uskl_all_syn S0 => pskl_all_syn (uskl_to_pskl S0)
  | uskl_all_etag _ S0 => pskl_all_syn (uskl_to_pskl S0)
  | uskl_hole => pskl_hole
  | uskl_tophole S0 => pskl_tophole (uskl_to_pskl S0)
  | uskl_holeg => pskl_hole
  | uskl_topholeg S0 => pskl_tophole (uskl_to_pskl S0)
  end.

(** Ghost-free unresolved skeletons: no ghosts of any kind.  Used for (i) the
    [N = TY] instantiation candidates (decorated TYPES φ, once combined with
    [is_tskl]) and (ii) the dotted-ghost-freeness side condition of the
    tag-solving FlexR rule (on decorated ψ, ghost-free ≡ dotted-ghost-free). *)
Inductive uskl_ghost_free : uskl -> Prop :=
| uskl_ghost_free__unit : uskl_ghost_free uskl_unit
| uskl_ghost_free__var : forall X, uskl_ghost_free (uskl_var_f X)
| uskl_ghost_free__arrow : forall S1 S2,
    uskl_ghost_free S1 -> uskl_ghost_free S2 ->
    uskl_ghost_free (uskl_arrow S1 S2)
| uskl_ghost_free__all_etag : forall L ε S,
    (forall X, X `notin` L ->
       uskl_ghost_free (open_uskl_wrt_uskl S (uskl_var_f X))) ->
    uskl_ghost_free (uskl_all_etag ε S)
| uskl_ghost_free__all_syn : forall L S,
    (forall X, X `notin` L ->
       uskl_ghost_free (open_uskl_wrt_uskl S (uskl_var_f X))) ->
    uskl_ghost_free (uskl_all_syn S).

(** [Θ ⊢^N tags{Ψg}{ψg}] (decorated ForallL premise, decorated-algosub:93):
    for [SK], ψg is a decorated skeleton ([is_tskl] + [tags{Ψg}]); for [TY],
    ψg is a decorated TYPE — additionally ghost-free. *)
Inductive a_tags_sort : a_sub_mode -> atoms -> uskl -> Prop :=
| a_tags_sort__sk : forall Ψ ψ,
    is_tskl ψ ->
    d_tags_skl Ψ ψ ->
    a_tags_sort a_sub_mode_sk Ψ ψ
| a_tags_sort__ty : forall Ψ ψ,
    is_tskl ψ ->
    d_tags_skl Ψ ψ ->
    uskl_ghost_free ψ ->
    a_tags_sort a_sub_mode_ty Ψ ψ.

(* ===================================================================== *)
(*  Decorated algorithmic consistency                                      *)
(*  [a_consistag Δ1 Δ2 P0 Ψ Θ0 S Q Θ1]                                    *)
(*    = paper  Θ0 ⊢[Δ1|Δ2][P0][Ψ] S ~ Q ⊣ Θ1                              *)
(*  (fig:decorated-alg-consistency; rules unchanged from the ordinary       *)
(*  system carry the empty tag context ·)                                  *)
(* ===================================================================== *)

Inductive a_consistag :
  atoms -> atoms -> pskl -> atoms -> aenv -> uskl -> pskl -> aenv -> Prop :=
(* — unchanged rules (empty tag context) — *)
| a_consistag__ghost : forall Δ1 Δ2 Ψ Θ0 P0,                  (* Ghost *)
    AtomSetImpl.inter Δ2 (ftvar_in_pskl P0) [=] empty ->
    Ψ [=] empty ->
    a_consistag Δ1 Δ2 P0 Ψ Θ0 uskl_hole P0 Θ0
| a_consistag__unit : forall Δ1 Δ2 Ψ Θ0,                      (* Unit *)
    Ψ [=] empty ->
    a_consistag Δ1 Δ2 pskl_unit Ψ Θ0 uskl_unit pskl_unit Θ0
| a_consistag__rigid : forall Δ1 Δ2 Ψ Θ0 α,                   (* Rigid *)
    binds α abind_tvar Θ0 ->
    Ψ [=] empty ->
    a_consistag Δ1 Δ2 (pskl_var_f α) Ψ Θ0 (uskl_var_f α) (pskl_var_f α) Θ0
| a_consistag__flex : forall Δ1 Δ2 Ψ Θ0 Θ1 α β,               (* Flex *)
    a_unify Θ0 (ptyp_var_f α) (ptyp_var_f β) Θ1 ->
    Ψ [=] empty ->
    a_consistag Δ1 Δ2 (pskl_var_f β) Ψ Θ0 (uskl_var_f α) (pskl_var_f α) Θ1
| a_consistag__flex_l : forall Δ1 Δ2 Ψ Θ0 Θ1 α P0,            (* FlexL *)
    a_non_flex Θ0 P0 ->
    a_assign Θ0 nil α P0 Θ1 ->
    Ψ [=] empty ->
    a_consistag Δ1 Δ2 P0 Ψ Θ0 (uskl_var_f α) (pskl_var_f α) Θ1
| a_consistag__flex_r : forall Δ1 Δ2 Ψ Θ0 Θ1 α S,             (* FlexR *)
    a_non_flex Θ0 (uskl_to_pskl S) ->
    a_assign Θ0 nil α (uskl_to_pskl S) Θ1 ->
    Ψ [=] empty ->
    a_consistag Δ1 Δ2 (pskl_var_f α) Ψ Θ0 S (pskl_var_f α) Θ1
(* — decorated rules (fig:decorated-alg-consistency) — *)
| a_consistag__ghostg : forall Δ1 Δ2 Ψ Θ0,                    (* GhostG *)
    Ψ [=] empty ->
    a_consistag Δ1 Δ2 pskl_hole Ψ Θ0 uskl_holeg pskl_hole Θ0
| a_consistag__arrow : forall Δ1 Δ2 Ψ Ψ1 Ψ2 Θ0 Θ1 Θ2 P0a P0b S1 S2 Q1 Q2,
    a_consistag Δ1 Δ2 P0a Ψ1 Θ0 S1 Q1 Θ1 ->                   (* Arrow *)
    a_consistag Δ1 Δ2 P0b Ψ2 Θ1 S2 Q2 Θ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    a_consistag Δ1 Δ2 (pskl_arrow P0a P0b) Ψ Θ0 (uskl_arrow S1 S2)
      (pskl_arrow Q1 Q2) Θ2
| a_consistag__forall_inh_tagged : forall L Δ1 Δ2 Ψ Ψ0 Θ0 Θ1 ε P0 S Q,
    (forall α, α `notin` L ->                                 (* ForallInh, δ=ε *)
       a_consistag (add α Δ1) (add α Δ2)
         (open_pskl_wrt_pskl P0 (pskl_var_f α)) Ψ0
         ((α ~ abind_tvar) ++ Θ0)
         (open_uskl_wrt_uskl S (uskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    Ψ [=] add ε Ψ0 ->
    a_consistag Δ1 Δ2 (pskl_all_syn P0) Ψ Θ0 (uskl_all_etag ε S)
      (pskl_all_syn Q) Θ1
| a_consistag__forall_inh_untagged : forall L Δ1 Δ2 Ψ Θ0 Θ1 P0 S Q,
    (forall α, α `notin` L ->                                 (* ForallInh, δ=· *)
       a_consistag (add α Δ1) (add α Δ2)
         (open_pskl_wrt_pskl P0 (pskl_var_f α)) Ψ
         ((α ~ abind_tvar) ++ Θ0)
         (open_uskl_wrt_uskl S (uskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    a_consistag Δ1 Δ2 (pskl_all_syn P0) Ψ Θ0 (uskl_all_syn S)
      (pskl_all_syn Q) Θ1
| a_consistag__forall_syn_tagged : forall L Δ1 Δ2 Ψ Θ0 Θ1 ε P0 S Q,
    (forall α, α `notin` L ->                                 (* ForallSyn, δ=ε *)
       a_consistag Δ1 (add α Δ2) (pskl_tophole P0) Ψ
         ((α ~ abind_tvar) ++ Θ0)
         (open_uskl_wrt_uskl S (uskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    a_consistag Δ1 Δ2 (pskl_tophole P0) Ψ Θ0 (uskl_all_etag ε S)
      (pskl_all_syn Q) Θ1
| a_consistag__forall_syn_untagged : forall L Δ1 Δ2 Ψ Θ0 Θ1 P0 S Q,
    (forall α, α `notin` L ->                                 (* ForallSyn, δ=· *)
       a_consistag Δ1 (add α Δ2) (pskl_tophole P0) Ψ
         ((α ~ abind_tvar) ++ Θ0)
         (open_uskl_wrt_uskl S (uskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    a_consistag Δ1 Δ2 (pskl_tophole P0) Ψ Θ0 (uskl_all_syn S)
      (pskl_all_syn Q) Θ1
| a_consistag__univ_ghost : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 S Q,      (* UnivGhost *)
    a_consistag Δ1 Δ2 P0 Ψ Θ0 S Q Θ1 ->
    a_consistag Δ1 Δ2 (pskl_tophole P0) Ψ Θ0 (uskl_tophole S)
      (pskl_tophole Q) Θ1
| a_consistag__univ_ghostg : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 S Q,     (* UnivGhostG *)
    a_consistag Δ1 Δ2 P0 Ψ Θ0 S Q Θ1 ->
    a_consistag Δ1 Δ2 (pskl_tophole P0) Ψ Θ0 (uskl_topholeg S)
      (pskl_tophole Q) Θ1
| a_consistag__univ_ghost1 : forall L Δ1 Δ2 Ψ Θ0 Θ1 P0 S Q,   (* UnivGhost1 *)
    (forall α, α `notin` L ->
       a_consistag (add α Δ1) Δ2
         (open_pskl_wrt_pskl P0 (pskl_var_f α)) Ψ
         ((α ~ abind_tvar) ++ Θ0)
         (uskl_tophole S)
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    a_consistag Δ1 Δ2 (pskl_all_syn P0) Ψ Θ0 (uskl_tophole S)
      (pskl_all_syn Q) Θ1
| a_consistag__univ_ghost2 : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 S Q,     (* UnivGhost2 *)
    guarded_pskl P0 ->
    a_non_flex Θ0 P0 ->
    a_consistag Δ1 Δ2 P0 Ψ Θ0 S Q Θ1 ->
    a_consistag Δ1 Δ2 P0 Ψ Θ0 (uskl_tophole S) Q Θ1
| a_consistag__ghost_r : forall Δ1 Δ2 Ψ Θ0 S,                 (* GhostR *)
    AtomSetImpl.inter Δ1 (ftvar_in_pskl (uskl_to_pskl S)) [=] empty ->
    Ψ [=] empty ->
    a_consistag Δ1 Δ2 pskl_hole Ψ Θ0 S (uskl_to_pskl S) Θ0
| a_consistag__univ_ghost_r : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 S Q,    (* UnivGhostR *)
    guarded_uskl S ->
    a_non_flex Θ0 (uskl_to_pskl S) ->
    a_consistag Δ1 Δ2 P0 Ψ Θ0 S Q Θ1 ->
    a_consistag Δ1 Δ2 (pskl_tophole P0) Ψ Θ0 S Q Θ1.

(* ===================================================================== *)
(*  Decorated algorithmic subtyping                                        *)
(*  [a_subtag NM M P0 Ψ Θ0 S Q Θ1]                                        *)
(*    = paper  Θ0 ⊢[N][M][P0][Ψ] S ⊑ Q ⊣ Θ1                               *)
(*  (fig:decorated-alg-subtyping)                                          *)
(* ===================================================================== *)

Inductive a_subtag :
  a_sub_mode -> mode -> pskl -> atoms -> aenv -> uskl -> pskl -> aenv -> Prop :=
| a_subtag__infer : forall NM Ψ Θ0 S,                         (* Infer *)
    Ψ [=] empty ->
    a_subtag NM mode_ti pskl_hole Ψ Θ0 S (uskl_to_pskl S) Θ0
| a_subtag__check : forall Ψ Θ0 Θ1 T B,                       (* Check *)
    guarded_uskl T ->
    guarded_pskl B ->
    a_consistag empty empty B Ψ Θ0 T B Θ1 ->
    a_subtag a_sub_mode_ty mode_tc B Ψ Θ0 T B Θ1
| a_subtag__forall_r : forall L Ψ Θ0 Θ1 Ξ S B,                (* ForallR *)
    a_suffix Ξ ->
    (forall α, α `notin` L ->
       a_subtag a_sub_mode_ty mode_tc (open_pskl_wrt_pskl B (pskl_var_f α)) Ψ
         ((α ~ abind_tvar) ++ Θ0) S (open_pskl_wrt_pskl B (pskl_var_f α))
         (Ξ ++ (α ~ abind_tvar) ++ Θ1)) ->
    a_subtag a_sub_mode_ty mode_tc (pskl_all_syn B) Ψ Θ0 S (pskl_all_syn B) Θ1
| a_subtag__univ_ghost_r : forall Ψ Θ0 S,                     (* UnivGhostR *)
    guarded_uskl S ->
    Ψ [=] empty ->
    a_subtag a_sub_mode_sk mode_tc pskl_hole Ψ Θ0 S
      (pskl_tophole (uskl_to_pskl S)) Θ0
| a_subtag__arrow : forall NM M Ψ Ψ1 Ψ2 Θ0 Θ1 Θ2 P0a P0b S1 S2 Q1 Q2,
    a_consistag empty empty P0a Ψ1 Θ0 S1 Q1 Θ1 ->             (* Arrow *)
    a_subtag NM M P0b Ψ2 Θ1 S2 Q2 Θ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    a_subtag NM (mode_fn M) (pskl_arrow P0a P0b) Ψ Θ0 (uskl_arrow S1 S2)
      (pskl_arrow Q1 Q2) Θ2
| a_subtag__forall_l_tagged : forall L NM M P0 Ψ Ψg Θ0 Θ1 ε S Q Ξ P1 ψg,
    M <> mode_ti ->                                           (* ForallL, δ=ε *)
    (guarded_pskl P0 \/ P0 = pskl_hole) ->
    (forall α, α `notin` L ->
       a_extract NM α M (uskl_to_pskl (open_uskl_wrt_uskl S (uskl_var_f α)))
         P0 Ξ P1) ->
    a_wf_pskl (Ξ ++ Θ0) P1 ->
    AtomSetImpl.inter Ψg Ψ [=] empty ->                       (* Ψg fresh *)
    a_tags_sort NM Ψg ψg ->                                   (* Θ,Ξ ⊢^N tags{Ψg}{ψg} *)
    uskl_to_pskl ψg = P1 ->                                   (* ⌊ψg⌋ = P1 *)
    a_subtag NM M P0 (Ψ `union` Ψg) (Ξ ++ Θ0)
      (open_uskl_wrt_uskl S ψg) Q Θ1 ->
    a_subtag NM M P0 Ψ Θ0 (uskl_all_etag ε S) Q Θ1
| a_subtag__forall_l_untagged : forall L NM M P0 Ψ Ψg Θ0 Θ1 S Q Ξ P1 ψg,
    M <> mode_ti ->                                           (* ForallL, δ=· *)
    (guarded_pskl P0 \/ P0 = pskl_hole) ->
    (forall α, α `notin` L ->
       a_extract NM α M (uskl_to_pskl (open_uskl_wrt_uskl S (uskl_var_f α)))
         P0 Ξ P1) ->
    a_wf_pskl (Ξ ++ Θ0) P1 ->
    AtomSetImpl.inter Ψg Ψ [=] empty ->
    a_tags_sort NM Ψg ψg ->
    uskl_to_pskl ψg = P1 ->
    a_subtag NM M P0 (Ψ `union` Ψg) (Ξ ++ Θ0)
      (open_uskl_wrt_uskl S ψg) Q Θ1 ->
    a_subtag NM M P0 Ψ Θ0 (uskl_all_syn S) Q Θ1
| a_subtag__ghost : forall M Ψ Θ0 P0,                         (* Ghost (unchanged) *)
    Ψ [=] empty ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 uskl_hole P0 Θ0
| a_subtag__ghostg : forall M Ψ Θ0,                           (* GhostG *)
    Ψ [=] empty ->
    a_subtag a_sub_mode_sk M pskl_hole Ψ Θ0 uskl_holeg pskl_hole Θ0
| a_subtag__univ_ghost_l : forall M Ψ Θ0 Θ1 P0 S Q,           (* UnivGhostL *)
    M <> mode_ti ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 S Q Θ1 ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 (uskl_tophole S) Q Θ1
| a_subtag__univ_ghost_lg : forall M Ψ Θ0 Θ1 P0 S Q,          (* UnivGhostLG *)
    M <> mode_ti ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 S Q Θ1 ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 (uskl_topholeg S) Q Θ1
| a_subtag__flex_mono : forall NM M P0 Ψ Θ0 Θ1 α A,           (* FlexMono (unchanged) *)
    a_sub_flex NM M P0 Θ0 nil α A Θ1 ->
    Ψ [=] empty ->
    a_subtag NM (mode_fn M) P0 Ψ Θ0 (uskl_var_f α) A Θ1.

(* ===================================================================== *)
(*  Decorated tag solving  (fig:decorated-tag-solving)                    *)
(*  [solvetag C ψ Ψ]: the tags of ψ solved by the constraint list C.       *)
(*  Contribution-only: constraints add tags only where their structure     *)
(*  matches ψ's.                                                          *)
(* ===================================================================== *)

Inductive a_solvetag_sub : uskl -> mode -> pskl -> atoms -> Prop :=
| a_solvetag_sub__var : forall X M Q Ψ,                       (* SSub-Var / Flex *)
    Ψ [=] empty ->
    a_solvetag_sub (uskl_var_f X) M Q Ψ
| a_solvetag_sub__forall_l : forall L ε ψ M Q Ψ,              (* SSub-ForallL *)
    (forall β, β `notin` L ->
       a_solvetag_sub (open_uskl_wrt_uskl ψ (uskl_var_f β)) M Q Ψ) ->
    a_solvetag_sub (uskl_all_etag ε ψ) M Q Ψ
| a_solvetag_sub__univ_ghost_lg : forall ψ M Q Ψ,             (* SSub-UnivGhostLG *)
    a_solvetag_sub ψ M Q Ψ ->
    a_solvetag_sub (uskl_topholeg ψ) M Q Ψ
| a_solvetag_sub__vacuous : forall ψ M Ψ,                     (* SSub-Vacuous *)
    Ψ [=] empty ->
    a_solvetag_sub ψ M pskl_hole Ψ
| a_solvetag_sub__check : forall ψ B Ψ,                       (* SSub-Check *)
    guarded_uskl ψ ->
    guarded_pskl B ->
    a_solvetag_eq ψ B Ψ ->
    a_solvetag_sub ψ mode_tc B Ψ
| a_solvetag_sub__forall_r : forall L ψ B Ψ,                  (* SSub-ForallR *)
    (forall β, β `notin` L ->
       a_solvetag_sub ψ mode_tc (open_pskl_wrt_pskl B (pskl_var_f β)) Ψ) ->
    a_solvetag_sub ψ mode_tc (pskl_all_syn B) Ψ
| a_solvetag_sub__arrow : forall ψ1 ψ2 M Q1 Q2 Ψ Ψ1 Ψ2,       (* SSub-Arrow *)
    a_solvetag_eq ψ1 Q1 Ψ1 ->
    a_solvetag_sub ψ2 M Q2 Ψ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    a_solvetag_sub (uskl_arrow ψ1 ψ2) (mode_fn M) (pskl_arrow Q1 Q2) Ψ

with a_solvetag_eq : uskl -> pskl -> atoms -> Prop :=
| a_solvetag_eq__unit : forall Ψ,                             (* SEq-Unit *)
    Ψ [=] empty ->
    a_solvetag_eq uskl_unit pskl_unit Ψ
| a_solvetag_eq__var : forall X Q Ψ,                          (* SEq-Var / FlexL *)
    Ψ [=] empty ->
    a_solvetag_eq (uskl_var_f X) Q Ψ
| a_solvetag_eq__vacuous : forall ψ Ψ,                        (* SEq-Vacuous *)
    Ψ [=] empty ->
    a_solvetag_eq ψ pskl_hole Ψ
| a_solvetag_eq__arrow : forall ψ1 ψ2 Q1 Q2 Ψ Ψ1 Ψ2,          (* SEq-Arrow *)
    a_solvetag_eq ψ1 Q1 Ψ1 ->
    a_solvetag_eq ψ2 Q2 Ψ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    a_solvetag_eq (uskl_arrow ψ1 ψ2) (pskl_arrow Q1 Q2) Ψ
| a_solvetag_eq__forall_inh : forall L ε ψ Q Ψ Ψ0,            (* SEq-ForallInh *)
    (forall β, β `notin` L ->
       a_solvetag_eq (open_uskl_wrt_uskl ψ (uskl_var_f β))
         (open_pskl_wrt_pskl Q (pskl_var_f β)) Ψ0) ->
    Ψ [=] add ε Ψ0 ->
    a_solvetag_eq (uskl_all_etag ε ψ) (pskl_all_syn Q) Ψ
| a_solvetag_eq__univ_ghostg : forall ψ Q Ψ,                  (* SEq-UnivGhostG *)
    a_solvetag_eq ψ Q Ψ ->
    a_solvetag_eq (uskl_topholeg ψ) (pskl_tophole Q) Ψ
| a_solvetag_eq__forall_syn : forall L ε ψ Q Ψ,               (* SEq-ForallSyn *)
    (forall β, β `notin` L ->
       a_solvetag_eq (open_uskl_wrt_uskl ψ (uskl_var_f β))
         (pskl_tophole Q) Ψ) ->
    a_solvetag_eq (uskl_all_etag ε ψ) (pskl_tophole Q) Ψ
| a_solvetag_eq__univ_ghost_r : forall ψ Q Ψ,                 (* SEq-UnivGhostR *)
    guarded_pskl (uskl_to_pskl ψ) ->
    a_solvetag_eq ψ Q Ψ ->
    a_solvetag_eq ψ (pskl_tophole Q) Ψ
| a_solvetag_eq__flex_r : forall ψ α Ψ,                       (* SEq-FlexR *)
    uskl_ghost_free ψ ->
    Ψ [=] empty ->
    a_solvetag_eq ψ (pskl_var_f α) Ψ.

(* [solvetag C ψ Ψ] (top box). *)
Inductive a_solvetag : a_cstrs -> uskl -> atoms -> Prop :=
| a_solvetag__empty : forall ψ Ψ,
    Ψ [=] empty ->
    a_solvetag nil ψ Ψ
| a_solvetag__sub : forall M Q ψ Ψ,
    a_solvetag_sub ψ M Q Ψ ->
    a_solvetag (a_cstr_sub M Q :: nil) ψ Ψ
| a_solvetag__eq : forall Q C ψ Ψ Ψ1 Ψ2,
    a_solvetag_eq ψ Q Ψ1 ->
    a_solvetag C ψ Ψ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    a_solvetag (a_cstr_eq Q :: C) ψ Ψ.
