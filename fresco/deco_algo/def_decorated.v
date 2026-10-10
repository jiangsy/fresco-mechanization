(** Decorated algorithmic judgments (paper appendices/decorated-algosub.tex).

    The decorated system re-runs the algorithmic subtyping/consistency over
    UNRESOLVED skeletons [R : uskl] (tagged quantifiers + dotted ghosts,
    extended with flexible variables), threading the tag context [Ψ] exactly
    as the declarative judgments do.  It is the bridge for the soundness
    proofs: ordinary run ⇒ decorated run ⇒ declarative derivation.

    Notations (paper forms):
      [{{ Θ ⊢[ Δ1 | Δ2 | P0 | Ψ ] R ∼ Q ⊣ Θ' }}da]  decorated consistency
      [{{ Θ ⊢[ NM | M | P0 | Ψ ] R ⩽ Q ⊣ Θ' }}da]   decorated subtyping
      [{{ ψ ≼[ M ] Q ⤳ Ψ }}da] / [{{ ψ ∼ Q ⤳ Ψ }}da] / [{{ C ⊩ ψ ⤳ Ψ }}da]  tag solving *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope fresco_da_scope.

Reserved Notation "{{ Θ ⊢[ Δ1 | Δ2 | P0 | Ψ ] R ∼ Q ⊣ Θ' }}da"
  (at level 0, Δ1 at level 0, Δ2 at level 0, P0 at level 0, Ψ at level 0, R at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢[  Δ1  |  Δ2  |  P0  |  Ψ  ]  R  ∼  Q  ⊣  Θ'  '}}da'").
Reserved Notation "{{ Θ ⊢[ NM | M | P0 | Ψ ] R ⩽ Q ⊣ Θ' }}da"
  (at level 0, NM at level 0, M at level 0, P0 at level 0, Ψ at level 0, R at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢[  NM  |  M  |  P0  |  Ψ  ]  R  ⩽  Q  ⊣  Θ'  '}}da'").
Reserved Notation "{{ ψ ≼[ M ] Q ⤳ Ψ }}da"
  (at level 0, M at level 0, Q at level 74, Ψ at level 74,
   format "'{{'  ψ  ≼[  M  ]  Q  ⤳  Ψ  '}}da'").
Reserved Notation "{{ ψ ∼ Q ⤳ Ψ }}da"
  (at level 0, Q at level 74, Ψ at level 74,
   format "'{{'  ψ  ∼  Q  ⤳  Ψ  '}}da'").
Reserved Notation "{{ C ⊩ ψ ⤳ Ψ }}da"
  (at level 0, ψ at level 74, Ψ at level 74,
   format "'{{'  C  ⊩  ψ  ⤳  Ψ  '}}da'").

(** Ghost-free unresolved skeletons: no ghosts of any kind.  Used for (i) the
    [N = TY] instantiation candidates (decorated TYPES φ, once combined with
    [is_dskl]) and (ii) the dotted-ghost-freeness side condition of the
    tag-solving FlexR rule (on decorated ψ, ghost-free ≡ dotted-ghost-free). *)
Inductive uskl_ghost_free : uskl -> Prop :=
| uskl_ghost_free__unit : uskl_ghost_free uskl_unit
| uskl_ghost_free__var : forall α, uskl_ghost_free (uskl_var_f α)
| uskl_ghost_free__arrow : forall R1 R2,
    uskl_ghost_free R1 -> uskl_ghost_free R2 ->
    uskl_ghost_free (uskl_arrow R1 R2)
| uskl_ghost_free__all_tag : forall L ε R,
    (forall α, α `notin` L ->
       uskl_ghost_free (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_ghost_free (uskl_all_tag ε R)
| uskl_ghost_free__all_syn : forall L R,
    (forall α, α `notin` L ->
       uskl_ghost_free (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_ghost_free (uskl_all_syn R).

(* Constructor hint (dedicated [fresco] db): ghost-freeness is dispatched
   structurally in metatheory. *)
#[export] Hint Constructors uskl_ghost_free : fresco.

(** [Θ ⊢^N tags{Ψg}{ψg}] (decorated ForallL premise, decorated-algosub:93):
    for [SK], ψg is a decorated skeleton ([is_dskl] + [tags{Ψg}]); for [TY],
    ψg is a decorated TYPE — additionally ghost-free. *)
Inductive a_tags_sort : a_sub_mode -> atoms -> uskl -> Prop :=
| a_tags_sort__sk : forall Ψ ψ,
    is_dskl ψ ->
    d_tags_skl Ψ ψ ->
    a_tags_sort a_sub_mode_sk Ψ ψ
| a_tags_sort__ty : forall Ψ ψ,
    is_dskl ψ ->
    d_tags_skl Ψ ψ ->
    uskl_ghost_free ψ ->
    a_tags_sort a_sub_mode_ty Ψ ψ.

(* ===================================================================== *)
(*  Decorated algorithmic consistency                                      *)
(*  [{{ Θ0 ⊢[Δ1|Δ2|P0|Ψ] R ∼ Q ⊣ Θ1 }}da]  (fig:decorated-alg-consistency;   *)
(*  rules unchanged from the ordinary system carry the empty tag context)  *)
(* ===================================================================== *)

Inductive a_consistag :
  atoms -> atoms -> pskl -> atoms -> aenv -> uskl -> pskl -> aenv -> Prop :=
(* — unchanged rules (empty tag context) — *)
| a_consistag__ghost : forall Δ1 Δ2 Ψ Θ0 P0,                  (* Ghost *)
    Δ2 ∩ ftvar_in_pskl P0 [=] empty ->
    Ψ [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] uskl_ghost ∼ P0 ⊣ Θ0 }}da
| a_consistag__unit : forall Δ1 Δ2 Ψ Θ0,                      (* Unit *)
    Ψ [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit | Ψ ] uskl_unit ∼ pskl_unit ⊣ Θ0 }}da
| a_consistag__rigid : forall Δ1 Δ2 Ψ Θ0 α,                   (* Rigid *)
    binds α abind_tvar Θ0 ->
    Ψ [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) | Ψ ] (uskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ0 }}da
| a_consistag__flex : forall Δ1 Δ2 Ψ Θ0 Θ1 α β,               (* Flex *)
    {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
    Ψ [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) | Ψ ] (uskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ1 }}da
(* FlexL / FlexR carry the plain rules' [P0 <> ◇] / [P <> ◇] guards
   ([a_consis__flex_l] / [__flex_r]; the SE-FlexR prose-completion, see
   docs/PAPER-GAPS.md): the paper inherits these rules UNCHANGED from the
   plain system (decorated-algosub.tex:237), so they say exactly what the
   plain rules say.  Decoration takes the guard from the plain rule it
   replays. *)
| a_consistag__flex_l : forall Δ1 Δ2 Ψ Θ0 Θ1 α P0,            (* FlexL *)
    a_non_flex Θ0 P0 ->
    P0 <> pskl_ghost ->
    {{ Θ0 ⊲[ nil ] α ≔ P0 ⊣ Θ1 }}a ->
    Ψ [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] (uskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ1 }}da
| a_consistag__flex_r : forall Δ1 Δ2 Ψ Θ0 Θ1 α P,            (* FlexR *)
    a_non_flex Θ0 P ->
    P <> pskl_ghost ->
    {{ Θ0 ⊲[ nil ] α ≔ P ⊣ Θ1 }}a ->
    Ψ [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) | Ψ ] (pskl_to_uskl P) ∼ (pskl_var_f α) ⊣ Θ1 }}da
(* — decorated rules (fig:decorated-alg-consistency) — *)
| a_consistag__ghostg : forall Δ1 Δ2 Ψ Θ0,                    (* GhostG *)
    Ψ [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | pskl_ghost | Ψ ] uskl_dot_ghost ∼ pskl_ghost ⊣ Θ0 }}da
| a_consistag__arrow : forall Δ1 Δ2 Ψ Ψ1 Ψ2 Θ0 Θ1 Θ2 P0a P0b R1 R2 Q1 Q2,
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0a | Ψ1 ] R1 ∼ Q1 ⊣ Θ1 }}da ->                (* Arrow *)
    {{ Θ1 ⊢[ Δ1 | Δ2 | P0b | Ψ2 ] R2 ∼ Q2 ⊣ Θ2 }}da ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) | Ψ ]
      (uskl_arrow R1 R2) ∼ (pskl_arrow Q1 Q2) ⊣ Θ2 }}da
| a_consistag__forall_inh_tagged : forall L Δ1 Δ2 Ψ Ψ0 Θ0 Θ1 ε P0 R Q,
    (forall α, α `notin` L ->                                 (* ForallInh, β1=ε *)
       {{ ((α ~ abind_tvar) ++ Θ0)
         ⊢[ (add α Δ1) | (add α Δ2)
           | (open_pskl_wrt_pskl P0 (pskl_var_f α)) | Ψ0 ]
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ⊣ ((α ~ abind_tvar) ++ Θ1) }}da) ->
    Ψ [=] add ε Ψ0 ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) | Ψ ]
      (uskl_all_tag ε R) ∼ (pskl_all_syn Q) ⊣ Θ1 }}da
| a_consistag__forall_inh_untagged : forall L Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,
    (forall α, α `notin` L ->                                 (* ForallInh, β1=· *)
       {{ ((α ~ abind_tvar) ++ Θ0)
         ⊢[ (add α Δ1) | (add α Δ2)
           | (open_pskl_wrt_pskl P0 (pskl_var_f α)) | Ψ ]
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ⊣ ((α ~ abind_tvar) ++ Θ1) }}da) ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) | Ψ ]
      (uskl_all_syn R) ∼ (pskl_all_syn Q) ⊣ Θ1 }}da
| a_consistag__forall_syn_tagged : forall L Δ1 Δ2 Ψ Θ0 Θ1 ε P0 R Q,
    (forall α, α `notin` L ->                                 (* ForallSyn, β1=ε *)
       {{ ((α ~ abind_tvar) ++ Θ0)
         ⊢[ Δ1 | (add α Δ2) | (pskl_univ_ghost P0) | Ψ ]
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ⊣ ((α ~ abind_tvar) ++ Θ1) }}da) ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) | Ψ ]
      (uskl_all_tag ε R) ∼ (pskl_all_syn Q) ⊣ Θ1 }}da
| a_consistag__forall_syn_untagged : forall L Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,
    (forall α, α `notin` L ->                                 (* ForallSyn, β1=· *)
       {{ ((α ~ abind_tvar) ++ Θ0)
         ⊢[ Δ1 | (add α Δ2) | (pskl_univ_ghost P0) | Ψ ]
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ⊣ ((α ~ abind_tvar) ++ Θ1) }}da) ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) | Ψ ]
      (uskl_all_syn R) ∼ (pskl_all_syn Q) ⊣ Θ1 }}da
| a_consistag__univ_ghost : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,      (* UnivGhost *)
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] R ∼ Q ⊣ Θ1 }}da ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) | Ψ ]
      (uskl_univ_ghost R) ∼ (pskl_univ_ghost Q) ⊣ Θ1 }}da
| a_consistag__univ_ghostg : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,     (* UnivGhostG *)
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] R ∼ Q ⊣ Θ1 }}da ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) | Ψ ]
      (uskl_dot_univ_ghost R) ∼ (pskl_univ_ghost Q) ⊣ Θ1 }}da
| a_consistag__univ_ghost1 : forall L Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,   (* UnivGhost1 *)
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ0)
         ⊢[ (add α Δ1) | Δ2
           | (open_pskl_wrt_pskl P0 (pskl_var_f α)) | Ψ ]
         (uskl_univ_ghost R) ∼ (open_pskl_wrt_pskl Q (pskl_var_f α))
         ⊣ ((α ~ abind_tvar) ++ Θ1) }}da) ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) | Ψ ]
      (uskl_univ_ghost R) ∼ (pskl_all_syn Q) ⊣ Θ1 }}da
| a_consistag__univ_ghost2 : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,     (* UnivGhost2 *)
    guarded_pskl P0 ->
    a_non_flex Θ0 P0 ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] R ∼ Q ⊣ Θ1 }}da ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] (uskl_univ_ghost R) ∼ Q ⊣ Θ1 }}da
| a_consistag__ghost_r : forall Δ1 Δ2 Ψ Θ0 R,                 (* GhostR *)
    Δ1 ∩ (ftvar_in_pskl ⌊ R ⌋ˢ) [=] empty ->
    Ψ [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | pskl_ghost | Ψ ] R ∼ ⌊ R ⌋ˢ ⊣ Θ0 }}da
| a_consistag__univ_ghost_r : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,    (* UnivGhostR *)
    guarded_uskl R ->
    a_non_flex Θ0 ⌊ R ⌋ˢ ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] R ∼ Q ⊣ Θ1 }}da ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) | Ψ ] R ∼ Q ⊣ Θ1 }}da
where "{{ Θ ⊢[ Δ1 | Δ2 | P0 | Ψ ] R ∼ Q ⊣ Θ' }}da" :=
  (a_consistag Δ1 Δ2 P0 Ψ Θ R Q Θ') : fresco_da_scope.

(* ===================================================================== *)
(*  Decorated algorithmic subtyping                                        *)
(*  [{{ Θ0 ⊢[N|M|P0|Ψ] R ⩽ Q ⊣ Θ1 }}da]  (fig:decorated-alg-subtyping)      *)
(* ===================================================================== *)

Inductive a_subtag :
  a_sub_mode -> mode -> pskl -> atoms -> aenv -> uskl -> pskl -> aenv -> Prop :=
| a_subtag__infer : forall NM Ψ Θ0 R,                         (* Infer *)
    Ψ [=] empty ->
    {{ Θ0 ⊢[ NM | mode_ti | pskl_ghost | Ψ ] R ⩽ ⌊ R ⌋ˢ ⊣ Θ0 }}da
| a_subtag__check : forall Ψ Θ0 Θ1 T B Q,                     (* Check *)
    (* SORT, mirroring [a_sub__check]: the paper's [guarded{T,B}]
       (decorated-algosub.tex:57) names an unresolved TYPE [T] and a type [B].
       ⚠️ Only the TARGET is mechanized here, unlike in the plain
       [a_sub__check].  The decorated system is a PROOF DEVICE consumed in
       one direction only (decoration [a_sub → a_subtag], then soundness
       [a_subtag → declarative]), so narrowing it buys no theorem and costs
       one: [a_subtag_decoration_var] rebuilds this row at a ρ-image of a
       STRIPPED subject, which would need a ghost-freeness analogue of
       [guarded_msubst_decorate] (a full structural induction through
       [msubst_uskl], where guardedness needs only a [destruct]).  The
       subject's sort is stated where it is load-bearing — on the plain
       rule. *)
    pskl_ghost_free B ->
    guarded_uskl T ->
    guarded_pskl B ->
    {{ Θ0 ⊢[ empty | empty | B | Ψ ] T ∼ Q ⊣ Θ1 }}da ->
    (* The consistency output [Q] is NOT pinned to [B], although the paper's
       [Check] (full-algo-spec.tex:799) writes it as [B]: when the target [B]
       is a type the output is only a type EQUIVALENT to [B].  Pinning it is
       unsound for a flexible subject [α̂] (all three witnesses — paper
       [U-FlexL] (:1665), [a_consis__flex_l], impl [U-FlexL]:182 — output
       [α̂]). *)
    {{ Θ0 ⊢[ a_sub_mode_ty | mode_tc | B | Ψ ] T ⩽ B ⊣ Θ1 }}da
| a_subtag__forall_r : forall α Ψ Θ0 Θ1 Ξ R B,                (* ForallR *)
    (* SORT, mirroring [a_sub__forall_r]: the target [∀α.B] is a TYPE. *)
    pskl_ghost_free (pskl_all_syn B) ->
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->                                          (* Barendregt (prose-completion) *)
    (* EXISTS-FRESH, mirroring [a_sub__forall_r]'s 2026-07-31 encoding fix:
       the junk suffix Ξ may lawfully mention the binder, so it cannot be
       one list shared by a cofinite family.  One sufficiently fresh α,
       Barendregt-conditioned; consumers re-freshen via renaming. *)
    α `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union`
      ftvar_in_uskl R `union` ftvar_in_pskl B ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ a_sub_mode_ty | mode_tc
        | (open_pskl_wrt_pskl B (pskl_var_f α)) | Ψ ]
      R ⩽ (open_pskl_wrt_pskl B (pskl_var_f α))
      ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}da ->
    {{ Θ0 ⊢[ a_sub_mode_ty | mode_tc | (pskl_all_syn B) | Ψ ]
      R ⩽ (pskl_all_syn B) ⊣ Θ1 }}da
| a_subtag__univ_ghost_r : forall Ψ Θ0 R,                     (* UnivGhostR *)
    guarded_uskl R ->
    Ψ [=] empty ->
    {{ Θ0 ⊢[ a_sub_mode_sk | mode_tc | pskl_ghost | Ψ ]
      R ⩽ (pskl_univ_ghost ⌊ R ⌋ˢ) ⊣ Θ0 }}da
| a_subtag__arrow : forall NM M Ψ Ψ1 Ψ2 Θ0 Θ1 Θ2 P0a P0b R1 R2 Q1 Q2,
    {{ Θ0 ⊢[ empty | empty | P0a | Ψ1 ] R1 ∼ Q1 ⊣ Θ1 }}da ->          (* Arrow *)
    {{ Θ1 ⊢[ NM | M | P0b | Ψ2 ] R2 ⩽ Q2 ⊣ Θ2 }}da ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Θ0 ⊢[ NM | (mode_fn M) | (pskl_arrow P0a P0b) | Ψ ]
      (uskl_arrow R1 R2) ⩽ (pskl_arrow Q1 Q2) ⊣ Θ2 }}da
(* The paper's [Ψg fresh] (decorated-algosub.tex:92) is prose-completed
   COFINITELY: the recursive premise holds for EVERY sufficiently fresh
   retagging (Ψg, ψg) of P1 — the tag analog of cofinite binder
   quantification (derivations are generic in the inert tag names).  The
   specific-pack completion [inter Ψg Ψ [=] empty] is too weak: the
   decoration lemmas (subtyping-proofs.tex:176-963) invert this node and
   rebuild it at an ENLARGED tag context Ψ ∪ Ψa, needing Ψg # Ψa — a
   freshness no inversion of a specific pack can supply (hazard noted in
   docs/DESIGN-subtyping.md §4.2).  Consumers recover a specific pack by
   instantiating at a decoration of P1 avoiding L ∪ Ψ
   ([pskl_decorate_exists]). *)
| a_subtag__forall_l_tagged : forall L NM M P0 Ψ Θ0 Θ1 ε R Q Ξ P1,
    M <> mode_ti ->                                           (* ForallL, β1=ε *)
    (guarded_pskl P0 \/ P0 = pskl_ghost) ->
    (forall α, α `notin` L ->
       a_extract Θ0 NM α M ⌊ open_uskl_wrt_uskl R (uskl_var_f α) ⌋ˢ P0 Ξ P1) ->
    uniq (Ξ ++ Θ0) ->                                         (* fresh Ξ (prose-completion) *)
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->                              (* DISCIPLINED wf (paper) *)
    (forall Ψg ψg,                                            (* Ψg fresh (cofinite) *)
       Ψg ∩ L [=] empty ->
       a_tags_sort NM Ψg ψg ->                                (* Θ,Ξ ⊢^N tags{Ψg}{ψg} *)
       ⌊ ψg ⌋ˢ = P1 ->                                        (* ⌊ψg⌋ = P1 *)
       {{ (Ξ ++ Θ0) ⊢[ NM | M | P0 | (Ψ `union` Ψg) ]
         (open_uskl_wrt_uskl R ψg) ⩽ Q ⊣ Θ1 }}da) ->
    {{ Θ0 ⊢[ NM | M | P0 | Ψ ] (uskl_all_tag ε R) ⩽ Q ⊣ Θ1 }}da
| a_subtag__forall_l_untagged : forall L NM M P0 Ψ Θ0 Θ1 R Q Ξ P1,
    M <> mode_ti ->                                           (* ForallL, β1=· *)
    (guarded_pskl P0 \/ P0 = pskl_ghost) ->
    (forall α, α `notin` L ->
       a_extract Θ0 NM α M ⌊ open_uskl_wrt_uskl R (uskl_var_f α) ⌋ˢ P0 Ξ P1) ->
    uniq (Ξ ++ Θ0) ->                                         (* fresh Ξ (prose-completion) *)
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->                              (* DISCIPLINED wf (paper) *)
    (forall Ψg ψg,                                            (* Ψg fresh (cofinite) *)
       Ψg ∩ L [=] empty ->
       a_tags_sort NM Ψg ψg ->
       ⌊ ψg ⌋ˢ = P1 ->
       {{ (Ξ ++ Θ0) ⊢[ NM | M | P0 | (Ψ `union` Ψg) ]
         (open_uskl_wrt_uskl R ψg) ⩽ Q ⊣ Θ1 }}da) ->
    {{ Θ0 ⊢[ NM | M | P0 | Ψ ] (uskl_all_syn R) ⩽ Q ⊣ Θ1 }}da
| a_subtag__ghost : forall M Ψ Θ0 P0,                         (* Ghost (unchanged) *)
    Ψ [=] empty ->
    {{ Θ0 ⊢[ a_sub_mode_sk | M | P0 | Ψ ] uskl_ghost ⩽ P0 ⊣ Θ0 }}da
| a_subtag__ghostg : forall M Ψ Θ0,                           (* GhostG *)
    Ψ [=] empty ->
    {{ Θ0 ⊢[ a_sub_mode_sk | M | pskl_ghost | Ψ ] uskl_dot_ghost ⩽ pskl_ghost ⊣ Θ0 }}da
| a_subtag__univ_ghost_l : forall M Ψ Θ0 Θ1 P0 R Q,           (* UnivGhostL *)
    M <> mode_ti ->
    {{ Θ0 ⊢[ a_sub_mode_sk | M | P0 | Ψ ] R ⩽ Q ⊣ Θ1 }}da ->
    {{ Θ0 ⊢[ a_sub_mode_sk | M | P0 | Ψ ] (uskl_univ_ghost R) ⩽ Q ⊣ Θ1 }}da
| a_subtag__univ_ghost_lg : forall M Ψ Θ0 Θ1 P0 R Q,          (* UnivGhostLG *)
    M <> mode_ti ->
    {{ Θ0 ⊢[ a_sub_mode_sk | M | P0 | Ψ ] R ⩽ Q ⊣ Θ1 }}da ->
    {{ Θ0 ⊢[ a_sub_mode_sk | M | P0 | Ψ ] (uskl_dot_univ_ghost R) ⩽ Q ⊣ Θ1 }}da
| a_subtag__flex_mono : forall NM M P0 Ψ Θ0 Θ1 α A,           (* FlexMono (unchanged) *)
    a_subtag_flex NM M P0 Θ0 nil α A Θ1 ->
    Ψ [=] empty ->
    {{ Θ0 ⊢[ NM | (mode_fn M) | P0 | Ψ ] (uskl_var_f α) ⩽ A ⊣ Θ1 }}da

(* The decorated flexible-variable walk.  The paper shows no rules for it —
   the walk is "inherited unchanged" with empty tag contexts — but its
   Flex-Solve/Flex-Assign premises re-enter DECORATED subtyping (the
   soundness proof recurses on them: lemma:sound-decorated-flex-subtyping's
   Flex-Solve case reads its premise as [asubtag],
   subtyping-proofs.tex:1119-1135), so the decorated system must be
   self-contained: mirroring [a_sub_flex] with the plain [a_sub] premise
   would leave the decorated soundness induction without a subderivation.
   All re-entries carry the empty tag context. *)
with a_subtag_flex :
  a_sub_mode -> mode -> pskl -> aenv -> aenv -> atom -> pskl -> aenv -> Prop :=
| a_subtag_flex__solve : forall NM M P0 Θ0 Θ1 Ξ α0 α β A,     (* Flex-Solve *)
    α <> β ->
    α `notin` add α0 (dom (Ξ ++ Θ0)) ->
    β `notin` add α0 (dom (Ξ ++ Θ0)) ->
    {{ (Ξ ++ (α0 ~ abind_flex_mono_def (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
        ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
      ⊢[ NM | (mode_fn M) | P0 | empty ]
      (uskl_arrow (uskl_var_f α) (uskl_var_f β)) ⩽ A ⊣ Θ1 }}da ->
    a_subtag_flex NM M P0 ((α0 ~ abind_flex_mono) ++ Θ0) Ξ α0 A Θ1
| a_subtag_flex__assign : forall NM M P0 Θ0 Θ1 Ξ α β τ A,     (* Flex-Assign *)
    (* merge + re-enter the MAIN decorated judgment with the substituted
       subject (paper full-algo-spec.tex:888-894; audit F1) *)
    β `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    {{ (Ξ ++ Θ0) ⊢[ NM | (mode_fn M)
                 | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) | empty ]
      (pskl_to_uskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))
      ⩽ A ⊣ Θ1 }}da ->
    a_subtag_flex NM M P0 ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α A
      ((β ~ abind_flex_mono_def τ) ++ Θ1)
| a_subtag_flex__depend : forall NM M P0 Θ0 Θ1 Ξ α β A,       (* Flex-Depend *)
    α <> β ->
    β `in` ftvar_in_pskl P0 ->
    a_subtag_flex NM M P0 Θ0 (Ξ ++ (β ~ abind_flex_mono)) α A Θ1 ->
    a_subtag_flex NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α A Θ1
| a_subtag_flex__skip : forall NM M P0 Θ0 Θ1 Ξ α β A,         (* Flex-Skip *)
    α <> β ->
    β `notin` ftvar_in_pskl P0 ->
    β `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    a_subtag_flex NM M P0 Θ0 Ξ α A Θ1 ->
    a_subtag_flex NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α A
      ((β ~ abind_flex_mono) ++ Θ1)
| a_subtag_flex__skip_rigid : forall NM M P0 Θ0 Θ1 Ξ α β A,   (* Flex-SkipRigid *)
    α <> β ->                               (* prose-completion (Barendregt) *)
    β `notin` ftvar_in_pskl P0 ->
    β `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    a_subtag_flex NM M P0 Θ0 Ξ α A Θ1 ->
    a_subtag_flex NM M P0 ((β ~ abind_tvar) ++ Θ0) Ξ α A ((β ~ abind_tvar) ++ Θ1)
(* the decorated mirrors of [a_sub_flex__skip_tm_var] / [__skip_tm_skl]
   (Flex-SkipTmVar, full-algo-spec.tex:914) *)
| a_subtag_flex__skip_tm_var : forall NM M P0 Θ0 Θ1 Ξ α x Q A,
    x `notin` dom Θ1 ->
    a_subtag_flex NM M P0 Θ0 Ξ α A Θ1 ->
    a_subtag_flex NM M P0 ((x ~ abind_var_typ Q) ++ Θ0) Ξ α A
      ((x ~ abind_var_typ Q) ++ Θ1)
| a_subtag_flex__skip_tm_skl : forall NM M P0 Θ0 Θ1 Ξ α x Q A,
    x `notin` dom Θ1 ->
    a_subtag_flex NM M P0 Θ0 Ξ α A Θ1 ->
    a_subtag_flex NM M P0 ((x ~ abind_var_skl Q) ++ Θ0) Ξ α A
      ((x ~ abind_var_skl Q) ++ Θ1)
where "{{ Θ ⊢[ NM | M | P0 | Ψ ] R ⩽ Q ⊣ Θ' }}da" :=
  (a_subtag NM M P0 Ψ Θ R Q Θ') : fresco_da_scope.

(* ===================================================================== *)
(*  Decorated tag solving  (fig:decorated-tag-solving)                    *)
(*  [{{ C ⊩ ψ ⤳ Ψ }}da]: the tags of ψ solved by the constraint list C.          *)
(*  Contribution-only: constraints add tags only where their structure     *)
(*  matches ψ's.                                                          *)
(* ===================================================================== *)

Inductive a_solvetag_sub : uskl -> mode -> pskl -> atoms -> Prop :=
| a_solvetag_sub__var : forall α M Q Ψ,                       (* SSub-Var / Flex *)
    Ψ [=] empty ->
    {{ (uskl_var_f α) ≼[ M ] Q ⤳ Ψ }}da
| a_solvetag_sub__forall_l : forall L ε ψ M Q Ψ,              (* SSub-ForallL *)
    (forall β, β `notin` L ->
       {{ (open_uskl_wrt_uskl ψ (uskl_var_f β)) ≼[ M ] Q ⤳ Ψ }}da) ->
    {{ (uskl_all_tag ε ψ) ≼[ M ] Q ⤳ Ψ }}da
| a_solvetag_sub__univ_ghost_lg : forall ψ M Q Ψ,             (* SSub-UnivGhostLG *)
    {{ ψ ≼[ M ] Q ⤳ Ψ }}da ->
    {{ (uskl_dot_univ_ghost ψ) ≼[ M ] Q ⤳ Ψ }}da
| a_solvetag_sub__vacuous : forall ψ M Ψ,                     (* SSub-Vacuous *)
    Ψ [=] empty ->
    {{ ψ ≼[ M ] pskl_ghost ⤳ Ψ }}da
| a_solvetag_sub__check : forall ψ B Ψ,                       (* SSub-Check *)
    (* SORT, mirroring [a_solve_sub__check]: target is a TYPE. *)
    pskl_ghost_free B ->
    guarded_uskl ψ ->
    guarded_pskl B ->
    {{ ψ ∼ B ⤳ Ψ }}da ->
    {{ ψ ≼[ mode_tc ] B ⤳ Ψ }}da
| a_solvetag_sub__forall_r : forall L ψ B Ψ,                  (* SSub-ForallR *)
    (* SORT, mirroring [a_solve_sub__forall_r]: TARGET only. *)
    pskl_ghost_free (pskl_all_syn B) ->
    (forall β, β `notin` L ->
       {{ ψ ≼[ mode_tc ] (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ψ }}da) ->
    {{ ψ ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ψ }}da
| a_solvetag_sub__arrow : forall ψ1 ψ2 M Q1 Q2 Ψ Ψ1 Ψ2,       (* SSub-Arrow *)
    {{ ψ1 ∼ Q1 ⤳ Ψ1 }}da ->
    {{ ψ2 ≼[ M ] Q2 ⤳ Ψ2 }}da ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ (uskl_arrow ψ1 ψ2) ≼[ (mode_fn M) ] (pskl_arrow Q1 Q2) ⤳ Ψ }}da

with a_solvetag_eq : uskl -> pskl -> atoms -> Prop :=
| a_solvetag_eq__unit : forall Ψ,                             (* SEq-Unit *)
    Ψ [=] empty ->
    {{ uskl_unit ∼ pskl_unit ⤳ Ψ }}da
| a_solvetag_eq__var : forall α Q Ψ,                          (* SEq-Var / FlexL *)
    Ψ [=] empty ->
    {{ (uskl_var_f α) ∼ Q ⤳ Ψ }}da
| a_solvetag_eq__vacuous : forall ψ Ψ,                        (* SEq-Vacuous *)
    Ψ [=] empty ->
    {{ ψ ∼ pskl_ghost ⤳ Ψ }}da
| a_solvetag_eq__arrow : forall ψ1 ψ2 Q1 Q2 Ψ Ψ1 Ψ2,          (* SEq-Arrow *)
    {{ ψ1 ∼ Q1 ⤳ Ψ1 }}da ->
    {{ ψ2 ∼ Q2 ⤳ Ψ2 }}da ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ (uskl_arrow ψ1 ψ2) ∼ (pskl_arrow Q1 Q2) ⤳ Ψ }}da
| a_solvetag_eq__forall_inh : forall L ε ψ Q Ψ Ψ0,            (* SEq-ForallInh *)
    (forall β, β `notin` L ->
       {{ (open_uskl_wrt_uskl ψ (uskl_var_f β)) ∼
         (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ψ0 }}da) ->
    Ψ [=] add ε Ψ0 ->
    {{ (uskl_all_tag ε ψ) ∼ (pskl_all_syn Q) ⤳ Ψ }}da
| a_solvetag_eq__univ_ghostg : forall ψ Q Ψ,                  (* SEq-UnivGhostG *)
    {{ ψ ∼ Q ⤳ Ψ }}da ->
    {{ (uskl_dot_univ_ghost ψ) ∼ (pskl_univ_ghost Q) ⤳ Ψ }}da
| a_solvetag_eq__forall_syn : forall L ε ψ Q Ψ,               (* SEq-ForallSyn *)
    (forall β, β `notin` L ->
       {{ (open_uskl_wrt_uskl ψ (uskl_var_f β)) ∼ (pskl_univ_ghost Q) ⤳ Ψ }}da) ->
    {{ (uskl_all_tag ε ψ) ∼ (pskl_univ_ghost Q) ⤳ Ψ }}da
| a_solvetag_eq__univ_ghost_r : forall ψ Q Ψ,                 (* SEq-UnivGhostR *)
    guarded_pskl ⌊ ψ ⌋ˢ ->
    {{ ψ ∼ Q ⤳ Ψ }}da ->
    {{ ψ ∼ (pskl_univ_ghost Q) ⤳ Ψ }}da
| a_solvetag_eq__flex_r : forall ψ α Ψ,                       (* SEq-FlexR *)
    uskl_ghost_free ψ ->
    Ψ [=] empty ->
    {{ ψ ∼ (pskl_var_f α) ⤳ Ψ }}da
where "{{ ψ ≼[ M ] Q ⤳ Ψ }}da" := (a_solvetag_sub ψ M Q Ψ) : fresco_da_scope
  and "{{ ψ ∼ Q ⤳ Ψ }}da" := (a_solvetag_eq ψ Q Ψ) : fresco_da_scope.

(* [{{ C ⊩ ψ ⤳ Ψ }}da] (top box). *)
Inductive a_solvetag : a_cstrs -> uskl -> atoms -> Prop :=
| a_solvetag__empty : forall ψ Ψ,
    Ψ [=] empty ->
    {{ nil ⊩ ψ ⤳ Ψ }}da
| a_solvetag__sub : forall M Q ψ Ψ,
    {{ ψ ≼[ M ] Q ⤳ Ψ }}da ->
    {{ (a_cstr_sub M Q :: nil) ⊩ ψ ⤳ Ψ }}da
| a_solvetag__eq : forall Q C ψ Ψ Ψ1 Ψ2,
    {{ ψ ∼ Q ⤳ Ψ1 }}da ->
    {{ C ⊩ ψ ⤳ Ψ2 }}da ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ (a_cstr_eq Q :: C) ⊩ ψ ⤳ Ψ }}da
where "{{ C ⊩ ψ ⤳ Ψ }}da" := (a_solvetag C ψ Ψ) : fresco_da_scope.
