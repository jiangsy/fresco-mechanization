(** Decorated algorithmic judgments (paper appendices/decorated-algosub.tex).

    The decorated system re-runs the algorithmic subtyping/consistency over
    UNRESOLVED skeletons [R : uskl] (tagged quantifiers + dotted ghosts,
    extended with flexible variables), threading the tag context [Ψ] exactly
    as the declarative judgments do.  It is the bridge for the soundness
    proofs: ordinary run ⇒ decorated run ⇒ declarative derivation.

    Notations (paper forms):
      [Θ ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] R ∼˙ Q ⊣ Θ']  decorated consistency
      [Θ ⊢ᵗ[ NM | M | P0 | Ψ ] R ⩽˙ Q ⊣ Θ']   decorated subtyping
      [ψ ≼ᵗ[ M ] Q ⤳ Ψ] / [ψ ∼ᵗ Q ⤳ Ψ] / [C ⊩ᵗ ψ ⤳ Ψ]  tag solving *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.

Set Implicit Arguments.

Reserved Notation "Θ ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] R ∼˙ Q ⊣ Θ'"
  (at level 70, Δ1 at level 0, Δ2 at level 0, P0 at level 0, Ψ at level 0,
   R at level 0, Q at level 0, Θ' at level 0, no associativity).
Reserved Notation "Θ ⊢ᵗ[ NM | M | P0 | Ψ ] R ⩽˙ Q ⊣ Θ'"
  (at level 70, NM at level 0, M at level 0, P0 at level 0, Ψ at level 0,
   R at level 0, Q at level 0, Θ' at level 0, no associativity).
Reserved Notation "ψ ≼ᵗ[ M ] Q ⤳ Ψ"
  (at level 75, M at level 0, Q at level 74, Ψ at level 74, no associativity).
Reserved Notation "ψ ∼ᵗ Q ⤳ Ψ"
  (at level 75, Q at level 74, Ψ at level 74, no associativity).
Reserved Notation "C ⊩ᵗ ψ ⤳ Ψ"
  (at level 75, ψ at level 74, Ψ at level 74, no associativity).

(* ===================================================================== *)
(*  Erasure  ⌊R⌋ : uskl → pskl  (decorated-algosub.tex:27-38)             *)
(*  Homomorphic; non-trivial cases: ∀^β1 ↦ ∀, HoleG ↦ □, TopHoleG ↦ ∀◇     *)
(* ===================================================================== *)

Fixpoint uskl_to_pskl (R : uskl) : pskl :=
  match R with
  | uskl_unit => pskl_unit
  | uskl_var_b n => pskl_var_b n
  | uskl_var_f α => pskl_var_f α
  | uskl_arrow R1 R2 => pskl_arrow (uskl_to_pskl R1) (uskl_to_pskl R2)
  | uskl_all_syn R0 => pskl_all_syn (uskl_to_pskl R0)
  | uskl_all_etag _ R0 => pskl_all_syn (uskl_to_pskl R0)
  | uskl_hole => pskl_hole
  | uskl_tophole R0 => pskl_tophole (uskl_to_pskl R0)
  | uskl_holeg => pskl_hole
  | uskl_topholeg R0 => pskl_tophole (uskl_to_pskl R0)
  end.

Notation "⌊ R ⌋ˢ" := (uskl_to_pskl R) (at level 0, R at level 99).

(** Plain skeletons as (untagged) unresolved skeletons: the embedding used
    by the flexible-variable rules, which are inherited unchanged from the
    ordinary algorithmic consistency (their subjects are plain skeletons). *)
Fixpoint pskl_to_uskl (P : pskl) : uskl :=
  match P with
  | pskl_unit => uskl_unit
  | pskl_var_b n => uskl_var_b n
  | pskl_var_f α => uskl_var_f α
  | pskl_arrow P1 P2 => uskl_arrow (pskl_to_uskl P1) (pskl_to_uskl P2)
  | pskl_all_syn P0 => uskl_all_syn (pskl_to_uskl P0)
  | pskl_hole => uskl_hole
  | pskl_tophole P0 => uskl_tophole (pskl_to_uskl P0)
  end.

(** Ghost-free unresolved skeletons: no ghosts of any kind.  Used for (i) the
    [N = TY] instantiation candidates (decorated TYPES φ, once combined with
    [is_tskl]) and (ii) the dotted-ghost-freeness side condition of the
    tag-solving FlexR rule (on decorated ψ, ghost-free ≡ dotted-ghost-free). *)
Inductive uskl_ghost_free : uskl -> Prop :=
| uskl_ghost_free__unit : uskl_ghost_free uskl_unit
| uskl_ghost_free__var : forall α, uskl_ghost_free (uskl_var_f α)
| uskl_ghost_free__arrow : forall R1 R2,
    uskl_ghost_free R1 -> uskl_ghost_free R2 ->
    uskl_ghost_free (uskl_arrow R1 R2)
| uskl_ghost_free__all_etag : forall L ε R,
    (forall α, α `notin` L ->
       uskl_ghost_free (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_ghost_free (uskl_all_etag ε R)
| uskl_ghost_free__all_syn : forall L R,
    (forall α, α `notin` L ->
       uskl_ghost_free (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_ghost_free (uskl_all_syn R).

(* Constructor hint (dedicated [frost] db): ghost-freeness is dispatched
   structurally in metatheory. *)
#[export] Hint Constructors uskl_ghost_free : frost.

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
(*  [Θ0 ⊢ᵗ[Δ1|Δ2|P0|Ψ] R ∼˙ Q ⊣ Θ1]  (fig:decorated-alg-consistency;        *)
(*  rules unchanged from the ordinary system carry the empty tag context)  *)
(* ===================================================================== *)

Inductive a_consistag :
  atoms -> atoms -> pskl -> atoms -> aenv -> uskl -> pskl -> aenv -> Prop :=
(* — unchanged rules (empty tag context) — *)
| a_consistag__ghost : forall Δ1 Δ2 Ψ Θ0 P0,                  (* Ghost *)
    Δ2 ∩ ftvar_in_pskl P0 [=] empty ->
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] uskl_hole ∼˙ P0 ⊣ Θ0
| a_consistag__unit : forall Δ1 Δ2 Ψ Θ0,                      (* Unit *)
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | pskl_unit | Ψ ] uskl_unit ∼˙ pskl_unit ⊣ Θ0
| a_consistag__rigid : forall Δ1 Δ2 Ψ Θ0 α,                   (* Rigid *)
    binds α abind_tvar Θ0 ->
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_var_f α) | Ψ ] (uskl_var_f α) ∼˙ (pskl_var_f α) ⊣ Θ0
| a_consistag__flex : forall Δ1 Δ2 Ψ Θ0 Θ1 α β,               (* Flex *)
    Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 ->
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_var_f β) | Ψ ] (uskl_var_f α) ∼˙ (pskl_var_f α) ⊣ Θ1
| a_consistag__flex_l : forall Δ1 Δ2 Ψ Θ0 Θ1 α P0,            (* FlexL *)
    a_non_flex Θ0 P0 ->
    Θ0 ⊲[ nil ] α ≔ P0 ⊣ Θ1 ->
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] (uskl_var_f α) ∼˙ (pskl_var_f α) ⊣ Θ1
| a_consistag__flex_r : forall Δ1 Δ2 Ψ Θ0 Θ1 α P,            (* FlexR *)
    a_non_flex Θ0 P ->
    Θ0 ⊲[ nil ] α ≔ P ⊣ Θ1 ->
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_var_f α) | Ψ ] (pskl_to_uskl P) ∼˙ (pskl_var_f α) ⊣ Θ1
(* — decorated rules (fig:decorated-alg-consistency) — *)
| a_consistag__ghostg : forall Δ1 Δ2 Ψ Θ0,                    (* GhostG *)
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | pskl_hole | Ψ ] uskl_holeg ∼˙ pskl_hole ⊣ Θ0
| a_consistag__arrow : forall Δ1 Δ2 Ψ Ψ1 Ψ2 Θ0 Θ1 Θ2 P0a P0b R1 R2 Q1 Q2,
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0a | Ψ1 ] R1 ∼˙ Q1 ⊣ Θ1 ->                (* Arrow *)
    Θ1 ⊢ᵗ[ Δ1 | Δ2 | P0b | Ψ2 ] R2 ∼˙ Q2 ⊣ Θ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_arrow P0a P0b) | Ψ ]
      (uskl_arrow R1 R2) ∼˙ (pskl_arrow Q1 Q2) ⊣ Θ2
| a_consistag__forall_inh_tagged : forall L Δ1 Δ2 Ψ Ψ0 Θ0 Θ1 ε P0 R Q,
    (forall α, α `notin` L ->                                 (* ForallInh, β1=ε *)
       ((α ~ abind_tvar) ++ Θ0)
         ⊢ᵗ[ (add α Δ1) | (add α Δ2)
           | (open_pskl_wrt_pskl P0 (pskl_var_f α)) | Ψ0 ]
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼˙
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
    Ψ [=] add ε Ψ0 ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_all_syn P0) | Ψ ]
      (uskl_all_etag ε R) ∼˙ (pskl_all_syn Q) ⊣ Θ1
| a_consistag__forall_inh_untagged : forall L Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,
    (forall α, α `notin` L ->                                 (* ForallInh, β1=· *)
       ((α ~ abind_tvar) ++ Θ0)
         ⊢ᵗ[ (add α Δ1) | (add α Δ2)
           | (open_pskl_wrt_pskl P0 (pskl_var_f α)) | Ψ ]
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼˙
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_all_syn P0) | Ψ ]
      (uskl_all_syn R) ∼˙ (pskl_all_syn Q) ⊣ Θ1
| a_consistag__forall_syn_tagged : forall L Δ1 Δ2 Ψ Θ0 Θ1 ε P0 R Q,
    (forall α, α `notin` L ->                                 (* ForallSyn, β1=ε *)
       ((α ~ abind_tvar) ++ Θ0)
         ⊢ᵗ[ Δ1 | (add α Δ2) | (pskl_tophole P0) | Ψ ]
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼˙
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_tophole P0) | Ψ ]
      (uskl_all_etag ε R) ∼˙ (pskl_all_syn Q) ⊣ Θ1
| a_consistag__forall_syn_untagged : forall L Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,
    (forall α, α `notin` L ->                                 (* ForallSyn, β1=· *)
       ((α ~ abind_tvar) ++ Θ0)
         ⊢ᵗ[ Δ1 | (add α Δ2) | (pskl_tophole P0) | Ψ ]
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼˙
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_tophole P0) | Ψ ]
      (uskl_all_syn R) ∼˙ (pskl_all_syn Q) ⊣ Θ1
| a_consistag__univ_ghost : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,      (* UnivGhost *)
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] R ∼˙ Q ⊣ Θ1 ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_tophole P0) | Ψ ]
      (uskl_tophole R) ∼˙ (pskl_tophole Q) ⊣ Θ1
| a_consistag__univ_ghostg : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,     (* UnivGhostG *)
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] R ∼˙ Q ⊣ Θ1 ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_tophole P0) | Ψ ]
      (uskl_topholeg R) ∼˙ (pskl_tophole Q) ⊣ Θ1
| a_consistag__univ_ghost1 : forall L Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,   (* UnivGhost1 *)
    (forall α, α `notin` L ->
       ((α ~ abind_tvar) ++ Θ0)
         ⊢ᵗ[ (add α Δ1) | Δ2
           | (open_pskl_wrt_pskl P0 (pskl_var_f α)) | Ψ ]
         (uskl_tophole R) ∼˙ (open_pskl_wrt_pskl Q (pskl_var_f α))
         ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_all_syn P0) | Ψ ]
      (uskl_tophole R) ∼˙ (pskl_all_syn Q) ⊣ Θ1
| a_consistag__univ_ghost2 : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,     (* UnivGhost2 *)
    guarded_pskl P0 ->
    a_non_flex Θ0 P0 ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] R ∼˙ Q ⊣ Θ1 ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] (uskl_tophole R) ∼˙ Q ⊣ Θ1
| a_consistag__ghost_r : forall Δ1 Δ2 Ψ Θ0 R,                 (* GhostR *)
    Δ1 ∩ (ftvar_in_pskl ⌊ R ⌋ˢ) [=] empty ->
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | pskl_hole | Ψ ] R ∼˙ ⌊ R ⌋ˢ ⊣ Θ0
| a_consistag__univ_ghost_r : forall Δ1 Δ2 Ψ Θ0 Θ1 P0 R Q,    (* UnivGhostR *)
    guarded_uskl R ->
    a_non_flex Θ0 ⌊ R ⌋ˢ ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] R ∼˙ Q ⊣ Θ1 ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_tophole P0) | Ψ ] R ∼˙ Q ⊣ Θ1
where "Θ ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] R ∼˙ Q ⊣ Θ'" :=
  (a_consistag Δ1 Δ2 P0 Ψ Θ R Q Θ') : type_scope.

(* ===================================================================== *)
(*  Decorated algorithmic subtyping                                        *)
(*  [Θ0 ⊢ᵗ[N|M|P0|Ψ] R ⩽˙ Q ⊣ Θ1]  (fig:decorated-alg-subtyping)           *)
(* ===================================================================== *)

Inductive a_subtag :
  a_sub_mode -> mode -> pskl -> atoms -> aenv -> uskl -> pskl -> aenv -> Prop :=
| a_subtag__infer : forall NM Ψ Θ0 R,                         (* Infer *)
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ NM | mode_ti | pskl_hole | Ψ ] R ⩽˙ ⌊ R ⌋ˢ ⊣ Θ0
| a_subtag__check : forall Ψ Θ0 Θ1 T B Q,                     (* Check *)
    guarded_uskl T ->
    guarded_pskl B ->
    Θ0 ⊢ᵗ[ empty | empty | B | Ψ ] T ∼˙ Q ⊣ Θ1 ->
    (* The consistency output [Q] is NOT used (paper full-algo-spec.tex:1441:
       "when the output Q is not used"); when the target [B] is a type it is
       a type EQUIVALENT to [B] (:1444), not literally [B].  Pinning it to [B]
       is unsound for a flexible subject [α̂] (all three witnesses — paper
       [FlexL]:1655, [a_consis__flex_l], impl [U-FlexL]:182 — output [α̂]). *)
    Θ0 ⊢ᵗ[ a_sub_mode_ty | mode_tc | B | Ψ ] T ⩽˙ B ⊣ Θ1
| a_subtag__forall_r : forall α Ψ Θ0 Θ1 Ξ R B,                (* ForallR *)
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->                                          (* Barendregt (prose-completion) *)
    (* EXISTS-FRESH, mirroring [a_sub__forall_r]'s 2026-07-31 encoding fix:
       the junk suffix Ξ may lawfully mention the binder, so it cannot be
       one list shared by a cofinite family.  One sufficiently fresh α,
       Barendregt-conditioned; consumers re-freshen via renaming. *)
    α `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union`
      ftvar_in_uskl R `union` ftvar_in_pskl B ->
    ((α ~ abind_tvar) ++ Θ0)
      ⊢ᵗ[ a_sub_mode_ty | mode_tc
        | (open_pskl_wrt_pskl B (pskl_var_f α)) | Ψ ]
      R ⩽˙ (open_pskl_wrt_pskl B (pskl_var_f α))
      ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) ->
    Θ0 ⊢ᵗ[ a_sub_mode_ty | mode_tc | (pskl_all_syn B) | Ψ ]
      R ⩽˙ (pskl_all_syn B) ⊣ Θ1
| a_subtag__univ_ghost_r : forall Ψ Θ0 R,                     (* UnivGhostR *)
    guarded_uskl R ->
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ a_sub_mode_sk | mode_tc | pskl_hole | Ψ ]
      R ⩽˙ (pskl_tophole ⌊ R ⌋ˢ) ⊣ Θ0
| a_subtag__arrow : forall NM M Ψ Ψ1 Ψ2 Θ0 Θ1 Θ2 P0a P0b R1 R2 Q1 Q2,
    Θ0 ⊢ᵗ[ empty | empty | P0a | Ψ1 ] R1 ∼˙ Q1 ⊣ Θ1 ->          (* Arrow *)
    Θ1 ⊢ᵗ[ NM | M | P0b | Ψ2 ] R2 ⩽˙ Q2 ⊣ Θ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    Θ0 ⊢ᵗ[ NM | (mode_fn M) | (pskl_arrow P0a P0b) | Ψ ]
      (uskl_arrow R1 R2) ⩽˙ (pskl_arrow Q1 Q2) ⊣ Θ2
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
    (guarded_pskl P0 \/ P0 = pskl_hole) ->
    (forall α, α `notin` L ->
       a_extract Θ0 NM α M ⌊ open_uskl_wrt_uskl R (uskl_var_f α) ⌋ˢ P0 Ξ P1) ->
    uniq (Ξ ++ Θ0) ->                                         (* fresh Ξ (prose-completion) *)
    (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P1 ->                              (* DISCIPLINED wf (paper) *)
    (forall Ψg ψg,                                            (* Ψg fresh (cofinite) *)
       Ψg ∩ L [=] empty ->
       a_tags_sort NM Ψg ψg ->                                (* Θ,Ξ ⊢^N tags{Ψg}{ψg} *)
       ⌊ ψg ⌋ˢ = P1 ->                                        (* ⌊ψg⌋ = P1 *)
       (Ξ ++ Θ0) ⊢ᵗ[ NM | M | P0 | (Ψ `union` Ψg) ]
         (open_uskl_wrt_uskl R ψg) ⩽˙ Q ⊣ Θ1) ->
    Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] (uskl_all_etag ε R) ⩽˙ Q ⊣ Θ1
| a_subtag__forall_l_untagged : forall L NM M P0 Ψ Θ0 Θ1 R Q Ξ P1,
    M <> mode_ti ->                                           (* ForallL, β1=· *)
    (guarded_pskl P0 \/ P0 = pskl_hole) ->
    (forall α, α `notin` L ->
       a_extract Θ0 NM α M ⌊ open_uskl_wrt_uskl R (uskl_var_f α) ⌋ˢ P0 Ξ P1) ->
    uniq (Ξ ++ Θ0) ->                                         (* fresh Ξ (prose-completion) *)
    (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P1 ->                              (* DISCIPLINED wf (paper) *)
    (forall Ψg ψg,                                            (* Ψg fresh (cofinite) *)
       Ψg ∩ L [=] empty ->
       a_tags_sort NM Ψg ψg ->
       ⌊ ψg ⌋ˢ = P1 ->
       (Ξ ++ Θ0) ⊢ᵗ[ NM | M | P0 | (Ψ `union` Ψg) ]
         (open_uskl_wrt_uskl R ψg) ⩽˙ Q ⊣ Θ1) ->
    Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] (uskl_all_syn R) ⩽˙ Q ⊣ Θ1
| a_subtag__ghost : forall M Ψ Θ0 P0,                         (* Ghost (unchanged) *)
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ a_sub_mode_sk | M | P0 | Ψ ] uskl_hole ⩽˙ P0 ⊣ Θ0
| a_subtag__ghostg : forall M Ψ Θ0,                           (* GhostG *)
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ a_sub_mode_sk | M | pskl_hole | Ψ ] uskl_holeg ⩽˙ pskl_hole ⊣ Θ0
| a_subtag__univ_ghost_l : forall M Ψ Θ0 Θ1 P0 R Q,           (* UnivGhostL *)
    M <> mode_ti ->
    Θ0 ⊢ᵗ[ a_sub_mode_sk | M | P0 | Ψ ] R ⩽˙ Q ⊣ Θ1 ->
    Θ0 ⊢ᵗ[ a_sub_mode_sk | M | P0 | Ψ ] (uskl_tophole R) ⩽˙ Q ⊣ Θ1
| a_subtag__univ_ghost_lg : forall M Ψ Θ0 Θ1 P0 R Q,          (* UnivGhostLG *)
    M <> mode_ti ->
    Θ0 ⊢ᵗ[ a_sub_mode_sk | M | P0 | Ψ ] R ⩽˙ Q ⊣ Θ1 ->
    Θ0 ⊢ᵗ[ a_sub_mode_sk | M | P0 | Ψ ] (uskl_topholeg R) ⩽˙ Q ⊣ Θ1
| a_subtag__flex_mono : forall NM M P0 Ψ Θ0 Θ1 α A,           (* FlexMono (unchanged) *)
    a_subtag_flex NM M P0 Θ0 nil α A Θ1 ->
    Ψ [=] empty ->
    Θ0 ⊢ᵗ[ NM | (mode_fn M) | P0 | Ψ ] (uskl_var_f α) ⩽˙ A ⊣ Θ1

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
    (Ξ ++ (α0 ~ abind_flex_mono_def (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
        ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
      ⊢ᵗ[ NM | (mode_fn M) | P0 | empty ]
      (uskl_arrow (uskl_var_f α) (uskl_var_f β)) ⩽˙ A ⊣ Θ1 ->
    a_subtag_flex NM M P0 ((α0 ~ abind_flex_mono) ++ Θ0) Ξ α0 A Θ1
| a_subtag_flex__assign : forall NM M P0 Θ0 Θ1 Ξ α β τ A,     (* Flex-Assign *)
    (* merge + re-enter the MAIN decorated judgment with the substituted
       subject (paper full-algo-spec.tex:888-894; audit F1) *)
    β `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    (Ξ ++ Θ0) ⊢ᵗ[ NM | (mode_fn M)
                 | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) | empty ]
      (pskl_to_uskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))
      ⩽˙ A ⊣ Θ1 ->
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
   ([paper-gap] Flex-SkipTmVar, algo/def_extra.v) *)
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
where "Θ ⊢ᵗ[ NM | M | P0 | Ψ ] R ⩽˙ Q ⊣ Θ'" :=
  (a_subtag NM M P0 Ψ Θ R Q Θ') : type_scope.

(* ===================================================================== *)
(*  Decorated tag solving  (fig:decorated-tag-solving)                    *)
(*  [C ⊩ᵗ ψ ⤳ Ψ]: the tags of ψ solved by the constraint list C.          *)
(*  Contribution-only: constraints add tags only where their structure     *)
(*  matches ψ's.                                                          *)
(* ===================================================================== *)

Inductive a_solvetag_sub : uskl -> mode -> pskl -> atoms -> Prop :=
| a_solvetag_sub__var : forall α M Q Ψ,                       (* SSub-Var / Flex *)
    Ψ [=] empty ->
    (uskl_var_f α) ≼ᵗ[ M ] Q ⤳ Ψ
| a_solvetag_sub__forall_l : forall L ε ψ M Q Ψ,              (* SSub-ForallL *)
    (forall β, β `notin` L ->
       (open_uskl_wrt_uskl ψ (uskl_var_f β)) ≼ᵗ[ M ] Q ⤳ Ψ) ->
    (uskl_all_etag ε ψ) ≼ᵗ[ M ] Q ⤳ Ψ
| a_solvetag_sub__univ_ghost_lg : forall ψ M Q Ψ,             (* SSub-UnivGhostLG *)
    ψ ≼ᵗ[ M ] Q ⤳ Ψ ->
    (uskl_topholeg ψ) ≼ᵗ[ M ] Q ⤳ Ψ
| a_solvetag_sub__vacuous : forall ψ M Ψ,                     (* SSub-Vacuous *)
    Ψ [=] empty ->
    ψ ≼ᵗ[ M ] pskl_hole ⤳ Ψ
| a_solvetag_sub__check : forall ψ B Ψ,                       (* SSub-Check *)
    guarded_uskl ψ ->
    guarded_pskl B ->
    ψ ∼ᵗ B ⤳ Ψ ->
    ψ ≼ᵗ[ mode_tc ] B ⤳ Ψ
| a_solvetag_sub__forall_r : forall L ψ B Ψ,                  (* SSub-ForallR *)
    (forall β, β `notin` L ->
       ψ ≼ᵗ[ mode_tc ] (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ψ) ->
    ψ ≼ᵗ[ mode_tc ] (pskl_all_syn B) ⤳ Ψ
| a_solvetag_sub__arrow : forall ψ1 ψ2 M Q1 Q2 Ψ Ψ1 Ψ2,       (* SSub-Arrow *)
    ψ1 ∼ᵗ Q1 ⤳ Ψ1 ->
    ψ2 ≼ᵗ[ M ] Q2 ⤳ Ψ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    (uskl_arrow ψ1 ψ2) ≼ᵗ[ (mode_fn M) ] (pskl_arrow Q1 Q2) ⤳ Ψ

with a_solvetag_eq : uskl -> pskl -> atoms -> Prop :=
| a_solvetag_eq__unit : forall Ψ,                             (* SEq-Unit *)
    Ψ [=] empty ->
    uskl_unit ∼ᵗ pskl_unit ⤳ Ψ
| a_solvetag_eq__var : forall α Q Ψ,                          (* SEq-Var / FlexL *)
    Ψ [=] empty ->
    (uskl_var_f α) ∼ᵗ Q ⤳ Ψ
| a_solvetag_eq__vacuous : forall ψ Ψ,                        (* SEq-Vacuous *)
    Ψ [=] empty ->
    ψ ∼ᵗ pskl_hole ⤳ Ψ
| a_solvetag_eq__arrow : forall ψ1 ψ2 Q1 Q2 Ψ Ψ1 Ψ2,          (* SEq-Arrow *)
    ψ1 ∼ᵗ Q1 ⤳ Ψ1 ->
    ψ2 ∼ᵗ Q2 ⤳ Ψ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    (uskl_arrow ψ1 ψ2) ∼ᵗ (pskl_arrow Q1 Q2) ⤳ Ψ
| a_solvetag_eq__forall_inh : forall L ε ψ Q Ψ Ψ0,            (* SEq-ForallInh *)
    (forall β, β `notin` L ->
       (open_uskl_wrt_uskl ψ (uskl_var_f β)) ∼ᵗ
         (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ψ0) ->
    Ψ [=] add ε Ψ0 ->
    (uskl_all_etag ε ψ) ∼ᵗ (pskl_all_syn Q) ⤳ Ψ
| a_solvetag_eq__univ_ghostg : forall ψ Q Ψ,                  (* SEq-UnivGhostG *)
    ψ ∼ᵗ Q ⤳ Ψ ->
    (uskl_topholeg ψ) ∼ᵗ (pskl_tophole Q) ⤳ Ψ
| a_solvetag_eq__forall_syn : forall L ε ψ Q Ψ,               (* SEq-ForallSyn *)
    (forall β, β `notin` L ->
       (open_uskl_wrt_uskl ψ (uskl_var_f β)) ∼ᵗ (pskl_tophole Q) ⤳ Ψ) ->
    (uskl_all_etag ε ψ) ∼ᵗ (pskl_tophole Q) ⤳ Ψ
| a_solvetag_eq__univ_ghost_r : forall ψ Q Ψ,                 (* SEq-UnivGhostR *)
    guarded_pskl ⌊ ψ ⌋ˢ ->
    ψ ∼ᵗ Q ⤳ Ψ ->
    ψ ∼ᵗ (pskl_tophole Q) ⤳ Ψ
| a_solvetag_eq__flex_r : forall ψ α Ψ,                       (* SEq-FlexR *)
    uskl_ghost_free ψ ->
    Ψ [=] empty ->
    ψ ∼ᵗ (pskl_var_f α) ⤳ Ψ
where "ψ ≼ᵗ[ M ] Q ⤳ Ψ" := (a_solvetag_sub ψ M Q Ψ) : type_scope
  and "ψ ∼ᵗ Q ⤳ Ψ" := (a_solvetag_eq ψ Q Ψ) : type_scope.

(* [C ⊩ᵗ ψ ⤳ Ψ] (top box). *)
Inductive a_solvetag : a_cstrs -> uskl -> atoms -> Prop :=
| a_solvetag__empty : forall ψ Ψ,
    Ψ [=] empty ->
    nil ⊩ᵗ ψ ⤳ Ψ
| a_solvetag__sub : forall M Q ψ Ψ,
    ψ ≼ᵗ[ M ] Q ⤳ Ψ ->
    (a_cstr_sub M Q :: nil) ⊩ᵗ ψ ⤳ Ψ
| a_solvetag__eq : forall Q C ψ Ψ Ψ1 Ψ2,
    ψ ∼ᵗ Q ⤳ Ψ1 ->
    C ⊩ᵗ ψ ⤳ Ψ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    (a_cstr_eq Q :: C) ⊩ᵗ ψ ⤳ Ψ
where "C ⊩ᵗ ψ ⤳ Ψ" := (a_solvetag C ψ Ψ) : type_scope.
