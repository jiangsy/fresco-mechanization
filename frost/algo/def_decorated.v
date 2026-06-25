(** Decorated algorithmic judgements (paper [subtyping-proofs.tex] /
    [decorated-algosub.tex]) — the bridge layer for proving ordinary
    algorithmic subtyping/consistency SOUND w.r.t. the declarative system.

    SCAFFOLDING to mechanise the statements and check the paper's reasoning;
    local admits/placeholders are expected (the paper's decorated→declarative
    soundness is itself [\wenhao{TODO}]).

    Encoding reuse: the decorated SOURCE skeleton [S] (with tagged ∀
    [\foralltag{δ}], dotted ghosts [\HoleG]/[\TopHoleG]) is exactly the
    declarative unresolved skeleton [uskl] ([uskl_all_etag] = [\foralltag],
    [uskl_holeg]/[uskl_topholeg] = the ghosts).  The tag [δ]/[ε] is an [εvar].
    The tag context [Ψ] is a SET [atoms] (paper set-union semantics, matching
    the type-level declarative [d_consis]/[d_sub]).  Outputs [Q] and target
    [P0] stay ordinary [pskl]; flex/rigid variables share the [ptypvar] atom
    namespace across [uskl]/[pskl].

    F16 (deferred): the SKELETON-level declarative judgements
    [d_pat_consis]/[d_pat_sub] still carry the tag context as a [list atom]
    (with non-idempotent [++]); they should be [atoms] like [d_consis]/[d_sub].
    Until that declarative refactor, the soundness bridge ([prop_decorated.v])
    converts [Ψ] via [AtomSetImpl.elements]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.def_ott.
Require Import src.frost.prop_ln.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.

Set Implicit Arguments.

(* Erasure  ⌊·⌋ : uskl -> pskl  (decorated-algosub.tex:35-45). *)
Fixpoint uskl_to_pskl (R : uskl) : pskl :=
  match R with
  | uskl_unit => pskl_unit
  | uskl_var_b n => pskl_var_b n
  | uskl_var_f X => pskl_var_f X
  | uskl_arrow R1 R2 => pskl_arrow (uskl_to_pskl R1) (uskl_to_pskl R2)
  | uskl_all_syn R0 => pskl_all_syn (uskl_to_pskl R0)
  | uskl_all_etag _ R0 => pskl_all_syn (uskl_to_pskl R0)
  | uskl_hole => pskl_hole
  | uskl_tophole R0 => pskl_tophole (uskl_to_pskl R0)
  | uskl_holeg => pskl_hole
  | uskl_topholeg _ R0 => pskl_tophole (uskl_to_pskl R0)
  end.

(* [a_tag_support Θ NM Ψ ψ] — paper [\tagsupp] (decorated-algosub.tex:99).
   PLACEHOLDER for the scaffolding. *)
Inductive a_tag_support : aenv -> a_sub_mode -> atoms -> uskl -> Prop :=
| a_tag_support__any : forall Θ NM Ψ ψ, a_tag_support Θ NM Ψ ψ.

Reserved Notation "Θ0 ⊢ᶜ[ P0 | Ψ ] S ⤳ Q ⊣ Θ1"
  (at level 80, P0 at level 0, Ψ at level 0, S at level 0, Q at level 0,
   Θ1 at level 0, no associativity).
Reserved Notation "Θ0 ⊢ˢ[ NM | M | P0 | Ψ ] S ⤳ Q ⊣ Θ1"
  (at level 80, NM at level 0, M at level 0, P0 at level 0, Ψ at level 0,
   S at level 0, Q at level 0, Θ1 at level 0, no associativity).

(* ===================================================================== *)
(*  Decorated algorithmic consistency  (fig:decorated-alg-consistency).    *)
(*  Flex-variable / inherited-unchanged rules OMITTED (scaffolding).        *)
(* ===================================================================== *)
Inductive a_consistag : pskl -> atoms -> aenv -> uskl -> pskl -> aenv -> Prop :=
| a_consistag__ghostg : forall Θ0,                          (* GhostG *)
    Θ0 ⊢ᶜ[ pskl_hole | empty ] uskl_holeg ⤳ pskl_hole ⊣ Θ0
| a_consistag__arrow : forall Θ0 Θ1 Θ2 P1' P2' S1 S2 Q1 Q2 Ψ1 Ψ2,   (* Arrow *)
    Θ0 ⊢ᶜ[ P1' | Ψ1 ] S1 ⤳ Q1 ⊣ Θ1 ->
    Θ1 ⊢ᶜ[ P2' | Ψ2 ] S2 ⤳ Q2 ⊣ Θ2 ->
    Θ0 ⊢ᶜ[ (pskl_arrow P1' P2') | (Ψ1 `union` Ψ2) ]
      (uskl_arrow S1 S2) ⤳ (pskl_arrow Q1 Q2) ⊣ Θ2
| a_consistag__forall_inh : forall L δ Θ0 Θ1 P0 R Q Ψ,      (* ForallInh *)
    (forall α, α `notin` L ->
       ((α ~ abind_tvar) ++ Θ0)
         ⊢ᶜ[ (open_pskl_wrt_pskl P0 (pskl_var_f α)) | Ψ ]
         (open_uskl_wrt_uskl R (uskl_var_f α)) ⤳
         (open_pskl_wrt_pskl Q (pskl_var_f α)) ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
    Θ0 ⊢ᶜ[ (pskl_all_syn P0) | (singleton δ `union` Ψ) ]
      (uskl_all_etag δ R) ⤳ (pskl_all_syn Q) ⊣ Θ1
| a_consistag__forall_syn : forall L δ Θ0 Θ1 P0 R Q Ψ,      (* ForallSyn *)
    (forall α, α `notin` L ->
       ((α ~ abind_tvar) ++ Θ0) ⊢ᶜ[ (pskl_tophole P0) | Ψ ]
         (open_uskl_wrt_uskl R (uskl_var_f α)) ⤳
         (open_pskl_wrt_pskl Q (pskl_var_f α)) ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
    Θ0 ⊢ᶜ[ (pskl_tophole P0) | Ψ ] (uskl_all_etag δ R) ⤳ (pskl_all_syn Q) ⊣ Θ1
| a_consistag__univ_ghost : forall Θ0 Θ1 P0 R Q Ψ,         (* UnivGhost *)
    Θ0 ⊢ᶜ[ P0 | Ψ ] R ⤳ Q ⊣ Θ1 ->
    Θ0 ⊢ᶜ[ (pskl_tophole P0) | Ψ ] (uskl_tophole R) ⤳ (pskl_tophole Q) ⊣ Θ1
| a_consistag__univ_ghostg : forall Θ0 Θ1 P0 ε R Q Ψ,      (* UnivGhostG *)
    (* Tagged ghost: like [forall_inh], the ghost tag [ε] is added to the
       output [Ψ] (declarative [d_pat_consis__topholeg]: [Ψ,δ] from [Ψ]). *)
    Θ0 ⊢ᶜ[ P0 | Ψ ] R ⤳ Q ⊣ Θ1 ->
    Θ0 ⊢ᶜ[ (pskl_tophole P0) | (singleton ε `union` Ψ) ]
      (uskl_topholeg ε R) ⤳ (pskl_tophole Q) ⊣ Θ1
| a_consistag__univ_ghost1 : forall L Θ0 Θ1 P0 R Q Ψ,      (* UnivGhost1 *)
    (forall α, α `notin` L ->
       ((α ~ abind_tvar) ++ Θ0) ⊢ᶜ[ (open_pskl_wrt_pskl P0 (pskl_var_f α)) | Ψ ]
         (uskl_tophole R) ⤳
         (open_pskl_wrt_pskl Q (pskl_var_f α)) ⊣ ((α ~ abind_tvar) ++ Θ1)) ->
    Θ0 ⊢ᶜ[ (pskl_all_syn P0) | Ψ ] (uskl_tophole R) ⤳ (pskl_all_syn Q) ⊣ Θ1
| a_consistag__univ_ghost2 : forall Θ0 Θ1 P0 R Q Ψ,        (* UnivGhost2 *)
    guarded_pskl P0 ->
    a_non_flex Θ0 P0 ->
    Θ0 ⊢ᶜ[ P0 | Ψ ] R ⤳ Q ⊣ Θ1 ->
    Θ0 ⊢ᶜ[ P0 | Ψ ] (uskl_tophole R) ⤳ Q ⊣ Θ1
| a_consistag__ghost_r : forall Θ0 R,                      (* GhostR (F15) *)
    Θ0 ⊢ᶜ[ pskl_hole | empty ] R ⤳ (uskl_to_pskl R) ⊣ Θ0
| a_consistag__univ_ghost_r : forall Θ0 Θ1 P0 R Q Ψ,       (* UnivGhostR (F15) *)
    guarded_pskl (uskl_to_pskl R) ->
    a_non_flex Θ0 (uskl_to_pskl R) ->
    Θ0 ⊢ᶜ[ P0 | Ψ ] R ⤳ Q ⊣ Θ1 ->
    Θ0 ⊢ᶜ[ (pskl_tophole P0) | Ψ ] R ⤳ Q ⊣ Θ1
where "Θ0 ⊢ᶜ[ P0 | Ψ ] S ⤳ Q ⊣ Θ1" := (a_consistag P0 Ψ Θ0 S Q Θ1) : type_scope.

(* ===================================================================== *)
(*  Decorated algorithmic subtyping  (fig:decorated-alg-subtyping).        *)
(* ===================================================================== *)
Inductive a_subtag : a_sub_mode -> mode -> pskl -> atoms -> aenv -> uskl -> pskl -> aenv -> Prop :=
| a_subtag__check : forall Θ0 Θ1 T B Ψ,                     (* Check *)
    guarded_pskl (uskl_to_pskl T) -> guarded_pskl B ->
    Θ0 ⊢ᶜ[ B | Ψ ] T ⤳ B ⊣ Θ1 ->
    a_subtag a_sub_mode_ty mode_tc B Ψ Θ0 T B Θ1
| a_subtag__forall_r : forall L Θ0 Θ1 Ξ S B Ψ,             (* ForallR *)
    a_suffix Ξ ->
    (forall α, α `notin` L ->
       a_subtag a_sub_mode_ty mode_tc (open_pskl_wrt_pskl B (pskl_var_f α)) Ψ
         ((α ~ abind_tvar) ++ Θ0) S (open_pskl_wrt_pskl B (pskl_var_f α))
         (Ξ ++ (α ~ abind_tvar) ++ Θ1)) ->
    a_subtag a_sub_mode_ty mode_tc (pskl_all_syn B) Ψ Θ0 S (pskl_all_syn B) Θ1
| a_subtag__univ_ghost_r : forall Θ0 S,                    (* UnivGhostR *)
    guarded_pskl (uskl_to_pskl S) ->
    a_subtag a_sub_mode_sk mode_tc pskl_hole empty Θ0 S
      (pskl_tophole (uskl_to_pskl S)) Θ0
| a_subtag__arrow : forall NM M Θ0 Θ1 Θ2 P1' P2' S1 S2 Q1 Q2 Ψ1 Ψ2,  (* Arrow *)
    Θ0 ⊢ᶜ[ P1' | Ψ1 ] S1 ⤳ Q1 ⊣ Θ1 ->
    a_subtag NM M P2' Ψ2 Θ1 S2 Q2 Θ2 ->
    a_subtag NM (mode_fn M) (pskl_arrow P1' P2') (Ψ1 `union` Ψ2) Θ0
      (uskl_arrow S1 S2) (pskl_arrow Q1 Q2) Θ2
| a_subtag__forall_l : forall L NM M P0 δ Θ0 Θ1 R Q Ψ Ψg ψg Ξ P1,  (* ForallL *)
    M <> mode_ti ->
    (guarded_pskl P0 \/ P0 = pskl_hole) ->
    a_wf_pskl (Ξ ++ Θ0) P1 ->
    a_tag_support (Ξ ++ Θ0) NM Ψg ψg ->
    uskl_to_pskl ψg = P1 ->
    (forall α, α `notin` L ->
       a_extract α M (uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α))) P0 Ξ P1) ->
    a_subtag NM M P0 (Ψ `union` Ψg) (Ξ ++ Θ0)
      (open_uskl_wrt_uskl R ψg) Q Θ1 ->
    a_subtag NM M P0 Ψ Θ0 (uskl_all_etag δ R) Q Θ1
| a_subtag__ghostg : forall M Θ0,                          (* GhostG *)
    a_subtag a_sub_mode_sk M pskl_hole empty Θ0 uskl_holeg pskl_hole Θ0
| a_subtag__univ_ghost_l : forall M Θ0 Θ1 P0 R Q Ψ,        (* UnivGhostL *)
    M <> mode_ti ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 R Q Θ1 ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 (uskl_tophole R) Q Θ1
| a_subtag__univ_ghost_lg : forall M Θ0 Θ1 P0 ε R Q Ψ,     (* UnivGhostL (tagged) *)
    (* Tagged ghost on the LHS; subtyping leaves [Ψ] unchanged
       (declarative [d_pat_sub__univ_ghost_lg]: [Ψ] from [Ψ]). *)
    M <> mode_ti ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 R Q Θ1 ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 (uskl_topholeg ε R) Q Θ1
where "Θ0 ⊢ˢ[ NM | M | P0 | Ψ ] S ⤳ Q ⊣ Θ1" := (a_subtag NM M P0 Ψ Θ0 S Q Θ1) : type_scope.
