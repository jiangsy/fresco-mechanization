(** Decorated algorithmic judgements (paper [subtyping-proofs.tex] /
    [decorated-algosub.tex]) — the bridge layer for proving ordinary
    algorithmic subtyping/consistency SOUND w.r.t. the declarative system.

    SCAFFOLDING to mechanise the statements and check the paper's reasoning;
    local admits/placeholders are expected (the paper's decorated→declarative
    soundness is itself [\wenhao{TODO}]).

    Encoding reuse: the decorated SOURCE skeleton [S] (with tagged ∀
    [\foralltag{δ}], dotted ghosts [\HoleG]/[\TopHoleG]) is exactly the
    declarative unresolved skeleton [uskl] ([uskl_all_etag] = [\foralltag],
    [uskl_holeg]/[uskl_topholeg] = the ghosts).  The tag [δ]/[ε] is an [εvar];
    the tag context [Ψ] is [atoms] (like the declarative [Δ]).  The outputs [Q]
    and target [P0] stay ordinary [pskl].  Flex/rigid variables share the
    [ptypvar] atom namespace across [uskl]/[pskl]. *)

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

(* ===================================================================== *)
(*  Erasure  ⌊·⌋ : uskl -> pskl  (decorated-algosub.tex:35-45).            *)
(*  Homomorphic; tags/ghosts erased: [all_etag]→[all_syn], [holeg]→[hole], *)
(*  [topholeg]→[tophole].                                                 *)
(* ===================================================================== *)
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
  | uskl_topholeg R0 => pskl_tophole (uskl_to_pskl R0)
  end.

Notation "⌊ R ⌋ᵤ" := (uskl_to_pskl R) (at level 0, R at level 0) : type_scope.

(* [a_tag_support Θ NM Ψ ψ] — paper [\tagsupp{Θ}{tags(Ψ)}{syn(ψ)}]
   (decorated-algosub.tex:99): the decorated instantiation [ψ] is supported by
   the tag set [Ψ] under [Θ] (sort [NM]).  PLACEHOLDER for the scaffolding —
   the faithful judgement (tag well-formedness of the syn-painted [ψ]) is
   deferred. *)
Inductive a_tag_support : aenv -> a_sub_mode -> atoms -> uskl -> Prop :=
| a_tag_support__any : forall Θ NM Ψ ψ, a_tag_support Θ NM Ψ ψ.

(* ===================================================================== *)
(*  Decorated algorithmic consistency                                     *)
(*  [a_consistag P0 Ψ Θ0 S Q Θ1]  =  [⊢ᶜ_tag[P0][Ψ] Θ0 ▷ S ◁ Q ⊲ Θ1]       *)
(*  (decorated-algosub.tex fig:decorated-alg-consistency).  S : uskl       *)
(*  (decorated source), Q : pskl (output), P0 : pskl (target), Ψ : atoms.  *)
(*  The flex-variable rules (Flex/FlexL/FlexR) are inherited from           *)
(*  [a_consis] with empty tag context — OMITTED here (scaffolding).         *)
(* ===================================================================== *)
Inductive a_consistag : pskl -> atoms -> aenv -> uskl -> pskl -> aenv -> Prop :=
| a_consistag__ghostg : forall Θ0,                          (* GhostG *)
    a_consistag pskl_hole empty Θ0 uskl_holeg pskl_hole Θ0
| a_consistag__arrow : forall Θ0 Θ1 Θ2 P1' P2' S1 S2 Q1 Q2 Ψ1 Ψ2,   (* Arrow *)
    a_consistag P1' Ψ1 Θ0 S1 Q1 Θ1 ->
    a_consistag P2' Ψ2 Θ1 S2 Q2 Θ2 ->
    a_consistag (pskl_arrow P1' P2') (Ψ1 `union` Ψ2) Θ0
      (uskl_arrow S1 S2) (pskl_arrow Q1 Q2) Θ2
| a_consistag__forall_inh : forall L δ Θ0 Θ1 P0 R Q Ψ,      (* ForallInh *)
    (forall α, α `notin` L ->
       a_consistag (open_pskl_wrt_pskl P0 (pskl_var_f α)) Ψ ((α ~ abind_tvar) ++ Θ0)
         (open_uskl_wrt_uskl R (uskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α)) ((α ~ abind_tvar) ++ Θ1)) ->
    a_consistag (pskl_all_syn P0) (Ψ `union` singleton δ) Θ0
      (uskl_all_etag δ R) (pskl_all_syn Q) Θ1
| a_consistag__forall_syn : forall L δ Θ0 Θ1 P0 R Q Ψ,      (* ForallSyn *)
    (forall α, α `notin` L ->
       a_consistag (pskl_tophole P0) Ψ ((α ~ abind_tvar) ++ Θ0)
         (open_uskl_wrt_uskl R (uskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α)) ((α ~ abind_tvar) ++ Θ1)) ->
    a_consistag (pskl_tophole P0) Ψ Θ0 (uskl_all_etag δ R) (pskl_all_syn Q) Θ1
| a_consistag__univ_ghost : forall Θ0 Θ1 P0 R Q Ψ,         (* UnivGhost *)
    a_consistag P0 Ψ Θ0 R Q Θ1 ->
    a_consistag (pskl_tophole P0) Ψ Θ0 (uskl_tophole R) (pskl_tophole Q) Θ1
| a_consistag__univ_ghostg : forall Θ0 Θ1 P0 R Q Ψ,        (* UnivGhostG *)
    a_consistag P0 Ψ Θ0 R Q Θ1 ->
    a_consistag (pskl_tophole P0) Ψ Θ0 (uskl_topholeg R) (pskl_tophole Q) Θ1
| a_consistag__univ_ghost1 : forall L Θ0 Θ1 P0 R Q Ψ,      (* UnivGhost1 *)
    (forall α, α `notin` L ->
       a_consistag (open_pskl_wrt_pskl P0 (pskl_var_f α)) Ψ ((α ~ abind_tvar) ++ Θ0)
         (uskl_tophole R)
         (open_pskl_wrt_pskl Q (pskl_var_f α)) ((α ~ abind_tvar) ++ Θ1)) ->
    a_consistag (pskl_all_syn P0) Ψ Θ0 (uskl_tophole R) (pskl_all_syn Q) Θ1
| a_consistag__univ_ghost2 : forall Θ0 Θ1 P0 R Q Ψ,        (* UnivGhost2 *)
    guarded_pskl P0 ->
    a_non_flex Θ0 P0 ->
    a_consistag P0 Ψ Θ0 R Q Θ1 ->
    a_consistag P0 Ψ Θ0 (uskl_tophole R) Q Θ1
| a_consistag__ghost_r : forall Θ0 R,                      (* GhostR *)
    a_consistag pskl_hole empty Θ0 R (uskl_to_pskl R) Θ0
| a_consistag__univ_ghost_r : forall Θ0 Θ1 P0 R Q Ψ,       (* UnivGhostR *)
    guarded_pskl (uskl_to_pskl R) ->
    a_non_flex Θ0 (uskl_to_pskl R) ->
    a_consistag P0 Ψ Θ0 R Q Θ1 ->
    a_consistag (pskl_tophole P0) Ψ Θ0 R Q Θ1.

(* ===================================================================== *)
(*  Decorated algorithmic subtyping                                       *)
(*  [a_subtag N M P0 Ψ Θ0 S Q Θ1] = [⊢_tag[N][M][P0][Ψ] Θ0 ▷ S ◁ Q ⊲ Θ1]   *)
(*  (decorated-algosub.tex fig:decorated-alg-subtyping).  Depends on        *)
(*  [a_consistag]; [ForallL] uses [a_extract] + the [a_tag_support]         *)
(*  placeholder.  Inherited-unchanged ordinary rules omitted (scaffolding). *)
(* ===================================================================== *)
Inductive a_subtag : a_sub_mode -> mode -> pskl -> atoms -> aenv -> uskl -> pskl -> aenv -> Prop :=
| a_subtag__check : forall Θ0 Θ1 T B Ψ,                     (* Check *)
    guarded_pskl (uskl_to_pskl T) -> guarded_pskl B ->
    a_consistag B Ψ Θ0 T B Θ1 ->
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
    a_consistag P1' Ψ1 Θ0 S1 Q1 Θ1 ->
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
| a_subtag__univ_ghost_lg : forall M Θ0 Θ1 P0 R Q Ψ,       (* UnivGhostLG *)
    M <> mode_ti ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 R Q Θ1 ->
    a_subtag a_sub_mode_sk M P0 Ψ Θ0 (uskl_topholeg R) Q Θ1.
