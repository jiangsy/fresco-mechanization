(** Frost declarative-system definitions for the current split syntax.

    This file follows [language.ott]'s latest categories directly:
    [ptyp], [btyp], [utyp], [pskl], [bskl], [uskl]. Here [pskl] is the
    plain skeleton category; synthesised/inherited colours belong to
    [bskl]. It intentionally does
    not reintroduce the removed legacy unified type layer. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.

Set Implicit Arguments.

(* All [⨟]-prefixed judgments keep their middle context slot at level 74
   (not 75): the single-Δ refinement [Γ ⨟ Δ ⊢ᵣ …] needs its
   inner slots below the notation level to avoid self-recursion, and
   camlp5 requires every notation sharing the [_ ⨟ _] prefix to agree on
   that slot's level.  Context slots only ever hold [Γ]/[Δ] built from
   [++]/[::]/[~] (all ≤ 60), so level 74 is ample. *)
(* Convention (paper-faithful): the ∀-scope context [Δ] comes AFTER [Γ]
   ([Γ ⨟ Δ ⊢ …]); the tag context [Ψ] comes BEFORE [Γ] ([Ψ ⨟ Γ ⊢ …]). *)
Reserved Notation "Γ ⨟ Δ ⊢ₚₛ P"
  (at level 75, Δ at level 74, P at level 75, no associativity).
Reserved Notation "Γ ⊢ᵦ B"
  (at level 75, B at level 75, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ᵤ C"
  (at level 75, Γ at level 74, C at level 75, no associativity).
Reserved Notation "Γ ⨟ Δ ⊢ᵤₛ R"
  (at level 75, Δ at level 74, R at level 75, no associativity).
Reserved Notation "Ψ ⨟ Γ ⊢ C ∼ B"
  (at level 75, Γ at level 74, C at level 74, B at level 74, no associativity).
Reserved Notation "Ψ ⨟ Γ ⊢[ M ] C ⩽ B"
  (at level 75, Γ at level 74, M at level 0, C at level 74, B at level 74,
   no associativity).
Reserved Notation "Γ ⨟ Δ ⊢ᵣ Q ⊳ P"
  (at level 75, Δ at level 74,
   Q at level 74, P at level 74, no associativity).
Reserved Notation "Ψ ⨟ Γ ⊢ₛ R ∼ Q"
  (at level 75, Γ at level 74, R at level 74, Q at level 74, no associativity).
Reserved Notation "Ψ ⨟ Γ ⊢ₛ[ M ] R ⩽ Q"
  (at level 75, Γ at level 74, M at level 0, R at level 74, Q at level 74,
   no associativity).

(* ===================================================================== *)
(*  Well-formedness                                                       *)
(* ===================================================================== *)

Reserved Notation "Γ ⊢ₚ A"
  (at level 75, A at level 75, no associativity).
Inductive d_wf_ptyp : list (atom * dbind) -> ptyp -> Prop :=
| d_wf_ptyp__unit : forall Γ,
    Γ ⊢ₚ ptyp_unit
| d_wf_ptyp__var : forall Γ X,
    binds X dbind_tvar Γ ->
    Γ ⊢ₚ (ptyp_var_f X)
| d_wf_ptyp__arrow : forall Γ A1 A2,
    Γ ⊢ₚ A1 ->
    Γ ⊢ₚ A2 ->
    Γ ⊢ₚ (ptyp_arrow A1 A2)
| d_wf_ptyp__all : forall L Γ A,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ₚ (open_ptyp_wrt_ptyp A (ptyp_var_f X))) ->
    Γ ⊢ₚ (ptyp_all A)
where "Γ ⊢ₚ A" := (d_wf_ptyp Γ A) : type_scope.

Inductive d_wf_btyp : list (atom * dbind) -> btyp -> Prop :=
| d_wf_btyp__unit : forall Γ,
    Γ ⊢ᵦ btyp_unit
| d_wf_btyp__var : forall Γ X,
    binds X dbind_tvar Γ ->
    Γ ⊢ᵦ (btyp_var_f X)
| d_wf_btyp__arrow : forall Γ B1 B2,
    Γ ⊢ᵦ B1 ->
    Γ ⊢ᵦ B2 ->
    Γ ⊢ᵦ (btyp_arrow B1 B2)
| d_wf_btyp__all_syn : forall L Γ B,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ᵦ (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Γ ⊢ᵦ (btyp_all_syn B)
| d_wf_btyp__all_inh : forall L Γ B,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ᵦ (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Γ ⊢ᵦ (btyp_all_inh B)
where "Γ ⊢ᵦ B" := (d_wf_btyp Γ B) : type_scope.

(* WT: I updated the notation in the paper to separate well-formedness
of unresolved/tagged types and their linear uses of tags. But I still
write Γ ⊢ T # Δ as checking both, which is consistent with the
definition here.
%
OK, now I saw d_tags defined below. Then we can just remove Δ here.

Done (WT review): the tag context is dropped — [d_wf_utyp] is now pure
well-scopedness ([Γ ⊢ C]); the linear tag content of a tagged type is
checked separately by [d_tags] below. *)
Reserved Notation "Γ ⊢ᵤ C"
  (at level 75, C at level 75, no associativity).
Inductive d_wf_utyp : list (atom * dbind) -> utyp -> Prop :=
| d_wf_utyp__unit : forall Γ,
    Γ ⊢ᵤ utyp_unit
| d_wf_utyp__var : forall Γ X,
    binds X dbind_tvar Γ ->
    Γ ⊢ᵤ (utyp_var_f X)
| d_wf_utyp__arrow : forall Γ C1 C2,
    Γ ⊢ᵤ C1 ->
    Γ ⊢ᵤ C2 ->
    Γ ⊢ᵤ (utyp_arrow C1 C2)
| d_wf_utyp__all_syn : forall L Γ C,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ᵤ (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    Γ ⊢ᵤ (utyp_all_syn C)
| d_wf_utyp__all_etag : forall L Γ ε C,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ᵤ (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    Γ ⊢ᵤ (utyp_all_etag ε C)
where "Γ ⊢ᵤ C" := (d_wf_utyp Γ C) : type_scope.

(* Skeleton well-formedness [Γ ⨟ Δ ⊢ₚₛ P] (declarative.tex:1300).  [Δ] is the
   ∀-scope context (paper's [Δ], the inherited-∀ vars), kept SEPARATE from the
   tvar context [Γ]; the two carry different types so a var occurrence consults
   either.  This is the paper's [Γ∣Δ] presentation with [Δ] as a separate set
   (∀-vars go to [Δ]; the [⫯] rule clears [Δ], matching [Γ\Δ]). *)
Inductive d_wf_pskl : list (atom * dbind) -> list atom -> pskl -> Prop :=
| d_wf_pskl__unit : forall Γ Δ,
    Γ ⨟ Δ ⊢ₚₛ pskl_unit
| d_wf_pskl__var : forall Γ Δ X,
    List.In X Δ \/ binds X dbind_tvar Γ ->
    Γ ⨟ Δ ⊢ₚₛ (pskl_var_f X)
| d_wf_pskl__arrow : forall Γ Δ P1 P2,
    Γ ⨟ Δ ⊢ₚₛ P1 ->
    Γ ⨟ Δ ⊢ₚₛ P2 ->
    Γ ⨟ Δ ⊢ₚₛ (pskl_arrow P1 P2)
| d_wf_pskl__all : forall L Γ Δ P,
    (forall X, X `notin` L ->
       Γ ⨟ (X :: Δ) ⊢ₚₛ (open_pskl_wrt_pskl P (pskl_var_f X))) ->
    Γ ⨟ Δ ⊢ₚₛ (pskl_all_syn P)
| d_wf_pskl__hole : forall Γ Δ,
    Γ ⨟ Δ ⊢ₚₛ pskl_hole
| d_wf_pskl__tophole : forall Γ Δ P,
    (* Paper [⫯.P] rule: [Δ] is cleared in the PREMISE (matching [Γ\Δ] since the
       ∀-vars are exactly [Δ]); the conclusion holds under an ARBITRARY [Δ]. *)
    guarded_pskl P ->
    Γ ⨟ nil ⊢ₚₛ P ->
    Γ ⨟ Δ ⊢ₚₛ (pskl_tophole P)
where "Γ ⨟ Δ ⊢ₚₛ P" := (d_wf_pskl Γ Δ P) : type_scope.

Inductive d_wf_uskl : list (atom * dbind) -> list atom -> uskl -> Prop :=
| d_wf_uskl__unit : forall Γ Δ,
    Γ ⨟ Δ ⊢ᵤₛ uskl_unit
| d_wf_uskl__var : forall Γ Δ X,
    List.In X Δ \/ binds X dbind_tvar Γ ->
    Γ ⨟ Δ ⊢ᵤₛ (uskl_var_f X)
| d_wf_uskl__arrow : forall Γ Δ R1 R2,
    Γ ⨟ Δ ⊢ᵤₛ R1 ->
    Γ ⨟ Δ ⊢ᵤₛ R2 ->
    Γ ⨟ Δ ⊢ᵤₛ (uskl_arrow R1 R2)
| d_wf_uskl__all_syn : forall L Γ Δ R,
    (forall X, X `notin` L ->
       Γ ⨟ (X :: Δ) ⊢ᵤₛ
         (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    Γ ⨟ Δ ⊢ᵤₛ (uskl_all_syn R)
| d_wf_uskl__all_etag : forall L Γ Δ ε R,
    (forall X, X `notin` L ->
       Γ ⨟ (X :: Δ) ⊢ᵤₛ
         (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    Γ ⨟ Δ ⊢ᵤₛ (uskl_all_etag ε R)
| d_wf_uskl__hole : forall Γ Δ,
    Γ ⨟ Δ ⊢ᵤₛ uskl_hole
| d_wf_uskl__tophole : forall Γ Δ R,
    guarded_uskl R ->
    Γ ⨟ nil ⊢ᵤₛ R ->
    Γ ⨟ Δ ⊢ᵤₛ (uskl_tophole R)
| d_wf_uskl__holeg : forall Γ Δ,
    Γ ⨟ Δ ⊢ᵤₛ uskl_holeg
| d_wf_uskl__topholeg : forall Γ Δ R,
    guarded_uskl R ->
    Γ ⨟ nil ⊢ᵤₛ R ->
    Γ ⨟ Δ ⊢ᵤₛ (uskl_topholeg R)
where "Γ ⨟ Δ ⊢ᵤₛ R" := (d_wf_uskl Γ Δ R) : type_scope.

(* ===================================================================== *)
(*  Tag relation  [tags{Δ}{φ}]  (paper notation [φ # Δ], declarative.tex) *)
(*  Pure tag-counting: [Δ] is exactly the set of ε-tags appearing in the  *)
(*  tagged type / skeleton, each used linearly (hence [list_disjoint] /    *)
(*  [~ In] sidecars mirroring the paper's [⊎]).  This is the relation the  *)
(*  latest paper factors out of the old combined [Δ | Γ ⊢ φ]: the [d_sub] *)
(*  ForallL premise is now [Γ ⊢ tags{Δ}{φ}] = well-scopedness (kept in     *)
(*  [d_wf_utyp]) ∧ this relation.  Decoupled from [Γ]: tags ignore the     *)
(*  type context. *)
(* ===================================================================== *)

(* Check fully passed *)
Inductive d_tags : atoms -> utyp -> Prop :=
| d_tags__unit : forall Ψ,
    Ψ [=] empty ->
    d_tags Ψ utyp_unit
| d_tags__var : forall Ψ X,
    Ψ [=] empty ->
    d_tags Ψ (utyp_var_f X)
| d_tags__arrow : forall Ψ Ψ1 Ψ2 C1 C2,
    d_tags Ψ1 C1 ->
    d_tags Ψ2 C2 ->
    AtomSetImpl.inter Ψ1 Ψ2 [=] empty ->         (* paper ⊎ : disjoint set union *)
    Ψ [=] Ψ1 `union` Ψ2 ->
    d_tags Ψ (utyp_arrow C1 C2)
| d_tags__all_etag : forall L Ψ Ψ0 ε C,
    (forall X, X `notin` L ->
       d_tags Ψ0 (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    ε `notin` Ψ0 ->
    Ψ [=] add ε Ψ0 ->
    d_tags Ψ (utyp_all_etag ε C).

(** Skeleton analog [tags{Ψ}{ψ}] (declarative.tex:1822).  Defined EXACTLY on
    the paper's decorated-skeleton grammar
    [ψ ::= 1 | α | ψ→ψ | ∀^ε α.ψ | HoleG | TopHoleG.ψ] (declarative.tex:1796):
    every quantifier is tagged; the only ghosts are the DOTTED ones.  A [HoleG]
    carries no tags; a dotted universal ghost [TopHoleG.ψ] carries exactly its
    body's tags (no ε of its own — unlike [all_etag]).  Plain [hole]/[tophole]
    and the untagged [all_syn] are NOT in ψ and have no case here. *)
Inductive d_tags_skl : atoms -> uskl -> Prop :=
| d_tags_skl__unit : forall Ψ, Ψ [=] empty -> d_tags_skl Ψ uskl_unit
| d_tags_skl__var : forall Ψ X, Ψ [=] empty -> d_tags_skl Ψ (uskl_var_f X)
| d_tags_skl__arrow : forall Ψ Ψ1 Ψ2 R1 R2,
    d_tags_skl Ψ1 R1 ->
    d_tags_skl Ψ2 R2 ->
    AtomSetImpl.inter Ψ1 Ψ2 [=] empty ->         (* paper ⊎ : disjoint set union *)
    Ψ [=] Ψ1 `union` Ψ2 ->
    d_tags_skl Ψ (uskl_arrow R1 R2)
| d_tags_skl__all_etag : forall L Ψ Ψ0 ε R,
    (forall X, X `notin` L ->
       d_tags_skl Ψ0 (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    ε `notin` Ψ0 ->
    Ψ [=] add ε Ψ0 ->
    d_tags_skl Ψ (uskl_all_etag ε R)
| d_tags_skl__holeg : forall Ψ,
    Ψ [=] empty ->
    d_tags_skl Ψ uskl_holeg
| d_tags_skl__topholeg : forall Ψ R,
    d_tags_skl Ψ R ->
    d_tags_skl Ψ (uskl_topholeg R).

(* Constructor hints for the tag-reading judgments (structural over the
   type / skeleton shape): [eauto] discharges their constructor-dispatch
   proofs.  The larger relational judgments below are NOT hinted. *)
#[export] Hint Constructors d_tags d_tags_skl : frost.

(* ===================================================================== *)
(*  Type consistency and subtyping                                        *)
(* ===================================================================== *)

(* Check fully passed *)
Inductive d_consis : atoms -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_consis__unit : forall Ψ Γ,
    Ψ [=] empty ->
    Ψ ⨟ Γ ⊢ utyp_unit ∼ btyp_unit
| d_consis__var : forall Ψ Γ X,
    binds X dbind_tvar Γ ->
    Ψ [=] empty ->
    Ψ ⨟ Γ ⊢ (utyp_var_f X) ∼ (btyp_var_f X)
| d_consis__arrow : forall Ψ Ψ1 Ψ2 Γ C1 C2 B1 B2,
    (* Paper [Arrow]: the tag context is the SET UNION [Ψ₁,Ψ₂]
       (declarative.tex:967, with Ψ a set), not a disjoint union — so we
       neither require nor record disjointness.  This faithfulness is what
       makes consistency transitivity (B.2) provable: composing two
       derivations may legitimately reuse a tag, which a set absorbs. *)
    Ψ1 ⨟ Γ ⊢ C1 ∼ B1 ->
    Ψ2 ⨟ Γ ⊢ C2 ∼ B2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    Ψ ⨟ Γ ⊢ (utyp_arrow C1 C2) ∼ (btyp_arrow B1 B2)
| d_consis__forall_inh_tagged : forall L Ψ Ψ0 Γ ε C B,
    (* Paper [ForallInh] with δ=ε: output is [Ψ,ε] = Ψ ∪ {ε}, the
       idempotent set union (declarative.tex:950) — no freshness side
       condition ([add] on a set is idempotent). *)
    (forall X, X `notin` L ->
       Ψ0 ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f X)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Ψ [=] add ε Ψ0 ->
    Ψ ⨟ Γ ⊢ (utyp_all_etag ε C) ∼ (btyp_all_inh B)
| d_consis__forall_inh_untagged : forall L Ψ Γ C B,
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f X)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Ψ ⨟ Γ ⊢ (utyp_all_syn C) ∼ (btyp_all_inh B)
| d_consis__forall_syn_tagged : forall L Ψ Γ ε C B,
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f X)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Ψ ⨟ Γ ⊢ (utyp_all_etag ε C) ∼ (btyp_all_syn B)
| d_consis__forall_syn : forall L Ψ Γ C B,
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f X)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Ψ ⨟ Γ ⊢ (utyp_all_syn C) ∼ (btyp_all_syn B)
where "Ψ ⨟ Γ ⊢ C ∼ B" := (d_consis Ψ Γ C B) : type_scope.

(* Check fully passed *)
Inductive d_sub : mode -> atoms -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_sub__infer : forall Ψ Γ C B,
    empty ⨟ Γ ⊢ C ∼ B ->
    is_styp B ->
    Ψ [=] empty ->
    Ψ ⨟ Γ ⊢[ mode_ti ] C ⩽ B
| d_sub__check : forall Ψ Γ C B,
    guarded_utyp C ->
    guarded_btyp B ->
    Ψ ⨟ Γ ⊢ C ∼ B ->
    is_ityp B ->
    Ψ ⨟ Γ ⊢[ mode_tc ] C ⩽ B
| d_sub__forall_r : forall L Ψ Γ C B,
    is_ityp (btyp_all_inh B) ->
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢[ mode_tc ] C ⩽
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Ψ ⨟ Γ ⊢[ mode_tc ] C ⩽ (btyp_all_inh B)
(* Todo: rename d_sub__arg to d_sub__arrow *)
| d_sub__arg : forall Ψ Ψ1 Ψ2 Γ m C1 C2 B1 B2,
    Ψ1 ⨟ Γ ⊢ C1 ∼ B1 ->
    Ψ2 ⨟ Γ ⊢[ m ] C2 ⩽ B2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    Ψ ⨟ Γ ⊢[ mode_fn m ] (utyp_arrow C1 C2) ⩽ (btyp_arrow B1 B2)
| d_sub__forall_l_tagged : forall Ψ Ψ' Γ m ε C ph B,
    m <> mode_ti ->
    AtomSetImpl.inter Ψ' Ψ [=] empty ->      (* Ψ' fresh w.r.t. the outer tags *)
    d_tags Ψ' ph ->                  (* tags{Ψ'}{φ} : Ψ' is exactly φ's tags *)
    Γ ⊢ᵤ ph ->                       (* Γ ⊢ φ : well-scopedness half (WT: no Ψ') *)
    is_ttyp ph ->
    (Ψ `union` Ψ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⩽ B ->
    Ψ ⨟ Γ ⊢[ m ] (utyp_all_etag ε C) ⩽ B
| d_sub__forall_l_untagged : forall Ψ Ψ' Γ m C ph B,
    m <> mode_ti ->
    AtomSetImpl.inter Ψ' Ψ [=] empty ->
    d_tags Ψ' ph ->
    Γ ⊢ᵤ ph ->
    is_ttyp ph ->
    (Ψ `union` Ψ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⩽ B ->
    Ψ ⨟ Γ ⊢[ m ] (utyp_all_syn C) ⩽ B
where "Ψ ⨟ Γ ⊢[ M ] C ⩽ B" := (d_sub M Ψ Γ C B) : type_scope.

Reserved Notation "Γ ⊢ A ≤ B"
  (at level 75, A at level 74, B at level 74, no associativity).
Inductive d_shallow_sub : list (atom * dbind) -> ptyp -> ptyp -> Prop :=
| d_shallow_sub__refl : forall Γ A,
    Γ ⊢ₚ A ->
    Γ ⊢ A ≤ A
| d_shallow_sub__forall_r : forall L Γ A1 A2,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ A1 ≤ (open_ptyp_wrt_ptyp A2 (ptyp_var_f X))) ->
    Γ ⊢ A1 ≤ (ptyp_all A2)
| d_shallow_sub__forall_l : forall Γ A1 A2 I,
    mono_ptyp I ->
    Γ ⊢ₚ I ->
    Γ ⊢ (open_ptyp_wrt_ptyp A1 I) ≤ A2 ->
    Γ ⊢ (ptyp_all A1) ≤ A2
where "Γ ⊢ A ≤ B" := (d_shallow_sub Γ A B) : type_scope.

(* ===================================================================== *)
(*  Skeleton refinement, consistency, and subtyping                       *)
(* ===================================================================== *)

(* Check mostly passed. 
    LHS are guaranteed to be all inh 
    some difference with the paper's "Growing both Γ and Δ version", but should be equivalent *)
(* Todo: we should not use P for RHS in all the rules, P is reserverd for pskl, but RHS is also a bskl here *)
Inductive d_refine_syn : list (atom * dbind) -> list atom -> bskl -> bskl -> Prop :=
| d_refine_syn__unit : forall Γ Δ,
    Γ ⨟ Δ ⊢ᵣ bskl_unit ⊳ bskl_unit
| d_refine_syn__var : forall Γ Δ X,
    (* Paper: [Γ,Δ ∋ α] — an inherited (Δ) or context (Γ) tvar. *)
    List.In X Δ \/ binds X dbind_tvar Γ ->
    Γ ⨟ Δ ⊢ᵣ (bskl_var_f X) ⊳ (bskl_var_f X)
| d_refine_syn__arrow : forall Γ Δ Q1 Q2 P1 P2,
    Γ ⨟ Δ ⊢ᵣ Q1 ⊳ P1 ->
    Γ ⨟ Δ ⊢ᵣ Q2 ⊳ P2 ->
    Γ ⨟ Δ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow P1 P2)
| d_refine_syn__all : forall L Γ Δ Q P,
    (* Inherited ∀: the bound var joins [Δ]. *)
    (forall X, X `notin` L ->
       Γ ⨟ (X :: Δ) ⊢ᵣ
         (open_bskl_wrt_bskl Q (bskl_var_f X)) ⊳
         (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    Γ ⨟ Δ ⊢ᵣ (bskl_all_inh Q) ⊳ (bskl_all_inh P)
| d_refine_syn__hole : forall Γ Δ P,
    (* [□ ⤳ syn{Q}]: the fill is well-formed under [Γ] alone (synthesised vars
       are in [Γ]); [Δ] is cleared so inherited vars cannot fill ghosts. *)
    Γ ⨟ nil ⊢ₚₛ P ->
    Γ ⨟ Δ ⊢ᵣ bskl_hole ⊳ (pskl_to_bskl_syn P)
| d_refine_syn__tophole_remove : forall Γ Δ Q P,
    (* [⫯.inh{P} ⤳ bid{Q}]: remove the universal ghost; keep [Δ]. *)
    Γ ⨟ Δ ⊢ᵣ Q ⊳ P ->
    Γ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ P
| d_refine_syn__tophole_fill : forall L Γ Δ Q P,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⨟ Δ ⊢ᵣ
         (bskl_tophole Q) ⊳ (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    Γ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_all_syn P)
| d_refine_syn__tophole_keep : forall Γ Δ Q P,
    guarded_bskl P ->
    Γ ⨟ Δ ⊢ᵣ Q ⊳ P ->
    Γ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_tophole P)
where "Γ ⨟ Δ ⊢ᵣ Q ⊳ P" := (d_refine_syn Γ Δ Q P) : type_scope.

(* Check passed *)
Inductive d_pat_consis : atoms -> list (atom * dbind) -> uskl -> bskl -> Prop :=
| d_pat_consis__unit : forall Ψ Γ,
    Ψ [=] empty ->
    Ψ ⨟ Γ ⊢ₛ uskl_unit ∼ bskl_unit
| d_pat_consis__var : forall Ψ Γ X,
    Ψ [=] empty ->
    binds X dbind_tvar Γ ->
    Ψ ⨟ Γ ⊢ₛ (uskl_var_f X) ∼ (bskl_var_f X)
| d_pat_consis__arrow : forall Ψ Ψ1 Ψ2 Γ R1 R2 Q1 Q2,
    Ψ1 ⨟ Γ ⊢ₛ R1 ∼ Q1 ->
    Ψ2 ⨟ Γ ⊢ₛ R2 ∼ Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    Ψ ⨟ Γ ⊢ₛ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2)
| d_pat_consis__forall_inh_tagged : forall L Ψ Ψ0 Γ ε R Q,
    (forall X, X `notin` L ->
       Ψ0 ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ [=] add ε Ψ0 ->
    Ψ ⨟ Γ ⊢ₛ (uskl_all_etag ε R) ∼ (bskl_all_inh Q)
| d_pat_consis__forall_inh_untagged : forall L Ψ Γ R Q,
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ₛ (uskl_all_syn R) ∼ (bskl_all_inh Q)
| d_pat_consis__forall_syn_tagged : forall L Ψ Γ ε R Q,
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ₛ (uskl_all_etag ε R) ∼ (bskl_all_syn Q)
| d_pat_consis__forall_syn : forall L Ψ Γ R Q,
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ₛ (uskl_all_syn R) ∼ (bskl_all_syn Q)
| d_pat_consis__ghostg : forall Ψ Γ,
    Ψ [=] empty ->
    (* Paper [GhostG] (declarative.tex eqlab): a ghost hole [HoleG] is
       consistent with a plain [Hole]. *)
    Ψ ⨟ Γ ⊢ₛ uskl_holeg ∼ bskl_hole
| d_pat_consis__topholeg : forall Ψ Γ R Q,
    (* Paper [UnivGhostG] (dotted): [TopHoleG.S ~ TopHole.P] from [S ~ P],
       tags UNCHANGED — [typconsis[Ψ]] from [typconsis[Ψ]] (no added tag,
       unlike the old tagged version). *)
    Ψ ⨟ Γ ⊢ₛ R ∼ Q ->
    Ψ ⨟ Γ ⊢ₛ (uskl_topholeg R) ∼ (bskl_tophole Q)
| d_pat_consis__hole : forall Ψ Γ P,
    Ψ [=] empty ->
    d_wf_pskl Γ nil P ->
    Ψ ⨟ Γ ⊢ₛ uskl_hole ∼ (pskl_to_bskl_inh P)
| d_pat_consis__tophole : forall Ψ Γ R Q,
    (* Paper [UnivGhost]: TopHole ∼ TopHole. *)
    Ψ ⨟ Γ ⊢ₛ R ∼ Q ->
    Ψ ⨟ Γ ⊢ₛ (uskl_tophole R) ∼ (bskl_tophole Q)
| d_pat_consis__tophole_inh : forall L Ψ Γ R Q,
    (* Paper [UnivGhost1] (was missing, WT): the RHS TopHole can produce
       an inherited quantifier.  LHS [TopHole.R] is unchanged; the RHS
       body [Q] is checked under a fresh [α]. *)
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ₛ
         (uskl_tophole R) ∼ (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ₛ (uskl_tophole R) ∼ (bskl_all_inh Q)
| d_pat_consis__tophole_drop : forall Ψ Γ R Q,
    (* Paper [UnivGhost2] (was missing, WT): the LHS TopHole can be
       dropped against a plain inherited RHS. *)
    Ψ ⨟ Γ ⊢ₛ R ∼ Q ->
    Ψ ⨟ Γ ⊢ₛ (uskl_tophole R) ∼ Q
where "Ψ ⨟ Γ ⊢ₛ R ∼ Q" := (d_pat_consis Ψ Γ R Q) : type_scope.

Inductive d_pat_sub : mode -> atoms -> list (atom * dbind) -> uskl -> bskl -> Prop :=
| d_pat_sub__infer : forall Ψ Γ R Q,
    (* Paper [Infer]: synthesise by consistency, dropping tags. *)
    Ψ [=] empty ->
    empty ⨟ Γ ⊢ₛ R ∼ Q ->
    is_sskl Q ->
    Ψ ⨟ Γ ⊢ₛ[ mode_ti ] R ⩽ Q
| d_pat_sub__univ_ghost_r : forall Γ R Q,
    (* Paper [UnivGhostR] (replaces the out-of-sync [check]; WT review):
       the checking rule produces a [TopHole] on the RHS, requires BOTH
       [R] and the synthesised body [Q] guarded, and [Q] synthesised
       ([is_sskl]) — answering WT's "shouldn't Q be synthesised?". *)
    (* Todo: lift Ψ quantification above *)
    forall Ψ,
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    empty ⨟ Γ ⊢ₛ R ∼ Q ->
    Ψ ⨟ Γ ⊢ₛ[ mode_tc ] R ⩽ (bskl_tophole Q)
| d_pat_sub__arg : forall Ψ Ψ1 Ψ2 Γ m R1 R2 Q1 Q2,
    (* Paper [Arrow]: set-union tag context. *)
    Ψ1 ⨟ Γ ⊢ₛ R1 ∼ Q1 ->
    Ψ2 ⨟ Γ ⊢ₛ[ m ] R2 ⩽ Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    Ψ ⨟ Γ ⊢ₛ[ mode_fn m ] (uskl_arrow R1 R2) ⩽ (bskl_arrow Q1 Q2)
| d_pat_sub__forall_l_tagged : forall Ψ Ψ' Γ m ε R psi Q,
    (* Paper [ForallL] (tagged head).  [Ψ' fresh] = [list_disjoint];
       well-scopedness is [Γ ⨟ nil ⊢ᵤₛ ψ] (S1: scope, not tags). *)
    m <> mode_ti ->
    AtomSetImpl.inter Ψ' Ψ [=] empty ->
    d_tags_skl Ψ' psi ->             (* tags{Ψ'}{ψ} : skeleton-tag relation *)
    Γ ⨟ nil ⊢ᵤₛ psi ->
    is_tskl psi ->
    (Ψ `union` Ψ') ⨟ Γ ⊢ₛ[ m ] (open_uskl_wrt_uskl R psi) ⩽ Q ->
    Ψ ⨟ Γ ⊢ₛ[ m ] (uskl_all_etag ε R) ⩽ Q
| d_pat_sub__forall_l_untagged : forall Ψ Ψ' Γ m R psi Q,
    m <> mode_ti ->
    AtomSetImpl.inter Ψ' Ψ [=] empty ->
    d_tags_skl Ψ' psi ->
    Γ ⨟ nil ⊢ᵤₛ psi ->
    is_tskl psi ->
    (Ψ `union` Ψ') ⨟ Γ ⊢ₛ[ m ] (open_uskl_wrt_uskl R psi) ⩽ Q ->
    Ψ ⨟ Γ ⊢ₛ[ m ] (uskl_all_syn R) ⩽ Q
| d_pat_sub__ghost : forall m Γ P,
    (* Paper [Ghost]: a [Hole] is below any inherited skeleton [inh{P}].
       [mod_comp_sk … m] is the judgment-wide [skmod{SK}] wf-condition
       (declarative.tex:1935): it excludes an ill-moded fill (a poly [inh{P}] at
       ti/tc is not [is_sskl]), so the sub output stays mode-compatible — the
       skeleton analog of [d_sub] having no ghost rule. *)
    (* Todo: lift Ψ quantification above *)
    forall Ψ, Ψ [=] empty ->
    d_wf_pskl Γ nil P ->
    mod_comp_sk (pskl_to_bskl_inh P) m ->
    Ψ ⨟ Γ ⊢ₛ[ m ] uskl_hole ⩽ (pskl_to_bskl_inh P)
| d_pat_sub__univ_ghost_l : forall m Ψ Γ R Q,
    (* Paper [UnivGhostL]: drop a [TopHole] on the LHS (any [M ≠ TI]). *)
    m <> mode_ti ->
    Ψ ⨟ Γ ⊢ₛ[ m ] R ⩽ Q ->
    Ψ ⨟ Γ ⊢ₛ[ m ] (uskl_tophole R) ⩽ Q
| d_pat_sub__ghostg : forall m Ψ Γ,
    (* Paper [GhostG]: a ghost hole [HoleG] is below a plain [Hole].
       [mod_comp_sk … m] ([skmod{SK}]) excludes the ill-moded [fn] case (a
       [bskl_hole] is not an arrow), keeping the output mode-compatible. *)
    Ψ [=] empty ->
    mod_comp_sk bskl_hole m ->
    Ψ ⨟ Γ ⊢ₛ[ m ] uskl_holeg ⩽ bskl_hole
| d_pat_sub__univ_ghost_lg : forall m Ψ Γ R Q,
    (* Paper [UnivGhostLG] (dotted): drop a dotted ghost [TopHoleG] on the
       LHS (any [M ≠ TI]).  [Ψ] unchanged — [patsub[M][Ψ]] from
       [patsub[M][Ψ]] (declarative.tex UnivGhostLG). *)
    m <> mode_ti ->
    Ψ ⨟ Γ ⊢ₛ[ m ] R ⩽ Q ->
    Ψ ⨟ Γ ⊢ₛ[ m ] (uskl_topholeg R) ⩽ Q
where "Ψ ⨟ Γ ⊢ₛ[ M ] R ⩽ Q" := (d_pat_sub M Ψ Γ R Q) : type_scope.

(* ===================================================================== *)
(*  Typing and pattern inference                                          *)
(* ===================================================================== *)

Reserved Notation "Γ ⊢[ M ] e ⦂ A"
  (at level 100, M at level 0, e at level 75, A at level 75, no associativity).
Reserved Notation "Γ ⊢[ M ] e ⇨ P"
  (at level 100, M at level 0, e at level 75, P at level 75, no associativity).
Reserved Notation "Γ ⊢ˢ[ M ] e ⦂ A"
  (at level 100, M at level 0, e at level 75, A at level 75, no associativity).

(** Skeleton inference [d_pat] ([⇨]) is SELF-CONTAINED — no [d_typing] premises
    (the paper's P-App infers the function, declarative.tex:1560) — so it is
    defined standalone, BEFORE [d_typing], rather than mutually. *)
(* Check fully passed *)
(* Todo : check if d_pat has skmod_sk satisfied, and i think we didn't even have skmod_sk defined *)
Inductive d_pat : mode -> list (atom * dbind) -> exp -> bskl -> Prop :=
(* Paper P-Unit/P-Var/P-Anno (declarative.tex:1634-1653): the skeleton
   subtyping judgement is EMBEDDED in the three base rules at every mode —
   there is no standalone P-Sub rule and no base-term restriction. *)
| d_pat__unit : forall Γ m Q,
    empty ⨟ Γ ⊢ₛ[ m ] uskl_unit ⩽ Q ->
    Γ ⊢[ m ] exp_unit ⇨ Q
| d_pat__var : forall Γ m x (P : pskl) d Q,
    binds x d Γ ->
    dbind_to_pskl d = Some P ->
    empty ⨟ Γ ⊢ₛ[ m ] (bskl_to_uskl (pskl_to_bskl_syn P)) ⩽ Q ->
    Γ ⊢[ m ] (exp_var_f x) ⇨ Q
| d_pat__anno : forall Γ m e (A : ptyp) Q,
    Γ ⊢ₚ A ->
    empty ⨟ Γ ⊢ₛ[ m ] (bskl_to_uskl (pskl_to_bskl_syn (ptyp_to_pskl A))) ⩽ Q ->
    Γ ⊢[ m ] (exp_anno e A) ⇨ Q
| d_pat__freeze : forall Γ e P,
    Γ ⊢[ mode_ti ] e ⇨ (pskl_to_bskl_syn P) ->
    Γ ⊢[ mode_tc ] (exp_freeze e) ⇨ (pskl_to_bskl_syn P)
| d_pat__abs : forall L Γ m e P Q,
    (* [mod_comp_sk … m] is the paper's [skmod{SK}] colour/mode discipline on the
       inferred arrow, mirroring [d_typing__abs]'s [mod_comp_ty]: at [ti] it forces
       [is_sskl], excluding a POLY inherited domain (ill-moded); at [FN m'] it
       threads [mod_comp_sk Q m'] for the body.  [m ≠ tc] keeps this disjoint from
       [abs_check] (which owns the checking mode). *)
    m <> mode_tc ->
    Γ ⨟ nil ⊢ₚₛ P ->
    mod_comp_sk (bskl_arrow (pskl_to_bskl_inh P) Q) m ->
    (forall x, x `notin` L ->
       ((x ~ dbind_skl P) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q) ->
    Γ ⊢[ m ] (exp_abs e) ⇨ (bskl_arrow (pskl_to_bskl_inh P) Q)
| d_pat__abs_anno : forall L Γ m e (A : ptyp) (B : btyp) Q,
    (* The arrow-arg skeleton [Sarg] is bidirectional, [bskl_to_pskl Sarg]
       the annotation's pattern.  [mod_comp_sk … m] as in [abs]. *)
    m <> mode_tc ->
    Γ ⊢ₚ A ->
    btyp_to_ptyp B = A ->
    mod_comp_sk (bskl_arrow (btyp_to_bskl B) Q) m ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q) ->
    Γ ⊢[ m ] (exp_abs_anno A e) ⇨ (bskl_arrow (btyp_to_bskl B) Q)
| d_pat__app : forall Γ m e1 e2 P (Q1 Q2 : bskl),
    (* Paper P-App (declarative.tex:1560): the function [e1] is SKELETON-
       INFERRED ([⇨]) in [FN] mode, not typed — d_pat is self-contained
       skeleton inference.  [P'] is the fill output (the arg skeleton). *)
    Γ ⊢[ mode_tc ] e2 ⇨ (pskl_to_bskl_syn P) ->
    Γ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Q1 ->
    Γ ⊢[ mode_fn m ] e1 ⇨ (bskl_arrow Q1 Q2) ->
    Γ ⊢[ m ] (exp_app e1 e2) ⇨ Q2
| d_pat__abs_check : forall L Γ e P,
    (forall x, x `notin` L ->
       ((x ~ dbind_skl pskl_hole) ++ Γ) ⊢[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ (pskl_to_bskl_syn P)) ->
    Γ ⊢[ mode_tc ] (exp_abs e) ⇨ (bskl_tophole (bskl_arrow bskl_hole (pskl_to_bskl_syn P)))
| d_pat__abs_anno_check : forall L Γ e A P,
    Γ ⊢ₚ A ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ (pskl_to_bskl_syn P)) ->
    Γ ⊢[ mode_tc ] (exp_abs_anno A e) ⇨ (bskl_tophole (bskl_arrow (btyp_to_bskl (ptyp_to_btyp_syn A)) (pskl_to_bskl_syn P)))
where "Γ ⊢[ M ] e ⇨ P" := (d_pat M Γ e P) : type_scope.

(** Typing [d_typing] ([⦂]) uses [d_pat] in [App] (it infers the argument's
    skeleton), so it is defined after [d_pat]. *)
(* Check fully passed *)
Inductive d_typing : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
| d_typing__unit : forall Γ,
    Γ ⊢[ mode_ti ] exp_unit ⦂ btyp_unit
| d_typing__var : forall Γ x A,
    binds x (dbind_typ A) Γ ->
    Γ ⊢[ mode_ti ] (exp_var_f x) ⦂ (ptyp_to_btyp_syn A)
| d_typing__anno : forall Γ e A,
    Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) ->
    Γ ⊢[ mode_ti ] (exp_anno e A) ⦂ (ptyp_to_btyp_syn A)
| d_typing__sub : forall Γ m e A B,
    (* Paper [Sub] (declarative.tex): applies to ANY term [M] — the base-term
       restriction was removed (commit "Removed base terms"); general
       subsumption is admissible, so the unrestricted rule is equivalent. *)
    (* Todo: not urgent, replace A with btyp B1 and use is_styp B1 *)
    Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) ->
    empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B ->
    Γ ⊢[ m ] e ⦂ B
| d_typing__freeze : forall Γ e A,
    (* Paper [Freeze]: TI [syn{A}] ⇒ TC [inh{A}].  The premise IS a synthesised
       colouring [syn A] and the result is repainted to [inh A]; keeping an
       arbitrary [B] would (i) accept a non-synthesised premise and (ii) let a
       synthesised colour be used directly in check mode. *)
    Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) ->
    Γ ⊢[ mode_tc ] (exp_freeze e) ⦂ (ptyp_to_btyp_inh A)
| d_typing__forall : forall L Γ e A,
    is_value e ->
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢[ mode_tc ] e ⦂ (open_btyp_wrt_btyp (ptyp_to_btyp_inh A) (btyp_var_f X))) ->
    Γ ⊢[ mode_tc ] e ⦂ (btyp_all_inh (ptyp_to_btyp_inh A))
| d_typing__abs : forall L Γ m e A B,
    (* Paper [Abs].  [mod_comp_ty … m] is the paper's implicit [skmod{TY}]
       colour/mode well-formedness on the conclusion: it excludes the ill-moded
       [ti] reading (whose result would have to be synthesised yet has an
       inherited domain) and forces the colour to match the mode. *)
    Γ ⊢ₚ A ->
    mod_comp_ty (btyp_arrow (ptyp_to_btyp_inh A) B) m ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B) ->
    Γ ⊢[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B)
| d_typing__abs_anno : forall L Γ m e A B1 B2,
    (* The arrow-arg is an arbitrary bidirectional [Barg] whose erasure
       [btyp_to_ptyp] is the annotation [A].  Paper [AbsAnno].  [mod_comp_ty … m]
       (paper's [skmod{TY}]) colours the domain by the mode: at [TC] it forces
       [is_ityp B1], i.e. [B1 = inh A]. *)
    Γ ⊢ₚ A ->
    btyp_to_ptyp B1 = A ->
    mod_comp_ty (btyp_arrow B1 B2) m ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B2) ->
    Γ ⊢[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow B1 B2)
| d_typing__app : forall Γ m e1 e2 P B1 B2,
    (* Paper [App]: ONE domain [inh A] (the refinement output) is used by both
       the refinement and the function premise; the argument is checked at the
       same [inh A].  (Previously the function domain was an arbitrary [Barg]
       with erasure [A], not justified by the [inh A] refinement output.) *)
    Γ ⊢[ mode_tc ] e2 ⇨ (pskl_to_bskl_syn P) ->
    Γ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B1) ->
    Γ ⊢[ mode_fn m ] e1 ⦂ (btyp_arrow B1 B2) ->
    Γ ⊢[ mode_tc ] e2 ⦂ (ptyp_to_btyp_inh (btyp_to_ptyp B1)) ->
    Γ ⊢[ m ] (exp_app e1 e2) ⦂ B2
where "Γ ⊢[ M ] e ⦂ A" := (d_typing M Γ e A) : type_scope.

(* ===================================================================== *)
(*  Syntax-directed declarative typing  (paper Fig. syntax-directed)      *)
(* ===================================================================== *)

Inductive d_sd_typing : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
(* Paper [sdtylab{Unit}]/[sdtylab{Var}]/[sdtylab{Anno}]: the standalone
   [dtylab{Sub}] was removed and its subtyping premise is EMBEDDED into the
   three base rules (declarative.tex, "we incorporate Sub into the three base
   rules"), so the system is syntax-directed with no [is_base_term] predicate. *)
| d_sd_typing__unit : forall Γ m B,
    empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn ptyp_unit) ⩽ B ->
    Γ ⊢ˢ[ m ] exp_unit ⦂ B
| d_sd_typing__var : forall Γ m x A B,
    binds x (dbind_typ A) Γ ->
    empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B ->
    Γ ⊢ˢ[ m ] (exp_var_f x) ⦂ B
| d_sd_typing__anno : forall Γ m e A B,
    Γ ⊢ˢ[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) ->
    empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B ->
    Γ ⊢ˢ[ m ] (exp_anno e A) ⦂ B
| d_sd_typing__freeze : forall Γ e A,
    (* Paper [Freeze]: TI [syn{A}] ⇒ TC [inh{A}]. *)
    Γ ⊢ˢ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) ->
    Γ ⊢ˢ[ mode_tc ] (exp_freeze e) ⦂ (ptyp_to_btyp_inh A)
| d_sd_typing__abs_check_step : forall L Γ e B,
    is_ityp (btyp_all_inh B) ->
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ˢ[ mode_tc ] (exp_abs e)
         ⦂ (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Γ ⊢ˢ[ mode_tc ] (exp_abs e) ⦂ (btyp_all_inh B)
| d_sd_typing__abs_check_base : forall L Γ e A B,
    Γ ⊢ₚ A ->
    is_ityp B ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢ˢ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B) ->
    Γ ⊢ˢ[ mode_tc ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B)
(* Paper [sdtylab{AbsAnnoCheck}]: same fold for the annotated checked lambda. *)
| d_sd_typing__abs_anno_check_step : forall L Γ A e B,
    is_ityp (btyp_all_inh B) ->
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ˢ[ mode_tc ] (exp_abs_anno A e)
         ⦂ (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Γ ⊢ˢ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_all_inh B)
| d_sd_typing__abs_anno_check_base : forall L Γ e A B,
    (* Paper [AbsAnnoCheck]: inherited annotation domain [inh A] in check mode. *)
    Γ ⊢ₚ A ->
    is_ityp B ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢ˢ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B) ->
    Γ ⊢ˢ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B)
| d_sd_typing__abs : forall L Γ m e A B,
    (* Paper [sdtylab{Abs}]: [M ≠ TC].  Same [mod_comp_ty] colour/mode discipline
       as [d_typing__abs] (so the equivalence transfers the premise directly). *)
    m <> mode_tc ->
    Γ ⊢ₚ A ->
    mod_comp_ty (btyp_arrow (ptyp_to_btyp_inh A) B) m ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢ˢ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B) ->
    Γ ⊢ˢ[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B)
| d_sd_typing__abs_anno : forall L Γ m e A B1 B2,
    (* Paper [sdtylab{AbsAnno}]: [M ≠ TC]. *)
    m <> mode_tc ->
    Γ ⊢ₚ A ->
    btyp_to_ptyp B1 = A ->
    mod_comp_ty (btyp_arrow B1 B2) m ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢ˢ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B2) ->
    Γ ⊢ˢ[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow B1 B2)
(* Paper [sdtylab{AbsCheck}]: the standalone [dtylab{Forall}] is FOLDED into
   the checked lambda rule.  [__abs_check_step] peels one inherited [∀] over
   the SAME lambda (this is [Forall] restricted to [λ]-values, self-recursive
   in [d_sd_typing] — no mutual block), and [__abs_check_base] is the [ᾱ = ·]
   arrow whose body checks.  Together they type [λx.M] at [∀ᾱ.(inh A → B)]. *)
| d_sd_typing__app : forall Γ m e1 e2 P B1 B2,
    (* Paper [App]: ONE domain [B1] used by both the refinement (its skeleton
       [btyp_to_bskl B1]) and the function premise; the argument is checked at
       the inherited colouring of the same domain. *)
    Γ ⊢[ mode_tc ] e2 ⇨ (pskl_to_bskl_syn P) ->
    Γ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B1) ->
    Γ ⊢ˢ[ (mode_fn m) ] e1 ⦂ (btyp_arrow B1 B2) ->
    Γ ⊢ˢ[ mode_tc ] e2 ⦂ (ptyp_to_btyp_inh (btyp_to_ptyp B1)) ->
    Γ ⊢ˢ[ m ] (exp_app e1 e2) ⦂ B2
where "Γ ⊢ˢ[ M ] e ⦂ A" := (d_sd_typing M Γ e A) : type_scope.