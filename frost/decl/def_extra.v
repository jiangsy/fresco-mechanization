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

Reserved Notation "Ψ ⨟ Γ ⊢ₚₛ P"
  (at level 75, Γ at level 75, P at level 75, no associativity).
Reserved Notation "Γ ⊢ᵦ B"
  (at level 75, B at level 75, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ᵤ C"
  (at level 75, Γ at level 75, C at level 75, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ᵤₛ R"
  (at level 75, Γ at level 75, R at level 75, no associativity).
Reserved Notation "Δ ⨟ Γ ⊨ C ≈ B"
  (at level 75, Γ at level 75, C at level 74, B at level 74, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢[ M ] C ⊑ B"
  (at level 75, Γ at level 75, M at level 0, C at level 74, B at level 74,
   no associativity).
Reserved Notation "Ψ ⨟ Γ ⊢ᵣ P ▸ Q"
  (at level 75, Γ at level 75, P at level 74, Q at level 74, no associativity).
Reserved Notation "Ψ ⨟ Γ ⊢ᵣ Q ⊳ P"
  (at level 75, Γ at level 75, Q at level 74, P at level 74, no associativity).
Reserved Notation "Δ ⨟ Γ ⊨ₛ R ≈ Q"
  (at level 75, Γ at level 75, R at level 74, Q at level 74, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ₛ[ M ] R ⊑ Q"
  (at level 75, Γ at level 75, M at level 0, R at level 74, Q at level 74,
   no associativity).

(* ===================================================================== *)
(*  Well-formedness                                                       *)
(* ===================================================================== *)

Inductive d_wf_ptyp : list (atom * dbind) -> ptyp -> Prop :=
| d_wf_ptyp__unit : forall Γ,
    d_wf_ptyp Γ ptyp_unit
| d_wf_ptyp__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_wf_ptyp Γ (ptyp_var_f X)
| d_wf_ptyp__arrow : forall Γ A1 A2,
    d_wf_ptyp Γ A1 ->
    d_wf_ptyp Γ A2 ->
    d_wf_ptyp Γ (ptyp_arrow A1 A2)
| d_wf_ptyp__all : forall L Γ A,
    (forall X, X `notin` L ->
       d_wf_ptyp ((X ~ dbind_tvar) ++ Γ)
         (open_ptyp_wrt_ptyp A (ptyp_var_f X))) ->
    d_wf_ptyp Γ (ptyp_all A).

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
Inductive d_wf_utyp : list (atom * dbind) -> utyp -> Prop :=
| d_wf_utyp__unit : forall Γ,
    d_wf_utyp Γ utyp_unit
| d_wf_utyp__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_wf_utyp Γ (utyp_var_f X)
| d_wf_utyp__arrow : forall Γ C1 C2,
    d_wf_utyp Γ C1 ->
    d_wf_utyp Γ C2 ->
    d_wf_utyp Γ (utyp_arrow C1 C2)
| d_wf_utyp__all_syn : forall L Γ C,
    (forall X, X `notin` L ->
       d_wf_utyp ((X ~ dbind_tvar) ++ Γ)
         (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    d_wf_utyp Γ (utyp_all_syn C)
| d_wf_utyp__all_etag : forall L Γ ε C,
    (forall X, X `notin` L ->
       d_wf_utyp ((X ~ dbind_tvar) ++ Γ)
         (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    d_wf_utyp Γ (utyp_all_etag ε C).

Notation "Γ ⊢ᵤ C" := (d_wf_utyp Γ C)
  (at level 75, C at level 75, no associativity) : type_scope.

Inductive d_wf_pskl : list atom -> list (atom * dbind) -> pskl -> Prop :=
| d_wf_pskl__unit : forall Ψ Γ,
    Ψ ⨟ Γ ⊢ₚₛ pskl_unit
| d_wf_pskl__var : forall Ψ Γ X,
    List.In X Ψ \/ binds X dbind_tvar Γ ->
    Ψ ⨟ Γ ⊢ₚₛ (pskl_var_f X)
| d_wf_pskl__arrow : forall Ψ Γ P1 P2,
    Ψ ⨟ Γ ⊢ₚₛ P1 ->
    Ψ ⨟ Γ ⊢ₚₛ P2 ->
    Ψ ⨟ Γ ⊢ₚₛ (pskl_arrow P1 P2)
| d_wf_pskl__all : forall L Ψ Γ P,
    (forall X, X `notin` L ->
       (X :: Ψ) ⨟ Γ ⊢ₚₛ (open_pskl_wrt_pskl P (pskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ₚₛ (pskl_all_syn P)
| d_wf_pskl__hole : forall Ψ Γ,
    Ψ ⨟ Γ ⊢ₚₛ pskl_hole
| d_wf_pskl__tophole : forall Γ P,
    guarded_pskl P ->
    nil ⨟ Γ ⊢ₚₛ P ->
    nil ⨟ Γ ⊢ₚₛ (pskl_tophole P)
where "Ψ ⨟ Γ ⊢ₚₛ P" := (d_wf_pskl Ψ Γ P) : type_scope.

(* WT: With d_tags_skl defined blow, we should remove Δ here but add Ψ
as in d_wf_pskl.

Done (WT review): the tag context is dropped; the first context is now
the skeleton-scope context [Ψ] (type variables bound by ∀ *within* the
skeleton), exactly as in [d_wf_pskl] — [Ψ] is cleared at every
[uskl_tophole], and the var rule consults [Ψ] or [Γ].  Linear tag
content is checked separately by [d_tags_skl] below. *)
Inductive d_wf_uskl : list atom -> list (atom * dbind) -> uskl -> Prop :=
| d_wf_uskl__unit : forall Ψ Γ,
    Ψ ⨟ Γ ⊢ᵤₛ uskl_unit
| d_wf_uskl__var : forall Ψ Γ X,
    List.In X Ψ \/ binds X dbind_tvar Γ ->
    Ψ ⨟ Γ ⊢ᵤₛ (uskl_var_f X)
| d_wf_uskl__arrow : forall Ψ Γ R1 R2,
    Ψ ⨟ Γ ⊢ᵤₛ R1 ->
    Ψ ⨟ Γ ⊢ᵤₛ R2 ->
    Ψ ⨟ Γ ⊢ᵤₛ (uskl_arrow R1 R2)
| d_wf_uskl__all_syn : forall L Ψ Γ R,
    (forall X, X `notin` L ->
       (X :: Ψ) ⨟ Γ ⊢ᵤₛ
         (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ᵤₛ (uskl_all_syn R)
| d_wf_uskl__all_etag : forall L Ψ Γ ε R,
    (forall X, X `notin` L ->
       (X :: Ψ) ⨟ Γ ⊢ᵤₛ
         (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ᵤₛ (uskl_all_etag ε R)
| d_wf_uskl__hole : forall Ψ Γ,
    Ψ ⨟ Γ ⊢ᵤₛ uskl_hole
| d_wf_uskl__tophole : forall Ψ Γ R,
    guarded_uskl R ->
    nil ⨟ Γ ⊢ᵤₛ R ->
    Ψ ⨟ Γ ⊢ᵤₛ (uskl_tophole R)
where "Ψ ⨟ Γ ⊢ᵤₛ R" := (d_wf_uskl Ψ Γ R) : type_scope.

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

(** Tag context is a SET ([atoms]), matching the paper ("a tag context Ψ
    is a set of tags", declarative.tex:799).  The paper's disjoint union
    [Ψ⊎Ψ'] (declarative.tex:826, the linear [tags] relation) is set union
    with a disjointness side-condition; the plain [Ψ,Ψ'] elsewhere is plain
    set union.  This is what makes [d_sub]'s [forall_l] reconstruct work:
    a set can be recovered by difference, an ordered list cannot. *)
(** Context-building rules carry their output set [Δ] up to set-equality
    [=], so the relation ranges over set-equivalence classes (Coq's [atoms]
    is not extensional: [empty] and [empty ∪ empty] are [=] but not
    convertible).  This makes the morphism [Δ [=] Δ' → … Δ … → … Δ' …]
    provable while keeping inversions one-case-per-type. *)
Inductive d_tags : atoms -> utyp -> Prop :=
| d_tags__unit : forall Δ,
    Δ [=] empty ->
    d_tags Δ utyp_unit
| d_tags__var : forall Δ X,
    Δ [=] empty ->
    d_tags Δ (utyp_var_f X)
| d_tags__arrow : forall Δ Δ1 Δ2 C1 C2,
    d_tags Δ1 C1 ->
    d_tags Δ2 C2 ->
    AtomSetImpl.inter Δ1 Δ2 [=] empty ->         (* paper ⊎ : disjoint set union *)
    Δ [=] Δ1 `union` Δ2 ->
    d_tags Δ (utyp_arrow C1 C2)
| d_tags__all_etag : forall L Δ Δ0 ε C,
    (forall X, X `notin` L ->
       d_tags Δ0 (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    ε `notin` Δ0 ->
    Δ [=] add ε Δ0 ->
    d_tags Δ (utyp_all_etag ε C).

(** Skeleton analog [tags{Δ}{ψ}] (declarative.tex, skeleton subtyping).
    Same as [d_tags] plus the two ghost cases: a [hole] carries no tags,
    and a universal ghost [⫯ψ] carries exactly the tags of its body. *)
Inductive d_tags_skl : list atom -> uskl -> Prop :=
| d_tags_skl__unit : d_tags_skl nil uskl_unit
| d_tags_skl__var : forall X, d_tags_skl nil (uskl_var_f X)
| d_tags_skl__arrow : forall Δ1 Δ2 R1 R2,
    d_tags_skl Δ1 R1 ->
    d_tags_skl Δ2 R2 ->
    list_disjoint Δ1 Δ2 ->
    d_tags_skl (Δ1 ++ Δ2) (uskl_arrow R1 R2)
| d_tags_skl__all_etag : forall L Δ ε R,
    (forall X, X `notin` L ->
       d_tags_skl Δ (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    ~ List.In ε Δ ->
    d_tags_skl (ε :: Δ) (uskl_all_etag ε R)
| d_tags_skl__hole : d_tags_skl nil uskl_hole
| d_tags_skl__tophole : forall Δ R,
    d_tags_skl Δ R ->
    d_tags_skl Δ (uskl_tophole R).

(* ===================================================================== *)
(*  Type consistency and subtyping                                        *)
(* ===================================================================== *)

Inductive d_consis : atoms -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_consis__unit : forall Δ Γ,
    Δ [=] empty ->
    Δ ⨟ Γ ⊨ utyp_unit ≈ btyp_unit
| d_consis__var : forall Δ Γ X,
    binds X dbind_tvar Γ ->
    Δ [=] empty ->
    Δ ⨟ Γ ⊨ (utyp_var_f X) ≈ (btyp_var_f X)
| d_consis__arrow : forall Δ Δ1 Δ2 Γ C1 C2 B1 B2,
    (* Paper [Arrow]: the tag context is the SET UNION [Δ₁,Δ₂]
       (declarative.tex:967, with Δ a set), not a disjoint union — so we
       neither require nor record disjointness.  This faithfulness is what
       makes consistency transitivity (B.2) provable: composing two
       derivations may legitimately reuse a tag, which a set absorbs. *)
    Δ1 ⨟ Γ ⊨ C1 ≈ B1 ->
    Δ2 ⨟ Γ ⊨ C2 ≈ B2 ->
    Δ [=] Δ1 `union` Δ2 ->
    Δ ⨟ Γ ⊨ (utyp_arrow C1 C2) ≈ (btyp_arrow B1 B2)
| d_consis__forall_inh_tagged : forall L Δ Δ0 Γ ε C B,
    (* Paper [ForallInh] with δ=ε: output is [Δ,ε] = Δ ∪ {ε}, the
       idempotent set union (declarative.tex:950) — no freshness side
       condition ([add] on a set is idempotent). *)
    (forall X, X `notin` L ->
       Δ0 ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨
         (open_utyp_wrt_utyp C (utyp_var_f X)) ≈
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Δ [=] add ε Δ0 ->
    Δ ⨟ Γ ⊨ (utyp_all_etag ε C) ≈ (btyp_all_inh B)
| d_consis__forall_inh_untagged : forall L Δ Γ C B,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨
         (open_utyp_wrt_utyp C (utyp_var_f X)) ≈
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Δ ⨟ Γ ⊨ (utyp_all_syn C) ≈ (btyp_all_inh B)
| d_consis__forall_syn_tagged : forall L Δ Γ ε C B,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨
         (open_utyp_wrt_utyp C (utyp_var_f X)) ≈
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Δ ⨟ Γ ⊨ (utyp_all_etag ε C) ≈ (btyp_all_syn B)
| d_consis__forall_syn : forall L Δ Γ C B,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨
         (open_utyp_wrt_utyp C (utyp_var_f X)) ≈
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Δ ⨟ Γ ⊨ (utyp_all_syn C) ≈ (btyp_all_syn B)
where "Δ ⨟ Γ ⊨ C ≈ B" := (d_consis Δ Γ C B) : type_scope.

Inductive d_sub : mode -> atoms -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_sub__infer : forall Δ Γ C B,
    empty ⨟ Γ ⊨ C ≈ B ->
    is_styp B ->
    Δ [=] empty ->
    Δ ⨟ Γ ⊢[ mode_ti ] C ⊑ B
| d_sub__check : forall Δ Γ C B,
    (* WT: I modified this case in the new draft to require both C and
    B to be guarded. *)
    guarded_utyp C ->
    guarded_btyp B ->
    Δ ⨟ Γ ⊨ C ≈ B ->
    is_ityp B ->
    Δ ⨟ Γ ⊢[ mode_tc ] C ⊑ B
| d_sub__forall_r : forall L Δ Γ C B,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢[ mode_tc ] C ⊑
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Δ ⨟ Γ ⊢[ mode_tc ] C ⊑ (btyp_all_inh B)
| d_sub__arg : forall Δ Δ1 Δ2 Γ m C1 C2 B1 B2,
    Δ1 ⨟ Γ ⊨ C1 ≈ B1 ->
    Δ2 ⨟ Γ ⊢[ m ] C2 ⊑ B2 ->
    Δ [=] Δ1 `union` Δ2 ->
    Δ ⨟ Γ ⊢[ mode_fn m ] (utyp_arrow C1 C2) ⊑ (btyp_arrow B1 B2)
| d_sub__forall_l_tagged : forall Δ Δ' Γ m ε C ph B,
    m <> mode_ti ->
    AtomSetImpl.inter Δ' Δ [=] empty ->      (* Δ' fresh w.r.t. the outer tags *)
    d_tags Δ' ph ->                  (* tags{Δ'}{φ} : Δ' is exactly φ's tags *)
    Γ ⊢ᵤ ph ->                       (* Γ ⊢ φ : well-scopedness half (WT: no Δ') *)
    is_ttyp ph ->
    (Δ `union` Δ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⊑ B ->
    Δ ⨟ Γ ⊢[ m ] (utyp_all_etag ε C) ⊑ B
| d_sub__forall_l_untagged : forall Δ Δ' Γ m C ph B,
    m <> mode_ti ->
    AtomSetImpl.inter Δ' Δ [=] empty ->
    d_tags Δ' ph ->
    Γ ⊢ᵤ ph ->   (* WT: no Δ' *)
    is_ttyp ph ->
    (Δ `union` Δ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⊑ B ->
    Δ ⨟ Γ ⊢[ m ] (utyp_all_syn C) ⊑ B
where "Δ ⨟ Γ ⊢[ M ] C ⊑ B" := (d_sub M Δ Γ C B) : type_scope.

Inductive d_shallow_sub : list (atom * dbind) -> ptyp -> ptyp -> Prop :=
| d_shallow_sub__refl : forall Γ A,
    d_wf_ptyp Γ A ->
    d_shallow_sub Γ A A
| d_shallow_sub__arrow : forall Γ A1 A2 A1' A2',
    d_shallow_sub Γ A1' A1 ->
    d_shallow_sub Γ A2 A2' ->
    d_shallow_sub Γ (ptyp_arrow A1 A2) (ptyp_arrow A1' A2')
| d_shallow_sub__forall_r : forall L Γ A1 A2,
    (forall X, X `notin` L ->
       d_shallow_sub ((X ~ dbind_tvar) ++ Γ) A1
         (open_ptyp_wrt_ptyp A2 (ptyp_var_f X))) ->
    d_shallow_sub Γ A1 (ptyp_all A2)
| d_shallow_sub__forall_l : forall Γ A1 A2 I,
    d_wf_ptyp Γ I ->
    d_shallow_sub Γ (open_ptyp_wrt_ptyp A1 I) A2 ->
    d_shallow_sub Γ (ptyp_all A1) A2.

(* ===================================================================== *)
(*  Skeleton refinement, consistency, and subtyping                       *)
(* ===================================================================== *)

(* Output is [bskl] (bidirectional), not [pskl]: the paper's refinement
   produces bidirectional skeletons [bid{Q}], e.g. the ∀-rule outputs an
   inherited [inh{∀α.}bid{Q}] (declarative.tex), which [pskl] (which has
   only [pskl_all_syn]) cannot express.  Filling a ghost [□] still yields
   a synthesised skeleton, encoded as a [pskl] coerced via
   [pskl_to_bskl_syn]. *)
Inductive d_refine_syn : list atom -> list (atom * dbind) -> bskl -> bskl -> Prop :=
(* WT: LHS is always an inherited skeleton. I'm not sure if it's worth
mentioning as a predicate. *)
| d_refine_syn__unit : forall Ψ Γ,
    Ψ ⨟ Γ ⊢ᵣ bskl_unit ⊳ bskl_unit
| d_refine_syn__var : forall Ψ Γ X,
    List.In X Ψ \/ binds X dbind_tvar Γ ->
    Ψ ⨟ Γ ⊢ᵣ (bskl_var_f X) ⊳ (bskl_var_f X)
| d_refine_syn__arrow : forall Ψ Γ Q1 Q2 P1 P2,
    Ψ ⨟ Γ ⊢ᵣ Q1 ⊳ P1 ->
    Ψ ⨟ Γ ⊢ᵣ Q2 ⊳ P2 ->
    Ψ ⨟ Γ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow P1 P2)
| d_refine_syn__all : forall L Ψ Γ Q P,
    (* Paper ∀-rule (declarative.tex): inh{∀α.P} ◁syn inh{∀α.}bid{Q} —
       the quantifier is inherited on both sides (the input is the
       inherited painting of the same skeleton fed by [d_*__app]). *)
    (forall X, X `notin` L ->
       (X :: Ψ) ⨟ Γ ⊢ᵣ
         (open_bskl_wrt_bskl Q (bskl_var_f X)) ⊳
         (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ᵣ (bskl_all_inh Q) ⊳ (bskl_all_inh P)
| d_refine_syn__hole : forall Ψ Γ P,
    (* [□ ◁syn syn{Q}]: clear Ψ so the filling cannot use variables
       bound by other universal quantifiers. *)
    nil ⨟ Γ ⊢ₚₛ P ->
    Ψ ⨟ Γ ⊢ᵣ bskl_hole ⊳ (pskl_to_bskl_syn P)
| d_refine_syn__tophole_remove : forall Ψ Γ Q P,
    (* [⫯.inh{P} ◁syn bid{Q}]: remove the universal ghost. *)
    nil ⨟ Γ ⊢ᵣ Q ⊳ P ->
    Ψ ⨟ Γ ⊢ᵣ (bskl_tophole Q) ⊳ P
| d_refine_syn__tophole_fill : forall L Ψ Γ Q P,
    (* [⫯.inh{P} ◁syn syn{∀α.}bid{Q}]: fill the universal ghost with a
       concrete quantifier; α joins Γ (it may be used filling ghosts,
       unlike ∀-bound vars which live in Ψ), Ψ cleared. *)
    (forall X, X `notin` L ->
       nil ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ᵣ
         (bskl_tophole Q) ⊳ (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_all_syn P)
| d_refine_syn__tophole_keep : forall Ψ Γ Q P,
    (* [⫯.inh{P} ◁syn ⫯.bid{Q}]: keep the universal ghost; the output
       under the ghost must be guarded to preserve well-formedness. *)
    guarded_bskl P ->
    nil ⨟ Γ ⊢ᵣ Q ⊳ P ->
    Ψ ⨟ Γ ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_tophole P)
where "Ψ ⨟ Γ ⊢ᵣ Q ⊳ P" := (d_refine_syn Ψ Γ Q P) : type_scope.

(* The latest paper keeps only the coloured refinement relation
   [Γ ⊢ inh{P} ◁syn bid{Q}] (the uncoloured [◁] is just its colour
   erasure).  The former uncoloured [d_refine] ([▸]) is therefore
   dropped; [d_refine_syn] ([⊳]) above is the single refinement
   relation.  (declarative.tex, "only keep the coloured refinement
   relation".) *)
(* WT: In the lastest draft I mentioned the uncoloured version is
defined by ignoring colours. I used the uncoloured version when
defining valid and safe skeletons. I would need to spend more time on
these definitions, so we can ignore it for now. *)

Inductive d_pat_consis : list atom -> list (atom * dbind) -> uskl -> bskl -> Prop :=
| d_pat_consis__unit : forall Γ,
    nil ⨟ Γ ⊨ₛ uskl_unit ≈ bskl_unit
| d_pat_consis__var : forall Γ X,
    binds X dbind_tvar Γ ->
    nil ⨟ Γ ⊨ₛ (uskl_var_f X) ≈ (bskl_var_f X)
| d_pat_consis__arrow : forall Δ1 Δ2 Γ R1 R2 Q1 Q2,
    Δ1 ⨟ Γ ⊨ₛ R1 ≈ Q1 ->
    Δ2 ⨟ Γ ⊨ₛ R2 ≈ Q2 ->
    (* WT: It shouldn't be disjoint union.
       [list_disjoint Δ1 Δ2] premise removed per WT review: tag
       contexts combine by (non-disjoint) set union, not disjoint union. *)
    (Δ1 ++ Δ2) ⨟ Γ ⊨ₛ (uskl_arrow R1 R2) ≈ (bskl_arrow Q1 Q2)
| d_pat_consis__forall_inh_tagged : forall L Δ Γ ε R Q,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    (* WT: codex confirmed the [~ List.In ε Δ] premise was checking
       freshness; removed per WT review. *)
    (ε :: Δ) ⨟ Γ ⊨ₛ (uskl_all_etag ε R) ≈ (bskl_all_inh Q)
| d_pat_consis__forall_inh_untagged : forall L Δ Γ R Q,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Δ ⨟ Γ ⊨ₛ (uskl_all_syn R) ≈ (bskl_all_inh Q)
| d_pat_consis__forall_syn_tagged : forall L Δ Γ ε R Q,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Δ ⨟ Γ ⊨ₛ (uskl_all_etag ε R) ≈ (bskl_all_syn Q)
| d_pat_consis__forall_syn : forall L Δ Γ R Q,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Δ ⨟ Γ ⊨ₛ (uskl_all_syn R) ≈ (bskl_all_syn Q)
(* NB: the consistency ghost-G rules [GhostTag] ([HoleG ~ Hole]) and
   [UnivGhostG] ([TopHoleG.S ~ TopHole.P]) are DEFERRED for the same
   reason as the [d_pat_sub] ghost-G rules — see the deferral note on
   [d_pat_sub] below (no [HoleG]/[TopHoleG] in [uskl]; feature tentative
   in the paper). *)
| d_pat_consis__hole : forall Γ P,
    (* Paper [Ghost]: a [Hole] matches any *inherited* skeleton [inh{P}]
       (WT: "RHS should just be P?" — the RHS is the inherited painting
       of the pattern skeleton, not the synthesised one). *)
    d_wf_pskl nil Γ P ->
    nil ⨟ Γ ⊨ₛ uskl_hole ≈ (pskl_to_bskl_inh P)
| d_pat_consis__tophole : forall Δ Γ R Q,
    (* Paper [UnivGhost]: TopHole ≈ TopHole. *)
    Δ ⨟ Γ ⊨ₛ R ≈ Q ->
    Δ ⨟ Γ ⊨ₛ (uskl_tophole R) ≈ (bskl_tophole Q)
| d_pat_consis__tophole_inh : forall L Δ Γ R Q,
    (* Paper [UnivGhost1] (was missing, WT): the RHS TopHole can produce
       an inherited quantifier.  LHS [TopHole.R] is unchanged; the RHS
       body [Q] is checked under a fresh [α]. *)
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ₛ
         (uskl_tophole R) ≈ (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Δ ⨟ Γ ⊨ₛ (uskl_tophole R) ≈ (bskl_all_inh Q)
| d_pat_consis__tophole_drop : forall Δ Γ R Q,
    (* Paper [UnivGhost2] (was missing, WT): the LHS TopHole can be
       dropped against a plain inherited RHS. *)
    Δ ⨟ Γ ⊨ₛ R ≈ Q ->
    Δ ⨟ Γ ⊨ₛ (uskl_tophole R) ≈ Q
where "Δ ⨟ Γ ⊨ₛ R ≈ Q" := (d_pat_consis Δ Γ R Q) : type_scope.

(* WT: "This definition seems rather out-of-sync. I'll skip it."
   Reworked (WT review) against the current paper looksub figure
   (declarative.tex, [patsub]).  [d_pat_sub] has no metatheory consumers
   yet, so this is a definition-only sync.  Note: paper rules [GhostG]
   ([HoleG ⊑ Hole]) and [UnivGhostLG] ([TopHoleG.S ⊑ P]) are NOT encoded
   — the mech skeleton AST has no separate ghost-tagged [HoleG] /
   [TopHoleG] constructors.

   DEFERRED (decision 2026-06-11): a faithful extension would add the
   ghost-tagged constructors to [uskl] ONLY (the paper's unresolved
   skeleton [S], declarative.tex:1638; the resolved [bskl]/[pskl] sorts
   have only plain [Hole]/[TopHole], so extending them would over-talk).
   But the paper marks [HoleG]/[TopHoleG] as tentative (`\hl{}` highlight
   + WT's note at declarative.tex:1649, "I don't think that simplifies
   much things"), so the [uskl] AST extension is held until the paper
   settles.  Same deferral applies to the consistency rules [GhostTag]
   ([HoleG ~ Hole]) and [UnivGhostG] ([TopHoleG.S ~ TopHole.P]). *)
Inductive d_pat_sub : mode -> list atom -> list (atom * dbind) -> uskl -> bskl -> Prop :=
| d_pat_sub__infer : forall Γ R Q,
    (* Paper [Infer]: synthesise by consistency, dropping tags. *)
    nil ⨟ Γ ⊨ₛ R ≈ Q ->
    is_sskl Q ->
    nil ⨟ Γ ⊢ₛ[ mode_ti ] R ⊑ Q
| d_pat_sub__univ_ghost_r : forall Γ R Q,
    (* Paper [UnivGhostR] (replaces the out-of-sync [check]; WT review):
       the checking rule produces a [TopHole] on the RHS, requires BOTH
       [R] and the synthesised body [Q] guarded, and [Q] synthesised
       ([is_sskl]) — answering WT's "shouldn't Q be synthesised?". *)
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    nil ⨟ Γ ⊨ₛ R ≈ Q ->
    nil ⨟ Γ ⊢ₛ[ mode_tc ] R ⊑ (bskl_tophole Q)
| d_pat_sub__arg : forall Δ1 Δ2 Γ m R1 R2 Q1 Q2,
    (* Paper [Arrow]: set-union tag context (no [list_disjoint]). *)
    Δ1 ⨟ Γ ⊨ₛ R1 ≈ Q1 ->
    Δ2 ⨟ Γ ⊢ₛ[ m ] R2 ⊑ Q2 ->
    (Δ1 ++ Δ2) ⨟ Γ ⊢ₛ[ mode_fn m ] (uskl_arrow R1 R2) ⊑ (bskl_arrow Q1 Q2)
| d_pat_sub__forall_l_tagged : forall Δ Δ' Γ m ε R psi Q,
    (* Paper [ForallL] (tagged head).  [Ψ' fresh] = [list_disjoint];
       well-scopedness is [nil ⨟ Γ ⊢ᵤₛ ψ] (S1: scope, not tags). *)
    m <> mode_ti ->
    list_disjoint Δ' Δ ->
    d_tags_skl Δ' psi ->             (* tags{Δ'}{ψ} : skeleton-tag relation *)
    nil ⨟ Γ ⊢ᵤₛ psi ->
    is_tskl psi ->
    (Δ ++ Δ') ⨟ Γ ⊢ₛ[ m ] (open_uskl_wrt_uskl R psi) ⊑ Q ->
    Δ ⨟ Γ ⊢ₛ[ m ] (uskl_all_etag ε R) ⊑ Q
| d_pat_sub__forall_l_untagged : forall Δ Δ' Γ m R psi Q,
    m <> mode_ti ->
    list_disjoint Δ' Δ ->
    d_tags_skl Δ' psi ->
    nil ⨟ Γ ⊢ᵤₛ psi ->
    is_tskl psi ->
    (Δ ++ Δ') ⨟ Γ ⊢ₛ[ m ] (open_uskl_wrt_uskl R psi) ⊑ Q ->
    Δ ⨟ Γ ⊢ₛ[ m ] (uskl_all_syn R) ⊑ Q
| d_pat_sub__ghost : forall m Γ P,
    (* Paper [Ghost]: a [Hole] is below any inherited skeleton [inh{P}]. *)
    d_wf_pskl nil Γ P ->
    nil ⨟ Γ ⊢ₛ[ m ] uskl_hole ⊑ (pskl_to_bskl_inh P)
| d_pat_sub__univ_ghost_l : forall m Δ Γ R Q,
    (* Paper [UnivGhostL]: drop a [TopHole] on the LHS (any [M ≠ TI]). *)
    m <> mode_ti ->
    Δ ⨟ Γ ⊢ₛ[ m ] R ⊑ Q ->
    Δ ⨟ Γ ⊢ₛ[ m ] (uskl_tophole R) ⊑ Q
where "Δ ⨟ Γ ⊢ₛ[ M ] R ⊑ Q" := (d_pat_sub M Δ Γ R Q) : type_scope.

(* ===================================================================== *)
(*  Typing and pattern inference                                          *)
(* ===================================================================== *)

Inductive is_base_term : exp -> Prop :=
| is_base_term__unit : is_base_term exp_unit
| is_base_term__var  : forall x, is_base_term (exp_var_f x)
| is_base_term__anno : forall e A, is_base_term (exp_anno e A).

Inductive d_typing : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
| d_typing__unit : forall Γ,
    d_typing mode_ti Γ exp_unit btyp_unit
| d_typing__var : forall Γ x A,
    binds x (dbind_typ A) Γ ->
    d_typing mode_ti Γ (exp_var_f x) (ptyp_to_btyp_syn A)
| d_typing__anno : forall Γ e A,
    d_typing mode_tc Γ e (ptyp_to_btyp_inh A) ->
    d_typing mode_ti Γ (exp_anno e A) (ptyp_to_btyp_syn A)
| d_typing__sub : forall Γ m e B1 B2,
    is_base_term e ->
    d_typing mode_ti Γ e B1 ->
    d_sub m empty Γ (ptyp_to_utyp_syn B1) B2 ->
    d_typing m Γ e B2
| d_typing__freeze : forall Γ e B,
    d_typing mode_ti Γ e B ->
    d_typing mode_tc Γ (exp_freeze e) B
| d_typing__forall : forall L Γ e B,
    is_value e ->
    (forall X, X `notin` L ->
       d_typing mode_tc ((X ~ dbind_tvar) ++ Γ) e
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    d_typing mode_tc Γ e (btyp_all_inh B)
| d_typing__abs : forall L Γ m e A B,
    d_wf_ptyp Γ A ->
    (forall x, x `notin` L ->
       d_typing (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing m Γ (exp_abs e) (btyp_arrow (ptyp_to_btyp_inh A) B)
| d_typing__abs_anno : forall L Γ m e A Barg B,
    (* WT: "A is not synthesised but bidirectional — there exists a
       bidirectional A whose uncoloured version is the annotation."
       Encoded: the conclusion's arrow-arg is an arbitrary bidirectional
       [Barg] whose erasure [btyp_to_ptyp] is the annotation [A]. *)
    d_wf_ptyp Γ A ->
    btyp_to_ptyp Barg = A ->
    (forall x, x `notin` L ->
       d_typing (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing m Γ (exp_abs_anno A e) (btyp_arrow Barg B)
| d_typing__app : forall Γ m e1 e2 P A Barg B,
    (* WT: the function-arg should be a bidirectional [A] (here [Barg]
       with [btyp_to_ptyp Barg = A]), not the forced inherited painting;
       the argument is still *checked* at [inh{A}] (paper D-App). *)
    btyp_to_ptyp Barg = A ->
    d_pat mode_tc Γ e2 (pskl_to_bskl_syn P) ->
    d_refine_syn nil Γ (pskl_to_bskl_inh P) (pskl_to_bskl_inh (ptyp_to_pskl A)) ->
    d_typing (mode_fn m) Γ e1 (btyp_arrow Barg B) ->
    d_typing mode_tc Γ e2 (ptyp_to_btyp_inh A) ->
    d_typing m Γ (exp_app e1 e2) B

with d_pat : mode -> list (atom * dbind) -> exp -> bskl -> Prop :=
| d_pat__unit : forall Γ,
    d_pat mode_ti Γ exp_unit bskl_unit
| d_pat__var : forall Γ x P,
    binds x (dbind_skl P) Γ ->
    d_pat mode_ti Γ (exp_var_f x) (pskl_to_bskl_syn P)
| d_pat__anno : forall Γ e A,
    d_wf_ptyp Γ A ->
    d_pat mode_ti Γ (exp_anno e A) (pskl_to_bskl_syn (ptyp_to_pskl A))
| d_pat__sub : forall Γ m e Q1 Q2,
    is_base_term e ->
    d_pat mode_ti Γ e Q1 ->
    d_pat_sub m nil Γ (bskl_to_uskl Q1) Q2 ->
    d_pat m Γ e Q2
| d_pat__freeze : forall Γ e Q,
    d_pat mode_ti Γ e Q ->
    d_pat mode_tc Γ (exp_freeze e) Q
| d_pat__abs : forall L Γ m e P Q,
    m <> mode_tc ->
    d_wf_pskl nil Γ P ->
    (forall x, x `notin` L ->
       d_pat (decr_mode m) ((x ~ dbind_skl P) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    (* WT: "P in the conclusion should be inherited" (paper P-Abs:
       [inh{P} → bid{Q}]). *)
    d_pat m Γ (exp_abs e) (bskl_arrow (pskl_to_bskl_inh P) Q)
| d_pat__abs_check : forall L Γ e Q,
    (forall x, x `notin` L ->
       d_pat mode_tc ((x ~ dbind_skl pskl_hole) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat mode_tc Γ (exp_abs e)
      (bskl_tophole (bskl_arrow bskl_hole Q))
| d_pat__abs_anno : forall L Γ m e A Sarg Q,
    (* WT: "as with d_typing, there exists a bidirectional A" — the
       arrow-arg skeleton [Sarg] is an arbitrary bidirectional skeleton
       whose erasure [bskl_to_pskl] is the annotation's pattern. *)
    m <> mode_tc ->
    d_wf_ptyp Γ A ->
    bskl_to_pskl Sarg = ptyp_to_pskl A ->
    (forall x, x `notin` L ->
       d_pat (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat m Γ (exp_abs_anno A e) (bskl_arrow Sarg Q)
| d_pat__abs_anno_check : forall L Γ e A Sarg Q,
    (* WT: "same here, A should be bidirectional". *)
    d_wf_ptyp Γ A ->
    bskl_to_pskl Sarg = ptyp_to_pskl A ->
    (forall x, x `notin` L ->
       d_pat mode_tc ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat mode_tc Γ (exp_abs_anno A e)
      (bskl_tophole (bskl_arrow Sarg Q))
| d_pat__app : forall Γ m e1 e2 P A1 A2 Barg1 Sres,
    (* WT: "there exists a bidirectional A; also, the result A_2 should
       be bidirectional" — [Barg1] is a bidirectional arg ([= A1]) and
       [Sres] a bidirectional result skeleton ([= A2]). *)
    btyp_to_ptyp Barg1 = A1 ->
    bskl_to_pskl Sres = ptyp_to_pskl A2 ->
    d_pat mode_tc Γ e2 (pskl_to_bskl_syn P) ->
    d_refine_syn nil Γ (pskl_to_bskl_inh P) (pskl_to_bskl_inh (ptyp_to_pskl A1)) ->
    d_typing (mode_fn m) Γ e1
      (btyp_arrow Barg1 (ptyp_to_btyp_inh A2)) ->
    d_pat m Γ (exp_app e1 e2) Sres.

(* WT: Other comments:
1. In the paper I have \skmod[\N]{\M}{P} as well-formedness conditions
for typing and skinfer judgements. I'm not sure if we want them to be
part of the definitions, but we should at least prove that they are
preserved. I mentioned this because in d_pat, some of the requirements
of colours are not mentioned explicitly, but can be guaranteed from
\skmod.
*)