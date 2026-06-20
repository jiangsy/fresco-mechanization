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
   (not 75): the three-context refinement [Γ ⨟ Δs ⨟ Δi ⊢ᵣ …] needs its
   inner slots below the notation level to avoid self-recursion, and
   camlp5 requires every notation sharing the [_ ⨟ _] prefix to agree on
   that slot's level.  Context slots only ever hold [Γ]/[Δ] built from
   [++]/[::]/[~] (all ≤ 60), so level 74 is ample. *)
Reserved Notation "Ψ ⨟ Γ ⊢ₚₛ P"
  (at level 75, Γ at level 74, P at level 75, no associativity).
Reserved Notation "Γ ⊢ᵦ B"
  (at level 75, B at level 75, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ᵤ C"
  (at level 75, Γ at level 74, C at level 75, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ᵤₛ R"
  (at level 75, Γ at level 74, R at level 75, no associativity).
Reserved Notation "Δ ⨟ Γ ⊨ C ≈ B"
  (at level 75, Γ at level 74, C at level 74, B at level 74, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢[ M ] C ⊑ B"
  (at level 75, Γ at level 74, M at level 0, C at level 74, B at level 74,
   no associativity).
Reserved Notation "Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P"
  (at level 75, Δs at level 74, Δi at level 74,
   Q at level 74, P at level 74, no associativity).
Reserved Notation "Δ ⨟ Γ ⊨ₛ R ≈ Q"
  (at level 75, Γ at level 74, R at level 74, Q at level 74, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ₛ[ M ] R ⊑ Q"
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
| d_wf_pskl__tophole : forall Ψ Γ P,
    (* Paper [⫯.P] rule (declarative.tex): the scope set [Ψ] (paper's [Δ])
       is cleared in the PREMISE, but the conclusion holds under an
       ARBITRARY [Ψ] — matching [d_wf_uskl__tophole].  (The old [nil]
       conclusion wrongly rejected [∀α.⫯.P].) *)
    guarded_pskl P ->
    nil ⨟ Γ ⊢ₚₛ P ->
    Ψ ⨟ Γ ⊢ₚₛ (pskl_tophole P)
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
(* Dotted ghosts: same well-formedness as the plain Hole / TopHole. *)
| d_wf_uskl__holeg : forall Ψ Γ,
    Ψ ⨟ Γ ⊢ᵤₛ uskl_holeg
| d_wf_uskl__topholeg : forall Ψ Γ R,
    guarded_uskl R ->
    nil ⨟ Γ ⊢ᵤₛ R ->
    Ψ ⨟ Γ ⊢ᵤₛ (uskl_topholeg R)
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
    d_tags_skl Δ (uskl_tophole R)
(* Dotted ghosts (declarative.tex:1698,1704): HoleG carries no tags;
   TopHoleG.ψ carries exactly the tags of its body — same as the plain
   Hole / TopHole. *)
| d_tags_skl__holeg : d_tags_skl nil uskl_holeg
| d_tags_skl__topholeg : forall Δ R,
    d_tags_skl Δ R ->
    d_tags_skl Δ (uskl_topholeg R).

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

Reserved Notation "Γ ⊢ A ≤ B"
  (at level 75, A at level 74, B at level 74, no associativity).
Inductive d_shallow_sub : list (atom * dbind) -> ptyp -> ptyp -> Prop :=
| d_shallow_sub__refl : forall Γ A,
    Γ ⊢ₚ A ->
    Γ ⊢ A ≤ A
| d_shallow_sub__arrow : forall Γ A1 A2 A1' A2',
    Γ ⊢ A1' ≤ A1 ->
    Γ ⊢ A2 ≤ A2' ->
    Γ ⊢ (ptyp_arrow A1 A2) ≤ (ptyp_arrow A1' A2')
| d_shallow_sub__forall_r : forall L Γ A1 A2,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ A1 ≤ (open_ptyp_wrt_ptyp A2 (ptyp_var_f X))) ->
    Γ ⊢ A1 ≤ (ptyp_all A2)
| d_shallow_sub__forall_l : forall Γ A1 A2 I,
    Γ ⊢ₚ I ->
    Γ ⊢ (open_ptyp_wrt_ptyp A1 I) ≤ A2 ->
    Γ ⊢ (ptyp_all A1) ≤ A2
where "Γ ⊢ A ≤ B" := (d_shallow_sub Γ A B) : type_scope.

(* ===================================================================== *)
(*  Skeleton refinement, consistency, and subtyping                       *)
(* ===================================================================== *)

(* Output is [bskl] (bidirectional), not [pskl]: the paper's refinement
   produces bidirectional skeletons [bid{Q}], e.g. the ∀-rule outputs an
   inherited [inh{∀α.}bid{Q}] (declarative.tex), which [pskl] (which has
   only [pskl_all_syn]) cannot express.  Filling a ghost [□] still yields
   a synthesised skeleton, encoded as a [pskl] coerced via
   [pskl_to_bskl_syn]. *)
(* Two skeleton-scope contexts beyond the existing tvar context [Γ]:
     - [Δs] : tvars bound by *synthesised* quantifiers seen so far in the
              skeleton (those introduced by filling a universal ghost
              [TopHole] with a concrete [∀^syn]);
     - [Δi] : tvars bound by *inherited* quantifiers ([∀^inh]) seen so far.
   The two are tracked separately because they have different scope
   discipline (see the [Hole] / [TopHole] rules below).  Earlier this
   was a single context [Ψ] plus dumping the syn-quantifier var into
   [Γ]; that let an inner body refer to an *outside* syn quantifier
   (e.g. refining [⫯.(□→unit)] to [∀^syn α.⫯.(α→unit)], which is NOT
   [d_wf_pskl]), breaking [d_refine_preserves_wf].  Clearing-profile:
     | context  | as var occ. | fills [Hole] | survives [TopHole] |
     | Γ         |     ✓       |      ✓       |        ✓           |
     | Δs (syn)  |     ✓       |      ✓       |        ✗           |
     | Δi (inh)  |     ✓       |      ✗       |        ✗           | *)
Inductive d_refine_syn : list (atom * dbind) -> list atom -> list atom -> bskl -> bskl -> Prop :=
(* WT: LHS is always an inherited skeleton. I'm not sure if it's worth
mentioning as a predicate. *)
| d_refine_syn__unit : forall Γ Δs Δi,
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ bskl_unit ⊳ bskl_unit
| d_refine_syn__var : forall Γ Δs Δi X,
    (* A plain occurrence may be any in-scope tvar (Γ, syn, or inh). *)
    List.In X Δs \/ List.In X Δi \/ binds X dbind_tvar Γ ->
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ (bskl_var_f X) ⊳ (bskl_var_f X)
| d_refine_syn__arrow : forall Γ Δs Δi Q1 Q2 P1 P2,
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q1 ⊳ P1 ->
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q2 ⊳ P2 ->
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow P1 P2)
| d_refine_syn__all : forall L Γ Δs Δi Q P,
    (* Paper ∀-rule (declarative.tex): inh{∀α.P} ◁syn inh{∀α.}bid{Q} —
       the quantifier is inherited on both sides (the input is the
       inherited painting of the same skeleton fed by [d_*__app]); the
       bound var joins the *inherited* context [Δi]. *)
    (forall X, X `notin` L ->
       Γ ⨟ Δs ⨟ (X :: Δi) ⊢ᵣ
         (open_bskl_wrt_bskl Q (bskl_var_f X)) ⊳
         (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ (bskl_all_inh Q) ⊳ (bskl_all_inh P)
| d_refine_syn__hole : forall Γ Δs Δi P,
    (* [□ ◁syn syn{Q}]: clear [Δi] so the filling cannot use inherited
       ∀-bound vars; keep [Δs] (syn-quantifier vars *can* fill ghosts).
       So the fill is checked by [d_wf_pskl] with scope set [Ψ := Δs]. *)
    Δs ⨟ Γ ⊢ₚₛ P ->
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ bskl_hole ⊳ (pskl_to_bskl_syn P)
| d_refine_syn__tophole_remove : forall Γ Δs Δi Q P,
    (* [⫯.inh{P} ◁syn bid{Q}]: remove the universal ghost.  Clear [Δi]
       (inherited vars unusable below a ghost), but KEEP [Δs]: the body
       is promoted to the same synthesised-quantifier scope, so prior
       syn-vars stay available. *)
    Γ ⨟ Δs ⨟ nil ⊢ᵣ Q ⊳ P ->
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ (bskl_tophole Q) ⊳ P
| d_refine_syn__tophole_fill : forall L Γ Δs Δi Q P,
    (* [⫯.inh{P} ◁syn syn{∀α.}bid{Q}]: fill the universal ghost with a
       concrete synthesised quantifier; α is ADDED to the *syn* context
       [Δs] (so consecutive synthesised quantifiers accumulate and may
       fill ghosts), while [Δi] is cleared. *)
    (forall X, X `notin` L ->
       Γ ⨟ (X :: Δs) ⨟ nil ⊢ᵣ
         (bskl_tophole Q) ⊳ (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_all_syn P)
| d_refine_syn__tophole_keep : forall Γ Δs Δi Q P,
    (* [⫯.inh{P} ◁syn ⫯.bid{Q}]: keep the universal ghost; the output
       under the ghost must be guarded to preserve well-formedness.
       This is a genuine universal-ghost boundary, so clear BOTH [Δs]
       and [Δi]. *)
    guarded_bskl P ->
    Γ ⨟ nil ⨟ nil ⊢ᵣ Q ⊳ P ->
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_tophole P)
where "Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P" := (d_refine_syn Γ Δs Δi Q P) : type_scope.

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
| d_pat_consis__ghostg : forall Γ,
    (* Paper [GhostG] (declarative.tex eqlab): a ghost hole [HoleG] is
       consistent with a plain [Hole]. *)
    nil ⨟ Γ ⊨ₛ uskl_holeg ≈ bskl_hole
| d_pat_consis__topholeg : forall Δ Γ R Q,
    (* Paper [UnivGhostG]: [TopHoleG.S ~ TopHole.P] from [S ~ P]. *)
    Δ ⨟ Γ ⊨ₛ R ≈ Q ->
    Δ ⨟ Γ ⊨ₛ (uskl_topholeg R) ≈ (bskl_tophole Q)
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

(* Reworked (WT review) against the current paper looksub figure
   (declarative.tex, [patsub]).  [d_pat_sub] is used only as a premise of
   [d_pat__sub] (the Sub rule of skeleton inference, paper [Sub] in
   fig:decl-skeleton-inference).  No proof reasons about its *content*
   (how skeleton subtyping behaves); the only consumer is the structural
   [d_pat_sub_weakening], reached transitively from D1's [app] case via
   [d_pat_ctx_weaken].  Its content-level consumers — Validity / Safety of
   skeleton inference ([d_pat_validity] / [d_pat_safety]) — are still open.
   The dotted-ghost constructors
   ([uskl_holeg]/[uskl_topholeg]) are now in the AST ([uskl] only — the
   paper's unresolved skeleton [S], declarative.tex:1638), so the paper
   rules [GhostG] ([HoleG ⊑ Hole]) and [UnivGhostLG] ([TopHoleG.S ⊑ P])
   are encoded below (and the matching consistency rules [GhostG]/
   [UnivGhostG] on [d_pat_consis]). *)
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
| d_pat_sub__ghostg : forall m Γ,
    (* Paper [GhostG]: a ghost hole [HoleG] is below a plain [Hole]. *)
    nil ⨟ Γ ⊢ₛ[ m ] uskl_holeg ⊑ bskl_hole
| d_pat_sub__univ_ghost_lg : forall m Δ Γ R Q,
    (* Paper [UnivGhostLG]: drop a [TopHoleG] on the LHS (any [M ≠ TI]). *)
    m <> mode_ti ->
    Δ ⨟ Γ ⊢ₛ[ m ] R ⊑ Q ->
    Δ ⨟ Γ ⊢ₛ[ m ] (uskl_topholeg R) ⊑ Q
where "Δ ⨟ Γ ⊢ₛ[ M ] R ⊑ Q" := (d_pat_sub M Δ Γ R Q) : type_scope.

(* ===================================================================== *)
(*  Typing and pattern inference                                          *)
(* ===================================================================== *)

Inductive is_base_term : exp -> Prop :=
| is_base_term__unit : is_base_term exp_unit
| is_base_term__var  : forall x, is_base_term (exp_var_f x)
| is_base_term__anno : forall e A, is_base_term (exp_anno e A).

Reserved Notation "Γ ⊢[ M ] e ⦂ A"
  (at level 100, M at level 0, e at level 75, A at level 75, no associativity).
Reserved Notation "Γ ⊢[ M ] e ⇨ P"
  (at level 100, M at level 0, e at level 75, P at level 75, no associativity).

Inductive d_typing : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
| d_typing__unit : forall Γ,
    Γ ⊢[ mode_ti ] exp_unit ⦂ btyp_unit
| d_typing__var : forall Γ x A,
    binds x (dbind_typ A) Γ ->
    Γ ⊢[ mode_ti ] (exp_var_f x) ⦂ (ptyp_to_btyp_syn A)
| d_typing__anno : forall Γ e A,
    Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) ->
    Γ ⊢[ mode_ti ] (exp_anno e A) ⦂ (ptyp_to_btyp_syn A)
| d_typing__sub : forall Γ m e B1 B2,
    is_base_term e ->
    Γ ⊢[ mode_ti ] e ⦂ B1 ->
    empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn B1) ⊑ B2 ->
    Γ ⊢[ m ] e ⦂ B2
| d_typing__freeze : forall Γ e B,
    Γ ⊢[ mode_ti ] e ⦂ B ->
    Γ ⊢[ mode_tc ] (exp_freeze e) ⦂ B
| d_typing__forall : forall L Γ e B,
    is_value e ->
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢[ mode_tc ] e ⦂ (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Γ ⊢[ mode_tc ] e ⦂ (btyp_all_inh B)
| d_typing__abs : forall L Γ m e A B,
    (* Paper [Abs] (syntax-directed.tex): [M ≠ TC]; the check-mode
       abstraction goes through [d_typing__abs_check] instead. *)
    m <> mode_tc ->
    Γ ⊢ₚ A ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B) ->
    Γ ⊢[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B)
| d_typing__abs_check : forall L Γ e A B,
    (* Paper [AbsCheck] (syntax-directed.tex), [ᾱ = ·] base; the [∀ᾱ]
       prefix is supplied by [d_typing__forall].  Mirrors [d_pat__abs_check]. *)
    Γ ⊢ₚ A ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B) ->
    Γ ⊢[ mode_tc ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B)
| d_typing__abs_anno : forall L Γ m e A Barg B,
    (* The arrow-arg is an arbitrary bidirectional [Barg] whose erasure
       [btyp_to_ptyp] is the annotation [A].  Paper [AbsAnno]: [M ≠ TC]. *)
    m <> mode_tc ->
    Γ ⊢ₚ A ->
    btyp_to_ptyp Barg = A ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B) ->
    Γ ⊢[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow Barg B)
| d_typing__abs_anno_check : forall L Γ e A Barg B,
    (* Paper [AbsAnnoCheck], [ᾱ = ·] base.  Mirrors [d_pat__abs_anno_check]. *)
    Γ ⊢ₚ A ->
    btyp_to_ptyp Barg = A ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B) ->
    Γ ⊢[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_arrow Barg B)
| d_typing__app : forall Γ m e1 e2 P A Barg B,
    (* The function-arg is a bidirectional [A] ([Barg] with
       [btyp_to_ptyp Barg = A]); the argument is checked at [inh{A}]. *)
    btyp_to_ptyp Barg = A ->
    Γ ⊢[ mode_tc ] e2 ⇨ (pskl_to_bskl_syn P) ->
    Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)) ->
    Γ ⊢[ mode_fn m ] e1 ⦂ (btyp_arrow Barg B) ->
    Γ ⊢[ mode_tc ] e2 ⦂ (ptyp_to_btyp_inh A) ->
    Γ ⊢[ m ] (exp_app e1 e2) ⦂ B

with d_pat : mode -> list (atom * dbind) -> exp -> bskl -> Prop :=
| d_pat__unit : forall Γ,
    Γ ⊢[ mode_ti ] exp_unit ⇨ bskl_unit
| d_pat__var : forall Γ x P d,
    binds x d Γ ->
    dbind_to_pskl d = Some P ->
    Γ ⊢[ mode_ti ] (exp_var_f x) ⇨ (pskl_to_bskl_syn P)
| d_pat__anno : forall Γ e A,
    Γ ⊢ₚ A ->
    Γ ⊢[ mode_ti ] (exp_anno e A) ⇨ (pskl_to_bskl_syn (ptyp_to_pskl A))
| d_pat__sub : forall Γ m e Q1 Q2,
    is_base_term e ->
    Γ ⊢[ mode_ti ] e ⇨ Q1 ->
    nil ⨟ Γ ⊢ₛ[ m ] (bskl_to_uskl Q1) ⊑ Q2 ->
    Γ ⊢[ m ] e ⇨ Q2
| d_pat__freeze : forall Γ e Q,
    Γ ⊢[ mode_ti ] e ⇨ Q ->
    Γ ⊢[ mode_tc ] (exp_freeze e) ⇨ Q
| d_pat__abs : forall L Γ m e P Q,
    m <> mode_tc ->
    nil ⨟ Γ ⊢ₚₛ P ->
    (forall x, x `notin` L ->
       ((x ~ dbind_skl P) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q) ->
    Γ ⊢[ m ] (exp_abs e) ⇨ (bskl_arrow (pskl_to_bskl_inh P) Q)
| d_pat__abs_check : forall L Γ e Q,
    (forall x, x `notin` L ->
       ((x ~ dbind_skl pskl_hole) ++ Γ) ⊢[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q) ->
    Γ ⊢[ mode_tc ] (exp_abs e) ⇨ (bskl_tophole (bskl_arrow bskl_hole Q))
| d_pat__abs_anno : forall L Γ m e A Sarg Q,
    (* The arrow-arg skeleton [Sarg] is bidirectional, [bskl_to_pskl Sarg]
       the annotation's pattern. *)
    m <> mode_tc ->
    Γ ⊢ₚ A ->
    bskl_to_pskl Sarg = ptyp_to_pskl A ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q) ->
    Γ ⊢[ m ] (exp_abs_anno A e) ⇨ (bskl_arrow Sarg Q)
| d_pat__abs_anno_check : forall L Γ e A Sarg Q,
    Γ ⊢ₚ A ->
    bskl_to_pskl Sarg = ptyp_to_pskl A ->
    (forall x, x `notin` L ->
       ((x ~ dbind_typ A) ++ Γ) ⊢[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q) ->
    Γ ⊢[ mode_tc ] (exp_abs_anno A e) ⇨ (bskl_tophole (bskl_arrow Sarg Q))
| d_pat__app : forall Γ m e1 e2 P P' Q,
    (* Paper P-App (declarative.tex:1560): the function [e1] is SKELETON-
       INFERRED ([⇨]) in [FN] mode, not typed — d_pat is self-contained
       skeleton inference.  [P'] is the fill output (the arg skeleton). *)
    Γ ⊢[ mode_tc ] e2 ⇨ (pskl_to_bskl_syn P) ->
    Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ P' ->
    Γ ⊢[ mode_fn m ] e1 ⇨ (bskl_arrow P' Q) ->
    Γ ⊢[ m ] (exp_app e1 e2) ⇨ Q
where "Γ ⊢[ M ] e ⦂ A" := (d_typing M Γ e A) : type_scope
  and "Γ ⊢[ M ] e ⇨ P" := (d_pat M Γ e P) : type_scope.

(* WT: Other comments:
1. In the paper I have \skmod[\N]{\M}{P} as well-formedness conditions
for typing and skinfer judgements. I'm not sure if we want them to be
part of the definitions, but we should at least prove that they are
preserved. I mentioned this because in d_pat, some of the requirements
of colours are not mentioned explicitly, but can be guaranteed from
\skmod.
*)