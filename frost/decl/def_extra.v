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
Require Import src.frost.def_extra.

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope frost_d_scope.

(* ⚠️ THE LEADING SLOT CARRIES NO LEVEL, and the rest sit at 74.  Every
   [{{ … }}X] notation in the tree shares the [{{] prefix with METALIB's
   atom-set singleton [{{ x }}] (Metatheory.v:41), and camlp5 can only factor
   rules whose shared prefix uses the same entry — metalib's is plain [constr],
   so annotating ours produces [notation-incompatible-prefix] and one of the
   two silently stops working.  The inner slots stay at 74 (below the old
   level-75 judgments) because context slots only ever hold [Γ]/[Δ] built from
   [++]/[::]/[~], all ≤ 60. *)
(* Convention (paper-faithful): the ∀-scope context [Δ] comes AFTER [Γ]
   ([Γ ⨟ Δ ⊢ …]); the tag context [Ψ] comes BEFORE [Γ] ([Ψ ⨟ Γ ⊢ …]). *)
Reserved Notation "{{ Γ ⨟ Δ ⊢ₚₛ P }}d"
  (at level 0, Δ at level 74, P at level 74,
   format "'{{'  Γ  ⨟  Δ  ⊢ₚₛ  P  '}}d'").
Reserved Notation "{{ Γ ⊢ᵦ B }}d"
  (at level 0, B at level 74,
   format "'{{'  Γ  ⊢ᵦ  B  '}}d'").
Reserved Notation "{{ Γ ⨟ Δ ⊢ᵤₛ R }}d"
  (at level 0, Δ at level 74, R at level 74,
   format "'{{'  Γ  ⨟  Δ  ⊢ᵤₛ  R  '}}d'").
Reserved Notation "{{ Ψ ⨟ Γ ⊢ C ∼ B }}d"
  (at level 0, Γ at level 74, C at level 74, B at level 74,
   format "'{{'  Ψ  ⨟  Γ  ⊢  C  ∼  B  '}}d'").
Reserved Notation "{{ Ψ ⨟ Γ ⊢[ M ] C ⩽ B }}d"
  (at level 0, Γ at level 74, M at level 0, C at level 74, B at level 74,
   format "'{{'  Ψ  ⨟  Γ  ⊢[  M  ]  C  ⩽  B  '}}d'").
Reserved Notation "{{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d"
  (at level 0, Δ at level 74, Q at level 74, P at level 74,
   format "'{{'  Γ  ⨟  Δ  ⊢ᵣ  Q  ⊳  P  '}}d'").
(* ⚙ the UNCOLOURED twin (declarative.tex:1516); [ₚ] is the sort subscript, as
   in [⊢ₚₛ] — cf. the same pair under [}}ad] *)
Reserved Notation "{{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}d"
  (at level 0, Δ at level 74, P at level 74, Q at level 74,
   format "'{{'  Γ  ⨟  Δ  ⊢ᵣₚ  P  ⊳  Q  '}}d'").
Reserved Notation "{{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d"
  (at level 0, Γ at level 74, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Γ  ⊢ˢ  R  ∼  Q  '}}d'").
Reserved Notation "{{ Ψ ⨟ Γ ⊢ˢ[ M ] R ⩽ Q }}d"
  (at level 0, Γ at level 74, M at level 0, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Γ  ⊢ˢ[  M  ]  R  ⩽  Q  '}}d'").

(* ===================================================================== *)
(*  Well-formedness                                                       *)
(* ===================================================================== *)

Reserved Notation "{{ Γ ⊢ₚ A }}d"
  (at level 0, A at level 74,
   format "'{{'  Γ  ⊢ₚ  A  '}}d'").
Inductive d_wf_ptyp : list (atom * dbind) -> ptyp -> Prop :=
| d_wf_ptyp__unit : forall Γ,
    {{ Γ ⊢ₚ ptyp_unit }}d
| d_wf_ptyp__var : forall Γ α,
    binds α dbind_tvar Γ ->
    {{ Γ ⊢ₚ (ptyp_var_f α) }}d
| d_wf_ptyp__arrow : forall Γ A1 A2,
    {{ Γ ⊢ₚ A1 }}d ->
    {{ Γ ⊢ₚ A2 }}d ->
    {{ Γ ⊢ₚ (ptyp_arrow A1 A2) }}d
| d_wf_ptyp__all : forall L Γ A,
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ₚ (open_ptyp_wrt_ptyp A (ptyp_var_f α)) }}d) ->
    {{ Γ ⊢ₚ (ptyp_all A) }}d
where "{{ Γ ⊢ₚ A }}d" := (d_wf_ptyp Γ A) : frost_d_scope.

Inductive d_wf_btyp : list (atom * dbind) -> btyp -> Prop :=
| d_wf_btyp__unit : forall Γ,
    {{ Γ ⊢ᵦ btyp_unit }}d
| d_wf_btyp__var : forall Γ α,
    binds α dbind_tvar Γ ->
    {{ Γ ⊢ᵦ (btyp_var_f α) }}d
| d_wf_btyp__arrow : forall Γ B1 B2,
    {{ Γ ⊢ᵦ B1 }}d ->
    {{ Γ ⊢ᵦ B2 }}d ->
    {{ Γ ⊢ᵦ (btyp_arrow B1 B2) }}d
| d_wf_btyp__all_syn : forall L Γ B,
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ᵦ (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Γ ⊢ᵦ (btyp_all_syn B) }}d
| d_wf_btyp__all_inh : forall L Γ B,
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ᵦ (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Γ ⊢ᵦ (btyp_all_inh B) }}d
where "{{ Γ ⊢ᵦ B }}d" := (d_wf_btyp Γ B) : frost_d_scope.

(* WT: I updated the notation in the paper to separate well-formedness
of unresolved/tagged types and their linear uses of tags. But I still
write Γ ⊢ T # Δ as checking both, which is consistent with the
definition here.
%
OK, now I saw d_tags defined below. Then we can just remove Δ here.

Done (WT review): the tag context is dropped — [d_wf_utyp] is now pure
well-scopedness ([Γ ⊢ C]); the linear tag content of a tagged type is
checked separately by [d_tags] below. *)
Reserved Notation "{{ Γ ⊢ᵤ C }}d"
  (at level 0, C at level 74,
   format "'{{'  Γ  ⊢ᵤ  C  '}}d'").
Inductive d_wf_utyp : list (atom * dbind) -> utyp -> Prop :=
| d_wf_utyp__unit : forall Γ,
    {{ Γ ⊢ᵤ utyp_unit }}d
| d_wf_utyp__var : forall Γ α,
    binds α dbind_tvar Γ ->
    {{ Γ ⊢ᵤ (utyp_var_f α) }}d
| d_wf_utyp__arrow : forall Γ C1 C2,
    {{ Γ ⊢ᵤ C1 }}d ->
    {{ Γ ⊢ᵤ C2 }}d ->
    {{ Γ ⊢ᵤ (utyp_arrow C1 C2) }}d
| d_wf_utyp__all_syn : forall L Γ C,
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ᵤ (open_utyp_wrt_utyp C (utyp_var_f α)) }}d) ->
    {{ Γ ⊢ᵤ (utyp_all_syn C) }}d
| d_wf_utyp__all_tag : forall L Γ ε C,
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ᵤ (open_utyp_wrt_utyp C (utyp_var_f α)) }}d) ->
    {{ Γ ⊢ᵤ (utyp_all_tag ε C) }}d
where "{{ Γ ⊢ᵤ C }}d" := (d_wf_utyp Γ C) : frost_d_scope.

(* Skeleton well-formedness [{{ Γ ⨟ Δ ⊢ₚₛ P }}d] (declarative.tex:1300).  [Δ] is the
   ∀-scope context (paper's [Δ], the inherited-∀ vars), kept SEPARATE from the
   tvar context [Γ]; the two carry different types so a var occurrence consults
   either.  This is the paper's [Γ∣Δ] presentation with [Δ] as a separate set
   (∀-vars go to [Δ]; the [⫯] rule clears [Δ], matching [Γ\Δ]). *)
Inductive d_wf_pskl : list (atom * dbind) -> list atom -> pskl -> Prop :=
| d_wf_pskl__unit : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ₚₛ pskl_unit }}d
| d_wf_pskl__var : forall Γ Δ α,
    List.In α Δ \/ binds α dbind_tvar Γ ->
    {{ Γ ⨟ Δ ⊢ₚₛ (pskl_var_f α) }}d
| d_wf_pskl__arrow : forall Γ Δ P1 P2,
    {{ Γ ⨟ Δ ⊢ₚₛ P1 }}d ->
    {{ Γ ⨟ Δ ⊢ₚₛ P2 }}d ->
    {{ Γ ⨟ Δ ⊢ₚₛ (pskl_arrow P1 P2) }}d
| d_wf_pskl__all : forall L Γ Δ P,
    (forall α, α `notin` L ->
       {{ Γ ⨟ (α :: Δ) ⊢ₚₛ (open_pskl_wrt_pskl P (pskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}d
| d_wf_pskl__hole : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ₚₛ pskl_hole }}d
| d_wf_pskl__tophole : forall Γ Δ P,
    (* Paper [⫯.P] rule: [Δ] is cleared in the PREMISE (matching [Γ\Δ] since the
       ∀-vars are exactly [Δ]); the conclusion holds under an ARBITRARY [Δ]. *)
    guarded_pskl P ->
    {{ Γ ⨟ nil ⊢ₚₛ P }}d ->
    {{ Γ ⨟ Δ ⊢ₚₛ (pskl_tophole P) }}d
where "{{ Γ ⨟ Δ ⊢ₚₛ P }}d" := (d_wf_pskl Γ Δ P) : frost_d_scope.

Inductive d_wf_uskl : list (atom * dbind) -> list atom -> uskl -> Prop :=
| d_wf_uskl__unit : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ᵤₛ uskl_unit }}d
| d_wf_uskl__var : forall Γ Δ α,
    List.In α Δ \/ binds α dbind_tvar Γ ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_var_f α) }}d
| d_wf_uskl__arrow : forall Γ Δ R1 R2,
    {{ Γ ⨟ Δ ⊢ᵤₛ R1 }}d ->
    {{ Γ ⨟ Δ ⊢ᵤₛ R2 }}d ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_arrow R1 R2) }}d
| d_wf_uskl__all_syn : forall L Γ Δ R,
    (forall α, α `notin` L ->
       {{ Γ ⨟ (α :: Δ) ⊢ᵤₛ
         (open_uskl_wrt_uskl R (uskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_all_syn R) }}d
| d_wf_uskl__all_tag : forall L Γ Δ ε R,
    (forall α, α `notin` L ->
       {{ Γ ⨟ (α :: Δ) ⊢ᵤₛ
         (open_uskl_wrt_uskl R (uskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_all_tag ε R) }}d
| d_wf_uskl__hole : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ᵤₛ uskl_hole }}d
| d_wf_uskl__tophole : forall Γ Δ R,
    guarded_uskl R ->
    {{ Γ ⨟ nil ⊢ᵤₛ R }}d ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_tophole R) }}d
| d_wf_uskl__holeg : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ᵤₛ uskl_holeg }}d
| d_wf_uskl__topholeg : forall Γ Δ R,
    guarded_uskl R ->
    {{ Γ ⨟ nil ⊢ᵤₛ R }}d ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_topholeg R) }}d
where "{{ Γ ⨟ Δ ⊢ᵤₛ R }}d" := (d_wf_uskl Γ Δ R) : frost_d_scope.

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
| d_tags__var : forall Ψ α,
    Ψ [=] empty ->
    d_tags Ψ (utyp_var_f α)
| d_tags__arrow : forall Ψ Ψ1 Ψ2 C1 C2,
    d_tags Ψ1 C1 ->
    d_tags Ψ2 C2 ->
    Ψ1 ∩ Ψ2 [=] empty ->         (* paper ⊎ : disjoint set union *)
    Ψ [=] Ψ1 `union` Ψ2 ->
    d_tags Ψ (utyp_arrow C1 C2)
| d_tags__all_tag : forall L Ψ Ψ0 ε C,
    (forall α, α `notin` L ->
       d_tags Ψ0 (open_utyp_wrt_utyp C (utyp_var_f α))) ->
    ε `notin` Ψ0 ->
    Ψ [=] add ε Ψ0 ->
    d_tags Ψ (utyp_all_tag ε C).

(** Skeleton analog [tags{Ψ}{ψ}] (declarative.tex:1822).  Defined EXACTLY on
    the paper's decorated-skeleton grammar
    [ψ ::= 1 | α | ψ→ψ | ∀^ε α.ψ | HoleG | TopHoleG.ψ] (declarative.tex:1796):
    every quantifier is tagged; the only ghosts are the DOTTED ones.  A [HoleG]
    carries no tags; a dotted universal ghost [TopHoleG.ψ] carries exactly its
    body's tags (no ε of its own — unlike [all_tag]).  Plain [hole]/[tophole]
    and the untagged [all_syn] are NOT in ψ and have no case here. *)
Inductive d_tags_skl : atoms -> uskl -> Prop :=
| d_tags_skl__unit : forall Ψ, Ψ [=] empty -> d_tags_skl Ψ uskl_unit
| d_tags_skl__var : forall Ψ α, Ψ [=] empty -> d_tags_skl Ψ (uskl_var_f α)
| d_tags_skl__arrow : forall Ψ Ψ1 Ψ2 R1 R2,
    d_tags_skl Ψ1 R1 ->
    d_tags_skl Ψ2 R2 ->
    Ψ1 ∩ Ψ2 [=] empty ->         (* paper ⊎ : disjoint set union *)
    Ψ [=] Ψ1 `union` Ψ2 ->
    d_tags_skl Ψ (uskl_arrow R1 R2)
| d_tags_skl__all_tag : forall L Ψ Ψ0 ε R,
    (forall α, α `notin` L ->
       d_tags_skl Ψ0 (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    ε `notin` Ψ0 ->
    Ψ [=] add ε Ψ0 ->
    d_tags_skl Ψ (uskl_all_tag ε R)
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
    {{ Ψ ⨟ Γ ⊢ utyp_unit ∼ btyp_unit }}d
| d_consis__var : forall Ψ Γ α,
    binds α dbind_tvar Γ ->
    Ψ [=] empty ->
    {{ Ψ ⨟ Γ ⊢ (utyp_var_f α) ∼ (btyp_var_f α) }}d
| d_consis__arrow : forall Ψ Ψ1 Ψ2 Γ C1 C2 B1 B2,
    (* Paper [Arrow]: the tag context is the SET UNION [Ψ₁,Ψ₂]
       (declarative.tex:967, with Ψ a set), not a disjoint union — so we
       neither require nor record disjointness.  This faithfulness is what
       makes consistency transitivity (B.2) provable: composing two
       derivations may legitimately reuse a tag, which a set absorbs. *)
    {{ Ψ1 ⨟ Γ ⊢ C1 ∼ B1 }}d ->
    {{ Ψ2 ⨟ Γ ⊢ C2 ∼ B2 }}d ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Γ ⊢ (utyp_arrow C1 C2) ∼ (btyp_arrow B1 B2) }}d
| d_consis__forall_inh_tagged : forall L Ψ Ψ0 Γ ε C B,
    (* Paper [ForallInh] with β1=ε: output is [Ψ,ε] = Ψ ∪ {ε}, the
       idempotent set union (declarative.tex:950) — no freshness side
       condition ([add] on a set is idempotent). *)
    (forall α, α `notin` L ->
       {{ Ψ0 ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f α)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    Ψ [=] add ε Ψ0 ->
    {{ Ψ ⨟ Γ ⊢ (utyp_all_tag ε C) ∼ (btyp_all_inh B) }}d
| d_consis__forall_inh_untagged : forall L Ψ Γ C B,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f α)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ (utyp_all_syn C) ∼ (btyp_all_inh B) }}d
| d_consis__forall_syn_tagged : forall L Ψ Γ ε C B,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f α)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ (utyp_all_tag ε C) ∼ (btyp_all_syn B) }}d
| d_consis__forall_syn : forall L Ψ Γ C B,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f α)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ (utyp_all_syn C) ∼ (btyp_all_syn B) }}d
where "{{ Ψ ⨟ Γ ⊢ C ∼ B }}d" := (d_consis Ψ Γ C B) : frost_d_scope.

(* Check fully passed *)
Inductive d_sub : mode -> atoms -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_sub__infer : forall Ψ Γ C B,
    {{ empty ⨟ Γ ⊢ C ∼ B }}d ->
    is_styp B ->
    Ψ [=] empty ->
    {{ Ψ ⨟ Γ ⊢[ mode_ti ] C ⩽ B }}d
| d_sub__check : forall Ψ Γ C B,
    guarded_utyp C ->
    guarded_btyp B ->
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
    is_ityp B ->
    {{ Ψ ⨟ Γ ⊢[ mode_tc ] C ⩽ B }}d
| d_sub__forall_r : forall L Ψ Γ C B,
    is_ityp (btyp_all_inh B) ->
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢[ mode_tc ] C ⩽
         (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢[ mode_tc ] C ⩽ (btyp_all_inh B) }}d
(* Todo: rename d_sub__arg to d_sub__arrow *)
| d_sub__arg : forall Ψ Ψ1 Ψ2 Γ m C1 C2 B1 B2,
    {{ Ψ1 ⨟ Γ ⊢ C1 ∼ B1 }}d ->
    {{ Ψ2 ⨟ Γ ⊢[ m ] C2 ⩽ B2 }}d ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Γ ⊢[ mode_fn m ] (utyp_arrow C1 C2) ⩽ (btyp_arrow B1 B2) }}d
| d_sub__forall_l_tagged : forall Ψ Ψ' Γ m ε C ph B,
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->      (* Ψ' fresh w.r.t. the outer tags … *)
    Ψ' ∩ (ftag_in_utyp (utyp_all_tag ε C)) [=] empty ->
                             (* … and w.r.t. the SUBJECT's own tags.  The
                                paper's [Ψ' fresh] is GLOBAL: the line above
                                alone dies at Arrow, which splits the tag
                                context but not the subject, and
                                [lemma:precision-substitution] is FALSE over
                                such derivations.  docs/PAPER-GAPS.md *)
    d_tags Ψ' ph ->                  (* tags{Ψ'}{φ} : Ψ' is exactly φ's tags *)
    {{ Γ ⊢ᵤ ph }}d ->                       (* Γ ⊢ φ : well-scopedness half (WT: no Ψ') *)
    is_ttyp ph ->
    {{ (Ψ `union` Ψ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⩽ B }}d ->
    {{ Ψ ⨟ Γ ⊢[ m ] (utyp_all_tag ε C) ⩽ B }}d
| d_sub__forall_l_untagged : forall Ψ Ψ' Γ m C ph B,
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_utyp (utyp_all_syn C)) [=] empty ->  (* GLOBAL, as above *)
    d_tags Ψ' ph ->
    {{ Γ ⊢ᵤ ph }}d ->
    is_ttyp ph ->
    {{ (Ψ `union` Ψ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⩽ B }}d ->
    {{ Ψ ⨟ Γ ⊢[ m ] (utyp_all_syn C) ⩽ B }}d
where "{{ Ψ ⨟ Γ ⊢[ M ] C ⩽ B }}d" := (d_sub M Ψ Γ C B) : frost_d_scope.

Reserved Notation "{{ Γ ⊢ A ≤ B }}d"
  (at level 0, A at level 74, B at level 74,
   format "'{{'  Γ  ⊢  A  ≤  B  '}}d'").
Inductive d_shallow_sub : list (atom * dbind) -> ptyp -> ptyp -> Prop :=
| d_shallow_sub__refl : forall Γ A,
    {{ Γ ⊢ₚ A }}d ->
    {{ Γ ⊢ A ≤ A }}d
| d_shallow_sub__forall_r : forall L Γ A1 A2,
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ A1 ≤ (open_ptyp_wrt_ptyp A2 (ptyp_var_f α)) }}d) ->
    {{ Γ ⊢ A1 ≤ (ptyp_all A2) }}d
| d_shallow_sub__forall_l : forall Γ A1 A2 I,
    mono_ptyp I ->
    {{ Γ ⊢ₚ I }}d ->
    {{ Γ ⊢ (open_ptyp_wrt_ptyp A1 I) ≤ A2 }}d ->
    {{ Γ ⊢ (ptyp_all A1) ≤ A2 }}d
where "{{ Γ ⊢ A ≤ B }}d" := (d_shallow_sub Γ A B) : frost_d_scope.

(* ===================================================================== *)
(*  Skeleton refinement, consistency, and subtyping                       *)
(* ===================================================================== *)

(* Check mostly passed. 
    LHS are guaranteed to be all inh 
    some difference with the paper's "Growing both Γ and Δ version", but should be equivalent *)
(* Todo: we should not use P for RHS in all the rules, P is reserverd for pskl, but RHS is also a bskl here *)
Inductive d_refine_syn : list (atom * dbind) -> list atom -> bskl -> bskl -> Prop :=
| d_refine_syn__unit : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ᵣ bskl_unit ⊳ bskl_unit }}d
| d_refine_syn__var : forall Γ Δ α,
    (* Paper: [Γ,Δ ∋ α] — an inherited (Δ) or context (Γ) tvar. *)
    List.In α Δ \/ binds α dbind_tvar Γ ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ (bskl_var_f α) }}d
| d_refine_syn__arrow : forall Γ Δ Q1 Q2 P1 P2,
    {{ Γ ⨟ Δ ⊢ᵣ Q1 ⊳ P1 }}d ->
    {{ Γ ⨟ Δ ⊢ᵣ Q2 ⊳ P2 }}d ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow P1 P2) }}d
| d_refine_syn__all : forall L Γ Δ Q P,
    (* Inherited ∀: the bound var joins [Δ]. *)
    (forall α, α `notin` L ->
       {{ Γ ⨟ (α :: Δ) ⊢ᵣ
         (open_bskl_wrt_bskl Q (bskl_var_f α)) ⊳
         (open_bskl_wrt_bskl P (bskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_all_inh Q) ⊳ (bskl_all_inh P) }}d
| d_refine_syn__hole : forall Γ Δ P,
    (* [□ ⤳ syn{Q}]: the fill is well-formed under [Γ] alone (synthesised vars
       are in [Γ]); [Δ] is cleared so inherited vars cannot fill ghosts. *)
    {{ Γ ⨟ nil ⊢ₚₛ P }}d ->
    {{ Γ ⨟ Δ ⊢ᵣ bskl_hole ⊳ (pskl_to_bskl_syn P) }}d
| d_refine_syn__tophole_remove : forall Γ Δ Q P,
    (* [⫯.inh{P} ⤳ bid{Q}]: remove the universal ghost; keep [Δ]. *)
    {{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ P }}d
| d_refine_syn__tophole_fill : forall L Γ Δ Q P,
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⨟ Δ ⊢ᵣ
         (bskl_tophole Q) ⊳ (open_bskl_wrt_bskl P (bskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_all_syn P) }}d
| d_refine_syn__tophole_keep : forall Γ Δ Q P,
    guarded_bskl P ->
    {{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_tophole P) }}d
where "{{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d" := (d_refine_syn Γ Δ Q P) : frost_d_scope.

(* Check passed *)
(** ⭐ THE UNCOLOURED DECLARATIVE REFINEMENT [{{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}d]
    (declarative.tex:1516 — *"As with well-formedness, we define the refinement
    of uncoloured skeletons by ignoring colours in the above rules"), which is
    the sort the paper's own presupposition on skeleton CONSISTENCY is stated
    at: *"skeleton consistency … requires well-formedness of syn{S} and bid{P}
    under Γ as well as the refinement judgement Γ ⊢ ⌊S⌋ ⊳ P"*
    (declarative.tex:2074).

    ⚙ [d_refine_syn] above is the COLOURED one, over [bskl]; it cannot serve,
    because the presupposition erases both sides ([uskl_to_pskl] on the left,
    [bskl_to_pskl] on the right) and the two colourings need not agree at a ∀.
    The [ad] layer has had the uncoloured version all along
    ([ad_refine_pskl], algo_decl/def_decl_algo.v); this is its
    flexible-free twin, and prop_conserv.v §5 relates them.

    ⚠️ [Δ] tracks the type variables bound IN THE SUBJECT, and
    [d_refine_pskl__hole] clears it: that is the paper's "for every ghost in P,
    it cannot represent skeletons that use type variables bound in P"
    (declarative.tex:1433).  [__tophole_fill] extends Γ instead — a UNIVERSAL
    ghost is allowed to capture, which is what generalisation means. *)
Inductive d_refine_pskl :
  list (atom * dbind) -> list atom -> pskl -> pskl -> Prop :=
| d_refine_pskl__unit : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ᵣₚ pskl_unit ⊳ pskl_unit }}d
| d_refine_pskl__var : forall Γ Δ α,
    List.In α Δ \/ binds α dbind_tvar Γ ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ (pskl_var_f α) }}d
| d_refine_pskl__arrow : forall Γ Δ P1 P2 Q1 Q2,
    {{ Γ ⨟ Δ ⊢ᵣₚ P1 ⊳ Q1 }}d ->
    {{ Γ ⨟ Δ ⊢ᵣₚ P2 ⊳ Q2 }}d ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_arrow P1 P2) ⊳ (pskl_arrow Q1 Q2) }}d
| d_refine_pskl__all : forall L Γ Δ P Q,
    (forall α, α `notin` L ->
       {{ Γ ⨟ (α :: Δ) ⊢ᵣₚ
         (open_pskl_wrt_pskl P (pskl_var_f α)) ⊳
         (open_pskl_wrt_pskl Q (pskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_all_syn P) ⊳ (pskl_all_syn Q) }}d
| d_refine_pskl__hole : forall Γ Δ Q,
    (* Δ CLEARED — the no-capture discipline *)
    {{ Γ ⨟ nil ⊢ₚₛ Q }}d ->
    {{ Γ ⨟ Δ ⊢ᵣₚ pskl_hole ⊳ Q }}d
| d_refine_pskl__tophole_remove : forall Γ Δ P Q,
    {{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}d ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_tophole P) ⊳ Q }}d
| d_refine_pskl__tophole_fill : forall L Γ Δ P Q,
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⨟ Δ ⊢ᵣₚ
         (pskl_tophole P) ⊳ (open_pskl_wrt_pskl Q (pskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_tophole P) ⊳ (pskl_all_syn Q) }}d
| d_refine_pskl__tophole_keep : forall Γ Δ P Q,
    guarded_pskl Q ->
    {{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}d ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_tophole P) ⊳ (pskl_tophole Q) }}d
where "{{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}d" := (d_refine_pskl Γ Δ P Q) : frost_d_scope.

Inductive d_pat_consis : atoms -> list (atom * dbind) -> uskl -> bskl -> Prop :=
| d_pat_consis__unit : forall Ψ Γ,
    Ψ [=] empty ->
    {{ Ψ ⨟ Γ ⊢ˢ uskl_unit ∼ bskl_unit }}d
| d_pat_consis__var : forall Ψ Γ α,
    Ψ [=] empty ->
    binds α dbind_tvar Γ ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_var_f α) ∼ (bskl_var_f α) }}d
| d_pat_consis__arrow : forall Ψ Ψ1 Ψ2 Γ R1 R2 Q1 Q2,
    {{ Ψ1 ⨟ Γ ⊢ˢ R1 ∼ Q1 }}d ->
    {{ Ψ2 ⨟ Γ ⊢ˢ R2 ∼ Q2 }}d ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2) }}d
| d_pat_consis__forall_inh_tagged : forall L Ψ Ψ0 Γ ε R Q,
    (forall α, α `notin` L ->
       {{ Ψ0 ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}d) ->
    Ψ [=] add ε Ψ0 ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_all_tag ε R) ∼ (bskl_all_inh Q) }}d
| d_pat_consis__forall_inh_untagged : forall L Ψ Γ R Q,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_all_syn R) ∼ (bskl_all_inh Q) }}d
| d_pat_consis__forall_syn_tagged : forall L Ψ Γ ε R Q,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_all_tag ε R) ∼ (bskl_all_syn Q) }}d
| d_pat_consis__forall_syn : forall L Ψ Γ R Q,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_all_syn R) ∼ (bskl_all_syn Q) }}d
| d_pat_consis__ghostg : forall Ψ Γ,
    Ψ [=] empty ->
    (* Paper [GhostG] (declarative.tex eqlab): a ghost hole [HoleG] is
       consistent with a plain [Hole]. *)
    {{ Ψ ⨟ Γ ⊢ˢ uskl_holeg ∼ bskl_hole }}d
| d_pat_consis__topholeg : forall Ψ Γ R Q,
    (* Paper [UnivGhostG] (dotted): [TopHoleG.R ~ TopHole.P] from [R ~ P],
       tags UNCHANGED — [typconsis[Ψ]] from [typconsis[Ψ]] (no added tag,
       unlike the old tagged version). *)
    {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_topholeg R) ∼ (bskl_tophole Q) }}d
| d_pat_consis__hole : forall Ψ Γ P,
    Ψ [=] empty ->
    d_wf_pskl Γ nil P ->
    {{ Ψ ⨟ Γ ⊢ˢ uskl_hole ∼ (pskl_to_bskl_inh P) }}d
| d_pat_consis__tophole : forall Ψ Γ R Q,
    (* Paper [UnivGhost]: TopHole ∼ TopHole. *)
    {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_tophole R) ∼ (bskl_tophole Q) }}d
| d_pat_consis__tophole_inh : forall L Ψ Γ R Q,
    (* Paper [UnivGhost1] (was missing, WT): the RHS TopHole can produce
       an inherited quantifier.  LHS [TopHole.R] is unchanged; the RHS
       body [Q] is checked under a fresh [α]. *)
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢ˢ
         (uskl_tophole R) ∼ (open_bskl_wrt_bskl Q (bskl_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_tophole R) ∼ (bskl_all_inh Q) }}d
| d_pat_consis__tophole_drop : forall Ψ Γ R Q,
    (* Paper [UnivGhost2] (was missing, WT): the LHS TopHole can be
       dropped against a plain inherited RHS. *)
    {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_tophole R) ∼ Q }}d
where "{{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d" := (d_pat_consis Ψ Γ R Q) : frost_d_scope.

Inductive d_pat_sub : mode -> atoms -> list (atom * dbind) -> uskl -> bskl -> Prop :=
| d_pat_sub__infer : forall Ψ Γ R Q,
    (* Paper [Infer]: synthesise by consistency, dropping tags. *)
    Ψ [=] empty ->
    {{ empty ⨟ Γ ⊢ˢ R ∼ Q }}d ->
    is_sskl Q ->
    (* ⭐ [paper-gap] THE PRESUPPOSITION OF SKELETON CONSISTENCY, transcribed.
       declarative.tex:2074 — *"skeleton consistency requires well-formedness of
       syn{S} and bid{P} under Γ AS WELL AS the refinement judgement
       Γ ⊢ ⌊S⌋ ⊳ P"*.  It is NOT derivable from the consistency rules: they put
       a ∀-bound rigid into Γ, refinement puts it into Δ and forbids a ghost's
       fill to mention Δ, so the rules alone admit the CAPTURE ∀X.◇ ∼ ∀ˢX.X
       that refinement rejects (cex/cex_ad_pat_join_not_leaf_valid.v).  The
       [ad] side has carried it since 2026-08-07 ([ad_pat_sub_gv]); this is the
       declarative twin, and until it was added the two systems disagreed
       (cex/cex_d_pat_bridges_false.v).  docs/ghost-capture.tex. *)
    {{ Γ ⨟ nil ⊢ᵣₚ (uskl_to_pskl R) ⊳ (bskl_to_pskl Q) }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ mode_ti ] R ⩽ Q }}d
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
    {{ empty ⨟ Γ ⊢ˢ R ∼ Q }}d ->
    (* the presupposition, at the STRIPPED counterpart [Q] — the [∀◇] the rule
       adds is the conclusion's, not the consistency premise's *)
    {{ Γ ⨟ nil ⊢ᵣₚ (uskl_to_pskl R) ⊳ (bskl_to_pskl Q) }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ mode_tc ] R ⩽ (bskl_tophole Q) }}d
| d_pat_sub__arg : forall Ψ Ψ1 Ψ2 Γ m R1 R2 Q1 Q2,
    (* Paper [Arrow]: set-union tag context. *)
    {{ Ψ1 ⨟ Γ ⊢ˢ R1 ∼ Q1 }}d ->
    (* the DOMAIN premise is a consistency judgement, so it carries the
       presupposition too *)
    {{ Γ ⨟ nil ⊢ᵣₚ (uskl_to_pskl R1) ⊳ (bskl_to_pskl Q1) }}d ->
    {{ Ψ2 ⨟ Γ ⊢ˢ[ m ] R2 ⩽ Q2 }}d ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Γ ⊢ˢ[ mode_fn m ] (uskl_arrow R1 R2) ⩽ (bskl_arrow Q1 Q2) }}d
| d_pat_sub__forall_l_tagged : forall Ψ Ψ' Γ m ε R psi Q,
    (* Paper [ForallL] (tagged head).  [Ψ' fresh] = [list_disjoint];
       well-scopedness is [{{ Γ ⨟ nil ⊢ᵤₛ ψ }}d] (R1: scope, not tags). *)
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_tag ε R)) [=] empty ->  (* GLOBAL freshness *)
    d_tags_skl Ψ' psi ->             (* tags{Ψ'}{ψ} : skeleton-tag relation *)
    {{ Γ ⨟ nil ⊢ᵤₛ psi }}d ->
    is_tskl psi ->
    {{ (Ψ `union` Ψ') ⨟ Γ ⊢ˢ[ m ] (open_uskl_wrt_uskl R psi) ⩽ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] (uskl_all_tag ε R) ⩽ Q }}d
| d_pat_sub__forall_l_untagged : forall Ψ Ψ' Γ m R psi Q,
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_syn R)) [=] empty ->     (* GLOBAL freshness *)
    d_tags_skl Ψ' psi ->
    {{ Γ ⨟ nil ⊢ᵤₛ psi }}d ->
    is_tskl psi ->
    {{ (Ψ `union` Ψ') ⨟ Γ ⊢ˢ[ m ] (open_uskl_wrt_uskl R psi) ⩽ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] (uskl_all_syn R) ⩽ Q }}d
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
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] uskl_hole ⩽ (pskl_to_bskl_inh P) }}d
| d_pat_sub__univ_ghost_l : forall m Ψ Γ R Q,
    (* Paper [UnivGhostL]: drop a [TopHole] on the LHS (any [M ≠ TI]). *)
    m <> mode_ti ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] R ⩽ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] (uskl_tophole R) ⩽ Q }}d
| d_pat_sub__ghostg : forall m Ψ Γ,
    (* Paper [GhostG]: a ghost hole [HoleG] is below a plain [Hole].
       [mod_comp_sk … m] ([skmod{SK}]) excludes the ill-moded [fn] case (a
       [bskl_hole] is not an arrow), keeping the output mode-compatible. *)
    Ψ [=] empty ->
    mod_comp_sk bskl_hole m ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] uskl_holeg ⩽ bskl_hole }}d
| d_pat_sub__univ_ghost_lg : forall m Ψ Γ R Q,
    (* Paper [UnivGhostLG] (dotted): drop a dotted ghost [TopHoleG] on the
       LHS (any [M ≠ TI]).  [Ψ] unchanged — [patsub[M][Ψ]] from
       [patsub[M][Ψ]] (declarative.tex UnivGhostLG). *)
    m <> mode_ti ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] R ⩽ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] (uskl_topholeg R) ⩽ Q }}d
where "{{ Ψ ⨟ Γ ⊢ˢ[ M ] R ⩽ Q }}d" := (d_pat_sub M Ψ Γ R Q) : frost_d_scope.

(* ===================================================================== *)
(*  Typing and pattern inference                                          *)
(* ===================================================================== *)

Reserved Notation "{{ Γ ⊢[ M ] e ⦂ A }}d"
  (at level 0, M at level 0, e at level 74, A at level 74,
   format "'{{'  Γ  ⊢[  M  ]  e  ⦂  A  '}}d'").
Reserved Notation "{{ Γ ⊢ˢ[ M ] e ⦂ P }}d"
  (at level 0, M at level 0, e at level 74, P at level 74,
   format "'{{'  Γ  ⊢ˢ[  M  ]  e  ⦂  P  '}}d'").
Reserved Notation "{{ Γ ⊢ˢᵈ[ M ] e ⦂ A }}d"
  (at level 0, M at level 0, e at level 74, A at level 74,
   format "'{{'  Γ  ⊢ˢᵈ[  M  ]  e  ⦂  A  '}}d'").

(** Skeleton inference [d_pat] ([⦂]) is SELF-CONTAINED — no [d_typing] premises
    (the paper's P-App infers the function, declarative.tex:1560) — so it is
    defined standalone, BEFORE [d_typing], rather than mutually. *)
(* Check fully passed *)
(* Todo : check if d_pat has skmod_sk satisfied, and i think we didn't even have skmod_sk defined *)
Inductive d_pat : mode -> list (atom * dbind) -> exp -> bskl -> Prop :=
(* Paper P-Unit/P-Var/P-Anno (declarative.tex:1634-1653): the skeleton
   subtyping judgement is EMBEDDED in the three base rules at every mode —
   there is no standalone P-Sub rule and no base-term restriction. *)
| d_pat__unit : forall Γ m Q,
    (* ⭐ [paper-gap] THE COUNTERPART'S WF, the paper's OTHER presupposition
       for skeleton inference: declarative.tex:1595 — *"we require
       well-formedness of M and bid{P} under Γ … as well as the compatibility
       between bidirectional skeletons and modes"* (WF-SIDE-CONDITIONS.md §4).
       [ad_pat] has carried it on these three rows since 2026-08-07; it is on
       the declarative twin from 2026-08-11 so the two agree rule for rule.
       ⚠️ It is NOT derivable from the refinement premise above: refinement's
       target wf would need the Γ↔Δ exchange, which the [⫯] row breaks (its
       premise clears Δ), and the paper says so itself — *"it's fine to keep Δ
       since we already required well-formedness separately"*
       (declarative.tex:1502). *)
    {{ Γ ⨟ nil ⊢ₚₛ (bskl_to_pskl Q) }}d ->
    {{ empty ⨟ Γ ⊢ˢ[ m ] uskl_unit ⩽ Q }}d ->
    {{ Γ ⊢ˢ[ m ] exp_unit ⦂ Q }}d
| d_pat__var : forall Γ m x (P : pskl) d Q,
    binds x d Γ ->
    dbind_to_pskl d = Some P ->
    {{ Γ ⨟ nil ⊢ₚₛ (bskl_to_pskl Q) }}d ->
    {{ empty ⨟ Γ ⊢ˢ[ m ] (bskl_to_uskl (pskl_to_bskl_syn P)) ⩽ Q }}d ->
    {{ Γ ⊢ˢ[ m ] (exp_var_f x) ⦂ Q }}d
| d_pat__anno : forall Γ m e (A : ptyp) Q,
    {{ Γ ⊢ₚ A }}d ->
    {{ Γ ⨟ nil ⊢ₚₛ (bskl_to_pskl Q) }}d ->
    {{ empty ⨟ Γ ⊢ˢ[ m ] (bskl_to_uskl (pskl_to_bskl_syn (ptyp_to_pskl A))) ⩽ Q }}d ->
    {{ Γ ⊢ˢ[ m ] (exp_anno e A) ⦂ Q }}d
| d_pat__freeze : forall Γ e P,
    {{ Γ ⊢ˢ[ mode_ti ] e ⦂ (pskl_to_bskl_syn P) }}d ->
    {{ Γ ⊢ˢ[ mode_tc ] (exp_freeze e) ⦂ (pskl_to_bskl_syn P) }}d
| d_pat__abs : forall L Γ m e P Q,
    (* [mod_comp_sk … m] is the paper's [skmod{SK}] colour/mode discipline on the
       inferred arrow, mirroring [d_typing__abs]'s [mod_comp_ty]: at [ti] it forces
       [is_sskl], excluding a POLY inherited domain (ill-moded); at [FN m'] it
       threads [mod_comp_sk Q m'] for the body.  [m ≠ tc] keeps this disjoint from
       [abs_check] (which owns the checking mode). *)
    m <> mode_tc ->
    {{ Γ ⨟ nil ⊢ₚₛ P }}d ->
    mod_comp_sk (bskl_arrow (pskl_to_bskl_inh P) Q) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_skl P) ++ Γ) ⊢ˢ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q }}d) ->
    {{ Γ ⊢ˢ[ m ] (exp_abs e) ⦂ (bskl_arrow (pskl_to_bskl_inh P) Q) }}d
| d_pat__abs_anno : forall L Γ m e (A : ptyp) (B : btyp) Q,
    (* The arrow-arg skeleton [Sarg] is bidirectional, [bskl_to_pskl Sarg]
       the annotation's pattern.  [mod_comp_sk … m] as in [abs]. *)
    m <> mode_tc ->
    {{ Γ ⊢ₚ A }}d ->
    btyp_to_ptyp B = A ->
    mod_comp_sk (bskl_arrow (btyp_to_bskl B) Q) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q }}d) ->
    {{ Γ ⊢ˢ[ m ] (exp_abs_anno A e) ⦂ (bskl_arrow (btyp_to_bskl B) Q) }}d
| d_pat__app : forall Γ m e1 e2 P (Q1 Q2 : bskl),
    (* Paper P-App (declarative.tex:1560): the function [e1] is SKELETON-
       INFERRED ([⦂]) in [FN] mode, not typed — d_pat is self-contained
       skeleton inference.  [P'] is the fill output (the arg skeleton). *)
    {{ Γ ⊢ˢ[ mode_tc ] e2 ⦂ (pskl_to_bskl_syn P) }}d ->
    {{ Γ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Q1 }}d ->
    {{ Γ ⊢ˢ[ mode_fn m ] e1 ⦂ (bskl_arrow Q1 Q2) }}d ->
    {{ Γ ⊢ˢ[ m ] (exp_app e1 e2) ⦂ Q2 }}d
| d_pat__abs_check : forall L Γ e P,
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_skl pskl_hole) ++ Γ) ⊢ˢ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ (pskl_to_bskl_syn P) }}d) ->
    {{ Γ ⊢ˢ[ mode_tc ] (exp_abs e) ⦂ (bskl_tophole (bskl_arrow bskl_hole (pskl_to_bskl_syn P))) }}d
| d_pat__abs_anno_check : forall L Γ e A P,
    {{ Γ ⊢ₚ A }}d ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ (pskl_to_bskl_syn P) }}d) ->
    {{ Γ ⊢ˢ[ mode_tc ] (exp_abs_anno A e) ⦂ (bskl_tophole (bskl_arrow (btyp_to_bskl (ptyp_to_btyp_syn A)) (pskl_to_bskl_syn P))) }}d
where "{{ Γ ⊢ˢ[ M ] e ⦂ P }}d" := (d_pat M Γ e P) : frost_d_scope.

(** Typing [d_typing] ([⦂]) uses [d_pat] in [App] (it infers the argument's
    skeleton), so it is defined after [d_pat]. *)
(* Check fully passed *)
Inductive d_typing : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
| d_typing__unit : forall Γ,
    {{ Γ ⊢[ mode_ti ] exp_unit ⦂ btyp_unit }}d
| d_typing__var : forall Γ x A,
    binds x (dbind_typ A) Γ ->
    {{ Γ ⊢[ mode_ti ] (exp_var_f x) ⦂ (ptyp_to_btyp_syn A) }}d
| d_typing__anno : forall Γ e A,
    {{ Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) }}d ->
    {{ Γ ⊢[ mode_ti ] (exp_anno e A) ⦂ (ptyp_to_btyp_syn A) }}d
| d_typing__sub : forall Γ m e A B,
    (* Paper [Sub] (declarative.tex): applies to ANY term [M] — the base-term
       restriction was removed (commit "Removed base terms"); general
       subsumption is admissible, so the unrestricted rule is equivalent. *)
    (* Todo: not urgent, replace A with btyp B1 and use is_styp B1 *)
    {{ Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) }}d ->
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
    {{ Γ ⊢[ m ] e ⦂ B }}d
| d_typing__freeze : forall Γ e A,
    (* Paper [Freeze]: TI [syn{A}] ⇒ TC [inh{A}].  The premise IS a synthesised
       colouring [syn A] and the result is repainted to [inh A]; keeping an
       arbitrary [B] would (i) accept a non-synthesised premise and (ii) let a
       synthesised colour be used directly in check mode. *)
    {{ Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) }}d ->
    {{ Γ ⊢[ mode_tc ] (exp_freeze e) ⦂ (ptyp_to_btyp_inh A) }}d
| d_typing__forall : forall L Γ e A,
    is_value e ->
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢[ mode_tc ] e ⦂ (open_btyp_wrt_btyp (ptyp_to_btyp_inh A) (btyp_var_f α)) }}d) ->
    {{ Γ ⊢[ mode_tc ] e ⦂ (btyp_all_inh (ptyp_to_btyp_inh A)) }}d
| d_typing__abs : forall L Γ m e A B,
    (* Paper [Abs].  [mod_comp_ty … m] is the paper's implicit [skmod{TY}]
       colour/mode well-formedness on the conclusion: it excludes the ill-moded
       [ti] reading (whose result would have to be synthesised yet has an
       inherited domain) and forces the colour to match the mode. *)
    {{ Γ ⊢ₚ A }}d ->
    mod_comp_ty (btyp_arrow (ptyp_to_btyp_inh A) B) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}d) ->
    {{ Γ ⊢[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}d
| d_typing__abs_anno : forall L Γ m e A B1 B2,
    (* The arrow-arg is an arbitrary bidirectional [Barg] whose erasure
       [btyp_to_ptyp] is the annotation [A].  Paper [AbsAnno].  [mod_comp_ty … m]
       (paper's [skmod{TY}]) colours the domain by the mode: at [TC] it forces
       [is_ityp B1], i.e. [B1 = inh A]. *)
    {{ Γ ⊢ₚ A }}d ->
    btyp_to_ptyp B1 = A ->
    mod_comp_ty (btyp_arrow B1 B2) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B2 }}d) ->
    {{ Γ ⊢[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow B1 B2) }}d
| d_typing__app : forall Γ m e1 e2 P B1 B2,
    (* Paper [App]: ONE domain [inh A] (the refinement output) is used by both
       the refinement and the function premise; the argument is checked at the
       same [inh A].  (Previously the function domain was an arbitrary [Barg]
       with erasure [A], not justified by the [inh A] refinement output.) *)
    {{ Γ ⊢ˢ[ mode_tc ] e2 ⦂ (pskl_to_bskl_syn P) }}d ->
    {{ Γ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B1) }}d ->
    {{ Γ ⊢[ mode_fn m ] e1 ⦂ (btyp_arrow B1 B2) }}d ->
    {{ Γ ⊢[ mode_tc ] e2 ⦂ (ptyp_to_btyp_inh (btyp_to_ptyp B1)) }}d ->
    {{ Γ ⊢[ m ] (exp_app e1 e2) ⦂ B2 }}d
where "{{ Γ ⊢[ M ] e ⦂ A }}d" := (d_typing M Γ e A) : frost_d_scope.

(* ===================================================================== *)
(*  Syntax-directed declarative typing  (paper Fig. syntax-directed)      *)
(* ===================================================================== *)

Inductive d_sd_typing : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
(* Paper [sdtylab{Unit}]/[sdtylab{Var}]/[sdtylab{Anno}]: the standalone
   [dtylab{Sub}] was removed and its subtyping premise is EMBEDDED into the
   three base rules (declarative.tex, "we incorporate Sub into the three base
   rules"), so the system is syntax-directed with no [is_base_term] predicate. *)
| d_sd_typing__unit : forall Γ m B,
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn ptyp_unit) ⩽ B }}d ->
    {{ Γ ⊢ˢᵈ[ m ] exp_unit ⦂ B }}d
| d_sd_typing__var : forall Γ m x A B,
    binds x (dbind_typ A) Γ ->
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
    {{ Γ ⊢ˢᵈ[ m ] (exp_var_f x) ⦂ B }}d
| d_sd_typing__anno : forall Γ m e A B,
    {{ Γ ⊢ˢᵈ[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) }}d ->
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
    {{ Γ ⊢ˢᵈ[ m ] (exp_anno e A) ⦂ B }}d
| d_sd_typing__freeze : forall Γ e A,
    (* Paper [Freeze]: TI [syn{A}] ⇒ TC [inh{A}]. *)
    {{ Γ ⊢ˢᵈ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) }}d ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] (exp_freeze e) ⦂ (ptyp_to_btyp_inh A) }}d
| d_sd_typing__abs_check_step : forall L Γ e B,
    is_ityp (btyp_all_inh B) ->
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ˢᵈ[ mode_tc ] (exp_abs e)
         ⦂ (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_all_inh B) }}d
| d_sd_typing__abs_check_base : forall L Γ e A B,
    {{ Γ ⊢ₚ A }}d ->
    is_ityp B ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢᵈ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}d) ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}d
(* Paper [sdtylab{AbsAnnoCheck}]: same fold for the annotated checked lambda. *)
| d_sd_typing__abs_anno_check_step : forall L Γ A e B,
    is_ityp (btyp_all_inh B) ->
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e)
         ⦂ (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_all_inh B) }}d
| d_sd_typing__abs_anno_check_base : forall L Γ e A B,
    (* Paper [AbsAnnoCheck]: inherited annotation domain [inh A] in check mode. *)
    {{ Γ ⊢ₚ A }}d ->
    is_ityp B ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢᵈ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}d) ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}d
| d_sd_typing__abs : forall L Γ m e A B,
    (* Paper [sdtylab{Abs}]: [M ≠ TC].  Same [mod_comp_ty] colour/mode discipline
       as [d_typing__abs] (so the equivalence transfers the premise directly). *)
    m <> mode_tc ->
    {{ Γ ⊢ₚ A }}d ->
    mod_comp_ty (btyp_arrow (ptyp_to_btyp_inh A) B) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢᵈ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}d) ->
    {{ Γ ⊢ˢᵈ[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}d
| d_sd_typing__abs_anno : forall L Γ m e A B1 B2,
    (* Paper [sdtylab{AbsAnno}]: [M ≠ TC]. *)
    m <> mode_tc ->
    {{ Γ ⊢ₚ A }}d ->
    btyp_to_ptyp B1 = A ->
    mod_comp_ty (btyp_arrow B1 B2) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢᵈ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B2 }}d) ->
    {{ Γ ⊢ˢᵈ[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow B1 B2) }}d
(* Paper [sdtylab{AbsCheck}]: the standalone [dtylab{Forall}] is FOLDED into
   the checked lambda rule.  [__abs_check_step] peels one inherited [∀] over
   the SAME lambda (this is [Forall] restricted to [λ]-values, self-recursive
   in [d_sd_typing] — no mutual block), and [__abs_check_base] is the [ᾱ = ·]
   arrow whose body checks.  Together they type [λx.M] at [∀ᾱ.(inh A → B)]. *)
| d_sd_typing__app : forall Γ m e1 e2 P B1 B2,
    (* Paper [App]: ONE domain [B1] used by both the refinement (its skeleton
       [btyp_to_bskl B1]) and the function premise; the argument is checked at
       the inherited colouring of the same domain. *)
    {{ Γ ⊢ˢ[ mode_tc ] e2 ⦂ (pskl_to_bskl_syn P) }}d ->
    {{ Γ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B1) }}d ->
    {{ Γ ⊢ˢᵈ[ (mode_fn m) ] e1 ⦂ (btyp_arrow B1 B2) }}d ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] e2 ⦂ (ptyp_to_btyp_inh (btyp_to_ptyp B1)) }}d ->
    {{ Γ ⊢ˢᵈ[ m ] (exp_app e1 e2) ⦂ B2 }}d
where "{{ Γ ⊢ˢᵈ[ M ] e ⦂ A }}d" := (d_sd_typing M Γ e A) : frost_d_scope.