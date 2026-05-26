(** Frost declarative typing metatheory: generalised relations in the
    current split syntax.

    The generalised left-hand side is a [gutyp], matching the paper's
    "generalised unresolved type" grammar: ordinary unresolved types
    extended with inherited forall while preserving ε-tagged forall. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.typing.prop_weakening.

Set Implicit Arguments.

Reserved Notation "Δ ⨟ Γ ⊨ᵍ G1 ≈ G2"
  (at level 75, Γ at level 75, G1 at level 74, G2 at level 74, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ᵍ[ M ] G ⊑ B"
  (at level 75, Γ at level 75, M at level 0, G at level 74, B at level 74,
   no associativity).
Reserved Notation "Γ ⊢ᵍ[ M ] e ⦂ B"
  (at level 100, M at level 0, e at level 75, B at level 75, no associativity).

Inductive d_consis_gen : list atom -> list (atom * dbind) -> gutyp -> gutyp -> Prop :=
| d_consis_gen__unit : forall Γ,
    nil ⨟ Γ ⊨ᵍ gutyp_unit ≈ gutyp_unit
| d_consis_gen__var : forall Γ X,
    binds X dbind_tvar Γ ->
    nil ⨟ Γ ⊨ᵍ (gutyp_var_f X) ≈ (gutyp_var_f X)
| d_consis_gen__arrow : forall Δ1 Δ2 Γ G1 G2 G1' G2',
    Δ1 ⨟ Γ ⊨ᵍ G1 ≈ G1' ->
    Δ2 ⨟ Γ ⊨ᵍ G2 ≈ G2' ->
    (* Paper [Arrow]: tag context is the set-union [Δ1 ∪ Δ2] (idempotent), so
       no [list_disjoint] — same set-semantics decision as non-gen
       [d_consis__arrow].  Disjoint-append was a too-strong artifact that
       blocks B.4 when a tag is reused across both arrow halves. *)
    (Δ1 ++ Δ2) ⨟ Γ ⊨ᵍ (gutyp_arrow G1 G2) ≈ (gutyp_arrow G1' G2')
| d_consis_gen__forall_tag_inh : forall L Δ Γ ε G1 G2,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ᵍ
         (open_gutyp_wrt_gutyp G1 (gutyp_var_f X)) ≈
         (open_gutyp_wrt_gutyp G2 (gutyp_var_f X))) ->
    (ε :: Δ) ⨟ Γ ⊨ᵍ (gutyp_all_etag ε G1) ≈ (gutyp_all_inh G2)
| d_consis_gen__forall_syn_inh : forall L Δ Γ ε G1 G2,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ᵍ
         (open_gutyp_wrt_gutyp G1 (gutyp_var_f X)) ≈
         (open_gutyp_wrt_gutyp G2 (gutyp_var_f X))) ->
    (ε :: Δ) ⨟ Γ ⊨ᵍ (gutyp_all_syn G1) ≈ (gutyp_all_inh G2)
| d_consis_gen__forall_tag_syn : forall L Δ Γ ε G1 G2,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ᵍ
         (open_gutyp_wrt_gutyp G1 (gutyp_var_f X)) ≈
         (open_gutyp_wrt_gutyp G2 (gutyp_var_f X))) ->
    Δ ⨟ Γ ⊨ᵍ (gutyp_all_etag ε G1) ≈ (gutyp_all_etag ε G2)
| d_consis_gen__forall_syn : forall L Δ Γ G1 G2,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ᵍ
         (open_gutyp_wrt_gutyp G1 (gutyp_var_f X)) ≈
         (open_gutyp_wrt_gutyp G2 (gutyp_var_f X))) ->
    Δ ⨟ Γ ⊨ᵍ (gutyp_all_syn G1) ≈ (gutyp_all_syn G2)
| d_consis_gen__forall_tag_syn_erasure : forall L Δ Γ ε G1 G2,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ᵍ
         (open_gutyp_wrt_gutyp G1 (gutyp_var_f X)) ≈
         (open_gutyp_wrt_gutyp G2 (gutyp_var_f X))) ->
    Δ ⨟ Γ ⊨ᵍ (gutyp_all_etag ε G1) ≈ (gutyp_all_syn G2)
| d_consis_gen__forall_inh : forall L Δ Γ G1 G2,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ᵍ
         (open_gutyp_wrt_gutyp G1 (gutyp_var_f X)) ≈
         (open_gutyp_wrt_gutyp G2 (gutyp_var_f X))) ->
    Δ ⨟ Γ ⊨ᵍ (gutyp_all_inh G1) ≈ (gutyp_all_inh G2)
where "Δ ⨟ Γ ⊨ᵍ B1 ≈ B2" := (d_consis_gen Δ Γ B1 B2) : type_scope.

Inductive d_sub_gen : mode -> list atom -> list (atom * dbind) -> gutyp -> btyp -> Prop :=
| d_sub_gen__infer_gen : forall Γ C B,
    (* I think we don't need the d_con *)
    is_syn B ->
    nil ⨟ Γ ⊨ C ≈ B ->
    nil ⨟ Γ ⊢ᵍ[ mode_ti ] (utyp_to_gutyp  C) ⊑ B
| d_sub_gen__check_gen : forall Δ Γ C B,
    guarded_utyp C ->
    is_inh B ->
    Δ ⨟ Γ ⊨ C ≈ B ->
    is_ityp B ->
    Δ ⨟ Γ ⊢ᵍ[ mode_tc ] (utyp_to_gutyp C) ⊑ B
| d_sub_gen__forall_r : forall L Δ Γ C B,
    is_inh (btyp_all_inh B) ->
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ᵍ[ mode_tc ]
         (utyp_to_gutyp (open_utyp_wrt_utyp C (utyp_var_f X)))
         ⊑ (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Δ ⨟ Γ ⊢ᵍ[ mode_tc ] (utyp_to_gutyp C) ⊑ (btyp_all_inh B)
| d_sub_gen__arg : forall Δ1 Δ2 Γ m B1 B2 D1 D2,
    Δ1 ⨟ Γ ⊨ D2 ≈ B1 ->
    Δ2 ⨟ Γ ⊢ᵍ[ m ] D1 ⊑ B2 ->
    (* set-union tag context (see [d_consis_gen__arrow]); no [list_disjoint] *)
    (Δ1 ++ Δ2) ⨟ Γ ⊢ᵍ[ mode_fn m ]
      (gutyp_arrow (utyp_to_gutyp D2) D1) ⊑ (btyp_arrow B1 B2)
| d_sub_gen__forall_l_tagged : forall Δ Δ' Γ m ε G ph B,
    m <> mode_ti ->
    (* set-union tag context; no [list_disjoint] (see [d_consis_gen__arrow]) *)
    d_tags Δ' ph ->                  (* tags{Δ'}{φ}, mirrors non-gen [d_sub] *)
    Δ' ⨟ Γ ⊢ᵤ ph ->
    is_ttyp ph ->
    (Δ ++ Δ') ⨟ Γ ⊢ᵍ[ m ] (open_gutyp_wrt_gutyp G (utyp_to_gutyp ph)) ⊑ B ->
    Δ ⨟ Γ ⊢ᵍ[ m ] (gutyp_all_etag ε G) ⊑ B
| d_sub_gen__forall_l_untagged : forall Δ Δ' Γ m G ph B,
    m <> mode_ti ->
    (* set-union tag context; no [list_disjoint] (see [d_consis_gen__arrow]) *)
    d_tags Δ' ph ->
    Δ' ⨟ Γ ⊢ᵤ ph ->
    is_ttyp ph ->
    (Δ ++ Δ') ⨟ Γ ⊢ᵍ[ m ] (open_gutyp_wrt_gutyp G (utyp_to_gutyp ph)) ⊑ B ->
    Δ ⨟ Γ ⊢ᵍ[ m ] (gutyp_all_syn G) ⊑ B
where "Δ ⨟ Γ ⊢ᵍ[ M ] D1 ⊑ D2" := (d_sub_gen M Δ Γ D1 D2) : type_scope.

Inductive d_typing_gen : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
| d_typing_gen__embed : forall m Γ e B,
    d_typing m Γ e B ->
    Γ ⊢ᵍ[ m ] e ⦂ B
| d_typing_gen__sub : forall Γ m e B1 B2,
    d_typing_gen mode_ti Γ e B1 ->
    d_sub_gen m nil Γ (btyp_to_gutyp B1) B2 ->
    Γ ⊢ᵍ[ m ] e ⦂ B2
where "Γ ⊢ᵍ[ M ] e ⦂ B" := (d_typing_gen M Γ e B) : type_scope.

Inductive is_fn_n_ti : mode -> Prop :=
| is_fn_n_ti__ti : is_fn_n_ti mode_ti
| is_fn_n_ti__fn : forall m, is_fn_n_ti m -> is_fn_n_ti (mode_fn m).

Fixpoint mode_fn_n_subst (m_orig m_new : mode) : mode :=
  match m_orig with
  | mode_ti => m_new
  | mode_tc => mode_tc
  | mode_fn m => mode_fn (mode_fn_n_subst m m_new)
  end.

Lemma d_typing_embed_gen : forall m Γ e B,
    d_typing m Γ e B ->
    Γ ⊢ᵍ[ m ] e ⦂ B.
Proof.
  intros. apply d_typing_gen__embed. exact H.
Qed.

Lemma d_typing_gen_collapse : forall m Γ e B,
    Γ ⊢ᵍ[ m ] e ⦂ B ->
    Γ ⊢[ m ] e ⦂ B.
Proof.
Admitted.

Lemma d_sub_gen_top_inherited_lhs_impossible : forall Γ m Δ B,
    ~ Δ ⨟ Γ ⊢ᵍ[ m ] (gutyp_all_inh gutyp_unit) ⊑ B.
Proof.
  intros Γ m Δ B H.
  dependent destruction H; simpl in *; try discriminate;
    match goal with
    | C : utyp |- _ => destruct C; simpl in *; discriminate
    | A : ptyp |- _ => destruct A; simpl in *; discriminate
    end.
Qed.
