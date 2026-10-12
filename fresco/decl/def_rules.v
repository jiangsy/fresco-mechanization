Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.

Set Implicit Arguments.

Open Scope fresco_d_scope.

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
Reserved Notation "{{ Γ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d"
  (at level 0, Δ at level 74, Q at level 74, Q' at level 74,
   format "'{{'  Γ  ⨟  Δ  ⊢ᵣ  Q  ⊳  Q'  '}}d'").
Reserved Notation "{{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}d"
  (at level 0, Δ at level 74, P at level 74, P' at level 74,
   format "'{{'  Γ  ⨟  Δ  ⊢ᵣₚ  P  ⊳  P'  '}}d'").
Reserved Notation "{{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d"
  (at level 0, Γ at level 74, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Γ  ⊢ˢ  R  ∼  Q  '}}d'").
Reserved Notation "{{ Ψ ⨟ Γ ⊢ˢ R ∼ᵣ Q }}d"
  (at level 0, Γ at level 74, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Γ  ⊢ˢ  R  ∼ᵣ  Q  '}}d'").
Reserved Notation "{{ Ψ ⨟ Γ ⊢ˢ[ M ] R ⩽ Q }}d"
  (at level 0, Γ at level 74, M at level 0, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Γ  ⊢ˢ[  M  ]  R  ⩽  Q  '}}d'").

Reserved Notation "{{ Γ ⊢ₚ A }}d"
  (at level 0, A at level 74,
   format "'{{'  Γ  ⊢ₚ  A  '}}d'").
Inductive d_wf_ptyp : list (atom * dbind) -> ptyp -> Prop :=
| d_wf_ptyp__unit : forall Γ,
    {{ Γ ⊢ₚ ptyp_unit }}d
| d_wf_ptyp__var : forall Γ α,
    binds α dbind_tvar Γ ->
    {{ Γ ⊢ₚ (ptyp_var_f α) }}d
| d_wf_ptyp__arrow : forall Γ (A1 A2 : ptyp),
    {{ Γ ⊢ₚ A1 }}d ->
    {{ Γ ⊢ₚ A2 }}d ->
    {{ Γ ⊢ₚ (ptyp_arrow A1 A2) }}d
| d_wf_ptyp__all : forall L Γ (A : ptyp),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ₚ (open_ptyp_wrt_ptyp A (ptyp_var_f α)) }}d) ->
    {{ Γ ⊢ₚ (ptyp_all A) }}d
where "{{ Γ ⊢ₚ A }}d" := (d_wf_ptyp Γ A) : fresco_d_scope.

Inductive d_wf_btyp : list (atom * dbind) -> btyp -> Prop :=
| d_wf_btyp__unit : forall Γ,
    {{ Γ ⊢ᵦ btyp_unit }}d
| d_wf_btyp__var : forall Γ α,
    binds α dbind_tvar Γ ->
    {{ Γ ⊢ᵦ (btyp_var_f α) }}d
| d_wf_btyp__arrow : forall Γ (B1 B2 : btyp),
    {{ Γ ⊢ᵦ B1 }}d ->
    {{ Γ ⊢ᵦ B2 }}d ->
    {{ Γ ⊢ᵦ (btyp_arrow B1 B2) }}d
| d_wf_btyp__all_syn : forall L Γ (B : btyp),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ᵦ (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Γ ⊢ᵦ (btyp_all_syn B) }}d
| d_wf_btyp__all_inh : forall L Γ (B : btyp),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ᵦ (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Γ ⊢ᵦ (btyp_all_inh B) }}d
where "{{ Γ ⊢ᵦ B }}d" := (d_wf_btyp Γ B) : fresco_d_scope.

Reserved Notation "{{ Γ ⊢ᵤ C }}d"
  (at level 0, C at level 74,
   format "'{{'  Γ  ⊢ᵤ  C  '}}d'").
Inductive d_wf_utyp : list (atom * dbind) -> utyp -> Prop :=
| d_wf_utyp__unit : forall Γ,
    {{ Γ ⊢ᵤ utyp_unit }}d
| d_wf_utyp__var : forall Γ α,
    binds α dbind_tvar Γ ->
    {{ Γ ⊢ᵤ (utyp_var_f α) }}d
| d_wf_utyp__arrow : forall Γ (C1 C2 : utyp),
    {{ Γ ⊢ᵤ C1 }}d ->
    {{ Γ ⊢ᵤ C2 }}d ->
    {{ Γ ⊢ᵤ (utyp_arrow C1 C2) }}d
| d_wf_utyp__all_syn : forall L Γ (C : utyp),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ᵤ (open_utyp_wrt_utyp C (utyp_var_f α)) }}d) ->
    {{ Γ ⊢ᵤ (utyp_all_syn C) }}d
| d_wf_utyp__all_tag : forall L Γ ε (C : utyp),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ᵤ (open_utyp_wrt_utyp C (utyp_var_f α)) }}d) ->
    {{ Γ ⊢ᵤ (utyp_all_tag ε C) }}d
where "{{ Γ ⊢ᵤ C }}d" := (d_wf_utyp Γ C) : fresco_d_scope.

Definition denv_minus (Γ : list (atom * dbind)) (Δ : atoms)
  : list (atom * dbind) :=
  List.filter (fun b => negb (AtomSetImpl.mem (fst b) Δ)) Γ.

Lemma denv_minus_app : forall Γ1 Γ2 Δ,
    denv_minus (Γ1 ++ Γ2) Δ = denv_minus Γ1 Δ ++ denv_minus Γ2 Δ.
Proof. intros. unfold denv_minus. apply filter_app. Qed.

Lemma denv_minus_cons_in : forall α b Γ Δ,
    α `in` Δ -> denv_minus ((α ~ b) ++ Γ) Δ = denv_minus Γ Δ.
Proof.
  intros. unfold denv_minus. simpl.
  replace (AtomSetImpl.mem α Δ) with true by (symmetry; apply mem_iff; assumption).
  reflexivity.
Qed.

Lemma denv_minus_cons_notin : forall α b Γ Δ,
    α `notin` Δ -> denv_minus ((α ~ b) ++ Γ) Δ = (α ~ b) ++ denv_minus Γ Δ.
Proof.
  intros. unfold denv_minus. simpl.
  replace (AtomSetImpl.mem α Δ) with false
    by (symmetry; apply not_mem_iff; assumption).
  reflexivity.
Qed.

Lemma binds_denv_minus : forall α b Γ Δ,
    binds α b (denv_minus Γ Δ) <-> binds α b Γ /\ α `notin` Δ.
Proof.
  intros α b Γ Δ. unfold binds, denv_minus. rewrite filter_In. simpl.
  rewrite negb_true_iff, <- not_mem_iff. reflexivity.
Qed.

Inductive d_wf_pskl : list (atom * dbind) -> atoms -> pskl -> Prop :=
| d_wf_pskl__ghost : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ₚₛ pskl_ghost }}d
| d_wf_pskl__unit : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ₚₛ pskl_unit }}d
| d_wf_pskl__var : forall Γ Δ α,
    binds α dbind_tvar Γ ->
    {{ Γ ⨟ Δ ⊢ₚₛ (pskl_var_f α) }}d
| d_wf_pskl__arrow : forall Γ Δ (P1 P2 : pskl),
    {{ Γ ⨟ Δ ⊢ₚₛ P1 }}d ->
    {{ Γ ⨟ Δ ⊢ₚₛ P2 }}d ->
    {{ Γ ⨟ Δ ⊢ₚₛ (pskl_arrow P1 P2) }}d
| d_wf_pskl__all : forall L Γ Δ (P : pskl),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⨟ (add α Δ) ⊢ₚₛ
         (open_pskl_wrt_pskl P (pskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}d
| d_wf_pskl__univ_ghost : forall Γ Δ (P : pskl),
    guarded_pskl P ->
    {{ (denv_minus Γ Δ) ⨟ empty ⊢ₚₛ P }}d ->
    {{ Γ ⨟ Δ ⊢ₚₛ (pskl_univ_ghost P) }}d
where "{{ Γ ⨟ Δ ⊢ₚₛ P }}d" := (d_wf_pskl Γ Δ P) : fresco_d_scope.

Inductive d_wf_uskl : list (atom * dbind) -> atoms -> uskl -> Prop :=
| d_wf_uskl__ghost : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ᵤₛ uskl_ghost }}d
| d_wf_uskl__unit : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ᵤₛ uskl_unit }}d
| d_wf_uskl__var : forall Γ Δ α,
    binds α dbind_tvar Γ ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_var_f α) }}d
| d_wf_uskl__arrow : forall Γ Δ (R1 R2 : uskl),
    {{ Γ ⨟ Δ ⊢ᵤₛ R1 }}d ->
    {{ Γ ⨟ Δ ⊢ᵤₛ R2 }}d ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_arrow R1 R2) }}d
| d_wf_uskl__all_syn : forall L Γ Δ (R : uskl),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⨟ (add α Δ) ⊢ᵤₛ
         (open_uskl_wrt_uskl R (uskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_all_syn R) }}d
| d_wf_uskl__all_tag : forall L Γ Δ ε (R : uskl),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⨟ (add α Δ) ⊢ᵤₛ
         (open_uskl_wrt_uskl R (uskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_all_tag ε R) }}d
| d_wf_uskl__univ_ghost : forall Γ Δ (R : uskl),
    guarded_uskl R ->
    {{ (denv_minus Γ Δ) ⨟ empty ⊢ᵤₛ R }}d ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_univ_ghost R) }}d
| d_wf_uskl__dot_ghost : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ᵤₛ uskl_dot_ghost }}d
| d_wf_uskl__dot_univ_ghost : forall Γ Δ (R : uskl),
    guarded_uskl R ->
    {{ (denv_minus Γ Δ) ⨟ empty ⊢ᵤₛ R }}d ->
    {{ Γ ⨟ Δ ⊢ᵤₛ (uskl_dot_univ_ghost R) }}d
where "{{ Γ ⨟ Δ ⊢ᵤₛ R }}d" := (d_wf_uskl Γ Δ R) : fresco_d_scope.

Lemma d_wf_pskl_tvar_mono : forall Γ Δ P,
    {{ Γ ⨟ Δ ⊢ₚₛ P }}d ->
    forall Γ', (forall α, binds α dbind_tvar Γ -> binds α dbind_tvar Γ') ->
    {{ Γ' ⨟ Δ ⊢ₚₛ P }}d.
Proof.
  intros Γ Δ P H; induction H; intros Γ' Hincl.
  - constructor.
  - constructor.
  - constructor. auto.
  - constructor; auto.
  - apply d_wf_pskl__all with (L := L). intros α Hα.
    apply H0; [ exact Hα | ].
    intros β Hb. apply binds_app_iff in Hb. apply binds_app_iff.
    destruct Hb; auto.
  - constructor; [ assumption | ]. apply IHd_wf_pskl.
    intros β Hb. apply binds_denv_minus in Hb. apply binds_denv_minus.
    destruct Hb; auto.
Qed.

Lemma d_wf_uskl_tvar_mono : forall Γ Δ R,
    {{ Γ ⨟ Δ ⊢ᵤₛ R }}d ->
    forall Γ', (forall α, binds α dbind_tvar Γ -> binds α dbind_tvar Γ') ->
    {{ Γ' ⨟ Δ ⊢ᵤₛ R }}d.
Proof.
  intros Γ Δ R H; induction H; intros Γ' Hincl;
    try solve [ constructor; auto ].
  - apply d_wf_uskl__all_syn with (L := L). intros α Hα.
    apply H0; [ exact Hα | ].
    intros β Hb. apply binds_app_iff in Hb. apply binds_app_iff.
    destruct Hb; auto.
  - apply d_wf_uskl__all_tag with (L := L). intros α Hα.
    apply H0; [ exact Hα | ].
    intros β Hb. apply binds_app_iff in Hb. apply binds_app_iff.
    destruct Hb; auto.
  - constructor; [ assumption | ]. apply IHd_wf_uskl.
    intros β Hb. apply binds_denv_minus in Hb. apply binds_denv_minus.
    destruct Hb; auto.
  - constructor; [ assumption | ]. apply IHd_wf_uskl.
    intros β Hb. apply binds_denv_minus in Hb. apply binds_denv_minus.
    destruct Hb; auto.
Qed.

Inductive d_tags : atoms -> utyp -> Prop :=
| d_tags__unit : forall Ψ,
    Ψ [=] empty ->
    d_tags Ψ utyp_unit
| d_tags__var : forall Ψ α,
    Ψ [=] empty ->
    d_tags Ψ (utyp_var_f α)
| d_tags__arrow : forall Ψ Ψ1 Ψ2 (C1 C2 : utyp),
    d_tags Ψ1 C1 ->
    d_tags Ψ2 C2 ->
    Ψ1 ∩ Ψ2 [=] empty ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    d_tags Ψ (utyp_arrow C1 C2)
| d_tags__all_tag : forall L Ψ Ψ0 ε (C : utyp),
    (forall α, α `notin` L ->
       d_tags Ψ0 (open_utyp_wrt_utyp C (utyp_var_f α))) ->
    ε `notin` Ψ0 ->
    Ψ [=] add ε Ψ0 ->
    d_tags Ψ (utyp_all_tag ε C).

Inductive d_tags_skl : atoms -> uskl -> Prop :=
| d_tags_skl__unit : forall Ψ, Ψ [=] empty -> d_tags_skl Ψ uskl_unit
| d_tags_skl__var : forall Ψ α, Ψ [=] empty -> d_tags_skl Ψ (uskl_var_f α)
| d_tags_skl__arrow : forall Ψ Ψ1 Ψ2 (R1 R2 : uskl),
    d_tags_skl Ψ1 R1 ->
    d_tags_skl Ψ2 R2 ->
    Ψ1 ∩ Ψ2 [=] empty ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    d_tags_skl Ψ (uskl_arrow R1 R2)
| d_tags_skl__all_tag : forall L Ψ Ψ0 ε (R : uskl),
    (forall α, α `notin` L ->
       d_tags_skl Ψ0 (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    ε `notin` Ψ0 ->
    Ψ [=] add ε Ψ0 ->
    d_tags_skl Ψ (uskl_all_tag ε R)
| d_tags_skl__dot_ghost : forall Ψ,
    Ψ [=] empty ->
    d_tags_skl Ψ uskl_dot_ghost
| d_tags_skl__dot_univ_ghost : forall Ψ (R : uskl),
    d_tags_skl Ψ R ->
    d_tags_skl Ψ (uskl_dot_univ_ghost R).

#[export] Hint Constructors d_tags d_tags_skl : fresco.

Inductive d_consis : atoms -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_consis__unit : forall Ψ Γ,
    Ψ [=] empty ->
    {{ Ψ ⨟ Γ ⊢ utyp_unit ∼ btyp_unit }}d
| d_consis__var : forall Ψ Γ α,
    binds α dbind_tvar Γ ->
    Ψ [=] empty ->
    {{ Ψ ⨟ Γ ⊢ (utyp_var_f α) ∼ (btyp_var_f α) }}d
| d_consis__forall_inh_tagged : forall L Ψ Ψ0 Γ ε (C : utyp) (B : btyp),
    (forall α, α `notin` L ->
       {{ Ψ0 ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f α)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    Ψ [=] add ε Ψ0 ->
    {{ Ψ ⨟ Γ ⊢ (utyp_all_tag ε C) ∼ (btyp_all_inh B) }}d
| d_consis__forall_inh_untagged : forall L Ψ Γ (C : utyp) (B : btyp),
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f α)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ (utyp_all_syn C) ∼ (btyp_all_inh B) }}d
| d_consis__forall_syn_tagged : forall L Ψ Γ ε (C : utyp) (B : btyp),
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f α)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ (utyp_all_tag ε C) ∼ (btyp_all_syn B) }}d
| d_consis__forall_syn : forall L Ψ Γ (C : utyp) (B : btyp),
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢
         (open_utyp_wrt_utyp C (utyp_var_f α)) ∼
         (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ (utyp_all_syn C) ∼ (btyp_all_syn B) }}d
| d_consis__arrow : forall Ψ Ψ1 Ψ2 Γ (C1 C2 : utyp) (B1 B2 : btyp),
    {{ Ψ1 ⨟ Γ ⊢ C1 ∼ B1 }}d ->
    {{ Ψ2 ⨟ Γ ⊢ C2 ∼ B2 }}d ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Γ ⊢ (utyp_arrow C1 C2) ∼ (btyp_arrow B1 B2) }}d
where "{{ Ψ ⨟ Γ ⊢ C ∼ B }}d" := (d_consis Ψ Γ C B) : fresco_d_scope.

Inductive d_sub : mode -> atoms -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_sub__infer : forall Ψ Γ (C : utyp) (B : btyp),
    {{ empty ⨟ Γ ⊢ C ∼ B }}d ->
    is_styp B ->
    Ψ [=] empty ->
    {{ Ψ ⨟ Γ ⊢[ mode_ti ] C ⩽ B }}d
| d_sub__check : forall Ψ Γ (C : utyp) (B : btyp),
    guarded_utyp C ->
    guarded_btyp B ->
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
    is_ityp B ->
    {{ Ψ ⨟ Γ ⊢[ mode_tc ] C ⩽ B }}d
| d_sub__forall_r : forall L Ψ Γ (C : utyp) (B : btyp),
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢[ mode_tc ] C ⩽
         (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢[ mode_tc ] C ⩽ (btyp_all_inh B) }}d
| d_sub__arrow : forall Ψ Ψ1 Ψ2 Γ m (C1 C2 : utyp) (B1 B2 : btyp),
    {{ Ψ1 ⨟ Γ ⊢ C1 ∼ B1 }}d ->
    {{ Ψ2 ⨟ Γ ⊢[ m ] C2 ⩽ B2 }}d ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Γ ⊢[ mode_fn m ] (utyp_arrow C1 C2) ⩽ (btyp_arrow B1 B2) }}d
| d_sub__forall_l_tagged : forall Ψ Ψ' Γ m ε (C ph : utyp) (B : btyp),
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_utyp (utyp_all_tag ε C)) [=] empty ->
    d_tags Ψ' ph ->
    {{ Γ ⊢ᵤ ph }}d ->
    is_dtyp ph ->
    {{ (Ψ `union` Ψ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⩽ B }}d ->
    {{ Ψ ⨟ Γ ⊢[ m ] (utyp_all_tag ε C) ⩽ B }}d
| d_sub__forall_l_untagged : forall Ψ Ψ' Γ m (C ph : utyp) (B : btyp),
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_utyp (utyp_all_syn C)) [=] empty ->
    d_tags Ψ' ph ->
    {{ Γ ⊢ᵤ ph }}d ->
    is_dtyp ph ->
    {{ (Ψ `union` Ψ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⩽ B }}d ->
    {{ Ψ ⨟ Γ ⊢[ m ] (utyp_all_syn C) ⩽ B }}d
where "{{ Ψ ⨟ Γ ⊢[ M ] C ⩽ B }}d" := (d_sub M Ψ Γ C B) : fresco_d_scope.

Reserved Notation "{{ Γ ⊢ A ≤ B }}d"
  (at level 0, A at level 74, B at level 74,
   format "'{{'  Γ  ⊢  A  ≤  B  '}}d'").
Inductive d_shallow_sub : list (atom * dbind) -> ptyp -> ptyp -> Prop :=
| d_shallow_sub__refl : forall Γ (A : ptyp),
    {{ Γ ⊢ₚ A }}d ->
    {{ Γ ⊢ A ≤ A }}d
| d_shallow_sub__forall_r : forall L Γ (A1 A2 : ptyp),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ A1 ≤ (open_ptyp_wrt_ptyp A2 (ptyp_var_f α)) }}d) ->
    {{ Γ ⊢ A1 ≤ (ptyp_all A2) }}d
| d_shallow_sub__forall_l : forall Γ (A1 A2 I : ptyp),
    mono_ptyp I ->
    {{ Γ ⊢ₚ I }}d ->
    {{ Γ ⊢ (open_ptyp_wrt_ptyp A1 I) ≤ A2 }}d ->
    {{ Γ ⊢ (ptyp_all A1) ≤ A2 }}d
where "{{ Γ ⊢ A ≤ B }}d" := (d_shallow_sub Γ A B) : fresco_d_scope.

Inductive d_refine_syn : list (atom * dbind) -> atoms -> bskl -> bskl -> Prop :=
| d_refine_syn__unit : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ᵣ bskl_unit ⊳ bskl_unit }}d
| d_refine_syn__var : forall Γ Δ α,
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ (bskl_var_f α) }}d
| d_refine_syn__arrow : forall Γ Δ (Q1 Q2 Q3 Q4 : bskl),
    is_iskl (bskl_arrow Q1 Q2) ->
    {{ Γ ⨟ Δ ⊢ᵣ Q1 ⊳ Q3 }}d ->
    {{ Γ ⨟ Δ ⊢ᵣ Q2 ⊳ Q4 }}d ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow Q3 Q4) }}d
| d_refine_syn__all : forall L Γ Δ (Q Q' : bskl),
    is_iskl (bskl_all_inh Q) ->
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⨟ (add α Δ) ⊢ᵣ
         (open_bskl_wrt_bskl Q (bskl_var_f α)) ⊳
         (open_bskl_wrt_bskl Q' (bskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_all_inh Q) ⊳ (bskl_all_inh Q') }}d
| d_refine_syn__ghost : forall Γ Δ (P : pskl),
    Δ ∩ ftvar_in_pskl P [=] empty ->
    {{ Γ ⨟ Δ ⊢ᵣ bskl_ghost ⊳ (pskl_to_bskl_syn P) }}d
| d_refine_syn__univ_ghost_remove : forall Γ Δ (Q Q' : bskl),
    is_iskl (bskl_univ_ghost Q) ->
    {{ Γ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ Q' }}d
| d_refine_syn__univ_ghost_fill : forall L Γ Δ (Q Q' : bskl),
    is_iskl (bskl_univ_ghost Q) ->
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⨟ Δ ⊢ᵣ
         (bskl_univ_ghost Q) ⊳ (open_bskl_wrt_bskl Q' (bskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ (bskl_all_syn Q') }}d
| d_refine_syn__univ_ghost_keep : forall Γ Δ (Q Q' : bskl),
    is_iskl (bskl_univ_ghost Q) ->
    {{ Γ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d ->
    {{ Γ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ (bskl_univ_ghost Q') }}d
where "{{ Γ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d" := (d_refine_syn Γ Δ Q Q') : fresco_d_scope.

Inductive d_refine_pskl :
  list (atom * dbind) -> atoms -> pskl -> pskl -> Prop :=
| d_refine_pskl__unit : forall Γ Δ,
    {{ Γ ⨟ Δ ⊢ᵣₚ pskl_unit ⊳ pskl_unit }}d
| d_refine_pskl__var : forall Γ Δ α,
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ (pskl_var_f α) }}d
| d_refine_pskl__arrow : forall Γ Δ (P1 P2 P3 P4 : pskl),
    {{ Γ ⨟ Δ ⊢ᵣₚ P1 ⊳ P3 }}d ->
    {{ Γ ⨟ Δ ⊢ᵣₚ P2 ⊳ P4 }}d ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_arrow P1 P2) ⊳ (pskl_arrow P3 P4) }}d
| d_refine_pskl__all : forall L Γ Δ (P P' : pskl),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⨟ (add α Δ) ⊢ᵣₚ
         (open_pskl_wrt_pskl P (pskl_var_f α)) ⊳
         (open_pskl_wrt_pskl P' (pskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_all_syn P) ⊳ (pskl_all_syn P') }}d
| d_refine_pskl__ghost : forall Γ Δ (P' : pskl),
    Δ ∩ ftvar_in_pskl P' [=] empty ->
    {{ Γ ⨟ Δ ⊢ᵣₚ pskl_ghost ⊳ P' }}d
| d_refine_pskl__univ_ghost_remove : forall Γ Δ (P P' : pskl),
    {{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}d ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ P' }}d
| d_refine_pskl__univ_ghost_fill : forall L Γ Δ (P P' : pskl),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⨟ Δ ⊢ᵣₚ
         (pskl_univ_ghost P) ⊳ (open_pskl_wrt_pskl P' (pskl_var_f α)) }}d) ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ (pskl_all_syn P') }}d
| d_refine_pskl__univ_ghost_keep : forall Γ Δ (P P' : pskl),
    {{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}d ->
    {{ Γ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ (pskl_univ_ghost P') }}d
where "{{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}d" := (d_refine_pskl Γ Δ P P') : fresco_d_scope.

Inductive d_pat_consis : atoms -> list (atom * dbind) -> uskl -> bskl -> Prop :=
| d_pat_consis__unit : forall Ψ Γ,
    Ψ [=] empty ->
    {{ Ψ ⨟ Γ ⊢ˢ uskl_unit ∼ bskl_unit }}d
| d_pat_consis__var : forall Ψ Γ α,
    Ψ [=] empty ->
    binds α dbind_tvar Γ ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_var_f α) ∼ (bskl_var_f α) }}d
| d_pat_consis__forall_inh_tagged : forall L Ψ Ψ0 Γ ε (R : uskl) (Q : bskl),
    (forall α, α `notin` L ->
       {{ Ψ0 ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}d) ->
    Ψ [=] add ε Ψ0 ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_all_tag ε R) ∼ (bskl_all_inh Q) }}d
| d_pat_consis__forall_inh_untagged : forall L Ψ Γ (R : uskl) (Q : bskl),
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_all_syn R) ∼ (bskl_all_inh Q) }}d
| d_pat_consis__forall_syn_tagged : forall L Ψ Γ ε (R : uskl) (Q : bskl),
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_all_tag ε R) ∼ (bskl_all_syn Q) }}d
| d_pat_consis__forall_syn : forall L Ψ Γ (R : uskl) (Q : bskl),
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_all_syn R) ∼ (bskl_all_syn Q) }}d
| d_pat_consis__arrow : forall Ψ Ψ1 Ψ2 Γ (R1 R2 : uskl) (Q1 Q2 : bskl),
    {{ Ψ1 ⨟ Γ ⊢ˢ R1 ∼ Q1 }}d ->
    {{ Ψ2 ⨟ Γ ⊢ˢ R2 ∼ Q2 }}d ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2) }}d
| d_pat_consis__ghost : forall Ψ Γ (P : pskl),
    Ψ [=] empty ->
    {{ Ψ ⨟ Γ ⊢ˢ uskl_ghost ∼ (pskl_to_bskl_inh P) }}d
| d_pat_consis__ghostg : forall Ψ Γ,
    Ψ [=] empty ->
    {{ Ψ ⨟ Γ ⊢ˢ uskl_dot_ghost ∼ bskl_ghost }}d
| d_pat_consis__dot_univ_ghost : forall Ψ Γ (R : uskl) (Q : bskl),
    {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_dot_univ_ghost R) ∼ (bskl_univ_ghost Q) }}d
| d_pat_consis__univ_ghost : forall Ψ Γ (R : uskl) (Q : bskl),

    {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_univ_ghost R) ∼ (bskl_univ_ghost Q) }}d
| d_pat_consis__univ_ghost_inh : forall L Ψ Γ (R : uskl) (Q : bskl),
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ dbind_tvar) ++ Γ) ⊢ˢ
         (uskl_univ_ghost R) ∼ (open_bskl_wrt_bskl Q (bskl_var_f α)) }}d) ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_univ_ghost R) ∼ (bskl_all_inh Q) }}d
| d_pat_consis__univ_ghost_drop : forall Ψ Γ (R : uskl) (Q : bskl),
    {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ (uskl_univ_ghost R) ∼ Q }}d
where "{{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d" := (d_pat_consis Ψ Γ R Q) : fresco_d_scope.

Definition d_consis_join (Ψ : atoms) (Γ : list (atom * dbind))
                         (R : uskl) (Q : bskl) : Prop :=
  {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d /\
  {{ Γ ⨟ empty ⊢ᵣₚ (uskl_to_pskl R) ⊳ (bskl_to_pskl Q) }}d.

Notation "{{ Ψ ⨟ Γ ⊢ˢ R ∼ᵣ Q }}d" := (d_consis_join Ψ Γ R Q) : fresco_d_scope.

Lemma d_consis_join_intro : forall Ψ Γ R Q,
  {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d ->
  {{ Γ ⨟ empty ⊢ᵣₚ (uskl_to_pskl R) ⊳ (bskl_to_pskl Q) }}d ->
  {{ Ψ ⨟ Γ ⊢ˢ R ∼ᵣ Q }}d.
Proof. intros; split; assumption. Qed.

#[export] Hint Resolve d_consis_join_intro : fresco.
#[export] Hint Unfold d_consis_join : fresco.

Inductive d_pat_sub : mode -> atoms -> list (atom * dbind) -> uskl -> bskl -> Prop :=
| d_pat_sub__infer : forall Ψ Γ (R : uskl) (Q : bskl),

    Ψ [=] empty ->
    {{ empty ⨟ Γ ⊢ˢ R ∼ᵣ Q }}d ->
    is_sskl Q ->
    {{ Ψ ⨟ Γ ⊢ˢ[ mode_ti ] R ⩽ Q }}d
| d_pat_sub__univ_ghost_r : forall Ψ Γ (R : uskl) (Q : bskl),
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    {{ empty ⨟ Γ ⊢ˢ R ∼ᵣ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ mode_tc ] R ⩽ (bskl_univ_ghost Q) }}d
| d_pat_sub__ghost : forall m Ψ Γ (P : pskl),

    Ψ [=] empty ->
    mod_comp_sk (pskl_to_bskl_inh P) m ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] uskl_ghost ⩽ (pskl_to_bskl_inh P) }}d
| d_pat_sub__ghostg : forall m Ψ Γ,
    Ψ [=] empty ->
    mod_comp_sk bskl_ghost m ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] uskl_dot_ghost ⩽ bskl_ghost }}d
| d_pat_sub__arrow : forall Ψ Ψ1 Ψ2 Γ m (R1 R2 : uskl) (Q1 Q2 : bskl),
    {{ Ψ1 ⨟ Γ ⊢ˢ R1 ∼ᵣ Q1 }}d ->
    {{ Ψ2 ⨟ Γ ⊢ˢ[ m ] R2 ⩽ Q2 }}d ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Γ ⊢ˢ[ mode_fn m ] (uskl_arrow R1 R2) ⩽ (bskl_arrow Q1 Q2) }}d
| d_pat_sub__forall_l_tagged : forall Ψ Ψ' Γ m ε (R psi : uskl) (Q : bskl),
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_tag ε R)) [=] empty ->
    d_tags_skl Ψ' psi ->
    {{ Γ ⨟ empty ⊢ᵤₛ psi }}d ->
    is_dskl psi ->
    {{ (Ψ `union` Ψ') ⨟ Γ ⊢ˢ[ m ] (open_uskl_wrt_uskl R psi) ⩽ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] (uskl_all_tag ε R) ⩽ Q }}d
| d_pat_sub__forall_l_untagged : forall Ψ Ψ' Γ m (R psi : uskl) (Q : bskl),
    m <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_syn R)) [=] empty ->
    d_tags_skl Ψ' psi ->
    {{ Γ ⨟ empty ⊢ᵤₛ psi }}d ->
    is_dskl psi ->
    {{ (Ψ `union` Ψ') ⨟ Γ ⊢ˢ[ m ] (open_uskl_wrt_uskl R psi) ⩽ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] (uskl_all_syn R) ⩽ Q }}d
| d_pat_sub__univ_ghost_l : forall m Ψ Γ (R : uskl) (Q : bskl),

    m <> mode_ti ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] R ⩽ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] (uskl_univ_ghost R) ⩽ Q }}d
| d_pat_sub__univ_ghost_lg : forall m Ψ Γ (R : uskl) (Q : bskl),
    m <> mode_ti ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] R ⩽ Q }}d ->
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] (uskl_dot_univ_ghost R) ⩽ Q }}d
where "{{ Ψ ⨟ Γ ⊢ˢ[ M ] R ⩽ Q }}d" := (d_pat_sub M Ψ Γ R Q) : fresco_d_scope.

Reserved Notation "{{ Γ ⊢[ M ] e ⦂ A }}d"
  (at level 0, M at level 0, e at level 74, A at level 74,
   format "'{{'  Γ  ⊢[  M  ]  e  ⦂  A  '}}d'").
Reserved Notation "{{ Γ ⊢ˢ[ M ] e ⦂ P }}d"
  (at level 0, M at level 0, e at level 74, P at level 74,
   format "'{{'  Γ  ⊢ˢ[  M  ]  e  ⦂  P  '}}d'").
Reserved Notation "{{ Γ ⊢ˢᵈ[ M ] e ⦂ A }}d"
  (at level 0, M at level 0, e at level 74, A at level 74,
   format "'{{'  Γ  ⊢ˢᵈ[  M  ]  e  ⦂  A  '}}d'").

Inductive d_pat : mode -> list (atom * dbind) -> exp -> bskl -> Prop :=
| d_pat__unit : forall Γ m (Q : bskl),
    {{ Γ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}d ->
    {{ empty ⨟ Γ ⊢ˢ[ m ] uskl_unit ⩽ Q }}d ->
    {{ Γ ⊢ˢ[ m ] exp_unit ⦂ Q }}d
| d_pat__var : forall Γ m x (P : pskl) d (Q : bskl),
    binds x d Γ ->
    dbind_to_pskl d = Some P ->
    {{ Γ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}d ->
    {{ empty ⨟ Γ ⊢ˢ[ m ] (bskl_to_uskl (pskl_to_bskl_syn P)) ⩽ Q }}d ->
    {{ Γ ⊢ˢ[ m ] (exp_var_f x) ⦂ Q }}d
| d_pat__anno : forall Γ m e (A : ptyp) (Q : bskl),
    {{ Γ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}d ->
    {{ empty ⨟ Γ ⊢ˢ[ m ] (bskl_to_uskl (pskl_to_bskl_syn (ptyp_to_pskl A))) ⩽ Q }}d ->
    {{ Γ ⊢ˢ[ m ] (exp_anno e A) ⦂ Q }}d
| d_pat__freeze : forall Γ e (P : pskl),
    {{ Γ ⊢ˢ[ mode_ti ] e ⦂ (pskl_to_bskl_syn P) }}d ->
    {{ Γ ⊢ˢ[ mode_tc ] (exp_freeze e) ⦂ (pskl_to_bskl_syn P) }}d
| d_pat__abs : forall L Γ m e (P : pskl) (Q : bskl),
    m <> mode_tc ->
    {{ Γ ⨟ empty ⊢ₚₛ P }}d ->
    mod_comp_sk (bskl_arrow (pskl_to_bskl_inh P) Q) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_skl P) ++ Γ) ⊢ˢ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q }}d) ->
    {{ Γ ⊢ˢ[ m ] (exp_abs e) ⦂ (bskl_arrow (pskl_to_bskl_inh P) Q) }}d
| d_pat__abs_anno : forall L Γ m e (A : ptyp) (B : btyp) (Q : bskl),
    m <> mode_tc ->
    {{ Γ ⊢ₚ A }}d ->
    btyp_to_ptyp B = A ->
    mod_comp_sk (bskl_arrow (btyp_to_bskl B) Q) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q }}d) ->
    {{ Γ ⊢ˢ[ m ] (exp_abs_anno A e) ⦂ (bskl_arrow (btyp_to_bskl B) Q) }}d
| d_pat__abs_check : forall L Γ e (P : pskl),
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_skl pskl_ghost) ++ Γ) ⊢ˢ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ (pskl_to_bskl_syn P) }}d) ->
    {{ Γ ⊢ˢ[ mode_tc ] (exp_abs e) ⦂ (bskl_univ_ghost (bskl_arrow bskl_ghost (pskl_to_bskl_syn P))) }}d
| d_pat__abs_anno_check : forall L Γ e (A : ptyp) (P : pskl),
    {{ Γ ⊢ₚ A }}d ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ (pskl_to_bskl_syn P) }}d) ->
    {{ Γ ⊢ˢ[ mode_tc ] (exp_abs_anno A e) ⦂ (bskl_univ_ghost (bskl_arrow (btyp_to_bskl (ptyp_to_btyp_syn A)) (pskl_to_bskl_syn P))) }}d
| d_pat__app : forall Γ m e1 e2 (P : pskl) (Q1 Q2 : bskl),
    {{ Γ ⊢ˢ[ mode_tc ] e2 ⦂ (pskl_to_bskl_syn P) }}d ->
    {{ Γ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Q1 }}d ->
    {{ Γ ⊢ˢ[ mode_fn m ] e1 ⦂ (bskl_arrow Q1 Q2) }}d ->
    {{ Γ ⊢ˢ[ m ] (exp_app e1 e2) ⦂ Q2 }}d
where "{{ Γ ⊢ˢ[ M ] e ⦂ P }}d" := (d_pat M Γ e P) : fresco_d_scope.

Inductive d_typing : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
| d_typing__unit : forall Γ,
    {{ Γ ⊢[ mode_ti ] exp_unit ⦂ btyp_unit }}d
| d_typing__var : forall Γ x (A : ptyp),
    binds x (dbind_typ A) Γ ->
    {{ Γ ⊢[ mode_ti ] (exp_var_f x) ⦂ (ptyp_to_btyp_syn A) }}d
| d_typing__anno : forall Γ e (A : ptyp),
    {{ Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) }}d ->
    {{ Γ ⊢[ mode_ti ] (exp_anno e A) ⦂ (ptyp_to_btyp_syn A) }}d
| d_typing__sub : forall Γ m e (A : ptyp) (B : btyp),

    {{ Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) }}d ->
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
    {{ Γ ⊢[ m ] e ⦂ B }}d
| d_typing__freeze : forall Γ e (A : ptyp),
    {{ Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) }}d ->
    {{ Γ ⊢[ mode_tc ] (exp_freeze e) ⦂ (ptyp_to_btyp_inh A) }}d
| d_typing__forall : forall L Γ e (A : ptyp),
    is_value e ->
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢[ mode_tc ] e ⦂ (open_btyp_wrt_btyp (ptyp_to_btyp_inh A) (btyp_var_f α)) }}d) ->
    {{ Γ ⊢[ mode_tc ] e ⦂ (btyp_all_inh (ptyp_to_btyp_inh A)) }}d
| d_typing__abs : forall L Γ m e (A : ptyp) (B : btyp),
    {{ Γ ⊢ₚ A }}d ->
    mod_comp_ty (btyp_arrow (ptyp_to_btyp_inh A) B) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}d) ->
    {{ Γ ⊢[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}d
| d_typing__abs_anno : forall L Γ m e (A : ptyp) (B1 B2 : btyp),
    {{ Γ ⊢ₚ A }}d ->
    btyp_to_ptyp B1 = A ->
    mod_comp_ty (btyp_arrow B1 B2) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B2 }}d) ->
    {{ Γ ⊢[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow B1 B2) }}d
| d_typing__app : forall Γ m e1 e2 (P : pskl) (B1 B2 : btyp),
    {{ Γ ⊢ˢ[ mode_tc ] e2 ⦂ (pskl_to_bskl_syn P) }}d ->
    {{ Γ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B1) }}d ->
    {{ Γ ⊢[ mode_fn m ] e1 ⦂ (btyp_arrow B1 B2) }}d ->
    {{ Γ ⊢[ mode_tc ] e2 ⦂ (ptyp_to_btyp_inh (btyp_to_ptyp B1)) }}d ->
    {{ Γ ⊢[ m ] (exp_app e1 e2) ⦂ B2 }}d
where "{{ Γ ⊢[ M ] e ⦂ A }}d" := (d_typing M Γ e A) : fresco_d_scope.

Inductive d_sd_typing : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
| d_sd_typing__unit : forall Γ m (B : btyp),
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn ptyp_unit) ⩽ B }}d ->
    {{ Γ ⊢ˢᵈ[ m ] exp_unit ⦂ B }}d
| d_sd_typing__var : forall Γ m x (A : ptyp) (B : btyp),
    binds x (dbind_typ A) Γ ->
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
    {{ Γ ⊢ˢᵈ[ m ] (exp_var_f x) ⦂ B }}d
| d_sd_typing__abs : forall L Γ m e (A : ptyp) (B : btyp),
    m <> mode_tc ->
    {{ Γ ⊢ₚ A }}d ->
    mod_comp_ty (btyp_arrow (ptyp_to_btyp_inh A) B) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢᵈ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}d) ->
    {{ Γ ⊢ˢᵈ[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}d
| d_sd_typing__abs_check_step : forall L Γ e (B : btyp),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ˢᵈ[ mode_tc ] (exp_abs e)
         ⦂ (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_all_inh B) }}d
| d_sd_typing__abs_check_base : forall L Γ e (A : ptyp) (B : btyp),
    {{ Γ ⊢ₚ A }}d ->
    is_ityp B ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢᵈ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}d) ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}d
| d_sd_typing__anno : forall Γ m e (A : ptyp) (B : btyp),
    {{ Γ ⊢ˢᵈ[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) }}d ->
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
    {{ Γ ⊢ˢᵈ[ m ] (exp_anno e A) ⦂ B }}d
| d_sd_typing__abs_anno : forall L Γ m e (A : ptyp) (B1 B2 : btyp),

    m <> mode_tc ->
    {{ Γ ⊢ₚ A }}d ->
    btyp_to_ptyp B1 = A ->
    mod_comp_ty (btyp_arrow B1 B2) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢᵈ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B2 }}d) ->
    {{ Γ ⊢ˢᵈ[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow B1 B2) }}d

| d_sd_typing__abs_anno_check_step : forall L Γ (A : ptyp) e (B : btyp),
    (forall α, α `notin` L ->
       {{ ((α ~ dbind_tvar) ++ Γ) ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e)
         ⦂ (open_btyp_wrt_btyp B (btyp_var_f α)) }}d) ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_all_inh B) }}d
| d_sd_typing__abs_anno_check_base : forall L Γ e (A : ptyp) (B : btyp),

    {{ Γ ⊢ₚ A }}d ->
    is_ityp B ->
    (forall x, x `notin` L ->
       {{ ((x ~ dbind_typ A) ++ Γ) ⊢ˢᵈ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}d) ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}d
| d_sd_typing__freeze : forall Γ e (A : ptyp),

    {{ Γ ⊢ˢᵈ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) }}d ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] (exp_freeze e) ⦂ (ptyp_to_btyp_inh A) }}d
| d_sd_typing__app : forall Γ m e1 e2 (P : pskl) (B1 B2 : btyp),
    {{ Γ ⊢ˢ[ mode_tc ] e2 ⦂ (pskl_to_bskl_syn P) }}d ->
    {{ Γ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B1) }}d ->
    {{ Γ ⊢ˢᵈ[ (mode_fn m) ] e1 ⦂ (btyp_arrow B1 B2) }}d ->
    {{ Γ ⊢ˢᵈ[ mode_tc ] e2 ⦂ (ptyp_to_btyp_inh (btyp_to_ptyp B1)) }}d ->
    {{ Γ ⊢ˢᵈ[ m ] (exp_app e1 e2) ⦂ B2 }}d
where "{{ Γ ⊢ˢᵈ[ M ] e ⦂ A }}d" := (d_sd_typing M Γ e A) : fresco_d_scope.
