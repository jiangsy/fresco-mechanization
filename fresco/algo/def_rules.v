Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.

Set Implicit Arguments.

Open Scope fresco_a_scope.

Reserved Notation "{{ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}a"
  (at level 0, Δ1 at level 0, Δ2 at level 0, P0 at level 0, P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢[  Δ1  |  Δ2  |  P0  ]  P  ∼  Q  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊲ A ≈ᵘ B ⊣ Θ' }}a"
  (at level 0, A at level 74, B at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊲  A  ≈ᵘ  B  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}a"
  (at level 0, Ξ at level 0, α at level 74, P at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊲[  Ξ  ]  α  ≔  P  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ' }}a"
  (at level 0, P0 at level 74, P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊲  P0  ▹  P  ⇢  Q  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊢[ N | m | P0 ] P ⩽ Q ⊣ Θ' }}a"
  (at level 0, N at level 0, m at level 0, P0 at level 0, P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢[  N  |  m  |  P0  ]  P  ⩽  Q  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ' }}a"
  (at level 0, m at level 0, P0 at level 0, e at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢ˢ[  m  ;  P0  ]  e  ⦂  Q  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊢[ m ; P0 ] e ⦂ B ⊣ Θ' }}a"
  (at level 0, m at level 0, P0 at level 0, e at level 74, B at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢[  m  ;  P0  ]  e  ⦂  B  ⊣  Θ'  '}}a'").

Inductive abind : Set :=
| abind_tvar : abind
| abind_var_typ : ptyp -> abind
| abind_var_skl : pskl -> abind
| abind_flex_mono : abind
| abind_flex_mono_def : ptyp -> abind.

Definition aenv : Set := list (atom * abind).

Definition abind_to_pskl (b : abind) : option pskl :=
  match b with
  | abind_var_skl P => Some P
  | abind_var_typ A => Some (ptyp_to_pskl A)
  | abind_tvar => None
  | abind_flex_mono => None
  | abind_flex_mono_def _ => None
  end.

Definition ftvar_in_abind (bd : abind) : atoms :=
  match bd with
  | abind_tvar            => empty
  | abind_var_typ A       => ftvar_in_ptyp A
  | abind_var_skl P       => ftvar_in_pskl P
  | abind_flex_mono       => empty
  | abind_flex_mono_def A => ftvar_in_ptyp A
  end.

Fixpoint ftvar_in_aenv (Θ : aenv) : atoms :=
  match Θ with
  | nil           => empty
  | (x, bd) :: Θ' => add x (ftvar_in_abind bd `union` ftvar_in_aenv Θ')
  end.

Inductive a_suffix_binding : abind -> Prop :=
| a_suffix_binding__flex_mono :
    a_suffix_binding abind_flex_mono
| a_suffix_binding__flex_mono_def : forall A,
    a_suffix_binding (abind_flex_mono_def A).

Inductive a_suffix : aenv -> Prop :=
| a_suffix__nil : a_suffix nil
| a_suffix__cons : forall a b Ξ,
    a_suffix Ξ ->
    a_suffix_binding b ->
    a_suffix ((a ~ b) ++ Ξ).

Definition a_binds_tvar (α : atom) (Θ : aenv) : Prop :=
  binds α abind_tvar Θ \/
  binds α abind_flex_mono Θ \/
  (exists τ, binds α (abind_flex_mono_def τ) Θ).

Inductive a_wf_ptyp : aenv -> ptyp -> Prop :=
| a_wf_ptyp__unit : forall Θ,
    a_wf_ptyp Θ ptyp_unit
| a_wf_ptyp__var : forall Θ α,
    a_binds_tvar α Θ ->
    a_wf_ptyp Θ (ptyp_var_f α)
| a_wf_ptyp__arrow : forall Θ A1 A2,
    a_wf_ptyp Θ A1 ->
    a_wf_ptyp Θ A2 ->
    a_wf_ptyp Θ (ptyp_arrow A1 A2)
| a_wf_ptyp__all : forall L Θ A,
    (forall α, α `notin` L ->
       a_wf_ptyp ((α ~ abind_tvar) ++ Θ) (open_ptyp_wrt_ptyp A (ptyp_var_f α))) ->
    a_wf_ptyp Θ (ptyp_all A).

Definition a_scope_pskl (Θ : aenv) (P : pskl) : Prop :=
  lc_pskl P /\ (forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ).

Reserved Notation "{{ Θ ⨟ Δ ⊢ₚₛ P }}a"
  (at level 0, Δ at level 74, P at level 74,
   format "'{{'  Θ  ⨟  Δ  ⊢ₚₛ  P  '}}a'").

Definition aenv_minus (Θ : aenv) (Δ : atoms) : aenv :=
  List.filter (fun b => negb (AtomSetImpl.mem (fst b) Δ)) Θ.

Lemma aenv_minus_app : forall Θ1 Θ2 Δ,
    aenv_minus (Θ1 ++ Θ2) Δ = aenv_minus Θ1 Δ ++ aenv_minus Θ2 Δ.
Proof. intros. unfold aenv_minus. apply filter_app. Qed.

Lemma aenv_minus_empty : forall Θ, aenv_minus Θ empty = Θ.
Proof.
  induction Θ as [|[a b] Θ IH]; simpl; [ reflexivity | ].
  unfold aenv_minus in *. simpl.
  replace (AtomSetImpl.mem a empty) with false
    by (symmetry; apply not_mem_iff; fsetdec).
  simpl. f_equal. assumption.
Qed.

Lemma aenv_minus_cons_notin : forall α b Θ Δ,
    α `notin` Δ -> aenv_minus ((α ~ b) ++ Θ) Δ = (α ~ b) ++ aenv_minus Θ Δ.
Proof.
  intros. unfold aenv_minus. simpl.
  replace (AtomSetImpl.mem α Δ) with false
    by (symmetry; apply not_mem_iff; assumption).
  reflexivity.
Qed.

Lemma aenv_minus_eq : forall Θ Δ1 Δ2,
    Δ1 [=] Δ2 -> aenv_minus Θ Δ1 = aenv_minus Θ Δ2.
Proof.
  intros Θ Δ1 Δ2 HΔ. unfold aenv_minus. apply List.filter_ext.
  intros [x b]. simpl. f_equal.
  destruct (AtomSetImpl.mem x Δ1) eqn:H1; destruct (AtomSetImpl.mem x Δ2) eqn:H2;
    try reflexivity.
  - rewrite <- mem_iff in H1. rewrite <- not_mem_iff in H2. fsetdec.
  - rewrite <- not_mem_iff in H1. rewrite <- mem_iff in H2. fsetdec.
Qed.

Lemma binds_aenv_minus : forall α b Θ Δ,
    binds α b (aenv_minus Θ Δ) <-> binds α b Θ /\ α `notin` Δ.
Proof.
  intros α b Θ Δ. unfold binds, aenv_minus. rewrite filter_In. simpl.
  rewrite negb_true_iff, <- not_mem_iff. reflexivity.
Qed.

Lemma a_binds_tvar_aenv_minus : forall α Θ Δ,
    a_binds_tvar α (aenv_minus Θ Δ) <-> a_binds_tvar α Θ /\ α `notin` Δ.
Proof.
  intros α Θ Δ. unfold a_binds_tvar. split.
  - intros [H | [H | [τ H]]]; apply binds_aenv_minus in H; destruct H;
      split; eauto.
  - intros [[H | [H | [τ H]]] Hn].
    + left. apply binds_aenv_minus; auto.
    + right; left. apply binds_aenv_minus; auto.
    + right; right. exists τ. apply binds_aenv_minus; auto.
Qed.

Lemma dom_aenv_minus : forall α Θ Δ,
    α `in` dom (aenv_minus Θ Δ) -> α `in` dom Θ /\ α `notin` Δ.
Proof.
  intros α Θ Δ. induction Θ as [|[a b] Θ IH]; simpl; intro H.
  - fsetdec.
  - unfold aenv_minus in H. simpl in H.
    destruct (AtomSetImpl.mem a Δ) eqn:Hm; simpl in H.
    + destruct (IH H). split; [ fsetdec | assumption ].
    + apply add_iff in H. destruct H as [<- | H].
      * split; [ fsetdec | apply not_mem_iff; assumption ].
      * destruct (IH H). split; [ fsetdec | assumption ].
Qed.

Inductive a_wf_pskl : aenv -> atoms -> pskl -> Prop :=
| a_wf_pskl__unit : forall Θ Δ,
    {{ Θ ⨟ Δ ⊢ₚₛ pskl_unit }}a
| a_wf_pskl__var : forall Θ Δ α,
    a_binds_tvar α Θ ->
    {{ Θ ⨟ Δ ⊢ₚₛ (pskl_var_f α) }}a
| a_wf_pskl__arrow : forall Θ Δ P1 P2,
    {{ Θ ⨟ Δ ⊢ₚₛ P1 }}a ->
    {{ Θ ⨟ Δ ⊢ₚₛ P2 }}a ->
    {{ Θ ⨟ Δ ⊢ₚₛ (pskl_arrow P1 P2) }}a
| a_wf_pskl__all : forall L Θ Δ P,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ₚₛ
         (open_pskl_wrt_pskl P (pskl_var_f α)) }}a) ->
    {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}a
| a_wf_pskl__ghost : forall Θ Δ,
    {{ Θ ⨟ Δ ⊢ₚₛ pskl_ghost }}a
| a_wf_pskl__univ_ghost : forall Θ Δ P,
    guarded_pskl P ->
    {{ (aenv_minus Θ Δ) ⨟ empty ⊢ₚₛ P }}a ->
    {{ Θ ⨟ Δ ⊢ₚₛ (pskl_univ_ghost P) }}a
where "{{ Θ ⨟ Δ ⊢ₚₛ P }}a" := (a_wf_pskl Θ Δ P) : fresco_a_scope.

Lemma a_binds_tvar_cons_tvar_inv : forall α β Θ,
    a_binds_tvar β ((α ~ abind_tvar) ++ Θ) -> β = α \/ a_binds_tvar β Θ.
Proof.
  intros α β Θ [Hb | [Hb | [τ Hb]]]; apply binds_app_iff in Hb;
    destruct Hb as [Hb | Hb]; try (apply binds_one_iff in Hb; destruct Hb as [? Hb]);
    try discriminate; unfold a_binds_tvar; eauto.
Qed.

Lemma a_binds_tvar_cons_tvar : forall α β Θ,
    β = α \/ a_binds_tvar β Θ -> a_binds_tvar β ((α ~ abind_tvar) ++ Θ).
Proof.
  intros α β Θ [-> | [Hb | [Hb | [τ Hb]]]]; unfold a_binds_tvar.
  - left. apply binds_app_iff. left. apply binds_one_iff. auto.
  - left. apply binds_app_iff. auto.
  - right; left. apply binds_app_iff. auto.
  - right; right. exists τ. apply binds_app_iff. auto.
Qed.

Lemma a_wf_pskl_tvar_mono_ftv : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ', (forall α, α `in` ftvar_in_pskl P ->
                        a_binds_tvar α Θ -> a_binds_tvar α Θ') ->
  {{ Θ' ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P H; induction H; intros Θ' Hincl; simpl in Hincl.
  - constructor.
  - constructor. apply Hincl; [ clear; fsetdec | assumption ].
  - constructor; [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      intros β Hβ Hb; apply Hincl; solve [ clear - Hβ; fsetdec | exact Hb ].
  - apply a_wf_pskl__all with (L := L). intros α Hα.
    apply H0; [ exact Hα | ].
    intros β Hβ Hb. apply a_binds_tvar_cons_tvar.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                  P (pskl_var_f α)) as Hup; simpl in Hup.
    destruct (eq_var β α) as [-> | Hne]; [ left; reflexivity | right ].
    destruct (a_binds_tvar_cons_tvar_inv Hb) as [-> | Hb']; [ congruence | ].
    apply Hincl; [ clear - Hup Hβ Hne; fsetdec | exact Hb' ].
  - constructor.
  - constructor; [ assumption | ]. apply IHa_wf_pskl.
    intros β Hβ Hb. apply a_binds_tvar_aenv_minus in Hb. destruct Hb as [Hb Hn].
    apply a_binds_tvar_aenv_minus. split; [ apply Hincl; assumption | exact Hn ].
Qed.

Lemma a_wf_pskl_tvar_mono : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ', (forall α, a_binds_tvar α Θ -> a_binds_tvar α Θ') ->
  {{ Θ' ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P H Θ' Hincl.
  apply (a_wf_pskl_tvar_mono_ftv H). intros α _. apply Hincl.
Qed.

Reserved Notation "{{ ⊢ Θ }}a"
  (at level 0, format "'{{'  ⊢  Θ  '}}a'").

Inductive a_wf_aenv : aenv -> Prop :=
| a_wf_aenv__nil :
    {{ ⊢ nil }}a
| a_wf_aenv__flex : forall α Θ,
    α `notin` dom Θ ->
    {{ ⊢ Θ }}a ->
    {{ ⊢ ((α ~ abind_flex_mono) ++ Θ) }}a
| a_wf_aenv__flex_def : forall α τ Θ,
    α `notin` dom Θ ->
    a_wf_ptyp Θ τ ->
    mono_ptyp τ ->
    {{ ⊢ Θ }}a ->
    {{ ⊢ ((α ~ abind_flex_mono_def τ) ++ Θ) }}a
| a_wf_aenv__var : forall x P Θ,
    x `notin` dom Θ ->
    {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
    {{ ⊢ Θ }}a ->
    {{ ⊢ ((x ~ abind_var_skl P) ++ Θ) }}a
| a_wf_aenv__var_typ : forall x A Θ,
    x `notin` dom Θ ->
    a_wf_ptyp Θ A ->
    {{ ⊢ Θ }}a ->
    {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a
| a_wf_aenv__tvar : forall α Θ,
    α `notin` dom Θ ->
    {{ ⊢ Θ }}a ->
    {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a
where "{{ ⊢ Θ }}a" := (a_wf_aenv Θ) : fresco_a_scope.

Inductive a_ty_mode_compat : mode -> pskl -> Prop :=
| a_ty_mode_compat__ti :
    a_ty_mode_compat mode_ti pskl_ghost
| a_ty_mode_compat__tc : forall A,

    a_ty_mode_compat mode_tc (ptyp_to_pskl A)
| a_ty_mode_compat__fn : forall M P Q,
    a_ty_mode_compat M Q ->
    a_ty_mode_compat (mode_fn M) (pskl_arrow P Q).

Inductive a_sk_mode_compat : mode -> pskl -> Prop :=
| a_sk_mode_compat__ti :
    a_sk_mode_compat mode_ti pskl_ghost
| a_sk_mode_compat__tc :
    a_sk_mode_compat mode_tc pskl_ghost
| a_sk_mode_compat__fn : forall M P Q,
    a_sk_mode_compat M Q ->
    a_sk_mode_compat (mode_fn M) (pskl_arrow P Q).

Inductive a_sub_mode : Set :=
| a_sub_mode_ty : a_sub_mode
| a_sub_mode_sk : a_sub_mode.

Inductive a_flex : aenv -> pskl -> Prop :=
| a_flex__var : forall Θ α,
    binds α abind_flex_mono Θ ->
    a_flex Θ (pskl_var_f α)
| a_flex__var_def : forall Θ α τ,
    binds α (abind_flex_mono_def τ) Θ ->
    a_flex Θ (pskl_var_f α).

Definition a_non_flex (Θ : aenv) (P : pskl) : Prop :=
  lc_pskl P /\ ~ a_flex Θ P.

Definition a_flex_tvar (Θ : aenv) (α : atom) : Prop :=
  binds α abind_flex_mono Θ \/
  (exists τ, binds α (abind_flex_mono_def τ) Θ).

Definition flex_r_off (Θ : aenv) (P' : pskl) : Prop :=
  forall β, P' = pskl_var_f β -> ~ a_flex_tvar Θ β.

Lemma flex_r_off_nonvar : forall Θ P',
  (forall β, P' <> pskl_var_f β) -> flex_r_off Θ P'.
Proof. intros Θ P' H β Heq; exfalso; exact (H β Heq). Qed.

Lemma flex_r_off_rigid : forall Θ β,
  ~ a_flex_tvar Θ β -> flex_r_off Θ (pskl_var_f β).
Proof. intros Θ β H β0 Heq; injection Heq as ->; exact H. Qed.

Inductive a_guess_mono : aenv -> pskl -> aenv -> ptyp -> Prop :=
| a_guess_mono__ghost : forall Θ α,
    α `notin` ftvar_in_aenv Θ ->
    a_guess_mono Θ pskl_ghost ((α ~ abind_flex_mono) ++ nil) (ptyp_var_f α)
| a_guess_mono__univ_ghost : forall Θ P Ξ A,
    a_guess_mono Θ P Ξ A ->
    a_guess_mono Θ (pskl_univ_ghost P) Ξ A
| a_guess_mono__var : forall Θ α,
    a_guess_mono Θ (pskl_var_f α) nil (ptyp_var_f α)
| a_guess_mono__unit : forall Θ,
    a_guess_mono Θ pskl_unit nil ptyp_unit
| a_guess_mono__arrow : forall Θ P Q Ξ1 Ξ2 A B,
    a_guess_mono Θ P Ξ1 A ->
    a_guess_mono Θ Q Ξ2 B ->
    a_guess_mono Θ (pskl_arrow P Q) (Ξ1 ++ Ξ2) (ptyp_arrow A B)
| a_guess_mono__forall : forall Θ P Ξ A β,
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P ->
    a_guess_mono ((β ~ abind_tvar) ++ Θ)
      (open_pskl_wrt_pskl P (pskl_var_f β)) Ξ A ->
    a_guess_mono Θ (pskl_all_syn P) Ξ (ptyp_all (close_ptyp_wrt_ptyp β A)).

Inductive a_guess : aenv -> a_sub_mode -> pskl -> aenv -> pskl -> Prop :=
| a_guess__sk : forall Θ Q,
    a_guess Θ a_sub_mode_sk Q nil Q
| a_guess__ty : forall Θ Q Ξ A,
    a_guess_mono Θ Q Ξ A ->
    a_guess Θ a_sub_mode_ty Q Ξ (ptyp_to_pskl A).

Inductive a_cstr : Set :=
| a_cstr_sub : mode -> pskl -> a_cstr
| a_cstr_eq : pskl -> a_cstr.
Definition a_cstrs : Set := list a_cstr.

Definition ftvar_in_a_cstr (c : a_cstr) : atoms :=
  match c with
  | a_cstr_sub _ P => ftvar_in_pskl P
  | a_cstr_eq P    => ftvar_in_pskl P
  end.

Fixpoint ftvar_in_a_cstrs (C : a_cstrs) : atoms :=
  match C with
  | nil      => empty
  | c :: C'  => ftvar_in_a_cstr c `union` ftvar_in_a_cstrs C'
  end.

Lemma ftvar_in_a_cstrs_app : forall C1 C2,
  ftvar_in_a_cstrs (C1 ++ C2)
  [=] ftvar_in_a_cstrs C1 `union` ftvar_in_a_cstrs C2.
Proof.
  induction C1 as [ | c C1' IH ]; intros; simpl; [ fsetdec | ].
  rewrite IH. fsetdec.
Qed.

Reserved Notation "{{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a"
  (at level 0, P at level 74, α at level 0, m at level 0, P' at level 74, Ξ at level 74, C at level 74,
   format "'{{'  Θ  ⊢  P  ≼[  α  ,  m  ]  P'  ⤳  Ξ  ⨾  C  '}}a'").
Reserved Notation "{{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a"
  (at level 0, P at level 74, α at level 0, P' at level 74, Ξ at level 74, C at level 74,
   format "'{{'  Θ  ⊢  P  ∼[  α  ]  P'  ⤳  Ξ  ⨾  C  '}}a'").

Inductive a_looksub : aenv -> atom -> mode -> pskl -> pskl -> aenv -> a_cstrs -> Prop :=
| a_looksub__var : forall Θ α m P,
    {{ Θ ⊢ (pskl_var_f α) ≼[ α , m ] P ⤳ nil ⨾ (a_cstr_sub m P :: nil) }}a
| a_looksub__absent : forall Θ α m P P',
    α `notin` ftvar_in_pskl P ->
    {{ Θ ⊢ P ≼[ α , m ] P' ⤳ nil ⨾ nil }}a
| a_looksub__vacuous : forall Θ α m P,
    P <> pskl_var_f α ->
    {{ Θ ⊢ P ≼[ α , m ] pskl_ghost ⤳ nil ⨾ nil }}a
| a_looksub__check : forall Θ α A B Ξ C,
    pskl_ghost_free B ->
    A <> pskl_var_f α ->
    guarded_pskl A ->
    guarded_pskl B ->
    {{ Θ ⊢ A ∼[ α ] B ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ A ≼[ α , mode_tc ] B ⤳ Ξ ⨾ C }}a
| a_looksub__forall_r : forall Θ α A B Ξ C β,
    pskl_ghost_free (pskl_all_syn B) ->
    β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl A
                       `union` ftvar_in_pskl B) ->
    α `in` ftvar_in_pskl A ->
    A <> pskl_var_f α ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ A ≼[ α , mode_tc ]
      (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ A ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C }}a
| a_looksub__arrow : forall Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,
    ftvar_in_a_cstrs C1 ∩ dom Ξ2 [=] empty ->
    ftvar_in_a_cstrs C2 ∩ dom Ξ1 [=] empty ->
    {{ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}a ->
    {{ Θ ⊢ P2 ≼[ α , m ] P2' ⤳ Ξ2 ⨾ C2 }}a ->
    {{ Θ ⊢ (pskl_arrow P1 P2) ≼[ α , (mode_fn m) ] (pskl_arrow P1' P2')
        ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2) }}a
| a_looksub__forall_l : forall Θ α m P P' Ξ C β,
    β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                       `union` ftvar_in_pskl P') ->

    α `in` ftvar_in_pskl (pskl_all_syn P) ->
    P' <> pskl_ghost ->
    forall_r_off m P' ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β))
      ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_all_syn P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a
| a_looksub__univ_ghost_l : forall Θ α m P P' Ξ C,
    P' <> pskl_ghost ->

    forall_r_off m P' ->
    {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_univ_ghost P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a

with a_lookeq : aenv -> atom -> pskl -> pskl -> aenv -> a_cstrs -> Prop :=
| a_lookeq__var : forall Θ α P,
    {{ Θ ⊢ (pskl_var_f α) ∼[ α ] P ⤳ nil ⨾ (a_cstr_eq P :: nil) }}a
| a_lookeq__absent : forall Θ α P P',
    α `notin` ftvar_in_pskl P ->
    {{ Θ ⊢ P ∼[ α ] P' ⤳ nil ⨾ nil }}a
| a_lookeq__vacuous : forall Θ α P,
    P <> pskl_var_f α ->
    {{ Θ ⊢ P ∼[ α ] pskl_ghost ⤳ nil ⨾ nil }}a
| a_lookeq__flex_r : forall Θ α P β α1,
    α1 `notin` add α (add β (ftvar_in_aenv Θ `union` ftvar_in_pskl P)) ->
    a_flex_tvar Θ β ->
    P <> pskl_var_f α ->
    α `in` ftvar_in_pskl P ->
    {{ Θ ⊢ P ∼[ α ] (pskl_var_f β) ⤳ ((α1 ~ abind_flex_mono) ++ nil)
        ⨾ (a_cstr_eq (pskl_var_f α1) :: nil) }}a
| a_lookeq__arrow : forall Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,

    ftvar_in_a_cstrs C1 ∩ dom Ξ2 [=] empty ->
    ftvar_in_a_cstrs C2 ∩ dom Ξ1 [=] empty ->
    {{ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}a ->
    {{ Θ ⊢ P2 ∼[ α ] P2' ⤳ Ξ2 ⨾ C2 }}a ->
    {{ Θ ⊢ (pskl_arrow P1 P2) ∼[ α ] (pskl_arrow P1' P2')
        ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2) }}a
| a_lookeq__forall_inh : forall Θ α P P' Ξ C β,
    β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                       `union` ftvar_in_pskl P') ->

    α `in` ftvar_in_pskl (pskl_all_syn P) ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
      (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}a
| a_lookeq__forall_syn : forall Θ α P P' Ξ C β,
    β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                       `union` ftvar_in_pskl P') ->

    α `in` ftvar_in_pskl (pskl_all_syn P) ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
      (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}a
| a_lookeq__univ_ghost : forall Θ α P P' Ξ C,
    {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_univ_ghost P) ∼[ α ] (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}a
| a_lookeq__univ_ghost1 : forall Θ α P P' Ξ C β,
    β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                       `union` ftvar_in_pskl P') ->

    α `in` ftvar_in_pskl (pskl_univ_ghost P) ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (pskl_univ_ghost P) ∼[ α ]
      (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_univ_ghost P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}a
| a_lookeq__univ_ghost2 : forall Θ α P P' Ξ C,
    guarded_pskl P' ->
    flex_r_off Θ P' ->
    {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_univ_ghost P) ∼[ α ] P' ⤳ Ξ ⨾ C }}a
| a_lookeq__univ_ghost_r : forall Θ α P P' Ξ C,
    P <> pskl_var_f α ->
    guarded_pskl P ->
    {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ P ∼[ α ] (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}a
where "{{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a" := (a_looksub Θ α m P P' Ξ C) : fresco_a_scope
  and "{{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a" := (a_lookeq Θ α P P' Ξ C) : fresco_a_scope.

Reserved Notation "{{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a"
  (at level 0, P at level 74, m at level 0, Q at level 74, Ξ at level 74, P' at level 74,
   format "'{{'  Θ  ⊢ₛ  P  ≼[  m  ]  Q  ⤳  Ξ  ⨾  P'  '}}a'").
Reserved Notation "{{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a"
  (at level 0, P at level 74, Q at level 74, Ξ at level 74, P' at level 74,
   format "'{{'  Θ  ⊢ₑ  P  ∼  Q  ⤳  Ξ  ⨾  P'  '}}a'").

Inductive a_solve_sub : aenv -> mode -> pskl -> pskl -> aenv -> pskl -> Prop :=
| a_solve_sub__var : forall Θ m α Q,
    {{ Θ ⊢ₛ (pskl_var_f α) ≼[ m ] Q ⤳ nil ⨾ (pskl_var_f α) }}a
| a_solve_sub__forall_l : forall Θ m P Q Ξ P' β,
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f β))
      ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₛ (pskl_all_syn P) ≼[ m ] Q
         ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}a
| a_solve_sub__univ_ghost_l : forall Θ m P Q Ξ P',
    {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₛ (pskl_univ_ghost P) ≼[ m ] Q ⤳ Ξ ⨾ (pskl_univ_ghost P') }}a
| a_solve_sub__vacuous : forall Θ m P,
    peel_l_off P ->
    {{ Θ ⊢ₛ P ≼[ m ] pskl_ghost ⤳ nil ⨾ P }}a
| a_solve_sub__check : forall Θ P Q Ξ P',
    pskl_ghost_free Q ->
    guarded_pskl P ->
    guarded_pskl Q ->
    {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₛ P ≼[ mode_tc ] Q ⤳ Ξ ⨾ P' }}a
| a_solve_sub__forall_r : forall Θ P B Ξ P' β,
    pskl_ghost_free (pskl_all_syn B) ->
    solve_l_off P ->
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl B ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
      (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a
| a_solve_sub__arrow : forall Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2',
    {{ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}a ->
    {{ (Ξ1 ++ Θ) ⊢ₛ P2 ≼[ m ] Q2 ⤳ Ξ2 ⨾ P2' }}a ->
    {{ Θ ⊢ₛ (pskl_arrow P1 P2) ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
         ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_arrow P1' P2') }}a
| a_solve_sub__ghost_l_fn : forall Θ m Q1 Q2 Ξ1 Ξ2 P1' P2',
    {{ Θ ⊢ₑ pskl_ghost ∼ Q1 ⤳ Ξ1 ⨾ P1' }}a ->
    {{ (Ξ1 ++ Θ) ⊢ₛ pskl_ghost ≼[ m ] Q2 ⤳ Ξ2 ⨾ P2' }}a ->
    {{ Θ ⊢ₛ pskl_ghost ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
         ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_univ_ghost (pskl_arrow P1' P2')) }}a
| a_solve_sub__ghost_l : forall Θ B,

    pskl_ghost_free B ->
    guarded_pskl B ->
    {{ Θ ⊢ₛ pskl_ghost ≼[ mode_tc ] B ⤳ nil ⨾ (pskl_univ_ghost B) }}a

with a_solve_eq : aenv -> pskl -> pskl -> aenv -> pskl -> Prop :=
| a_solve_eq__unit : forall Θ,
    {{ Θ ⊢ₑ pskl_unit ∼ pskl_unit ⤳ nil ⨾ pskl_unit }}a
| a_solve_eq__var : forall Θ α Q,
    {{ Θ ⊢ₑ (pskl_var_f α) ∼ Q ⤳ nil ⨾ (pskl_var_f α) }}a
| a_solve_eq__flex_r : forall Θ α P Ξ A,
    a_flex_tvar Θ α ->
    a_non_flex Θ P ->
    nonghost_pskl P ->
    a_guess_mono Θ P Ξ A ->
    {{ Θ ⊢ₑ P ∼ (pskl_var_f α) ⤳ Ξ ⨾ (ptyp_to_pskl A) }}a
| a_solve_eq__ghost_l : forall Θ Q,
    {{ Θ ⊢ₑ pskl_ghost ∼ Q ⤳ nil ⨾ Q }}a
| a_solve_eq__ghost_r : forall Θ P,
    {{ Θ ⊢ₑ P ∼ pskl_ghost ⤳ nil ⨾ P }}a
| a_solve_eq__arrow : forall Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2',

    {{ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}a ->
    {{ (Ξ1 ++ Θ) ⊢ₑ P2 ∼ Q2 ⤳ Ξ2 ⨾ P2' }}a ->
    {{ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2)
         ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_arrow P1' P2') }}a
| a_solve_eq__forall : forall Θ P Q Ξ P' β,
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
         ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_all_syn Q)
         ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}a
| a_solve_eq__univ_ghost_both : forall Θ P Q Ξ P',
    {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ (pskl_univ_ghost P) ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ (pskl_univ_ghost P') }}a
| a_solve_eq__univ_ghost_l_all : forall Θ P Q Ξ P' β,
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (pskl_univ_ghost P)
      ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ (pskl_univ_ghost P) ∼ (pskl_all_syn Q)
         ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}a
| a_solve_eq__univ_ghost_l_guarded : forall Θ P Q Ξ P',
    guarded_pskl Q ->
    {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ (pskl_univ_ghost P) ∼ Q ⤳ Ξ ⨾ P' }}a
| a_solve_eq__all_l_univ_ghost : forall Θ P Q Ξ P' β,
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
      ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_univ_ghost Q)
         ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}a
| a_solve_eq__univ_ghost_r_guarded : forall Θ P Q Ξ P',
    guarded_pskl P ->
    {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ P ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ P' }}a
where "{{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a" := (a_solve_sub Θ m P Q Ξ P') : fresco_a_scope
  and "{{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a" := (a_solve_eq Θ P Q Ξ P') : fresco_a_scope.

Reserved Notation "{{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}a"
  (at level 0, C at level 74, P at level 74, Ξ at level 74, Q at level 74,
   format "'{{'  Θ  ⊩  C  ⨾  P  ⤳  Ξ  ⨾  Q  '}}a'").

Inductive a_solve_cstr : aenv -> a_cstrs -> pskl -> aenv -> pskl -> Prop :=
| a_solve_cstr__empty : forall Θ P,
    {{ Θ ⊩ nil ⨾ P ⤳ nil ⨾ P }}a
| a_solve_cstr__sub : forall Θ m Q P Ξ P',
    {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊩ (a_cstr_sub m Q :: nil) ⨾ P ⤳ Ξ ⨾ P' }}a
| a_solve_cstr__eq : forall Θ Q C P Ξ1 Ξ2 P' P'',
    {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}a ->
    {{ (Ξ1 ++ Θ) ⊩ C ⨾ P'' ⤳ Ξ2 ⨾ P' }}a ->
    {{ Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ (Ξ2 ++ Ξ1) ⨾ P' }}a
where "{{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}a" := (a_solve_cstr Θ C P Ξ Q) : fresco_a_scope.

Reserved Notation "{{ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}a"
  (at level 0, P at level 74, NM at level 0, α at level 0, m at level 0, P' at level 74, Ξ at level 74, Q at level 74,
   format "'{{'  Θ0  ⊢  P  ⊳[  NM  ,  α  ,  m  ]  P'  ⤳  Ξ  ↪  Q  '}}a'").
Inductive a_extract : aenv -> a_sub_mode -> atom -> mode -> pskl -> pskl -> aenv -> pskl -> Prop :=
| a_extract__solve : forall Θ0 NM α m P P' Ξ Ξs Ξ' C Q Q',
    {{ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
    {{ (Ξ ++ Θ0) ⊩ C ⨾ pskl_ghost ⤳ Ξs ⨾ Q }}a ->
    a_guess (Ξs ++ Ξ ++ Θ0) NM Q Ξ' Q' ->
    ftvar_in_a_cstrs C ∩ dom Ξs [=] empty ->
    (ftvar_in_a_cstrs C ∪ ftvar_in_pskl Q) ∩ dom Ξ' [=] empty ->
    {{ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ (Ξ ++ Ξs ++ Ξ') ↪ Q' }}a
where "{{ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}a" := (a_extract Θ0 NM α m P P' Ξ Q) : fresco_a_scope.

Inductive a_assign : aenv -> aenv -> atom -> pskl -> aenv -> Prop :=
| a_assign__univ_ghost_id : forall Θ0 α,
    {{ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ nil ] α ≔ (pskl_univ_ghost (pskl_var_f α))
      ⊣ ((α ~ abind_flex_mono) ++ Θ0) }}a
| a_assign__solve_m : forall Θ0 Ξ α P βs τ,
    α `notin` ftvar_in_pskl P ->
    a_guess_mono Θ0 P βs τ ->
    mono_ptyp τ ->

    uniq βs ->
    (forall α1, α1 `in` dom βs ->
       α1 `notin` add α (dom (Ξ ++ Θ0))) ->
    {{ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0) }}a
| a_assign__assign : forall Θ0 Θ1 Ξ α β τ P Q,
    a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α ->
    β `notin` dom Θ1 ->
    {{ (Ξ ++ Θ0) ⊢[ empty | empty
         | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) ]
      (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ∼ Q ⊣ Θ1 }}a ->
    {{ ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((β ~ abind_flex_mono_def τ) ++ Θ1) }}a
| a_assign__depend : forall Θ0 Θ1 Ξ α β P,
    α <> β ->
    β `in` ftvar_in_pskl P ->
    {{ Θ0 ⊲[ Ξ ++ (β ~ abind_flex_mono) ] α ≔ P ⊣ Θ1 }}a ->
    {{ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a
| a_assign__skip : forall Θ0 Θ1 Ξ α β P,
    α <> β ->
    β `notin` ftvar_in_pskl P ->
    β `notin` dom Θ1 ->
    {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
    {{ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((β ~ abind_flex_mono) ++ Θ1) }}a
| a_assign__skip_rigid : forall Θ0 Θ1 Ξ α β P,
    β `notin` ftvar_in_pskl P ->
    β `notin` dom Θ1 ->
    {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
    {{ ((β ~ abind_tvar) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ ((β ~ abind_tvar) ++ Θ1) }}a
| a_assign__skip_tm_var : forall Θ0 Θ1 Ξ α x A P,

    x `notin` dom Θ1 ->
    {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
    {{ ((x ~ abind_var_typ A) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((x ~ abind_var_typ A) ++ Θ1) }}a
| a_assign__skip_tm_skl : forall Θ0 Θ1 Ξ α x Q P,
    x `notin` dom Θ1 ->
    {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
    {{ ((x ~ abind_var_skl Q) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((x ~ abind_var_skl Q) ++ Θ1) }}a

with a_unify : aenv -> atom -> atom -> aenv -> Prop :=
| a_unify__flex_id : forall Θ0 α,
    a_flex_tvar Θ0 α ->
    {{ Θ0 ⊲ α ≈ᵘ α ⊣ Θ0 }}a
| a_unify__flex_l : forall Θ0 α β,
    α <> β ->

    a_flex_tvar Θ0 β ->
    {{ ((α ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
      ⊣ ((α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0) }}a
| a_unify__flex_r : forall Θ0 α β,
    α <> β ->
    a_flex_tvar Θ0 α ->
    {{ ((β ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
      ⊣ ((β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0) }}a
| a_unify__flex_assign : forall Θ0 Θ1 α1 τ α β Q,
    a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) α ->
    a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β ->
    α1 `notin` dom Θ1 ->
    {{ Θ0 ⊢[ empty | empty
         | (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β))) ]
      (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))) ∼ Q ⊣ Θ1 }}a ->
    {{ ((α1 ~ abind_flex_mono_def τ) ++ Θ0) ⊲ α ≈ᵘ β
      ⊣ ((α1 ~ abind_flex_mono_def τ) ++ Θ1) }}a
| a_unify__flex_skip : forall Θ0 Θ1 α1 α β,
    α1 <> α ->
    α1 <> β ->
    α1 `notin` dom Θ1 ->
    {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
    {{ ((α1 ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ ((α1 ~ abind_flex_mono) ++ Θ1) }}a
| a_unify__skip_other : forall Θ0 Θ1 c b α β,
    (b = abind_tvar \/
     (exists A, b = abind_var_typ A) \/
     (exists Q, b = abind_var_skl Q)) ->
    c `notin` dom Θ1 ->
    {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
    {{ ((c ~ b) ++ Θ0) ⊲ α ≈ᵘ β ⊣ ((c ~ b) ++ Θ1) }}a

with a_consis : atoms -> atoms -> aenv -> pskl -> pskl -> pskl -> aenv -> Prop :=
| a_consis__ghost : forall Δ1 Δ2 Θ0 P0,
    Δ2 ∩ ftvar_in_pskl P0 [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] pskl_ghost ∼ P0 ⊣ Θ0 }}a
| a_consis__unit : forall Δ1 Δ2 Θ0,
    {{ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ] pskl_unit ∼ pskl_unit ⊣ Θ0 }}a
| a_consis__rigid : forall Δ1 Δ2 Θ0 α,
    binds α abind_tvar Θ0 ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ] (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ0 }}a
| a_consis__arrow : forall Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2,
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θ1 }}a ->
    {{ Θ1 ⊢[ Δ1 | Δ2 | P0b ] P2 ∼ Q2 ⊣ Θ2 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ]
      (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2) ⊣ Θ2 }}a
| a_consis__forall_inh : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,
    α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
      `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ (add α Δ1) | (add α Δ2)
        | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
      (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
      ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
      (pskl_all_syn P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}a
| a_consis__forall_syn : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,
    α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
      `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ Δ1 | (add α Δ2) | (pskl_univ_ghost P0) ]
      (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
      ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
      (pskl_all_syn P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}a
| a_consis__univ_ghost : forall Δ1 Δ2 Θ0 Θ1 P0 P Q,
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
      (pskl_univ_ghost P) ∼ (pskl_univ_ghost Q) ⊣ Θ1 }}a
| a_consis__univ_ghost1 : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,

    α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
      `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ (add α Δ1) | Δ2
        | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
      (pskl_univ_ghost P) ∼ Q
      ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
      (pskl_univ_ghost P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}a
| a_consis__univ_ghost2 : forall Δ1 Δ2 Θ0 Θ1 P0 P Q,
    guarded_pskl P0 ->
    a_non_flex Θ0 P0 ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_univ_ghost P) ∼ Q ⊣ Θ1 }}a
| a_consis__flex : forall Δ1 Δ2 Θ0 Θ1 α β,
    {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ] (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ1 }}a
| a_consis__flex_l : forall Δ1 Δ2 Θ0 Θ1 α P0,
    a_non_flex Θ0 P0 ->
    P0 <> pskl_ghost ->
    {{ Θ0 ⊲[ nil ] α ≔ P0 ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ1 }}a
| a_consis__flex_r : forall Δ1 Δ2 Θ0 Θ1 α P,
    a_non_flex Θ0 P ->
    P <> pskl_ghost ->
    {{ Θ0 ⊲[ nil ] α ≔ P ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ] P ∼ (pskl_var_f α) ⊣ Θ1 }}a
| a_consis__ghost_r : forall Δ1 Δ2 Θ0 P,
    Δ1 ∩ ftvar_in_pskl P [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | pskl_ghost ] P ∼ P ⊣ Θ0 }}a
| a_consis__univ_ghost_r : forall Δ1 Δ2 Θ0 Θ1 P0 P Q,
    guarded_pskl P ->
    a_non_flex Θ0 P ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ] P ∼ Q ⊣ Θ1 }}a
where "{{ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}a" := (a_assign Θ Ξ α P Θ') : fresco_a_scope
and "{{ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}a" := (a_unify Θ α β Θ') : fresco_a_scope
and "{{ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}a" :=
  (a_consis Δ1 Δ2 Θ P0 P Q Θ') : fresco_a_scope.

Scheme a_assign_mind := Induction for a_assign Sort Prop
  with a_unify_mind  := Induction for a_unify  Sort Prop
  with a_consis_mind := Induction for a_consis Sort Prop.
Combined Scheme a_assign_unify_consis_mutind
  from a_assign_mind, a_unify_mind, a_consis_mind.

Notation "{{ Θ ⊢[ P0 ] P ∼ Q ⊣ Θ' }}a" := (a_consis empty empty Θ P0 P Q Θ')
  (at level 0, P0 at level 0, P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢[  P0  ]  P  ∼  Q  ⊣  Θ'  '}}a'") : fresco_a_scope.

Definition a_consis_chk (Θ0 : aenv) (P P0 : pskl) (Θ1 : aenv) : Prop :=
  exists Q, {{ Θ0 ⊢[ P0 ] P ∼ Q ⊣ Θ1 }}a.

Inductive a_sub : a_sub_mode -> mode -> pskl -> aenv -> pskl -> pskl -> aenv -> Prop :=
| a_sub__infer : forall NM P Θ0,
    a_sub NM mode_ti pskl_ghost Θ0 P P Θ0
| a_sub__check : forall Θ0 Θ1 A B,
    pskl_ghost_free A -> pskl_ghost_free B ->
    guarded_pskl A -> guarded_pskl B ->
    a_consis_chk Θ0 A B Θ1 ->
    a_sub a_sub_mode_ty mode_tc B Θ0 A B Θ1
| a_sub__forall_r : forall α Θ0 Θ1 Ξ A B,
    pskl_ghost_free (pskl_all_syn B) ->
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->
    α `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union`
      ftvar_in_pskl A `union` ftvar_in_pskl B ->
    a_sub a_sub_mode_ty mode_tc (open_pskl_wrt_pskl B (pskl_var_f α))
      ((α ~ abind_tvar) ++ Θ0) A (open_pskl_wrt_pskl B (pskl_var_f α))
      (Ξ ++ (α ~ abind_tvar) ++ Θ1) ->
    a_sub a_sub_mode_ty mode_tc (pskl_all_syn B) Θ0 A (pskl_all_syn B) Θ1
| a_sub__univ_ghost_r : forall Θ0 P,
    guarded_pskl P ->
    a_sub a_sub_mode_sk mode_tc pskl_ghost Θ0 P (pskl_univ_ghost P) Θ0
| a_sub__flex_mono : forall NM M P0 Θ0 Θ1 α Q,
    a_sub_flex NM M P0 Θ0 nil α Q Θ1 ->
    a_sub NM (mode_fn M) P0 Θ0 (pskl_var_f α) Q Θ1
| a_sub__arrow : forall NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2,
    {{ Θ0 ⊢[ P0a ] P1 ∼ Q1 ⊣ Θ1 }}a ->
    a_sub NM M P0b Θ1 P2 Q2 Θ2 ->
    a_sub NM (mode_fn M) (pskl_arrow P0a P0b) Θ0 (pskl_arrow P1 P2)
      (pskl_arrow Q1 Q2) Θ2
| a_sub__forall_l : forall α NM M P0 Θ0 Θ1 P Q Ξ P1,
    M <> mode_ti ->
    (guarded_pskl P0 \/ P0 = pskl_ghost) ->
    α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P
      `union` ftvar_in_pskl P0 ->
    {{ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α)) ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}a ->
    uniq (Ξ ++ Θ0) ->
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
    a_sub NM M P0 (Ξ ++ Θ0) (open_pskl_wrt_pskl P P1) Q Θ1 ->
    a_sub NM M P0 Θ0 (pskl_all_syn P) Q Θ1
| a_sub__ghost : forall M Θ0 P0,
    M <> mode_ti ->
    a_sub a_sub_mode_sk M P0 Θ0 pskl_ghost P0 Θ0
| a_sub__univ_ghost_l : forall M Θ0 Θ1 P0 P Q,
    M <> mode_ti ->
    a_sub a_sub_mode_sk M P0 Θ0 P Q Θ1 ->
    a_sub a_sub_mode_sk M P0 Θ0 (pskl_univ_ghost P) Q Θ1

with a_sub_flex : a_sub_mode -> mode -> pskl -> aenv -> aenv -> atom -> pskl -> aenv -> Prop :=
| a_sub_flex__solve : forall NM M P0 Θ0 Θ1 Ξ α0 α β Q,

    α <> β ->
    α `notin` add α0 (dom (Ξ ++ Θ0)) ->
    β `notin` add α0 (dom (Ξ ++ Θ0)) ->
    a_sub NM (mode_fn M) P0
      (Ξ ++ (α0 ~ abind_flex_mono_def (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
          ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
      (pskl_arrow (pskl_var_f α) (pskl_var_f β)) Q Θ1 ->
    a_sub_flex NM M P0 ((α0 ~ abind_flex_mono) ++ Θ0) Ξ α0 Q Θ1
| a_sub_flex__assign : forall NM M P0 Θ0 Θ1 Ξ α β τ Q,
    β `notin` dom Θ1 ->
    a_sub NM (mode_fn M) (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
      (Ξ ++ Θ0)
      (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) Q Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α Q
      ((β ~ abind_flex_mono_def τ) ++ Θ1)
| a_sub_flex__depend : forall NM M P0 Θ0 Θ1 Ξ α β Q,
    α <> β ->
    β `in` ftvar_in_pskl P0 ->
    a_sub_flex NM M P0 Θ0 (Ξ ++ (β ~ abind_flex_mono)) α Q Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α Q Θ1
| a_sub_flex__skip : forall NM M P0 Θ0 Θ1 Ξ α β Q,
    α <> β ->
    β `notin` ftvar_in_pskl P0 ->
    β `notin` dom Θ1 ->
    a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α Q
      ((β ~ abind_flex_mono) ++ Θ1)
| a_sub_flex__skip_rigid : forall NM M P0 Θ0 Θ1 Ξ α β Q,
    α <> β ->
    β `notin` ftvar_in_pskl P0 ->
    β `notin` dom Θ1 ->
    a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_tvar) ++ Θ0) Ξ α Q ((β ~ abind_tvar) ++ Θ1)
| a_sub_flex__skip_tm_var : forall NM M P0 Θ0 Θ1 Ξ α x Apay Q,
    x `notin` dom Θ1 ->
    a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
    a_sub_flex NM M P0 ((x ~ abind_var_typ Apay) ++ Θ0) Ξ α Q
      ((x ~ abind_var_typ Apay) ++ Θ1)
| a_sub_flex__skip_tm_skl : forall NM M P0 Θ0 Θ1 Ξ α x Qpay Q,
    x `notin` dom Θ1 ->
    a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
    a_sub_flex NM M P0 ((x ~ abind_var_skl Qpay) ++ Θ0) Ξ α Q
      ((x ~ abind_var_skl Qpay) ++ Θ1).

Inductive a_split : aenv -> pskl -> pskl -> pskl -> aenv -> Prop :=
| a_split__arrow : forall Θ0 P Q,
    {{ Θ0 ⊲ (pskl_arrow P Q) ▹ P ⇢ Q ⊣ Θ0 }}a
| a_split__ghost : forall Θ0,
    {{ Θ0 ⊲ pskl_ghost ▹ pskl_ghost ⇢ pskl_ghost ⊣ Θ0 }}a
| a_split__flex : forall Θ0 Θ1 α β α1 Q,
    β `notin` ftvar_in_aenv Θ0 ->
    α1 `notin` add β (ftvar_in_aenv Θ0) ->
    {{ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θ0)
      ⊢[ empty | empty | (pskl_arrow (pskl_var_f β) (pskl_var_f α1)) ]
        (pskl_var_f α) ∼ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊲ (pskl_var_f α) ▹ (pskl_var_f β) ⇢ (pskl_var_f α1) ⊣ Θ1 }}a
where "{{ Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ' }}a" := (a_split Θ P0 P Q Θ') : fresco_a_scope
  and "{{ Θ ⊢[ N | m | P0 ] P ⩽ Q ⊣ Θ' }}a" := (a_sub N m P0 Θ P Q Θ') : fresco_a_scope.

Inductive a_pat : mode -> aenv -> pskl -> exp -> pskl -> aenv -> Prop :=
| a_pat__unit : forall m Θ0 Θ1 P0 P,
    {{ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] pskl_unit ⩽ P ⊣ Θ1 }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] exp_unit ⦂ P ⊣ Θ1 }}a
| a_pat__var : forall m Θ0 Θ1 P0 x A Q,
    binds x (abind_var_typ A) Θ0 ->
    {{ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] (ptyp_to_pskl A) ⩽ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] (exp_var_f x) ⦂ Q ⊣ Θ1 }}a
| a_pat__var_skl : forall m Θ0 Θ1 P0 x P Q,
    binds x (abind_var_skl P) Θ0 ->
    {{ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] P ⩽ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] (exp_var_f x) ⦂ Q ⊣ Θ1 }}a
| a_pat__anno : forall m Θ0 Θ1 P0 e A Q,
    {{ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] (ptyp_to_pskl A) ⩽ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] (exp_anno e A) ⦂ Q ⊣ Θ1 }}a
| a_pat__freeze : forall Θ0 e Q Θ1,
    {{ Θ0 ⊢ˢ[ mode_ti ; pskl_ghost ] e ⦂ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] (exp_freeze e) ⦂ Q ⊣ Θ1 }}a
| a_pat__abs : forall x m Θ0 Θ1 Θ2 P0 P Q0 e Q Ξ,
    m <> mode_tc ->
    {{ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}a ->
    a_suffix Ξ ->
    x `notin` dom (Ξ ++ Θ1) `union` dom Θ2 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_skl P) ++ Θ1) ⊢ˢ[ (decr_mode m) ; Q0 ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q ⊣ (Ξ ++ (x ~ abind_var_skl P) ++ Θ2) }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] (exp_abs e) ⦂ (pskl_arrow P Q) ⊣ (Ξ ++ Θ2) }}a
| a_pat__abs_anno : forall x m Θ0 Θ1 Θ2 Θ3 P0 P Q0 A e Q Ξ,
    m <> mode_tc ->
    {{ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}a ->
    a_consis_chk Θ1 (ptyp_to_pskl A) P Θ2 ->
    a_suffix Ξ ->
    x `notin` dom (Ξ ++ Θ2) `union` dom Θ3 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ Θ2) ⊢ˢ[ (decr_mode m) ; Q0 ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] (exp_abs_anno A e) ⦂ (pskl_arrow (ptyp_to_pskl A) Q) ⊣ (Ξ ++ Θ3) }}a
| a_pat__abs_check : forall x Θ0 Θ1 e Q Ξ,
    a_suffix Ξ ->
    x `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_skl pskl_ghost) ++ Θ0) ⊢ˢ[ mode_tc ; pskl_ghost ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q ⊣ (Ξ ++ (x ~ abind_var_skl pskl_ghost) ++ Θ1) }}a ->
    {{ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] (exp_abs e)
      ⦂ (pskl_univ_ghost (pskl_arrow pskl_ghost Q)) ⊣ (Ξ ++ Θ1) }}a
| a_pat__abs_anno_check : forall x Θ0 Θ1 A e Q Ξ,
    a_suffix Ξ ->
    x `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ Θ0) ⊢ˢ[ mode_tc ; pskl_ghost ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ1) }}a ->
    {{ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] (exp_abs_anno A e)
      ⦂ (pskl_univ_ghost (pskl_arrow (ptyp_to_pskl A) Q)) ⊣ (Ξ ++ Θ1) }}a
| a_pat__app : forall m Θ0 Θ1 Θ2 P0 Q0 P Q e1 e2,
    {{ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] e2 ⦂ P0 ⊣ Θ1 }}a ->
    {{ Θ1 ⊢ˢ[ (mode_fn m) ; (pskl_arrow P0 Q0) ] e1 ⦂ (pskl_arrow P Q) ⊣ Θ2 }}a ->
    {{ Θ0 ⊢ˢ[ m ; Q0 ] (exp_app e1 e2) ⦂ Q ⊣ Θ2 }}a
where "{{ Θ ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ' }}a" := (a_pat m Θ P0 e Q Θ') : fresco_a_scope.

Inductive a_typing : mode -> aenv -> pskl -> exp -> ptyp -> aenv -> Prop :=
| a_typing__unit : forall m Θ0 P0 A Θ1,
    {{ Θ0 ⊢[ a_sub_mode_ty | m | P0 ] pskl_unit ⩽ (ptyp_to_pskl A) ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ m ; P0 ] exp_unit ⦂ A ⊣ Θ1 }}a
| a_typing__var : forall m Θ0 P0 x A B Θ1,
    binds x (abind_var_typ A) Θ0 ->
    {{ Θ0 ⊢[ a_sub_mode_ty | m | P0 ] (ptyp_to_pskl A) ⩽ (ptyp_to_pskl B) ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ m ; P0 ] (exp_var_f x) ⦂ B ⊣ Θ1 }}a
| a_typing__anno : forall m Θ0 P0 e A B Θ1 Θ2,
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A) ] e ⦂ A ⊣ Θ1 }}a ->
    {{ Θ1 ⊢[ a_sub_mode_ty | m | P0 ] (ptyp_to_pskl A) ⩽ (ptyp_to_pskl B) ⊣ Θ2 }}a ->
    {{ Θ0 ⊢[ m ; P0 ] (exp_anno e A) ⦂ B ⊣ Θ2 }}a
| a_typing__freeze : forall Θ0 e A B Θ1 Θ2,
    {{ Θ0 ⊢[ mode_ti ; pskl_ghost ] e ⦂ B ⊣ Θ1 }}a ->
    a_consis_chk Θ1 (ptyp_to_pskl B) (ptyp_to_pskl A) Θ2 ->
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A) ] (exp_freeze e) ⦂ A ⊣ Θ2 }}a
| a_typing__abs : forall x m Θ0 Θ1 Θ2 P0 P Q αs A e B Ξ,
    m <> mode_tc ->
    {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a ->
    a_guess_mono Θ1 P αs A ->
    uniq (αs ++ Θ1) ->
    a_suffix Ξ ->

    x `notin` dom (Ξ ++ αs ++ Θ1) `union` dom Θ2 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ αs ++ Θ1) ⊢[ (decr_mode m) ; Q ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ B ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) }}a ->
    {{ Θ0 ⊢[ m ; P0 ] (exp_abs e) ⦂ (ptyp_arrow A B) ⊣ (Ξ ++ Θ2) }}a
| a_typing__abs_anno : forall x m Θ0 Θ1 Θ2 Θ3 P0 P Q A e B Ξ,
    m <> mode_tc ->
    {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a ->
    a_consis_chk Θ1 (ptyp_to_pskl A) P Θ2 ->
    a_suffix Ξ ->
    x `notin` dom (Ξ ++ Θ2) `union` dom Θ3 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ Θ2) ⊢[ (decr_mode m) ; Q ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ B ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}a ->
    {{ Θ0 ⊢[ m ; P0 ] (exp_abs_anno A e) ⦂ (ptyp_arrow A B) ⊣ (Ξ ++ Θ3) }}a
| a_typing__abs_check_step : forall α Θ0 Θ1 A0 e A Ξ,
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
    α `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union`
      ftvar_in_ptyp A0 `union` ftvar_in_ptyp A `union`
      ftvar_in_exp (exp_abs e) ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
      (exp_abs e) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
      ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}a ->
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ] (exp_abs e) ⦂ (ptyp_all A) ⊣ Θ1 }}a
| a_typing__abs_check_base : forall x Θ0 Θ1 Θ2 A0 A B B1 e Ξ,
    {{ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A) ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}a ->
    a_suffix Ξ ->
    uniq (Ξ ++ Θ1) ->
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1) ->
    x `notin` dom (Ξ ++ Θ1) `union` dom Θ2 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ Θ1) ⊢[ mode_tc ; (ptyp_to_pskl B) ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ B1 ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) }}a ->
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A0) ] (exp_abs e) ⦂ (ptyp_arrow A B1) ⊣ Θ2 }}a
| a_typing__abs_anno_check_step : forall α Θ0 Θ1 A0 Aan e A Ξ,
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
    α `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union`
      ftvar_in_ptyp A0 `union` ftvar_in_ptyp A `union`
      ftvar_in_exp (exp_abs_anno Aan e) ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
      (exp_abs_anno Aan e) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
      ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}a ->
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ] (exp_abs_anno Aan e)
      ⦂ (ptyp_all A) ⊣ Θ1 }}a
| a_typing__abs_anno_check_base : forall x Θ0 Θ1 Θ2 Θ3 A0 A' A B B1 e Ξ,
    {{ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A') ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}a ->
    a_consis_chk Θ1 (ptyp_to_pskl A') (ptyp_to_pskl A) Θ2 ->
    a_suffix Ξ ->
    uniq (Ξ ++ Θ2) ->
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1) ->
    x `notin` dom (Ξ ++ Θ2) `union` dom Θ3 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ Θ2) ⊢[ mode_tc ; (ptyp_to_pskl B) ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ B1 ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}a ->
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A0) ] (exp_abs_anno A e)
      ⦂ (ptyp_arrow A' B1) ⊣ Θ3 }}a
| a_typing__app : forall m Θ0 Θ1 Θ2 Θ3 P Q A A' B e1 e2,
    {{ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] e2 ⦂ P ⊣ Θ1 }}a ->
    {{ Θ1 ⊢[ (mode_fn m) ; (pskl_arrow P Q) ] e1 ⦂ (ptyp_arrow A B) ⊣ Θ2 }}a ->
    {{ Θ2 ⊢[ mode_tc ; (ptyp_to_pskl A) ] e2 ⦂ A' ⊣ Θ3 }}a ->
    {{ Θ0 ⊢[ m ; Q ] (exp_app e1 e2) ⦂ B ⊣ Θ3 }}a
where "{{ Θ ⊢[ m ; P0 ] e ⦂ B ⊣ Θ' }}a" := (a_typing m Θ P0 e B Θ') : fresco_a_scope.
