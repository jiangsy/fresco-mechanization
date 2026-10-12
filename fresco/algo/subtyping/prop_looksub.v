Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.consistency.prop_soundness_consis.

Set Implicit Arguments.

Scheme a_looksub_mutind := Induction for a_looksub Sort Prop
  with a_lookeq_mutind := Induction for a_lookeq Sort Prop.

Combined Scheme a_looksub_lookeq_mutind
  from a_looksub_mutind, a_lookeq_mutind.

Lemma a_looksub_lookeq_decls :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a -> a_decls Ξ) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a -> a_decls Ξ).
Proof.
  apply a_looksub_lookeq_mutind;
    intros; try solve [ assumption ]; try solve [ apply a_decls__nil ];
    try solve [ apply a_decls_app; assumption ];
    try solve [ destruct (atom_fresh L) as [β0 Hβ0]; eauto ].

  econstructor; apply a_decls__nil.
Qed.

Lemma a_looksub_decls : forall Θ α m P P' Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a -> a_decls Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_decls); eauto. Qed.

Lemma a_guess_decls : forall Θ NM P Ξ P',
  a_guess Θ NM P Ξ P' -> a_decls Ξ.
Proof.
  intros Θ NM P Ξ P' H; destruct H;
    [ apply a_decls__nil | eapply a_guess_mono_decls; eauto ].
Qed.

Lemma a_looksub_lookeq_generated_ftvar :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a -> ftvar_in_aenv Ξ [<=] dom Ξ) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a -> ftvar_in_aenv Ξ [<=] dom Ξ).
Proof.
  apply a_looksub_lookeq_mutind;
    intros; simpl; try solve [ fsetdec ];
    try solve [ destruct (atom_fresh L) as [β0 Hβ0]; eauto ];
    rewrite ftvar_in_aenv_app, dom_app; fsetdec.
Qed.

Lemma a_looksub_generated_ftvar : forall Θ α m P P' Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_generated_ftvar); eauto. Qed.

Lemma a_lookeq_generated_ftvar : forall Θ α P P' Ξ 𝒞,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros; eapply (proj2 a_looksub_lookeq_generated_ftvar); eauto. Qed.

Lemma a_extract_decls : forall Θ0 NM α m P P' Ξ P0,
  {{ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ P0 }}a -> a_decls Ξ.
Proof.
  intros Θ0 NM α m P P' Ξ P0 H; destruct H.
  apply a_decls_app; [ eapply a_looksub_decls; eauto | ].
  apply a_decls_app;
    [ eapply a_solve_cstr_decls; eauto | eapply a_guess_decls; eauto ].
Qed.

Definition subst_cstr (γ β : atom) (c : a_cstr) : a_cstr :=
  match c with
  | a_cstr_sub m P => a_cstr_sub m (subst_pskl_in_pskl (pskl_var_f γ) β P)
  | a_cstr_eq P    => a_cstr_eq (subst_pskl_in_pskl (pskl_var_f γ) β P)
  end.

Fixpoint subst_cstrs (γ β : atom) (C : a_cstrs) : a_cstrs :=
  match C with
  | nil     => nil
  | c :: C' => subst_cstr γ β c :: subst_cstrs γ β C'
  end.

Lemma subst_cstrs_fresh_eq : forall γ β C,
  β `notin` ftvar_in_a_cstrs C -> subst_cstrs γ β C = C.
Proof.
  induction C as [ | c C' IH ]; intros Hβ; simpl in *; [ reflexivity | ].
  rewrite IH by (clear - Hβ; fsetdec).
  destruct c; simpl; rewrite subst_pskl_in_pskl_fresh_eq
    by (clear - Hβ; simpl in Hβ; fsetdec); reflexivity.
Qed.

Lemma ftvar_in_a_cstrs_subst_upper : forall γ β C,
  ftvar_in_a_cstrs (subst_cstrs γ β C)
    [<=] singleton γ `union` remove β (ftvar_in_a_cstrs C).
Proof.
  induction C as [ | c C' IH ]; simpl; [ fsetdec | ].
  destruct c; simpl;
    match goal with |- context[ftvar_in_pskl (subst_pskl_in_pskl _ _ ?P)] =>
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f γ) β) as Hup
    end; simpl in Hup; clear - IH Hup; fsetdec.
Qed.

Lemma a_looksub_lookeq_ftv :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall α0, α0 `in` ftvar_in_a_cstrs 𝒞 ->
       α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
       α0 `notin` ftvar_in_aenv Θ) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall α0, α0 `in` ftvar_in_a_cstrs 𝒞 ->
       α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
       α0 `notin` ftvar_in_aenv Θ).
Proof.
  apply a_looksub_lookeq_mutind;
    intros; simpl in *;

    try solve [ left; match goal with Hin : _ `in` _ |- _ =>
                  clear - Hin; fsetdec end ].
  all: try solve [ exact (H α0 H0) ].
  all: try solve [
         rewrite ftvar_in_a_cstrs_app in H1; rewrite dom_app;
         destruct (AtomSetProperties.In_dec α0 (ftvar_in_a_cstrs C1))
           as [Hin | Hin];
         [ destruct (H α0 Hin) as [Hd | Hd]
         | destruct (H0 α0 ltac:(clear - H1 Hin; solve_notin_auto)) as [Hd | Hd] ];
         solve [ left; clear - Hd; fsetdec | right; exact Hd ] ].
  all: destruct (H α0 H0) as [Hl | Hr].
  all: try solve [ right; clear - Hr; fsetdec ].
  all: try solve [ left; exact Hl ].
  all: match goal with
       | Hl : _ `in` union (ftvar_in_pskl (open_pskl_wrt_pskl ?B _)) _ |- _ =>
           pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β))
             as Hup
       end; simpl in Hup;
       destruct (α0 == β) as [-> | Hne];
         [ right; clear - n; fsetdec | left; clear - Hl Hup Hne; fsetdec ].
Qed.

Lemma a_lookeq_cstr_eq : forall Θ α P P' Ξ 𝒞,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  Forall (fun c => exists Q, c = a_cstr_eq Q) 𝒞.
Proof.
  intros Θ α P P' Ξ 𝒞 H; induction H.
  - constructor; [ eexists; reflexivity | constructor ].
  - constructor.
  - constructor.
  - constructor; [ eexists; reflexivity | constructor ].
  - apply Forall_app; split; assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma a_looksub_ftv : forall Θ α m P P' Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  forall α0, α0 `in` ftvar_in_a_cstrs 𝒞 ->
    α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/ α0 `notin` ftvar_in_aenv Θ.
Proof. intros * H; eapply (proj1 a_looksub_lookeq_ftv); eauto. Qed.

Lemma a_looksub_ftv_ctx : forall Θ α m P P' Ξ 𝒞 α0,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  α0 `in` dom Θ ->
  α0 `notin` ftvar_in_pskl P' ->
  α0 `notin` dom Ξ ->
  α0 `notin` ftvar_in_a_cstrs 𝒞.
Proof.
  intros * H Hdom HP' HΞ Hin.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hdf.
  destruct (a_looksub_ftv H Hin) as [Hl | Hr];
    [ clear - Hl HP' HΞ | clear - Hdom Hdf Hr ]; fsetdec.
Qed.

Lemma a_lookeq_ftv_ctx : forall Θ α P P' Ξ 𝒞 α0,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  α0 `in` dom Θ ->
  α0 `notin` ftvar_in_pskl P' ->
  α0 `notin` dom Ξ ->
  α0 `notin` ftvar_in_a_cstrs 𝒞.
Proof.
  intros * H Hdom HP' HΞ Hin.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hdf.
  destruct ((proj2 a_looksub_lookeq_ftv) _ _ _ _ _ _ H _ Hin) as [Hl | Hr];
    [ clear - Hl HP' HΞ | clear - Hdom Hdf Hr ]; fsetdec.
Qed.

Lemma a_solve_cstr_ftv : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  forall α, α `in` ftvar_in_pskl P' ->
    α `in` (ftvar_in_pskl P `union` ftvar_in_a_cstrs 𝒞) \/ α `notin` dom Θ.
Proof.
  intros Θ 𝒞 P Ξ P' H; induction H; simpl; intros α0 Hα0.
  - left; fsetdec.
  - destruct (a_solve_sub_ftv H Hα0) as [Hl | Hr];
      [ left; clear - Hl; fsetdec | right; exact Hr ].
  -
    pose proof (a_solve_eq_ftv H) as He.
    destruct (IHa_solve_cstr α0 Hα0) as [Hl | Hr];
      [ | right; rewrite dom_app in Hr; clear - Hr; fsetdec ].
    destruct (AtomSetProperties.In_dec α0 (dom Ξ1)) as [Hd | Hd];
      [ right; eapply a_solve_eq_generated_notin_dom; eassumption
      | left; clear - Hl He Hd; fsetdec ].
Qed.

Lemma a_solve_cstr_ftv_eq : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  Forall (fun c => exists Q, c = a_cstr_eq Q) 𝒞 ->
  ftvar_in_pskl P' [<=]
    ftvar_in_pskl P `union` ftvar_in_a_cstrs 𝒞 `union` dom Ξ.
Proof.
  intros Θ 𝒞 P Ξ P' H; induction H; simpl; intros Hall.
  - clear; fsetdec.
  -
    exfalso. inversion Hall as [ | c cs Hc _ ]; subst.
    destruct Hc as [Q0 Hc]. discriminate Hc.
  - inversion Hall as [ | c cs Hc Htl ]; subst.
    pose proof (a_solve_eq_ftv H) as He.
    specialize (IHa_solve_cstr Htl).
    rewrite dom_app. clear - He IHa_solve_cstr. fsetdec.
Qed.

Lemma ptyp_to_pskl_ftv : forall A,
  ftvar_in_pskl (ptyp_to_pskl A) [<=] ftvar_in_ptyp A.
Proof. induction A; simpl; fsetdec. Qed.

Lemma subst_neq_var_keep : forall P P0 β α,
  P <> pskl_var_f α -> α `notin` ftvar_in_pskl P0 ->
  subst_pskl_in_pskl P0 β P <> pskl_var_f α.
Proof.
  intros P P0 β α Hne Hα Hc.
  destruct P; simpl in Hc; try discriminate Hc.
  destruct (α0 == β) as [-> | Hne2].
  - rewrite Hc in Hα. simpl in Hα. clear - Hα. fsetdec.
  - inversion Hc; subst. congruence.
Qed.

Lemma a_looksub_lookeq_absent_nil :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil).
Proof.
  apply a_looksub_lookeq_mutind;
    intros; simpl in *;
    try solve [ auto ];
    try solve [ exfalso; fsetdec ];
    try match goal with
        | IH1 : _ -> ?Ξ1 = nil /\ ?C1 = nil,
          IH2 : _ -> ?Ξ2 = nil /\ ?C2 = nil
          |- ?Ξ1 ++ ?Ξ2 = nil /\ ?C1 ++ ?C2 = nil =>
            destruct IH1 as [-> ->]; [ fsetdec | ];
            destruct IH2 as [-> ->]; [ fsetdec | ];
            auto
        end;
    try match goal with
        | IH : _ `notin` ftvar_in_pskl (open_pskl_wrt_pskl ?Pb _) -> _ ,
          Hn : _ `notin` ftvar_in_pskl _ ,
          Hsc : _ `notin` add _ _ |- _ =>
            apply IH;
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          Pb (pskl_var_f β)) as Hup;
            simpl in Hup; clear - Hup Hn Hsc; fsetdec
        end;
    try match goal with
        | IH : _ -> _ = nil /\ _ = nil |- _ => apply IH; assumption
        end.
Qed.

Lemma a_looksub_ghost_target : forall Θ α m P Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , m ] pskl_ghost ⤳ Ξ ⨾ 𝒞 }}a ->
  Ξ = nil /\ (𝒞 = nil
              \/ (P = pskl_var_f α /\ 𝒞 = a_cstr_sub m pskl_ghost :: nil)).
Proof.
  intros Θ α m P Ξ 𝒞 H.
  remember pskl_ghost as T eqn:HT.
  induction H; subst; try discriminate HT.
  -
    split; [ reflexivity | right; split; reflexivity ].
  -  split; [ reflexivity | left; reflexivity ].
  -  split; [ reflexivity | left; reflexivity ].
  -
    match goal with Hg : guarded_pskl pskl_ghost |- _ => inversion Hg end.
  -
    match goal with Hnh : pskl_ghost <> pskl_ghost |- _ =>
      exfalso; exact (Hnh eq_refl) end.
  -
    match goal with Hnh : pskl_ghost <> pskl_ghost |- _ =>
      exfalso; exact (Hnh eq_refl) end.
Qed.

Lemma ftv_open_absent : forall α β P,
  β `notin` add α (ftvar_in_pskl P) ->
  α `notin` ftvar_in_pskl (pskl_all_syn P) ->
  α `notin` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f β)).
Proof.
  intros α β P Hβ Hα.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
  simpl in *. clear - Hβ Hα Hup. fsetdec.
Qed.

Lemma a_looksub_forall_r_adm : forall Θ α A B Ξ C β,
  pskl_ghost_free (pskl_all_syn B) ->
  A <> pskl_var_f α ->
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl A
                     `union` ftvar_in_pskl B) ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ A ≼[ α , mode_tc ]
     (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ A ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α A B Ξ C β Hgf Hnv Hβ Hp.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl A)) as [Hin | Hni].
  - apply a_looksub__forall_r with (β := β); assumption.
  -
    destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ Hp Hni)
      as [-> ->].
    apply a_looksub__absent; exact Hni.
Qed.

Lemma a_looksub_forall_l_adm : forall Θ α m P P' Ξ C β,
  P' <> pskl_ghost ->
  forall_r_off m P' ->
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β))
     ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ (pskl_all_syn P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α m P P' Ξ C β Hnh Hfr Hβ Hp.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_all_syn P)))
    as [Hin | Hni].
  - apply a_looksub__forall_l with (β := β); assumption.
  - assert (Hno : α `notin` ftvar_in_pskl
                    (open_pskl_wrt_pskl P (pskl_var_f β)))
      by (apply ftv_open_absent; [ clear - Hβ; fsetdec | exact Hni ]).
    destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ Hp Hno)
      as [-> ->].
    apply a_looksub__absent; exact Hni.
Qed.

Lemma a_lookeq_forall_inh_adm : forall Θ α P P' Ξ C β,
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
     (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α P P' Ξ C β Hβ Hp.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_all_syn P)))
    as [Hin | Hni].
  - apply a_lookeq__forall_inh with (β := β); assumption.
  - assert (Hno : α `notin` ftvar_in_pskl
                    (open_pskl_wrt_pskl P (pskl_var_f β)))
      by (apply ftv_open_absent; [ clear - Hβ; fsetdec | exact Hni ]).
    destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hp Hno)
      as [-> ->].
    apply a_lookeq__absent; exact Hni.
Qed.

Lemma a_lookeq_forall_syn_adm : forall Θ α P P' Ξ C β,
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
     (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α P P' Ξ C β Hβ Hp.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_all_syn P)))
    as [Hin | Hni].
  - apply a_lookeq__forall_syn with (β := β); assumption.
  - assert (Hno : α `notin` ftvar_in_pskl
                    (open_pskl_wrt_pskl P (pskl_var_f β)))
      by (apply ftv_open_absent; [ clear - Hβ; fsetdec | exact Hni ]).
    destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hp Hno)
      as [-> ->].
    apply a_lookeq__absent; exact Hni.
Qed.

Lemma a_lookeq_univ_ghost1_adm : forall Θ α P P' Ξ C β,
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (pskl_univ_ghost P) ∼[ α ]
     (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ (pskl_univ_ghost P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α P P' Ξ C β Hβ Hp.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_univ_ghost P)))
    as [Hin | Hni].
  - apply a_lookeq__univ_ghost1 with (β := β); assumption.
  -
    destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hp Hni)
      as [-> ->].
    apply a_lookeq__absent; exact Hni.
Qed.

Lemma a_looksub_var_subject_inv : forall Θ α m P' Ξ 𝒞,
  {{ Θ ⊢ (pskl_var_f α) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  Ξ = nil /\ 𝒞 = a_cstr_sub m P' :: nil.
Proof.
  intros Θ α m P' Ξ 𝒞 H.
  remember (pskl_var_f α) as S eqn:HS.
  destruct H; try discriminate HS.
  -  split; reflexivity.
  -
    exfalso. subst P. simpl in H. clear - H. fsetdec.
  -  exfalso. congruence.
  -  exfalso. congruence.
  -  exfalso. congruence.
Qed.

Lemma a_looksub_open_target : forall Θ α P B Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ 𝒞 }}a ->
  pskl_ghost_free (pskl_all_syn B) ->
  (P = pskl_var_f α /\ Ξ = nil
     /\ 𝒞 = a_cstr_sub mode_tc (pskl_all_syn B) :: nil)
  \/ (exists β,
        β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                           `union` ftvar_in_pskl B)
        /\ {{ ((β ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , mode_tc ]
              (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ 𝒞 }}a).
Proof.
  intros Θ α P B Ξ 𝒞 H Hgf.
  remember (pskl_all_syn B) as T eqn:HT.
  remember mode_tc as m0 eqn:Hm0.
  destruct H as
    [ Θ0 α0 m1 Q
    | Θ0 α0 m1 Q Q' Hnf
    | Θ0 α0 m1 Q Hnv0
    | Θ0 α0 A0 B0 Ξ0 C0 Hgf0 Hne0 Hg1 Hg2 Hp
    | Θ0 α0 A0 B0 Ξ0 C0 b Hgf0 Hfr0 Hocc0 Hnv0 Hp
    | Θ0 α0 m1 P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 Hp2
    | Θ0 α0 m1 Q Q' Ξ0 C0 b Hfr0 Hocc0 Hnh0 Hfr3 Hp
    | Θ0 α0 m1 Q Q' Ξ0 C0 Hnh0 Hfr3 Hp ];
    try discriminate HT; try discriminate Hm0.
  -
    left. rewrite HT. split; [ reflexivity | split; reflexivity ].
  -
    right.
    pick fresh β for
      (add α0 (ftvar_in_aenv Θ0 `union` ftvar_in_pskl Q
                 `union` ftvar_in_pskl B)).
    exists β. split; [ clear - Fr; solve_notin | ].
    apply a_looksub__absent; exact Hnf.
  -
    exfalso. rewrite HT in Hg2. inversion Hg2.
  -
    right. injection HT as HTB; subst B0.
    exists b. split; [ exact Hfr0 | exact Hp ].
  -
    exfalso. rewrite HT in Hgf. exact (Hfr3 B HT Hm0 Hgf).
  -
    exfalso. rewrite HT in Hgf. exact (Hfr3 B HT Hm0 Hgf).
Qed.

Lemma subst_cstrs_same : forall β 𝒞, subst_cstrs β β 𝒞 = 𝒞.
Proof.
  induction 𝒞 as [ | c 𝒞' IH ]; cbn; [ reflexivity | ].
  rewrite IH; destruct c; cbn; rewrite subst_pskl_var_same; reflexivity.
Qed.

Lemma notin_add_atom : forall (γ δ : atom) S,
  γ <> δ -> γ `notin` S -> γ `notin` add δ S.
Proof. intros; fsetdec. Qed.

Lemma notin_ftvar_in_aenv_cons_tvar : forall γ δ Θ,
  γ <> δ -> γ `notin` ftvar_in_aenv Θ ->
  γ `notin` ftvar_in_aenv ((δ ~ abind_tvar) ++ Θ).
Proof. intros; simpl; fsetdec. Qed.

Lemma notin_ftvar_in_aenv_rename : forall γ α1 β Θ,
  γ <> α1 -> γ `notin` ftvar_in_aenv Θ ->
  γ `notin` ftvar_in_aenv (rename_aenv α1 β Θ).
Proof.
  intros γ α1 β Θ Hne HΘ.
  pose proof (@ftvar_in_aenv_rename_aenv Θ α1 β) as H. fsetdec.
Qed.

Lemma notin_ftvar_subst_var : forall γ α1 β P,
  γ <> α1 -> γ `notin` ftvar_in_pskl P ->
  γ `notin` ftvar_in_pskl (subst_pskl_in_pskl (pskl_var_f α1) β P).
Proof.
  intros γ α1 β P Hne HP.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f α1) β) as H.
  simpl in H. fsetdec.
Qed.

Lemma notin_ftvar_in_a_cstrs_subst_away : forall γ δ 𝒞,
  γ <> δ -> γ `notin` ftvar_in_a_cstrs (subst_cstrs δ γ 𝒞).
Proof.
  intros γ δ 𝒞 Hne.
  pose proof (ftvar_in_a_cstrs_subst_upper δ γ 𝒞) as H. fsetdec.
Qed.

Lemma notin_ftvar_in_a_cstrs_subst : forall γ δ β 𝒞,
  γ <> δ -> γ `notin` ftvar_in_a_cstrs 𝒞 ->
  γ `notin` ftvar_in_a_cstrs (subst_cstrs δ β 𝒞).
Proof.
  intros γ δ β 𝒞 Hne H𝒞.
  pose proof (ftvar_in_a_cstrs_subst_upper δ β 𝒞) as H. fsetdec.
Qed.

Ltac look_fresh_leaf :=
  first [ solve [ assumption ]
        | solve [ congruence ]
        | solve [ match goal with
                  | H : _ `notin` _ |- _ => clear - H; fsetdec
                  end ] ].

Ltac look_fresh :=
  repeat first
    [ apply notin_union_3
    | apply notin_add_atom
    | look_fresh_leaf
    | apply notin_ftvar_in_aenv_cons_tvar
    | apply notin_ftvar_in_aenv_rename
    | apply notin_ftvar_open_pskl_var
    | apply notin_ftvar_in_a_cstrs_subst_away
    | apply notin_ftvar_in_a_cstrs_subst
    | apply notin_ftvar_subst_var ].

Lemma a_looksub_lookeq_ctx_ftv_mono :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall Θ', ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     (forall β, β `in` ftvar_in_pskl P' ->
        (a_flex_tvar Θ β <-> a_flex_tvar Θ' β)) ->
     {{ Θ' ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall Θ', ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     (forall β, β `in` ftvar_in_pskl P' ->
        (a_flex_tvar Θ β <-> a_flex_tvar Θ' β)) ->
     {{ Θ' ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a).
Proof.
  assert (Hcons : forall (β : atom) Θ Θ',
            ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
            ftvar_in_aenv ((β ~ abind_tvar) ++ Θ')
              [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (intros; rewrite ! ftvar_in_aenv_cons_tvar; fsetdec).
  assert (Hfopen : forall (b : atom) (Θa Θb : aenv) (B : pskl),
            ftvar_in_aenv Θb [<=] ftvar_in_aenv Θa ->
            b `notin` ftvar_in_aenv Θa ->
            (forall β, β `in` ftvar_in_pskl B ->
               (a_flex_tvar Θa β <-> a_flex_tvar Θb β)) ->
            forall β,
              β `in` ftvar_in_pskl (open_pskl_wrt_pskl B (pskl_var_f b)) ->
              (a_flex_tvar ((b ~ abind_tvar) ++ Θa) β
               <-> a_flex_tvar ((b ~ abind_tvar) ++ Θb) β)).
  { intros b Θa Θb B Hincl Hb Hf β Hβ.
    rewrite ! a_flex_tvar_cons_tvar_any.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
      as Hup.
    destruct (β == b) as [-> | Hne].
    -
      pose proof (dom_subset_ftvar_in_aenv Θa) as HdA.
      pose proof (dom_subset_ftvar_in_aenv Θb) as HdB.
      split; intro Hfx; exfalso; apply a_flex_tvar_in_dom in Hfx;
        [ clear - Hb HdA Hfx | clear - Hb HdA HdB Hincl Hfx ]; fsetdec.
    - apply Hf. simpl in Hup. clear - Hup Hβ Hne. fsetdec. }
  apply a_looksub_lookeq_mutind.
  -  intros. apply a_looksub__var.
  -  intros Θ α m P P' Hnf Θ' Hm Hf.
    apply a_looksub__absent; exact Hnf.
  -  intros. apply a_looksub__vacuous. assumption.
  -  intros Θ α A B Ξ C Hgf Hne Hg Hg0 Hp IH Θ' Hm Hf.
    apply a_looksub__check;
      solve [ assumption | apply IH; [ exact Hm | exact Hf ] ].
  -  intros Θ α A B Ξ C β Hgf Hfr Hocc Hnv Hp IH Θ' Hm Hf.
    apply a_looksub__forall_r with (β := β);
      [ exact Hgf | clear - Hfr Hm; fsetdec | exact Hocc | exact Hnv
      | apply IH;
        [ apply Hcons; exact Hm
        | apply Hfopen;
          [ exact Hm | clear - Hfr; fsetdec | exact Hf ] ] ].
  -
    intros Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 IH1 Hp2 IH2 Θ' Hm Hf.
    apply a_looksub__arrow;
      [ exact Hg1 | exact Hg2 | apply IH1 | apply IH2 ]; solve
      [ exact Hm | intros β0 Hβ0; apply Hf; simpl; clear - Hβ0; fsetdec ].
  -  intros Θ α m P P' Ξ C β Hfr Hocc Hnh Hfr3 Hp IH Θ' Hm Hf.
    apply a_looksub__forall_l with (β := β);
      [ clear - Hfr Hm; fsetdec | exact Hocc | exact Hnh | exact Hfr3
      | apply IH;
        [ apply Hcons; exact Hm
        | intros β0 Hβ0; rewrite ! a_flex_tvar_cons_tvar_any;
          exact (Hf β0 Hβ0) ] ].
  -  intros Θ α m P P' Ξ C Hnh Hfr3 Hp IH Θ' Hm Hf.
    apply a_looksub__univ_ghost_l;
      [ exact Hnh | exact Hfr3 | apply IH; [ exact Hm | exact Hf ] ].
  -  intros. apply a_lookeq__var.
  -  intros Θ α P P' Hnf Θ' Hm Hf.
    apply a_lookeq__absent; exact Hnf.
  -  intros. apply a_lookeq__vacuous. assumption.
  -
    intros Θ α P β α1 Hfr Hflx Hne Hin Θ' Hm Hf.
    apply a_lookeq__flex_r;
      [ clear - Hfr Hm; fsetdec
      | apply (proj1 (Hf β ltac:(simpl; clear; fsetdec))); exact Hflx
      | exact Hne | exact Hin ].
  -
    intros Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 IH1 Hp2 IH2 Θ' Hm Hf.
    apply a_lookeq__arrow;
      [ exact Hg1 | exact Hg2 | apply IH1 | apply IH2 ]; solve
      [ exact Hm | intros β0 Hβ0; apply Hf; simpl; clear - Hβ0; fsetdec ].
  -  intros Θ α P P' Ξ C β Hfr Hocc Hp IH Θ' Hm Hf.
    apply a_lookeq__forall_inh with (β := β);
      [ clear - Hfr Hm; fsetdec | exact Hocc
      | apply IH;
        [ apply Hcons; exact Hm
        | apply Hfopen;
          [ exact Hm | clear - Hfr; fsetdec | exact Hf ] ] ].
  -  intros Θ α P P' Ξ C β Hfr Hocc Hp IH Θ' Hm Hf.
    apply a_lookeq__forall_syn with (β := β);
      [ clear - Hfr Hm; fsetdec | exact Hocc
      | apply IH;
        [ apply Hcons; exact Hm
        | intros β0 Hβ0; rewrite ! a_flex_tvar_cons_tvar_any;
          exact (Hf β0 Hβ0) ] ].
  -  intros Θ α P P' Ξ C Hp IH Θ' Hm Hf.
    apply a_lookeq__univ_ghost; apply IH; [ exact Hm | exact Hf ].
  -  intros Θ α P P' Ξ C β Hfr Hocc Hp IH Θ' Hm Hf.
    apply a_lookeq__univ_ghost1 with (β := β);
      [ clear - Hfr Hm; fsetdec | exact Hocc
      | apply IH;
        [ apply Hcons; exact Hm
        | apply Hfopen;
          [ exact Hm | clear - Hfr; fsetdec | exact Hf ] ] ].
  -
    intros Θ α P P' Ξ C Hg Hfx Hp IH Θ' Hm Hf.
    apply a_lookeq__univ_ghost2;
      [ exact Hg
      | intros β Heq Hflx; subst P';
        exact (Hfx β eq_refl
                 (proj2 (Hf β ltac:(simpl; clear; fsetdec)) Hflx))
      | apply IH; [ exact Hm | exact Hf ] ].
  -  intros Θ α P P' Ξ C Hne Hg Hp IH Θ' Hm Hf.
    apply a_lookeq__univ_ghost_r;
      [ exact Hne | exact Hg | apply IH; [ exact Hm | exact Hf ] ].
Qed.

Lemma a_looksub_ctx_ftv_mono : forall Θ α m P P' Ξ 𝒞 Θ',
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
  (forall β, β `in` ftvar_in_pskl P' ->
     (a_flex_tvar Θ β <-> a_flex_tvar Θ' β)) ->
  {{ Θ' ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a.
Proof. intros; eapply (proj1 a_looksub_lookeq_ctx_ftv_mono); eauto. Qed.

Lemma a_lookeq_ctx_ftv_mono : forall Θ α P P' Ξ 𝒞 Θ',
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
  (forall β, β `in` ftvar_in_pskl P' ->
     (a_flex_tvar Θ β <-> a_flex_tvar Θ' β)) ->
  {{ Θ' ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a.
Proof. intros; eapply (proj2 a_looksub_lookeq_ctx_ftv_mono); eauto. Qed.

Lemma a_looksub_ctx_exchange : forall Θ α m P P' Ξ 𝒞 β1 β2,
  {{ ((β1 ~ abind_tvar) ++ (β2 ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ ((β2 ~ abind_tvar) ++ (β1 ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a.
Proof.
  intros. eapply a_looksub_ctx_ftv_mono; [ eassumption | | ].
  - rewrite ! ftvar_in_aenv_cons_tvar. fsetdec.
  -
    intros β0 _; rewrite ! a_flex_tvar_cons_tvar_any; reflexivity.
Qed.

Lemma a_looksub_lookeq_generated_fresh :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall γ, γ `in` ftvar_in_aenv Θ -> γ `notin` dom Ξ) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall γ, γ `in` ftvar_in_aenv Θ -> γ `notin` dom Ξ).
Proof.
  assert (Hgrow : forall (β γ : atom) Θ,
            γ `in` ftvar_in_aenv Θ ->
            γ `in` ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (intros; rewrite ftvar_in_aenv_cons_tvar; fsetdec).
  apply a_looksub_lookeq_mutind.
  -  intros; simpl; fsetdec.
  -  intros; simpl; fsetdec.
  -  intros; simpl; fsetdec.
  -  intros Θ α A B Ξ C Hgf Hne Hg Hg0 Hp IH γ Hγ. exact (IH γ Hγ).
  -  intros Θ α A B Ξ C β Hgf Hfr Hocc Hnv Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  -  intros Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 IH1 Hp2 IH2 γ Hγ.
    rewrite dom_app.
    pose proof (IH1 γ Hγ); pose proof (IH2 γ Hγ). fsetdec.
  -  intros Θ α m P P' Ξ C β Hfr Hocc Hnh Hfr3 Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  -  intros Θ α m P P' Ξ C Hnh Hfr3 Hp IH γ Hγ.
    exact (IH γ Hγ).
  -  intros; simpl; fsetdec.
  -  intros; simpl; fsetdec.
  -  intros; simpl; fsetdec.
  -
    intros Θ α P β α1 Hfr Hflx Hne Hin γ Hγ.
    simpl. clear - Hfr Hγ. fsetdec.
  -  intros Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 IH1 Hp2 IH2 γ Hγ.
    rewrite dom_app.
    pose proof (IH1 γ Hγ); pose proof (IH2 γ Hγ). fsetdec.
  -  intros Θ α P P' Ξ C β Hfr Hocc Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  -  intros Θ α P P' Ξ C β Hfr Hocc Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  -  intros Θ α P P' Ξ C Hp IH γ Hγ. exact (IH γ Hγ).
  -  intros Θ α P P' Ξ C β Hfr Hocc Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  -  intros Θ α P P' Ξ C Hg Hfx Hp IH γ Hγ. exact (IH γ Hγ).
  -  intros Θ α P P' Ξ C Hne Hg Hp IH γ Hγ. exact (IH γ Hγ).
Qed.

Lemma a_looksub_binder_not_generated : forall β Θ α m P P' Ξ 𝒞,
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  β `notin` ftvar_in_aenv Ξ.
Proof.
  intros β Θ α m P P' Ξ 𝒞 Hlk.
  pose proof (a_looksub_generated_ftvar Hlk) as Hftv.
  assert (Hin : β `in` ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (rewrite ftvar_in_aenv_cons_tvar; fsetdec).
  pose proof ((proj1 a_looksub_lookeq_generated_fresh) _ _ _ _ _ _ _ Hlk β Hin).
  fsetdec.
Qed.

Lemma a_lookeq_binder_not_generated : forall β Θ α P P' Ξ 𝒞,
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  β `notin` ftvar_in_aenv Ξ.
Proof.
  intros β Θ α P P' Ξ 𝒞 Hlk.
  pose proof (a_lookeq_generated_ftvar Hlk) as Hftv.
  assert (Hin : β `in` ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (rewrite ftvar_in_aenv_cons_tvar; fsetdec).
  pose proof ((proj2 a_looksub_lookeq_generated_fresh) _ _ _ _ _ _ Hlk β Hin).
  fsetdec.
Qed.

Lemma swap_cstrs_as_subst : forall β γ (C : a_cstrs),
  γ `notin` ftvar_in_a_cstrs C ->
  swap_cstrs β γ C = subst_cstrs γ β C.
Proof.
  induction C as [| c C' IH]; intros Hγ; [reflexivity |].
  simpl in Hγ. rewrite swap_cstrs_cons. cbn [subst_cstrs].
  f_equal; [ | apply IH; clear - Hγ; fsetdec ].
  destruct c; simpl in Hγ |- *; f_equal; apply swap_pskl_as_subst; fsetdec.
Qed.

Lemma a_looksub_move_binder : forall Θ α m P P' Ξ 𝒞 b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  b <> α -> b `notin` ftvar_in_aenv Θ -> β <> α -> β <> b ->
  β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl P'
            `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f β) b P) ≼[ α , m ]
    (subst_pskl_in_pskl (pskl_var_f β) b P') ⤳ Ξ ⨾ (subst_cstrs β b 𝒞) }}a.
Proof.
  intros * Hp Hbα HbΘ Hβα Hβb Hβ.
  pose proof (a_looksub_generated_ftvar Hp) as HΞ.
  pose proof (a_looksub_binder_not_generated Hp) as HbΞ.
  pose proof (proj1 (a_looksub_lookeq_swap b β) _ _ _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar, (swap_atom_other b β α) in Hr
    by auto.
  rewrite (swap_aenv_fresh_id b β Θ), (swap_aenv_fresh_id b β Ξ),
    (swap_pskl_as_subst b β P), (swap_pskl_as_subst b β P'),
    (@swap_cstrs_as_subst b β 𝒞) in Hr by (clear - HbΘ HbΞ HΞ Hβ; fsetdec).
  exact Hr.
Qed.

Lemma a_lookeq_move_binder : forall Θ α P P' Ξ 𝒞 b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  b <> α -> b `notin` ftvar_in_aenv Θ -> β <> α -> β <> b ->
  β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl P'
            `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f β) b P) ∼[ α ]
    (subst_pskl_in_pskl (pskl_var_f β) b P') ⤳ Ξ ⨾ (subst_cstrs β b 𝒞) }}a.
Proof.
  intros * Hp Hbα HbΘ Hβα Hβb Hβ.
  pose proof (a_lookeq_generated_ftvar Hp) as HΞ.
  pose proof (a_lookeq_binder_not_generated Hp) as HbΞ.
  pose proof (proj2 (a_looksub_lookeq_swap b β) _ _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar, (swap_atom_other b β α) in Hr
    by auto.
  rewrite (swap_aenv_fresh_id b β Θ), (swap_aenv_fresh_id b β Ξ),
    (swap_pskl_as_subst b β P), (swap_pskl_as_subst b β P'),
    (@swap_cstrs_as_subst b β 𝒞) in Hr by (clear - HbΘ HbΞ HΞ Hβ; fsetdec).
  exact Hr.
Qed.

Lemma a_lookeq_forall_move : forall Θ α P P' Ξ 𝒞 b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f b)) ∼[ α ]
    (open_pskl_wrt_pskl P' (pskl_var_f b)) ⤳ Ξ ⨾ 𝒞 }}a ->
  b `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  β <> α ->
  β `notin` ftvar_in_aenv Θ
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P' (pskl_var_f b))
            `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
    (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ (subst_cstrs β b 𝒞) }}a.
Proof.
  intros Θ α P P' Ξ 𝒞 b β Hp Hb Hβα Hβ.
  destruct (β == b) as [-> | Hβb];
    [ rewrite subst_cstrs_same; exact Hp | ].
  assert (Hbα : b <> α) by (clear - Hb; fsetdec).
  assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hb; fsetdec).
  pose proof (a_lookeq_move_binder Hp Hbα HbΘ Hβα Hβb Hβ) as Hr.
  rewrite <- (subst_pskl_in_pskl_intro b P (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  rewrite <- (subst_pskl_in_pskl_intro b P' (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  exact Hr.
Qed.

Lemma a_lookeq_forall_move_l : forall Θ α P Pt Ξ 𝒞 b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f b)) ∼[ α ] Pt
    ⤳ Ξ ⨾ 𝒞 }}a ->
  b `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl Pt) ->
  β <> α ->
  β `notin` ftvar_in_aenv Θ
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
            `union` ftvar_in_pskl Pt `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ] Pt
    ⤳ Ξ ⨾ (subst_cstrs β b 𝒞) }}a.
Proof.
  intros Θ α P Pt Ξ 𝒞 b β Hp Hb Hβα Hβ.
  destruct (β == b) as [-> | Hβb];
    [ rewrite subst_cstrs_same; exact Hp | ].
  assert (Hbα : b <> α) by (clear - Hb; fsetdec).
  assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hb; fsetdec).
  pose proof (a_lookeq_move_binder Hp Hbα HbΘ Hβα Hβb Hβ) as Hr.
  rewrite (subst_pskl_in_pskl_fresh_eq Pt) in Hr by (clear - Hb; fsetdec).
  rewrite <- (subst_pskl_in_pskl_intro b P (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  exact Hr.
Qed.

Lemma a_lookeq_forall_move_r : forall Θ α Ps P' Ξ 𝒞 b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ Ps ∼[ α ] (open_pskl_wrt_pskl P' (pskl_var_f b))
    ⤳ Ξ ⨾ 𝒞 }}a ->
  b `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
                     `union` ftvar_in_pskl P') ->
  β <> α ->
  β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P' (pskl_var_f b))
            `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ Ps ∼[ α ] (open_pskl_wrt_pskl P' (pskl_var_f β))
    ⤳ Ξ ⨾ (subst_cstrs β b 𝒞) }}a.
Proof.
  intros Θ α Ps P' Ξ 𝒞 b β Hp Hb Hβα Hβ.
  destruct (β == b) as [-> | Hβb];
    [ rewrite subst_cstrs_same; exact Hp | ].
  assert (Hbα : b <> α) by (clear - Hb; fsetdec).
  assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hb; fsetdec).
  pose proof (a_lookeq_move_binder Hp Hbα HbΘ Hβα Hβb Hβ) as Hr.
  rewrite (subst_pskl_in_pskl_fresh_eq Ps) in Hr by (clear - Hb; fsetdec).
  rewrite <- (subst_pskl_in_pskl_intro b P' (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  exact Hr.
Qed.

Lemma ftv_subst_var_in : forall P α α',
  α `in` ftvar_in_pskl P ->
  α' `in` ftvar_in_pskl (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  induction P as [ | | α1 | | | | ]; intros α α' Hin; simpl in *;
    try solve [ exfalso; fsetdec ].
  - destruct_if as [-> | Hne]; simpl; [ fsetdec | exfalso; fsetdec ].
  - destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P1)) as [Hi | Hni];
      [ pose proof (IHP1 _ α' Hi) | ];
      destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P2)) as [Hi2 | Hni2];
      try pose proof (IHP2 _ α' Hi2); try fsetdec.
  - eauto.
  - eauto.
Qed.

Lemma subst_var_neq_new : forall P α α',
  P <> pskl_var_f α -> α' `notin` ftvar_in_pskl P ->
  subst_pskl_in_pskl (pskl_var_f α') α P <> pskl_var_f α'.
Proof.
  intros P α α' Hne Hα' Hc.
  destruct P; simpl in Hc; try discriminate Hc.
  destruct (α0 == α) as [-> | Hne2];
    [ congruence | inversion Hc; subst; simpl in Hα'; fsetdec ].
Qed.

Lemma a_looksub_rename_binder : forall L {Θ α m P P' Ξ 𝒞 b},
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  b <> α -> b `notin` ftvar_in_aenv Θ ->
  b `notin` dom Ξ -> b `notin` ftvar_in_a_cstrs 𝒞 ->
  exists δ, δ <> α /\
    δ `notin` add α (add b (L `union` ftvar_in_aenv Θ `union` dom Ξ
                              `union` ftvar_in_a_cstrs 𝒞)) /\
    {{ ((δ ~ abind_tvar) ++ Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f δ) b P)
         ≼[ α , m ] (subst_pskl_in_pskl (pskl_var_f δ) b P') ⤳ Ξ ⨾ 𝒞 }}a.
Proof.
  intros * Hp Hbα HbΘ HbΞ HbC.
  pick fresh δ for (add α (add b (L `union` ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞))).
  exists δ. split; [ clear - Fr; fsetdec | ].
  split; [ clear - Fr; fsetdec | ].
  rewrite <- (@subst_cstrs_fresh_eq δ b 𝒞 HbC).
  apply (a_looksub_move_binder Hp Hbα HbΘ); clear - Fr; fsetdec.
Qed.

Lemma a_lookeq_rename_binder : forall L {Θ α P P' Ξ 𝒞 b},
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  b <> α -> b `notin` ftvar_in_aenv Θ ->
  b `notin` dom Ξ -> b `notin` ftvar_in_a_cstrs 𝒞 ->
  exists δ, δ <> α /\
    δ `notin` add α (add b (L `union` ftvar_in_aenv Θ `union` dom Ξ
                              `union` ftvar_in_a_cstrs 𝒞)) /\
    {{ ((δ ~ abind_tvar) ++ Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f δ) b P)
         ∼[ α ] (subst_pskl_in_pskl (pskl_var_f δ) b P') ⤳ Ξ ⨾ 𝒞 }}a.
Proof.
  intros * Hp Hbα HbΘ HbΞ HbC.
  pick fresh δ for (add α (add b (L `union` ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞))).
  exists δ. split; [ clear - Fr; fsetdec | ].
  split; [ clear - Fr; fsetdec | ].
  rewrite <- (@subst_cstrs_fresh_eq δ b 𝒞 HbC).
  apply (a_lookeq_move_binder Hp Hbα HbΘ); clear - Fr; fsetdec.
Qed.

Lemma a_looksub_lookeq_rename_var_size : forall n,
  (forall Θ α m P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') + 1 <= n ->
     {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall α', α' `notin` ftvar_in_pskl P ->
     α' `notin` dom Ξ -> α' `notin` ftvar_in_a_cstrs 𝒞 ->
     {{ Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞 }}a) /\
  (forall Θ α P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') <= n ->
     {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall α', α' `notin` ftvar_in_pskl P ->
     α' `notin` dom Ξ -> α' `notin` ftvar_in_a_cstrs 𝒞 ->
     {{ Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ∼[ α' ] P' ⤳ Ξ ⨾ 𝒞 }}a).
Proof.
  induction n as [ | n IHn ].
  { split;
      [ intros Θ α m P P' Ξ 𝒞 Hn Hd | intros Θ α P P' Ξ 𝒞 Hn Hd ];
      exfalso; pose proof (size_pskl_min P); pose proof (size_pskl_min P'); lia. }
  destruct IHn as [IHs IHe].
  split.

  { intros Θ α m P P' Ξ 𝒞 Hn Hd α' Hα'P Hα'Ξ Hα'C.
    destruct Hd as
      [ Θ α m Q
      | Θ α m Q Q' Hnf
      | Θ α m Q
      | Θ α A B Ξ0 C0 Hgf0 Hne Hg Hg0 Hp
      | Θ α A B Ξ0 C0 b Hgf0 Hfr0 Hocc0 Hnv0 Hp
      | Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 Hp2
      | Θ α m Q Q' Ξ0 C0 b Hfr0 Hocc0 Hnh0 Hfr3 Hp
      | Θ α m Q Q' Ξ0 C0 Hnh0 Hfr3 Hp ];
      cbn in Hn, Hα'P |- *.
    -
      destruct_if as [_ | Hne]; [ | exfalso; congruence ].
      apply a_looksub__var.
    -
      rewrite subst_pskl_in_pskl_fresh_eq by exact Hnf.
      apply a_looksub__absent; exact Hα'P.
    -  apply a_looksub__vacuous.
      apply subst_var_neq_new; assumption.
    -
      apply a_looksub__check;
        [ assumption
        | apply subst_var_neq_new; assumption
        | apply guarded_pskl_subst_var; assumption
        | assumption
        | apply IHe; solve [ lia | assumption ] ].
    -
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbA : b `notin` ftvar_in_pskl A) by (clear - Hfr0; fsetdec).
      assert (HbB : b `notin` ftvar_in_pskl B) by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      +
        destruct (a_looksub_rename_binder (ftvar_in_pskl A `union` ftvar_in_pskl B)
                    Hp Hbα HbΘ Hα'Ξ Hα'C) as [δ [Hδα [Hδ H1]]].
        rewrite (subst_pskl_in_pskl_fresh_eq A) in H1 by exact HbA.
        rewrite <- (subst_pskl_in_pskl_intro b B (pskl_var_f δ)) in H1
          by exact HbB.
        apply a_looksub__forall_r with (β := δ);
          [ ghost_free_auto | look_fresh
          | apply ftv_subst_var_in; exact Hocc0
          | apply subst_var_neq_new; assumption | ].
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact H1 | exact HbA | exact Hα'Ξ | exact Hα'C ].
      +
        apply a_looksub__forall_r with (β := b);
          [ ghost_free_auto | look_fresh
          | apply ftv_subst_var_in; exact Hocc0
          | apply subst_var_neq_new; assumption | ].
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact Hp | exact Hα'P | exact Hα'Ξ | exact Hα'C ].
    -
      rewrite dom_app in Hα'Ξ. rewrite ftvar_in_a_cstrs_app in Hα'C.

      apply a_looksub__arrow;
        [ exact Hg1 | exact Hg2 | apply IHe | apply IHs ];
        solve [ lia | assumption
              | clear - Hα'P; fsetdec | clear - Hα'Ξ; fsetdec
              | clear - Hα'C; fsetdec ].
    -
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + destruct (a_looksub_rename_binder (ftvar_in_pskl Q `union` ftvar_in_pskl Q')
                    Hp Hbα HbΘ Hα'Ξ Hα'C) as [δ [Hδα [Hδ H1]]].
        rewrite (subst_pskl_in_pskl_fresh_eq Q') in H1 by exact HbQ'.
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
          by exact HbQ.
        apply a_looksub__forall_l with (β := δ);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0
          | assumption | assumption | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
          by (solve [ congruence | constructor ]).
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact H1 | look_fresh | exact Hα'Ξ | exact Hα'C ].
      + apply a_looksub__forall_l with (β := b);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0
          | assumption | assumption | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α'))
          by (solve [ congruence | constructor ]).
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact Hp | look_fresh | exact Hα'Ξ | exact Hα'C ].
    -
      apply a_looksub__univ_ghost_l; [ assumption | assumption | ]; apply IHs;
        solve [ lia | assumption ]. }

  { intros Θ α P P' Ξ 𝒞 Hn Hd α' Hα'P Hα'Ξ Hα'C.
    destruct Hd as
      [ Θ α Q
      | Θ α Q Q' Hnf
      | Θ α Q
      | Θ α Q b γ Hfr0 Hflx Hne Hin
      | Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 Hp2
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hocc0 Hp
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hocc0 Hp
      | Θ α Q Q' Ξ0 C0 Hp
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hocc0 Hp
      | Θ α Q Q' Ξ0 C0 Hg Hfx Hp
      | Θ α Q Q' Ξ0 C0 Hne Hg Hp ];
      cbn in Hn, Hα'P |- *.
    -
      destruct_if as [_ | Hne]; [ | exfalso; congruence ].
      apply a_lookeq__var.
    -
      rewrite subst_pskl_in_pskl_fresh_eq by exact Hnf.
      apply a_lookeq__absent; exact Hα'P.
    -  apply a_lookeq__vacuous.
      apply subst_var_neq_new; assumption.
    -
      cbn in Hfr0, Hα'Ξ |- *.
      apply a_lookeq__flex_r;
        [ look_fresh
        | exact Hflx
        | apply subst_var_neq_new; assumption
        | apply ftv_subst_var_in; exact Hin ].
    -
      rewrite dom_app in Hα'Ξ. rewrite ftvar_in_a_cstrs_app in Hα'C.
      apply a_lookeq__arrow;
        [ exact Hg1 | exact Hg2 | apply IHe | apply IHe ];
        solve [ lia | assumption
              | clear - Hα'P; fsetdec | clear - Hα'Ξ; fsetdec
              | clear - Hα'C; fsetdec ].
    -
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + destruct (a_lookeq_rename_binder (ftvar_in_pskl Q `union` ftvar_in_pskl Q')
                    Hp Hbα HbΘ Hα'Ξ Hα'C) as [δ [Hδα [Hδ H1]]].
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
          by exact HbQ.
        rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f δ)) in H1
          by exact HbQ'.
        apply a_lookeq__forall_inh with (β := δ);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
          by (solve [ congruence | constructor ]).
        apply IHe;
          [ rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia
          | exact H1 | look_fresh | exact Hα'Ξ | exact Hα'C ].
      + apply a_lookeq__forall_inh with (β := b);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α'))
          by (solve [ congruence | constructor ]).
        apply IHe;
          [ rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia
          | exact Hp | look_fresh | exact Hα'Ξ | exact Hα'C ].
    -
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + destruct (a_lookeq_rename_binder (ftvar_in_pskl Q `union` ftvar_in_pskl Q')
                    Hp Hbα HbΘ Hα'Ξ Hα'C) as [δ [Hδα [Hδ H1]]].
        rewrite (subst_pskl_in_pskl_fresh_eq (pskl_univ_ghost Q')) in H1
          by exact HbQ'.
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
          by exact HbQ.
        apply a_lookeq__forall_syn with (β := δ);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
          by (solve [ congruence | constructor ]).
        apply IHe with (P' := pskl_univ_ghost Q');
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact H1 | look_fresh | exact Hα'Ξ | exact Hα'C ].
      + apply a_lookeq__forall_syn with (β := b);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α'))
          by (solve [ congruence | constructor ]).
        apply IHe with (P' := pskl_univ_ghost Q');
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hp | look_fresh | exact Hα'Ξ | exact Hα'C ].
    -
      apply a_lookeq__univ_ghost; apply IHe; solve [ lia | assumption ].
    -
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + destruct (a_lookeq_rename_binder (ftvar_in_pskl Q `union` ftvar_in_pskl Q')
                    Hp Hbα HbΘ Hα'Ξ Hα'C) as [δ [Hδα [Hδ H1]]].
        rewrite (subst_pskl_in_pskl_fresh_eq (pskl_univ_ghost Q)) in H1
          by exact HbQ.
        rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f δ)) in H1
          by exact HbQ'.
        apply a_lookeq__univ_ghost1 with (β := δ);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        apply IHe with (P := pskl_univ_ghost Q);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact H1 | cbn; exact HbQ | exact Hα'Ξ | exact Hα'C ].
      + apply a_lookeq__univ_ghost1 with (β := b);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        apply IHe with (P := pskl_univ_ghost Q);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hp | cbn; exact Hα'P | exact Hα'Ξ | exact Hα'C ].
    -
      apply a_lookeq__univ_ghost2;
        [ exact Hg | exact Hfx | apply IHe; solve [ lia | assumption ] ].
    -
      apply a_lookeq__univ_ghost_r;
        [ apply subst_var_neq_new; assumption
        | apply guarded_pskl_subst_var; exact Hg
        | apply IHe; solve [ lia | assumption ] ]. }
Qed.

Lemma a_looksub_rename_var : forall Θ α m P P' Ξ 𝒞 α',
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  α' `notin` ftvar_in_pskl P ->
  α' `notin` dom Ξ -> α' `notin` ftvar_in_a_cstrs 𝒞 ->
  {{ Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞 }}a.
Proof.
  intros. eapply (proj1 (a_looksub_lookeq_rename_var_size
                           (2 * (size_pskl P + size_pskl P') + 1))); eauto.
Qed.

Lemma a_extract_family_of_instance : forall Θ0 NM M α P P0 Ξ P1,
  {{ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α)) ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}a ->
  α `notin` ftvar_in_pskl P ->
  exists L, forall α',
    α' `notin` (singleton α `union` ftvar_in_pskl P `union` L) ->
    {{ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α')) ⊳[ NM , α' , M ] P0 ⤳ Ξ ↪ P1 }}a.
Proof.
  intros Θ0 NM M α P P0 Ξ P1 Hex Hfr.
  inversion Hex as [ Θ0' NM' α'' m' Ps Ps' Ξl Ξs Ξg 𝒞l Q Q' Hlk Hsol Hgu
                     Hgd Hgd2 HeqΘ HeqNM Heqα Heqm HeqP HeqP0 ]; subst.
  exists (dom Ξl `union` ftvar_in_a_cstrs 𝒞l).
  intros α' Hα'.
  eapply a_extract__solve;
    [ | eassumption | eassumption | eassumption | eassumption ].
  assert (Hα'P : α' `notin`
                   ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                  P (pskl_var_f α)) as Hup.
    simpl in Hup. clear - Hα' Hup; fsetdec. }
  pose proof (a_looksub_rename_var Hlk Hα'P
                ltac:(clear - Hα'; solve_notin_auto) ltac:(clear - Hα'; solve_notin_auto))
    as Hlk'.
  rewrite <- (subst_pskl_in_pskl_intro α P (pskl_var_f α') Hfr) in Hlk'.
  exact Hlk'.
Qed.
