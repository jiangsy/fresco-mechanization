Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_typing.

Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.typing.prop_typing_closed.
Require Import src.fresco.algo_decl.prop_conservativity.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.typing.def_typing.
Require Import src.fresco.ext_algo.typing.prop_typing.
Require Import src.fresco.ext_algo.consistency.def_consis_impl.
Require Import src.fresco.ext_algo.subtyping.def_sub_impl.
Require Import src.fresco.ext_algo.typing.def_typing_impl.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.typing.prop_typing_complete.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.typing.prop_soundness_typing.
Require Import src.fresco.ext_algo.subtyping.prop_solve_rel.
Require Import src.fresco.ext_algo.lifting.prop_lift_context.
Require Import src.fresco.ext_algo.lifting.prop_lift.
Require Import src.fresco.ext_algo.lifting.prop_lift_typing.
Require Import src.fresco.algo_decl.prop_precision.

Open Scope fresco_e_scope.

Corollary e_typing_run_sound_infer : forall e r,
  {{ nil ⊢ᵉ e }}a ->
  e_typing_run (entry_supply pskl_ghost e)
    mode_ti nil pskl_ghost e = Some r ->
  nil ⊴ (ty_ctx r) /\ {{ ⊢ (ty_ctx r) }}a /\ a_wf_ptyp (ty_ctx r) (ty_out r) /\
  ({{ (ty_ctx r) ⨟ empty ⊢ᵣ bskl_ghost
      ⊳ (btyp_to_bskl (ptyp_to_btyp_syn (ty_out r))) }}ad) /\
  exists ζ, ζ ∷ (ty_ctx r) ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_ti ]
        e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ (ty_out r))) }}d) /\
    ({{ nil ⊢[ mode_ti ]
        e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ (ty_out r))) }}d).
Proof.
  intros e r Hexp Hrun.
  apply e_typing_run_sound in Hrun.
  apply e_typing_sound_init in Hrun.
  apply a_typing_sound_infer; assumption.
Qed.

Lemma e_typing_run_complete_unit_infer : forall S0,
  e_typing_run S0 mode_ti nil pskl_ghost exp_unit
  = Some (mk_typing_result S0 nil ptyp_unit).
Proof.
  intros. unfold e_typing_run.
  simp e_typing_impl.
  cbn.
  unfold e_sub_impl.
  simp e_sub_call_impl.
  cbn.
  reflexivity.
Qed.

Lemma e_typing_run_complete_unit_check : forall S0,
  e_typing_run S0 mode_tc nil (ptyp_to_pskl ptyp_unit) exp_unit
  = Some (mk_typing_result S0 nil ptyp_unit).
Proof.
  intros. unfold e_typing_run.
  simp e_typing_impl.
  cbn.
  unfold e_sub_impl.
  simp e_sub_call_impl.
  cbn.
  unfold e_consis_impl.
  simp e_consis_call_impl.
  cbn.
  reflexivity.
Qed.

Corollary e_typing_run_complete_init : forall m P0 e Sd Θd Bd,
  {{ (entry_supply P0 e) ↝ Sd
     ⊨ nil ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e ->
  lc_pskl P0 -> lc_exp e ->
  exists r,
    e_typing_run (entry_supply P0 e)
      m nil P0 e = Some r.
Proof.
  intros * Hd HP0 He.
  unfold entry_supply in Hd |- *.
  destruct (e_typing_run_complete Hd HP0 He lc_aenv_nil
              (List.Forall_nil _) (uniq_nil _)
              ltac:(simpl; fsetdec)) as [r [ps [Heq _]]].
  exists r. exact Heq.
Qed.

Definition e_typable (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) : Prop :=
  exists Sd Θd Bd, {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e.

Corollary e_typing_dec : forall S0 m Θ0 P0 e,
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
    [<=] S0 ->
  sumbool (e_typable S0 m Θ0 P0 e) (~ e_typable S0 m Θ0 P0 e).
Proof.
  intros S0 m Θ0 P0 e HP0 He HΘ HD Hu Hcov.
  destruct (e_typing_run S0 m Θ0 P0 e) as [ r | ] eqn:Hrun.
  -
    left. exists (ty_supply r), (ty_ctx r), (ty_out r).
    exact (e_typing_run_sound _ _ _ _ _ _ Hrun).
  -
    right. intros [Sd [Θd [Bd Hd]]].
    destruct (e_typing_run_complete Hd HP0 He HΘ HD Hu Hcov)
      as [r [ps [Heq _]]].
    rewrite Hrun in Heq. discriminate.
Qed.

Corollary e_typing_dec_init : forall m P0 e,
  lc_pskl P0 -> lc_exp e ->
  sumbool (e_typable (entry_supply P0 e) m nil P0 e)
          (~ e_typable (entry_supply P0 e) m nil P0 e).
Proof.
  intros m P0 e HP0 He.
  unfold entry_supply.
  apply e_typing_dec; try assumption;
    [ apply lc_aenv_nil | apply (List.Forall_nil _) | apply (uniq_nil _)
    | simpl; fsetdec ].
Qed.

Lemma lift_typing_nil_instance :
  rel_inj (@nil (atom * atom)%type) empty /\
  rel_fun (@nil (atom * atom)%type) empty (dom (@nil (atom * abind)%type)) /\
  flex_agree_rel (@nil (atom * atom)%type) empty
    (@nil (atom * abind)%type) (@nil (atom * abind)%type).
Proof.
  split; [ | split ].
  - intros a1 a2 b H1 H2.
    inversion H1 as [ u1 v1 Hp | u1 Hv ]; subst; [ inversion Hp | ].
    inversion H2 as [ u2 v2 Hp2 | u2 Hv2 ]; subst;
      [ inversion Hp2 | reflexivity ].
  - intros a b1 b2 Hd0 H1 H2.
    inversion H1 as [ u1 v1 Hp | u1 Hv ]; subst; [ inversion Hp | ].
    inversion H2 as [ u2 v2 Hp2 | u2 Hv2 ]; subst;
      [ inversion Hp2 | reflexivity ].
  - split;
      [ intros v Hv; exfalso; clear - Hv; fsetdec
      | intros a b Hin; inversion Hin ].
Qed.

Lemma e_typing_run_complete_closed {m P e B Θ1} :
  {{ nil ⊢ᵉ e }}a ->
  {{ (@nil (atom * abind)%type) ⨟ empty ⊢ₚₛ P }}a -> lc_pskl P ->
  ftvar_in_pskl P [<=] empty -> a_ty_mode_compat m P ->
  {{ nil ⊢[ m ; P ] e ⦂ B ⊣ Θ1 }}a ->
  exists r, e_typing_run (entry_supply P e) m nil P e = Some r.
Proof.
  intros Hwfe HwfP HlcP HftP Hmod Ha.
  destruct lift_typing_nil_instance as (Hinj & Hfun & Hagr).
  assert (Hfv : fvar_in_exp e [<=] empty).
  { intros z Hz. destruct (a_typing_fvar_binds Ha Hz) as (bd & Hb & _).
    inversion Hb. }
  assert (Hftv : ftvar_in_exp e [<=] empty).
  { pose proof (a_wf_exp_ftv_dom Hwfe) as Hb. simpl in Hb. exact Hb. }
  assert (H1 : rel_aenv (@nil (atom * atom)%type) empty
                 (@nil (atom * abind)%type) (@nil (atom * abind)%type))
    by apply rel_aenv__nil.
  assert (H2 : rel_pskl (@nil (atom * atom)%type) empty P P)
    by (apply rel_pskl_refl; clear - HftP; fsetdec).
  assert (H3 : rel_exp (@nil (atom * atom)%type) empty e e)
    by (apply rel_exp_refl; clear - Hfv Hftv; fsetdec).
  assert (H7 : {{ ⊢ (@nil (atom * abind)%type) }}a) by apply a_wf_aenv__nil.
  assert (H8 : uniq (@nil (atom * abind)%type)) by apply uniq_nil.
  assert (H9 : ftvar_in_aenv (@nil (atom * abind)%type)
               [<=] ftvar_in_pskl P ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H10 : empty [<=] ftvar_in_aenv (@nil (atom * abind)%type))
    by (clear; fsetdec).
  assert (H11 : forall a, a `in` dom Θ1 ->
                a `notin` dom (@nil (atom * abind)%type) ->
                a `notin` cols_l (@nil (atom * atom)%type))
    by (intros a Hx Hy Hc; simpl in Hc; clear - Hc; fsetdec).
  assert (H12 : dom (@nil (atom * abind)%type)
                [<=] ftvar_in_pskl P ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H13 : empty ∪ cols_r (@nil (atom * atom)%type)
                [<=] ftvar_in_pskl P ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H14 : ftvar_in_pskl P ∪ ftvar_in_exp e ∪ fvar_in_exp e
                [<=] ftvar_in_pskl P ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (clear; fsetdec).
  destruct (a_typing_rel_e Ha H1 H2 H3 Hagr Hinj Hfun H7 H8 H9 H10 H11
              H12 H13 H14 HwfP Hwfe Hmod)
    as (S1 & ρe & Θ1e & Be & De & _).
  exact (e_typing_run_complete_init _ _ _ _ _ _ De HlcP (a_wf_exp_lc Hwfe)).
Qed.

Corollary e_typing_run_complete_decl_infer : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}d ->
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists r,
    e_typing_run (entry_supply pskl_ghost e)
      mode_ti nil pskl_ghost e = Some r.
Proof.
  intros e B Hwfd Hd.
  pose proof (d_wf_exp_to_a _ _ Hwfd) as Hwfe. simpl in Hwfe.
  destruct (a_typing_complete_decl_infer Hwfe Hd) as (A1 & Θ1 & Ha & _).
  assert (Hft : ftvar_in_pskl pskl_ghost [<=] empty) by (simpl; fsetdec).
  exact (e_typing_run_complete_closed Hwfe (a_wf_pskl__ghost _ _)
           lc_pskl_ghost Hft a_ty_mode_compat__ti Ha).
Qed.

Corollary e_typing_run_complete_decl_check : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}d ->
  d_wf_ptyp nil (btyp_to_ptyp B) ->
  {{ nil ⊢[ mode_tc ] e ⦂ B }}d ->
  exists r,
    e_typing_run (entry_supply (ptyp_to_pskl (btyp_to_ptyp B)) e)
      mode_tc nil (ptyp_to_pskl (btyp_to_ptyp B)) e = Some r.
Proof.
  intros e B Hwfd HwfBd Hd.
  pose proof (d_wf_exp_to_a _ _ Hwfd) as Hwfe. simpl in Hwfe.
  pose proof (d_wf_ptyp_to_a _ _ HwfBd) as HwfB. simpl in HwfB.
  destruct (a_typing_complete_decl_check Hwfe Hd) as (A1 & Θ1 & Ha & _).
  assert (HftB : ftvar_in_pskl (ptyp_to_pskl (btyp_to_ptyp B)) [<=] empty).
  { pose proof (ftvar_ptyp_to_pskl (btyp_to_ptyp B)) as He.
    pose proof (a_wf_ptyp_ftv_dom HwfB) as Hb. simpl in Hb.
    clear - He Hb. fsetdec. }
  exact (e_typing_run_complete_closed Hwfe (a_wf_ptyp_to_wf_pskl empty HwfB)
           (ptyp_to_pskl_lc (a_wf_ptyp_lc HwfB)) HftB
           (a_ty_mode_compat__tc _) Ha).
Qed.

Definition fresco_infer (e : exp) (Hwf : {{ nil ⊢ᵉ e }}d) :
  sumor
    (sig (fun r : typing_result =>
       e_typing_run (entry_supply pskl_ghost e)
         mode_ti nil pskl_ghost e = Some r /\
       exists ζ, ζ ∷ (ty_ctx r) ⊑ nil /\
         {{ nil ⊢[ mode_ti ]
            e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ (ty_out r))) }}d))
    (~ exists B : btyp, {{ nil ⊢[ mode_ti ] e ⦂ B }}d).
Proof.
  destruct (e_typing_run
              (entry_supply pskl_ghost e)
              mode_ti nil pskl_ghost e) as [ r | ] eqn:Hrun.
  -
    apply inleft.
    refine (exist _ r (conj eq_refl _)).
    pose proof (d_wf_exp_to_a _ _ Hwf) as Hwfe. simpl in Hwfe.
    destruct (e_typing_run_sound_infer _ _ Hwfe Hrun)
      as (_ & _ & _ & _ & ζ & Hinc & _ & Hdd).
    exact (ex_intro _ ζ (conj Hinc Hdd)).
  -
    apply inright.
    intros [B Hd].
    destruct (e_typing_run_complete_decl_infer _ _ Hwf Hd) as [r Hr].
    rewrite Hrun in Hr. discriminate.
Defined.

Lemma fresco_infer_complete : forall e (Hwf : {{ nil ⊢ᵉ e }}d) (B : btyp),
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists H', fresco_infer e Hwf = inleft H'.
Proof.
  intros e Hwf B Hd.
  destruct (fresco_infer e Hwf) as [ H' | Hno ];
    [ exists H'; reflexivity | exfalso; exact (Hno (ex_intro _ B Hd)) ].
Qed.

Corollary d_typing_infer_dec : forall e,
  {{ nil ⊢ᵉ e }}d ->
  sumbool (exists B : btyp, {{ nil ⊢[ mode_ti ] e ⦂ B }}d)
          (~ exists B : btyp, {{ nil ⊢[ mode_ti ] e ⦂ B }}d).
Proof.
  intros e Hwf.
  destruct (fresco_infer e Hwf) as [ [r Hfact] | Hno ];
    [ left | right; exact Hno ].
  destruct Hfact as [_ [ζ [_ Hdd]]].
  exists (ptyp_to_btyp_syn (msubst_ptyp ζ (ty_out r))). exact Hdd.
Qed.
