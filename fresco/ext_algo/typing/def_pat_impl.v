Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_ln.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_uip.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.def_sub.
Require Import src.fresco.ext_algo.typing.def_pat.
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.consistency.def_consis_impl.
Require Import src.fresco.ext_algo.subtyping.def_sub_impl.

Set Equations With UIP.

Open Scope fresco_e_scope.

Fixpoint degree_ptyp_ck (n : nat) (A : ptyp) : bool :=
  match A with
  | ptyp_unit => true
  | ptyp_var_b m => Nat.ltb m n
  | ptyp_var_f _ => true
  | ptyp_arrow A1 A2 => degree_ptyp_ck n A1 && degree_ptyp_ck n A2
  | ptyp_all A1 => degree_ptyp_ck (S n) A1
  end.

Lemma degree_ptyp_ck_sound : forall A k,
  degree_ptyp_ck k A = true -> degree_ptyp_wrt_ptyp k A.
Proof.
  induction A; simpl; intros k Hck; try constructor; try discriminate;
    try solve [ apply IHA; exact Hck ].
  - apply Nat.ltb_lt; exact Hck.
  - apply andb_prop in Hck; destruct Hck; apply IHA1; assumption.
  - apply andb_prop in Hck; destruct Hck; apply IHA2; assumption.
Qed.

Corollary lc_ptyp_ck_sound : forall A,
  degree_ptyp_ck 0 A = true -> lc_ptyp A.
Proof. intros; apply lc_ptyp_of_degree, degree_ptyp_ck_sound; assumption. Qed.

Fixpoint degree_pskl_ck (n : nat) (P : pskl) : bool :=
  match P with
  | pskl_unit => true
  | pskl_var_b m => Nat.ltb m n
  | pskl_var_f _ => true
  | pskl_arrow P1 P2 => degree_pskl_ck n P1 && degree_pskl_ck n P2
  | pskl_all_syn P1 => degree_pskl_ck (S n) P1
  | pskl_ghost => true
  | pskl_univ_ghost P1 => degree_pskl_ck n P1
  end.

Lemma degree_pskl_ck_sound : forall P k,
  degree_pskl_ck k P = true -> degree_pskl_wrt_pskl k P.
Proof.
  induction P; simpl; intros k Hck; try constructor; try discriminate;
    try solve [ apply IHP; exact Hck ].
  - apply Nat.ltb_lt; exact Hck.
  - apply andb_prop in Hck; destruct Hck; apply IHP1; assumption.
  - apply andb_prop in Hck; destruct Hck; apply IHP2; assumption.
Qed.

Corollary lc_pskl_ck_sound : forall P,
  degree_pskl_ck 0 P = true -> lc_pskl P.
Proof. intros; apply lc_pskl_of_degree, degree_pskl_ck_sound; assumption. Qed.

Definition entry_def_mono_ck (xb : atom * abind) : bool :=
  match snd xb with
  | abind_flex_mono_def τ => mono_ck τ
  | _ => true
  end.

Fixpoint defs_mono_ck (Θ : aenv) : bool :=
  match Θ with
  | nil => true
  | xb :: Θ' => entry_def_mono_ck xb && defs_mono_ck Θ'
  end.

Lemma defs_mono_ck_sound : forall Θ,
  defs_mono_ck Θ = true -> aenv_defs_mono Θ.
Proof.
  induction Θ as [ | [x b] Θ' IH ]; simpl; intros Hck; [ constructor | ].
  apply andb_prop in Hck; destruct Hck as [He Ht].
  constructor; [ | apply IH; exact Ht ].
  destruct b; simpl in He; try exact I.
  simpl. apply mono_ck_sound; exact He.
Qed.

Fixpoint ptyp_eqb (A B : ptyp) : bool :=
  match A, B with
  | ptyp_unit, ptyp_unit => true
  | ptyp_var_b n, ptyp_var_b m => Nat.eqb n m
  | ptyp_var_f α, ptyp_var_f β => if α == β then true else false
  | ptyp_arrow A1 A2, ptyp_arrow B1 B2 => ptyp_eqb A1 B1 && ptyp_eqb A2 B2
  | ptyp_all A1, ptyp_all B1 => ptyp_eqb A1 B1
  | _, _ => false
  end.

Lemma ptyp_eqb_sound : forall A B, ptyp_eqb A B = true -> A = B.
Proof.
  induction A; destruct B; simpl; intros Hck; try discriminate;
    try reflexivity.
  - apply Nat.eqb_eq in Hck; subst; reflexivity.
  - destruct (α == α0); [ subst; reflexivity | discriminate ].
  - apply andb_prop in Hck; destruct Hck.
    erewrite IHA1, IHA2 by eassumption; reflexivity.
  - erewrite IHA by eassumption; reflexivity.
Qed.

Definition lookup_binding (x : atom)
    : forall Θ : aenv, option (sig (fun b : abind => binds x b Θ)).
Proof.
  refine (fix go (Θ : aenv)
      : option (sig (fun b : abind => binds x b Θ)) :=
    match Θ with
    | nil => None
    | (y, b) :: Θ' =>
        match x == y with
        | left Heq => Some (exist _ b _)
        | right _ =>
            match go Θ' with
            | Some (exist _ b' Hb') => Some (exist _ b' _)
            | None => None
            end
        end
    end).
  - rewrite Heq; unfold binds; left; reflexivity.
  - unfold binds in *; right; exact Hb'.
Defined.

Definition arrow_split (P : pskl)
    : option (sig (fun p : pskl * pskl
                   => P = pskl_arrow (fst p) (snd p))) :=
  match P with
  | pskl_arrow P1 P2 => Some (exist _ (P1, P2) eq_refl)
  | _ => None
  end.

Definition abind_var_skl_get (b : abind)
    : option (sig (fun P : pskl => b = abind_var_skl P)) :=
  match b with
  | abind_var_skl P => Some (exist _ P eq_refl)
  | _ => None
  end.

Definition abind_var_typ_get (b : abind)
    : option (sig (fun A : ptyp => b = abind_var_typ A)) :=
  match b with
  | abind_var_typ A => Some (exist _ A eq_refl)
  | _ => None
  end.

Definition split_at_key_skl (x : atom)
    : forall Θ : aenv,
      option (sig (fun t : aenv * pskl * aenv
                   => Θ = fst (fst t) ++ (x ~ abind_var_skl (snd (fst t)))
                          ++ snd t)).
Proof.
  refine (fix go (Θ : aenv)
      : option (sig (fun t : aenv * pskl * aenv
                     => Θ = fst (fst t)
                            ++ (x ~ abind_var_skl (snd (fst t))) ++ snd t)) :=
    match Θ with
    | nil => None
    | (y, b) :: Θ' =>
        match x == y with
        | left Heq =>
            match abind_var_skl_get b with
            | Some (exist _ P HP) => Some (exist _ (nil, P, Θ') _)
            | None => None
            end
        | right _ =>
            match go Θ' with
            | Some (exist _ t Ht) =>
                Some (exist _ ((y, b) :: fst (fst t), snd (fst t), snd t) _)
            | None => None
            end
        end
    end).
  - simpl; rewrite Heq; rewrite HP; reflexivity.
  - simpl; rewrite Ht at 1; reflexivity.
Defined.

Definition split_at_key_typ (x : atom)
    : forall Θ : aenv,
      option (sig (fun t : aenv * ptyp * aenv
                   => Θ = fst (fst t) ++ (x ~ abind_var_typ (snd (fst t)))
                          ++ snd t)).
Proof.
  refine (fix go (Θ : aenv)
      : option (sig (fun t : aenv * ptyp * aenv
                     => Θ = fst (fst t)
                            ++ (x ~ abind_var_typ (snd (fst t))) ++ snd t)) :=
    match Θ with
    | nil => None
    | (y, b) :: Θ' =>
        match x == y with
        | left Heq =>
            match abind_var_typ_get b with
            | Some (exist _ A HA) => Some (exist _ (nil, A, Θ') _)
            | None => None
            end
        | right _ =>
            match go Θ' with
            | Some (exist _ t Ht) =>
                Some (exist _ ((y, b) :: fst (fst t), snd (fst t), snd t) _)
            | None => None
            end
        end
    end).
  - simpl; rewrite Heq; rewrite HA; reflexivity.
  - simpl; rewrite Ht at 1; reflexivity.
Defined.

Definition pskl_readback
    : forall P : pskl, option (sig (fun A : ptyp => P = ptyp_to_pskl A)).
Proof.
  refine (fix go (P : pskl)
      : option (sig (fun A : ptyp => P = ptyp_to_pskl A)) :=
    match P with
    | pskl_unit => Some (exist _ ptyp_unit eq_refl)
    | pskl_var_b n => Some (exist _ (ptyp_var_b n) eq_refl)
    | pskl_var_f α => Some (exist _ (ptyp_var_f α) eq_refl)
    | pskl_arrow P1 P2 =>
        match go P1 with
        | None => None
        | Some (exist _ A1 H1) =>
            match go P2 with
            | None => None
            | Some (exist _ A2 H2) =>
                Some (exist _ (ptyp_arrow A1 A2) _)
            end
        end
    | pskl_all_syn P1 =>
        match go P1 with
        | None => None
        | Some (exist _ A1 H1) => Some (exist _ (ptyp_all A1) _)
        end
    | pskl_ghost => None
    | pskl_univ_ghost _ => None
    end); simpl; subst; reflexivity.
Defined.

Definition pskl_readback_all (P : pskl)
    : option (sig (fun A0 : ptyp => P = ptyp_to_pskl (ptyp_all A0))) :=
  match P with
  | pskl_all_syn P1 =>
      match pskl_readback P1 with
      | None => None
      | Some (exist _ A1 H1) =>
          Some (exist _ A1
                  (f_equal pskl_all_syn H1
                   : pskl_all_syn P1 = ptyp_to_pskl (ptyp_all A1)))
      end
  | _ => None
  end.

Lemma inter_empty_notin_all : forall S1 S2,
  is_empty (inter S1 S2) = true ->
  forall γ, γ `in` S1 -> γ `notin` S2.
Proof.
  intros S1 S2 Hck γ Hin Hin2.
  apply AtomSetFacts.is_empty_iff in Hck.
  exact (Hck γ (inter_3 Hin Hin2)).
Qed.

Inductive e_pat_order : supply -> mode -> aenv -> pskl -> exp -> Prop :=
| e_pat_order__intro : forall S0 m Θ0 P0 e,

    (forall e1, e = exp_freeze e1 ->
       e_pat_order S0 mode_ti Θ0 pskl_ghost e1) ->

    (forall e1, e = exp_abs e1 ->
       forall S1 Θ1 P Q0, {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}e ->
       e_pat_order (add (supply_fresh S1) S1) (decr_mode m)
         ((supply_fresh S1 ~ abind_var_skl P) ++ Θ1) Q0
         (open_exp_wrt_exp e1 (exp_var_f (supply_fresh S1)))) ->

    (forall A e1, e = exp_abs_anno A e1 ->
       forall S1 Θ1 P Q0, {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}e ->
       forall S2 Θ2 Qc,
         {{ S1 ↝ S2 ⊨ Θ1 ⊢[ empty | empty | P ]
            (ptyp_to_pskl A) ∼ Qc ⊣ Θ2 }}e ->
       e_pat_order (add (supply_fresh S2) S2) (decr_mode m)
         ((supply_fresh S2 ~ abind_var_typ A) ++ Θ2) Q0
         (open_exp_wrt_exp e1 (exp_var_f (supply_fresh S2)))) ->

    (forall e1, e = exp_abs e1 ->
       e_pat_order (add (supply_fresh S0) S0) mode_tc
         ((supply_fresh S0 ~ abind_var_skl pskl_ghost) ++ Θ0) pskl_ghost
         (open_exp_wrt_exp e1 (exp_var_f (supply_fresh S0)))) ->

    (forall A e1, e = exp_abs_anno A e1 ->
       e_pat_order (add (supply_fresh S0) S0) mode_tc
         ((supply_fresh S0 ~ abind_var_typ A) ++ Θ0) pskl_ghost
         (open_exp_wrt_exp e1 (exp_var_f (supply_fresh S0)))) ->
    (forall e1 e2, e = exp_app e1 e2 ->
       e_pat_order S0 mode_tc Θ0 pskl_ghost e2) ->
    (forall e1 e2, e = exp_app e1 e2 ->
       forall S1 Θ1 P1,
         {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] e2 ⦂ P1 ⊣ Θ1 }}e ->
       e_pat_order S1 (mode_fn m) Θ1 (pskl_arrow P1 P0) e1) ->
    e_pat_order S0 m Θ0 P0 e.

Lemma e_pat_order_total_n : forall n S0 m Θ0 P0 e,
  size_exp e <= n -> e_pat_order S0 m Θ0 P0 e.
Proof.
  induction n as [ n IH ] using lt_wf_ind; intros * Hsz.
  destruct n as [ | n' ];
    [ pose proof (size_exp_min e); exfalso; lia | ].
  constructor; intros; subst; simpl in Hsz;
    (match goal with
     | |- e_pat_order _ _ _ _ ?e' => apply (IH (size_exp e'))
     end;
     [ try rewrite size_exp_open_exp_wrt_exp_var; lia
     | apply le_n ]).
Qed.

Theorem e_pat_order_total : forall S0 m Θ0 P0 e,
  e_pat_order S0 m Θ0 P0 e.
Proof. intros; eapply e_pat_order_total_n; apply le_n. Qed.

Record split_result : Type := mk_split_result {
  sp_supply : supply;
  sp_ctx    : aenv;
  sp_dom    : pskl;
  sp_cod    : pskl
}.

Definition split_spec (S0 : supply) (Θ0 : aenv) (P0 : pskl)
    (r : split_result) : Prop :=
  {{ S0 ↝ (sp_supply r) ⊨ Θ0 ⊲ P0 ▹ (sp_dom r) ⇢ (sp_cod r)
     ⊣ (sp_ctx r) }}e.

Record pat_result : Type := mk_pat_result {
  pt_supply : supply;
  pt_ctx    : aenv;
  pt_skel   : pskl
}.

Definition pat_spec (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) (r : pat_result) : Prop :=
  {{ S0 ↝ (pt_supply r) ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ (pt_skel r)
     ⊣ (pt_ctx r) }}e.

#[local] Hint Resolve supply_fresh_notin mem_true_in mem_false_notin
  lc_pskl_ck_sound lc_ptyp_ck_sound defs_mono_ck_sound
  ptyp_to_pskl_lc pskl_eqb_sound ptyp_eqb_sound suffix_ck_sound
  e_consis_order_total e_sub_order_total
  e_consis_defs_mono lc_pskl_all_syn_inv : patdec.
#[local] Hint Constructors e_split lc_pskl lc_ptyp : patdec.
#[local] Hint Extern 4 (_ <> _) => congruence : patdec.
#[local] Hint Extern 3 (e_consis_chk _ _ _ _ _ _) =>
  (unfold e_consis_chk; eexists; eassumption) : patdec.

#[local] Hint Extern 4 (Forall entry_def_mono _) =>
  repeat first [ assumption
               | apply defs_mono_ck_sound; assumption
               | apply Forall_app_intro
               | apply List.Forall_cons
               | apply List.Forall_nil ];
  auto using entry_def_mono_flex, entry_def_mono_tvar,
    entry_def_mono_var_typ, entry_def_mono_var_skl, entry_def_mono_def
  : patdec.

#[local] Ltac pat_impl_tac :=
  cbv zeta; intros;
  try match goal with
      | H : e_pat_order _ _ _ _ _ |- _ => inversion H; subst
      end;
  unfold split_spec, pat_spec, consis_spec, sub_spec, guess_spec in *;
  repeat match goal with
         | Hb : _ && _ = true |- _ => apply andb_prop in Hb; destruct Hb
         end;

  repeat match goal with
         | He : pskl_eqb _ _ = true |- _ => apply pskl_eqb_sound in He
         | He : ptyp_eqb _ _ = true |- _ => apply ptyp_eqb_sound in He
         end;
  simpl in *; try subst;

  repeat match goal with
         | Hc : snd (fst _) = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : pt_ctx _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : pt_skel _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : sp_dom _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : sp_cod _ = _ |- _ => rewrite Hc in *; clear Hc
         | Hc : sb_out _ = _ |- _ => rewrite Hc in *; clear Hc
         end;
  try congruence;
  try solve [ eauto 7 with patdec ];
  solve [ econstructor; eauto 6 with patdec ].

#[tactic="pat_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_split_impl (S0 : supply) (Θ0 : aenv) (P0 : pskl)
    : option (sig (split_spec S0 Θ0 P0)) :=

| S0, Θ0, pskl_arrow P Q =>
    Some (exist _ (mk_split_result S0 Θ0 P Q) _)
| S0, Θ0, pskl_ghost =>
    Some (exist _ (mk_split_result S0 Θ0 pskl_ghost pskl_ghost) _)
| S0, Θ0, pskl_var_f α =>
    match sumbool_of_bool (defs_mono_ck Θ0) with
    | right _ => None
    | left _ =>
        match e_consis_impl empty empty
                (add (supply_fresh (add (supply_fresh S0) S0))
                   (add (supply_fresh S0) S0))
                ((supply_fresh (add (supply_fresh S0) S0)
                    ~ abind_flex_mono)
                   ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0)
                (pskl_arrow (pskl_var_f (supply_fresh S0))
                   (pskl_var_f (supply_fresh (add (supply_fresh S0) S0))))
                (pskl_var_f α) _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_split_result (cs_supply r) (cs_ctx r)
                    (pskl_var_f (supply_fresh S0))
                    (pskl_var_f
                       (supply_fresh (add (supply_fresh S0) S0)))) _)
        end
    end
| S0, Θ0, P0 => None.

#[tactic="pat_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_pat_impl (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) (H : e_pat_order S0 m Θ0 P0 e)
    : option (sig (pat_spec S0 m Θ0 P0 e)) by struct H :=

| S0, m, Θ0, P0, exp_unit, H =>
    match sumbool_of_bool (degree_pskl_ck 0 P0 && defs_mono_ck Θ0) with
    | right _ => None
    | left _ =>
        match e_sub_impl S0 a_sub_mode_sk m P0 Θ0 pskl_unit _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_pat_result (sb_supply r) (sb_ctx r)
                    (sb_out r)) _)
        end
    end

| S0, m, Θ0, P0, exp_var_f x, H =>
    match lookup_binding x Θ0 with
    | None => None
    | Some (exist _ b Hb) =>
        match abind_var_typ_get b with
        | Some (exist _ A HA) =>
            match sumbool_of_bool (degree_ptyp_ck 0 A
                                   && degree_pskl_ck 0 P0
                                   && defs_mono_ck Θ0) with
            | right _ => None
            | left _ =>
                match e_sub_impl S0 a_sub_mode_sk m P0 Θ0 (ptyp_to_pskl A)
                        _ _ _ _ with
                | None => None
                | Some (exist _ r Hr) =>
                    Some (exist _ (mk_pat_result (sb_supply r) (sb_ctx r)
                            (sb_out r)) _)
                end
            end
        | None =>
            match abind_var_skl_get b with
            | None => None
            | Some (exist _ P HP) =>
                match sumbool_of_bool (degree_pskl_ck 0 P
                                       && degree_pskl_ck 0 P0
                                       && defs_mono_ck Θ0) with
                | right _ => None
                | left _ =>
                    match e_sub_impl S0 a_sub_mode_sk m P0 Θ0 P
                            _ _ _ _ with
                    | None => None
                    | Some (exist _ r Hr) =>
                        Some (exist _ (mk_pat_result (sb_supply r)
                                (sb_ctx r) (sb_out r)) _)
                    end
                end
            end
        end
    end

| S0, m, Θ0, P0, exp_anno e1 A, H =>
    match sumbool_of_bool (degree_ptyp_ck 0 A && degree_pskl_ck 0 P0
                           && defs_mono_ck Θ0) with
    | right _ => None
    | left _ =>
        match e_sub_impl S0 a_sub_mode_sk m P0 Θ0 (ptyp_to_pskl A)
                _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_pat_result (sb_supply r) (sb_ctx r)
                    (sb_out r)) _)
        end
    end

| S0, mode_tc, Θ0, pskl_ghost, exp_freeze e1, H =>
    match e_pat_impl S0 mode_ti Θ0 pskl_ghost e1 _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, m, Θ0, P0, exp_freeze e1, H => None

| S0, mode_ti, Θ0, P0, exp_abs e1, H =>
    match e_split_impl S0 Θ0 P0 with
    | None => None
    | Some (exist _ rs Hrs) =>
        match e_pat_impl (add (supply_fresh (sp_supply rs)) (sp_supply rs))
                (decr_mode mode_ti)
                ((supply_fresh (sp_supply rs) ~ abind_var_skl (sp_dom rs))
                   ++ sp_ctx rs)
                (sp_cod rs)
                (open_exp_wrt_exp e1
                   (exp_var_f (supply_fresh (sp_supply rs)))) _ with
        | None => None
        | Some (exist _ r Hr) =>
            match split_at_key_skl (supply_fresh (sp_supply rs))
                    (pt_ctx r) with
            | None => None
            | Some (exist _ t HΘ) =>
                match sumbool_of_bool
                        (pskl_eqb (snd (fst t)) (sp_dom rs)
                         && suffix_ck (fst (fst t))) with
                | right _ => None
                | left _ =>
                    Some (exist _ (mk_pat_result (pt_supply r)
                            (fst (fst t) ++ snd t)
                            (pskl_arrow (sp_dom rs) (pt_skel r))) _)
                end
            end
        end
    end
| S0, mode_fn m', Θ0, P0, exp_abs e1, H =>
    match e_split_impl S0 Θ0 P0 with
    | None => None
    | Some (exist _ rs Hrs) =>
        match e_pat_impl (add (supply_fresh (sp_supply rs)) (sp_supply rs))
                (decr_mode (mode_fn m'))
                ((supply_fresh (sp_supply rs) ~ abind_var_skl (sp_dom rs))
                   ++ sp_ctx rs)
                (sp_cod rs)
                (open_exp_wrt_exp e1
                   (exp_var_f (supply_fresh (sp_supply rs)))) _ with
        | None => None
        | Some (exist _ r Hr) =>
            match split_at_key_skl (supply_fresh (sp_supply rs))
                    (pt_ctx r) with
            | None => None
            | Some (exist _ t HΘ) =>
                match sumbool_of_bool
                        (pskl_eqb (snd (fst t)) (sp_dom rs)
                         && suffix_ck (fst (fst t))) with
                | right _ => None
                | left _ =>
                    Some (exist _ (mk_pat_result (pt_supply r)
                            (fst (fst t) ++ snd t)
                            (pskl_arrow (sp_dom rs) (pt_skel r))) _)
                end
            end
        end
    end

| S0, mode_tc, Θ0, pskl_ghost, exp_abs e1, H =>
    match e_pat_impl (add (supply_fresh S0) S0) mode_tc
            ((supply_fresh S0 ~ abind_var_skl pskl_ghost) ++ Θ0) pskl_ghost
            (open_exp_wrt_exp e1 (exp_var_f (supply_fresh S0))) _ with
    | None => None
    | Some (exist _ r Hr) =>
        match split_at_key_skl (supply_fresh S0) (pt_ctx r) with
        | None => None
        | Some (exist _ t HΘ) =>
            match sumbool_of_bool (pskl_eqb (snd (fst t)) pskl_ghost
                                   && suffix_ck (fst (fst t))) with
            | right _ => None
            | left _ =>
                Some (exist _ (mk_pat_result (pt_supply r)
                        (fst (fst t) ++ snd t)
                        (pskl_univ_ghost
                           (pskl_arrow pskl_ghost (pt_skel r)))) _)
            end
        end
    end
| S0, mode_tc, Θ0, P0, exp_abs e1, H => None

| S0, mode_ti, Θ0, P0, exp_abs_anno A e1, H =>
    match e_split_impl S0 Θ0 P0 with
    | None => None
    | Some (exist _ rs Hrs) =>
        match sumbool_of_bool (degree_ptyp_ck 0 A
                               && degree_pskl_ck 0 (sp_dom rs)
                               && defs_mono_ck (sp_ctx rs)) with
        | right _ => None
        | left _ =>
            match e_consis_impl empty empty (sp_supply rs) (sp_ctx rs)
                    (sp_dom rs) (ptyp_to_pskl A) _ _ _ _ with
            | None => None
            | Some (exist _ rc Hrc) =>
                match e_pat_impl
                        (add (supply_fresh (cs_supply rc)) (cs_supply rc))
                        (decr_mode mode_ti)
                        ((supply_fresh (cs_supply rc) ~ abind_var_typ A)
                           ++ cs_ctx rc)
                        (sp_cod rs)
                        (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh (cs_supply rc)))) _ with
                | None => None
                | Some (exist _ r Hr) =>
                    match split_at_key_typ (supply_fresh (cs_supply rc))
                            (pt_ctx r) with
                    | None => None
                    | Some (exist _ t HΘ) =>
                        match sumbool_of_bool
                                (ptyp_eqb (snd (fst t)) A
                                 && suffix_ck (fst (fst t))) with
                        | right _ => None
                        | left _ =>
                            Some (exist _ (mk_pat_result (pt_supply r)
                                    (fst (fst t) ++ snd t)
                                    (pskl_arrow (ptyp_to_pskl A)
                                       (pt_skel r))) _)
                        end
                    end
                end
            end
        end
    end
| S0, mode_fn m', Θ0, P0, exp_abs_anno A e1, H =>
    match e_split_impl S0 Θ0 P0 with
    | None => None
    | Some (exist _ rs Hrs) =>
        match sumbool_of_bool (degree_ptyp_ck 0 A
                               && degree_pskl_ck 0 (sp_dom rs)
                               && defs_mono_ck (sp_ctx rs)) with
        | right _ => None
        | left _ =>
            match e_consis_impl empty empty (sp_supply rs) (sp_ctx rs)
                    (sp_dom rs) (ptyp_to_pskl A) _ _ _ _ with
            | None => None
            | Some (exist _ rc Hrc) =>
                match e_pat_impl
                        (add (supply_fresh (cs_supply rc)) (cs_supply rc))
                        (decr_mode (mode_fn m'))
                        ((supply_fresh (cs_supply rc) ~ abind_var_typ A)
                           ++ cs_ctx rc)
                        (sp_cod rs)
                        (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh (cs_supply rc)))) _ with
                | None => None
                | Some (exist _ r Hr) =>
                    match split_at_key_typ (supply_fresh (cs_supply rc))
                            (pt_ctx r) with
                    | None => None
                    | Some (exist _ t HΘ) =>
                        match sumbool_of_bool
                                (ptyp_eqb (snd (fst t)) A
                                 && suffix_ck (fst (fst t))) with
                        | right _ => None
                        | left _ =>
                            Some (exist _ (mk_pat_result (pt_supply r)
                                    (fst (fst t) ++ snd t)
                                    (pskl_arrow (ptyp_to_pskl A)
                                       (pt_skel r))) _)
                        end
                    end
                end
            end
        end
    end

| S0, mode_tc, Θ0, pskl_ghost, exp_abs_anno A e1, H =>
    match e_pat_impl (add (supply_fresh S0) S0) mode_tc
            ((supply_fresh S0 ~ abind_var_typ A) ++ Θ0) pskl_ghost
            (open_exp_wrt_exp e1 (exp_var_f (supply_fresh S0))) _ with
    | None => None
    | Some (exist _ r Hr) =>
        match split_at_key_typ (supply_fresh S0) (pt_ctx r) with
        | None => None
        | Some (exist _ t HΘ) =>
            match sumbool_of_bool (ptyp_eqb (snd (fst t)) A
                                   && suffix_ck (fst (fst t))) with
            | right _ => None
            | left _ =>
                Some (exist _ (mk_pat_result (pt_supply r)
                        (fst (fst t) ++ snd t)
                        (pskl_univ_ghost
                           (pskl_arrow (ptyp_to_pskl A) (pt_skel r)))) _)
            end
        end
    end
| S0, mode_tc, Θ0, P0, exp_abs_anno A e1, H => None

| S0, m, Θ0, P0, exp_app e1 e2, H =>
    match e_pat_impl S0 mode_tc Θ0 pskl_ghost e2 _ with
    | None => None
    | Some (exist _ r2 Hr2) =>
        match e_pat_impl (pt_supply r2) (mode_fn m) (pt_ctx r2)
                (pskl_arrow (pt_skel r2) P0) e1 _ with
        | None => None
        | Some (exist _ r1 Hr1) =>
            match arrow_split (pt_skel r1) with
            | None => None
            | Some (exist _ p Hp) =>
                Some (exist _ (mk_pat_result (pt_supply r1) (pt_ctx r1)
                        (snd p)) _)
            end
        end
    end

| S0, m, Θ0, P0, exp_var_b n, H => None.

Definition e_pat_run (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) : option pat_result :=
  match e_pat_impl S0 m Θ0 P0 e (e_pat_order_total S0 m Θ0 P0 e) with
  | Some r => Some (proj1_sig r)
  | None => None
  end.

Lemma e_pat_run_sound : forall S0 m Θ0 P0 e r,
  e_pat_run S0 m Θ0 P0 e = Some r ->
  {{ S0 ↝ (pt_supply r) ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ (pt_skel r)
     ⊣ (pt_ctx r) }}e.
Proof.
  intros *. unfold e_pat_run.
  destruct (e_pat_impl S0 m Θ0 P0 e (e_pat_order_total S0 m Θ0 P0 e))
    as [ [r' Hr'] | ];
    intro Heq; inversion Heq; subst; exact Hr'.
Qed.
