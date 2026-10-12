Require Import Metalib.Metatheory.

Require Export src.fresco.def_ott.
Require Export src.fresco.prop_ln.

Definition decr_mode (m : mode) : mode :=
  match m with
  | mode_ti => mode_ti
  | mode_tc => mode_tc
  | mode_fn m' => m'
  end.

Fixpoint ftag_in_utyp (C : utyp) : atoms :=
  match C with
  | utyp_unit => {}
  | utyp_var_b _ => {}
  | utyp_var_f _ => {}
  | utyp_arrow C1 C2 => ftag_in_utyp C1 `union` ftag_in_utyp C2
  | utyp_all_syn C0 => ftag_in_utyp C0
  | utyp_all_tag ε C0 => add ε (ftag_in_utyp C0)
  end.

Fixpoint ftag_in_uskl (R : uskl) : atoms :=
  match R with
  | uskl_unit => {}
  | uskl_var_b _ => {}
  | uskl_var_f _ => {}
  | uskl_arrow R1 R2 => ftag_in_uskl R1 `union` ftag_in_uskl R2
  | uskl_all_syn R0 => ftag_in_uskl R0
  | uskl_all_tag ε R0 => add ε (ftag_in_uskl R0)
  | uskl_ghost => {}
  | uskl_univ_ghost R0 => ftag_in_uskl R0
  | uskl_dot_ghost => {}
  | uskl_dot_univ_ghost R0 => ftag_in_uskl R0
  end.

Inductive mono_ptyp : ptyp -> Prop :=
| mono_ptyp__unit  : mono_ptyp ptyp_unit
| mono_ptyp__var   : forall α, mono_ptyp (ptyp_var_f α)
| mono_ptyp__arrow : forall A1 A2,
    mono_ptyp A1 -> mono_ptyp A2 -> mono_ptyp (ptyp_arrow A1 A2).

Inductive is_dtyp : utyp -> Prop :=
| is_dtyp__unit  : is_dtyp utyp_unit
| is_dtyp__var   : forall α, is_dtyp (utyp_var_f α)
| is_dtyp__arrow : forall C1 C2,
    is_dtyp C1 -> is_dtyp C2 -> is_dtyp (utyp_arrow C1 C2)
| is_dtyp__all_tag   : forall L ε C,
    (forall α, α `notin` L ->
       is_dtyp (open_utyp_wrt_utyp C (utyp_var_f α))) ->
    is_dtyp (utyp_all_tag ε C).

Inductive is_dskl : uskl -> Prop :=
| is_dskl__unit    : is_dskl uskl_unit
| is_dskl__var     : forall α, is_dskl (uskl_var_f α)
| is_dskl__arrow   : forall R1 R2,
    is_dskl R1 -> is_dskl R2 -> is_dskl (uskl_arrow R1 R2)
| is_dskl__all_tag     : forall L ε R,
    (forall α, α `notin` L ->
       is_dskl (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    is_dskl (uskl_all_tag ε R)
| is_dskl__dot_ghost    : is_dskl uskl_dot_ghost
| is_dskl__dot_univ_ghost : forall R, is_dskl R -> is_dskl (uskl_dot_univ_ghost R).

Inductive is_styp : btyp -> Prop :=
| is_styp__unit  : is_styp btyp_unit
| is_styp__var   : forall α, is_styp (btyp_var_f α)
| is_styp__arrow : forall B1 B2,
    is_styp B1 -> is_styp B2 -> is_styp (btyp_arrow B1 B2)
| is_styp__all   : forall L B,
    (forall α, α `notin` L ->
       is_styp (open_btyp_wrt_btyp B (btyp_var_f α))) ->
    is_styp (btyp_all_syn B).

Inductive is_ityp : btyp -> Prop :=
| is_ityp__unit  : is_ityp btyp_unit
| is_ityp__var   : forall α, is_ityp (btyp_var_f α)
| is_ityp__arrow : forall B1 B2,
    is_ityp B1 -> is_ityp B2 -> is_ityp (btyp_arrow B1 B2)
| is_ityp__all   : forall L A,
    (forall α, α `notin` L ->
       is_ityp (open_btyp_wrt_btyp A (btyp_var_f α))) ->
    is_ityp (btyp_all_inh A).

Inductive is_sskl : bskl -> Prop :=
| is_sskl__unit    : is_sskl bskl_unit
| is_sskl__var     : forall α, is_sskl (bskl_var_f α)
| is_sskl__arrow   : forall A B,
    is_sskl A -> is_sskl B -> is_sskl (bskl_arrow A B)
| is_sskl__all     : forall L A,
    (forall α, α `notin` L ->
       is_sskl (open_bskl_wrt_bskl A (bskl_var_f α))) ->
    is_sskl (bskl_all_syn A)
| is_sskl__ghost    : is_sskl bskl_ghost
| is_sskl__univ_ghost : forall A, is_sskl A -> is_sskl (bskl_univ_ghost A).

Inductive is_iskl : bskl -> Prop :=
| is_iskl__unit    : is_iskl bskl_unit
| is_iskl__var     : forall α, is_iskl (bskl_var_f α)
| is_iskl__arrow   : forall A B,
    is_iskl A -> is_iskl B -> is_iskl (bskl_arrow A B)
| is_iskl__all     : forall L A,
    (forall α, α `notin` L ->
       is_iskl (open_bskl_wrt_bskl A (bskl_var_f α))) ->
    is_iskl (bskl_all_inh A)
| is_iskl__ghost    : is_iskl bskl_ghost
| is_iskl__univ_ghost : forall A, is_iskl A -> is_iskl (bskl_univ_ghost A).

Inductive guarded_pskl : pskl -> Prop :=
| guarded_pskl__unit  : guarded_pskl pskl_unit
| guarded_pskl__var   : forall α, guarded_pskl (pskl_var_f α)
| guarded_pskl__arrow : forall P1 P2, lc_pskl P1 -> lc_pskl P2 -> guarded_pskl (pskl_arrow P1 P2).

Inductive guarded_btyp : btyp -> Prop :=
| guarded_btyp__unit  : guarded_btyp btyp_unit
| guarded_btyp__var   : forall α, guarded_btyp (btyp_var_f α)
| guarded_btyp__arrow : forall B1 B2,
    lc_btyp B1 -> lc_btyp B2 -> guarded_btyp (btyp_arrow B1 B2).

Inductive guarded_utyp : utyp -> Prop :=
| guarded_utyp__unit  : guarded_utyp utyp_unit
| guarded_utyp__var   : forall α, guarded_utyp (utyp_var_f α)
| guarded_utyp__arrow : forall C1 C2,
    lc_utyp C1 -> lc_utyp C2 -> guarded_utyp (utyp_arrow C1 C2).

Inductive guarded_bskl : bskl -> Prop :=
| guarded_bskl__unit  : guarded_bskl bskl_unit
| guarded_bskl__var   : forall α, guarded_bskl (bskl_var_f α)
| guarded_bskl__arrow : forall Q1 Q2,
    lc_bskl Q1 -> lc_bskl Q2 -> guarded_bskl (bskl_arrow Q1 Q2).

Inductive guarded_uskl : uskl -> Prop :=
| guarded_uskl__unit  : guarded_uskl uskl_unit
| guarded_uskl__var   : forall α, guarded_uskl (uskl_var_f α)
| guarded_uskl__arrow : forall R1 R2,
    lc_uskl R1 -> lc_uskl R2 -> guarded_uskl (uskl_arrow R1 R2).

Inductive nonghost_pskl : pskl -> Prop :=
| nonghost_pskl__unit  : nonghost_pskl pskl_unit
| nonghost_pskl__var   : forall α, nonghost_pskl (pskl_var_f α)
| nonghost_pskl__arrow : forall P1 P2, nonghost_pskl (pskl_arrow P1 P2)
| nonghost_pskl__all   : forall P, nonghost_pskl (pskl_all_syn P).

Fixpoint pskl_no_ghost (P : pskl) : Prop :=
  match P with
  | pskl_unit => True
  | pskl_var_b _ => True
  | pskl_var_f _ => True
  | pskl_arrow P1 P2 => pskl_no_ghost P1 /\ pskl_no_ghost P2
  | pskl_all_syn P0 => pskl_no_ghost P0
  | pskl_ghost => False
  | pskl_univ_ghost P0 => pskl_no_ghost P0
  end.

Fixpoint uskl_no_ghost (R : uskl) : Prop :=
  match R with
  | uskl_ghost => False
  | uskl_arrow R1 R2 => uskl_no_ghost R1 /\ uskl_no_ghost R2
  | uskl_all_syn R0 | uskl_all_tag _ R0
  | uskl_univ_ghost R0 | uskl_dot_univ_ghost R0 => uskl_no_ghost R0
  | uskl_unit | uskl_var_b _ | uskl_var_f _ | uskl_dot_ghost => True
  end.

Inductive is_value : exp -> Prop :=
| is_value__unit     : is_value exp_unit
| is_value__var      : forall x, is_value (exp_var_f x)
| is_value__abs      : forall e, is_value (exp_abs e)
| is_value__abs_anno : forall A e, is_value (exp_abs_anno A e)
| is_value__anno     : forall e A, is_value e -> is_value (exp_anno e A).

Inductive mod_comp_ty : btyp -> mode -> Prop :=
| mod_comp_ty__ti : forall B, is_styp B -> mod_comp_ty B mode_ti
| mod_comp_ty__tc : forall B, is_ityp B -> mod_comp_ty B mode_tc
| mod_comp_ty__fn : forall m B1 B2,
    mod_comp_ty B2 m ->
    mod_comp_ty (btyp_arrow B1 B2) (mode_fn m).

Inductive mod_comp_sk : bskl -> mode -> Prop :=
| mod_comp_sk__ti : forall Q, is_sskl Q -> mod_comp_sk Q mode_ti
| mod_comp_sk__tc : forall Q, is_sskl Q -> mod_comp_sk Q mode_tc
| mod_comp_sk__fn : forall m Q1 Q2,
    mod_comp_sk Q2 m ->
    mod_comp_sk (bskl_arrow Q1 Q2) (mode_fn m).

Fixpoint pskl_ghost_free (P : pskl) : Prop :=
  match P with
  | pskl_unit => True
  | pskl_var_b _ => True
  | pskl_var_f _ => True
  | pskl_arrow P1 P2 => pskl_ghost_free P1 /\ pskl_ghost_free P2
  | pskl_all_syn P0 => pskl_ghost_free P0
  | pskl_ghost => False
  | pskl_univ_ghost _ => False
  end.

Fixpoint bskl_ghost_free (Q : bskl) : Prop :=
  match Q with
  | bskl_unit => True
  | bskl_var_b _ => True
  | bskl_var_f _ => True
  | bskl_arrow Q1 Q2 => bskl_ghost_free Q1 /\ bskl_ghost_free Q2
  | bskl_all_syn Q0 => bskl_ghost_free Q0
  | bskl_all_inh Q0 => bskl_ghost_free Q0
  | bskl_ghost => False
  | bskl_univ_ghost _ => False
  end.

Definition forall_r_off (m : mode) (P' : pskl) : Prop :=
  forall B, P' = pskl_all_syn B -> m = mode_tc ->
    ~ pskl_ghost_free (pskl_all_syn B).

Lemma forall_r_off_nontc : forall m P',
  m <> mode_tc -> forall_r_off m P'.
Proof. intros m P' Hne B _ Hm; exfalso; exact (Hne Hm). Qed.

Lemma forall_r_off_nonall : forall m P',
  (forall B, P' <> pskl_all_syn B) -> forall_r_off m P'.
Proof. intros m P' Hne B Heq; exfalso; apply (Hne B); exact Heq. Qed.

Lemma forall_r_off_ghosty : forall m B,
  ~ pskl_ghost_free (pskl_all_syn B) -> forall_r_off m (pskl_all_syn B).
Proof.
  intros m B Hg B0 Heq _. injection Heq as Heq0; subst B0. exact Hg.
Qed.

Definition peel_l_off (P : pskl) : Prop :=
  (forall Q, P <> pskl_all_syn Q) /\ (forall Q, P <> pskl_univ_ghost Q).

Definition solve_l_off (P : pskl) : Prop :=
  (forall α, P <> pskl_var_f α) /\ peel_l_off P.

Lemma solve_l_off_peel : forall P, solve_l_off P -> peel_l_off P.
Proof. intros P [_ H]; exact H. Qed.

Lemma peel_l_off_unit : peel_l_off pskl_unit.
Proof. split; intros; discriminate. Qed.

Lemma peel_l_off_var_b : forall n, peel_l_off (pskl_var_b n).
Proof. intros; split; intros; discriminate. Qed.

Lemma peel_l_off_var : forall α, peel_l_off (pskl_var_f α).
Proof. intros; split; intros; discriminate. Qed.

Lemma peel_l_off_arrow : forall P Q, peel_l_off (pskl_arrow P Q).
Proof. intros; split; intros; discriminate. Qed.

Lemma peel_l_off_ghost : peel_l_off pskl_ghost.
Proof. split; intros; discriminate. Qed.

Lemma solve_l_off_unit : solve_l_off pskl_unit.
Proof. split; [ intros; discriminate | apply peel_l_off_unit ]. Qed.

Lemma solve_l_off_var_b : forall n, solve_l_off (pskl_var_b n).
Proof. intros; split; [ intros; discriminate | apply peel_l_off_var_b ]. Qed.

Lemma solve_l_off_arrow : forall P Q, solve_l_off (pskl_arrow P Q).
Proof. intros; split; [ intros; discriminate | apply peel_l_off_arrow ]. Qed.

Lemma solve_l_off_ghost : solve_l_off pskl_ghost.
Proof. split; [ intros; discriminate | apply peel_l_off_ghost ]. Qed.

#[export] Hint Resolve peel_l_off_unit peel_l_off_var_b peel_l_off_var
  peel_l_off_arrow peel_l_off_ghost solve_l_off_unit solve_l_off_var_b
  solve_l_off_arrow solve_l_off_ghost solve_l_off_peel : fresco.

#[export] Hint Constructors mono_ptyp is_dtyp is_dskl is_styp is_ityp is_sskl
  is_iskl guarded_pskl guarded_btyp guarded_utyp guarded_bskl
  guarded_uskl mod_comp_ty mod_comp_sk : fresco.

Set Implicit Arguments.

Inductive bskl_monoish : bskl -> Prop :=
| bmi_unit : bskl_monoish bskl_unit
| bmi_var : forall α, bskl_monoish (bskl_var_f α)
| bmi_arrow : forall Q1 Q2,
    bskl_monoish Q1 -> bskl_monoish Q2 ->
    bskl_monoish (bskl_arrow Q1 Q2).
Unset Implicit Arguments.
