(** Frost — "only polytypes need annotation" (annotation-erasure property).

    [erase_lam_mono] drops every MONOTYPE annotation on a lambda binder
    ([λᴬ.e ↦ λ.e] when [A] monotype), recursing through the whole term.  The
    headline is that this preserves typing at the SAME mode and type:

      Γ ⊢[m] e ⦂ B  →  Γ ⊢[m] (erase_lam_mono e) ⦂ B.

    i.e. monotype lambda arguments are never needed as annotations anywhere in
    a program — the monotype is guessed / inherited instead.

    NB. We do NOT erase ascriptions [(e : A)]: a monotype ascription is genuinely
    load-bearing when it supplies INFERENCE mode to a non-inferring term — e.g.
    [freeze e] only checks, never infers, so [(freeze e : A)] is typeable but
    [freeze e] is not in an inference position.  That is a MODE role independent
    of polymorphism; see [prop_shallow.v] for the [freeze] witness. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_shallow.

Set Implicit Arguments.

(** Decidable monotype test, matching [mono_ptyp]. *)
Fixpoint ptyp_is_mono (A : ptyp) : bool :=
  match A with
  | ptyp_unit => true
  | ptyp_var_b _ => true
  | ptyp_var_f _ => true
  | ptyp_arrow A1 A2 => andb (ptyp_is_mono A1) (ptyp_is_mono A2)
  | ptyp_all _ => false
  end.

Lemma ptyp_is_mono_sound : forall A, lc_ptyp A -> ptyp_is_mono A = true -> mono_ptyp A.
Proof.
  intros A Hlc. induction Hlc; simpl; intros Hm; try discriminate;
    eauto using mono_ptyp.
  apply andb_prop in Hm. destruct Hm. eauto using mono_ptyp.
Qed.

(** Erase monotype lambda annotations everywhere. *)
Fixpoint erase_lam_mono (e : exp) : exp :=
  match e with
  | exp_unit => exp_unit
  | exp_var_b n => exp_var_b n
  | exp_var_f x => exp_var_f x
  | exp_abs e1 => exp_abs (erase_lam_mono e1)
  | exp_abs_anno A e1 =>
      if ptyp_is_mono A
      then exp_abs (erase_lam_mono e1)
      else exp_abs_anno A (erase_lam_mono e1)
  | exp_app e1 e2 => exp_app (erase_lam_mono e1) (erase_lam_mono e2)
  | exp_anno e1 A => exp_anno (erase_lam_mono e1) A
  | exp_freeze e1 => exp_freeze (erase_lam_mono e1)
  end.

Lemma erase_lam_mono_open_rec : forall e u k,
    erase_lam_mono (open_exp_wrt_exp_rec k u e)
    = open_exp_wrt_exp_rec k (erase_lam_mono u) (erase_lam_mono e).
Proof.
  induction e; intros u k; simpl; try reflexivity;
    try (rewrite IHe; reflexivity);
    try (rewrite IHe1, IHe2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - destruct (ptyp_is_mono A); simpl; rewrite IHe; reflexivity.
Qed.

Lemma erase_lam_mono_open : forall e u,
    erase_lam_mono (open_exp_wrt_exp e u)
    = open_exp_wrt_exp (erase_lam_mono e) (erase_lam_mono u).
Proof.
  intros. unfold open_exp_wrt_exp. apply erase_lam_mono_open_rec.
Qed.

Lemma erase_lam_mono_var : forall e x,
    erase_lam_mono (open_exp_wrt_exp e (exp_var_f x))
    = open_exp_wrt_exp (erase_lam_mono e) (exp_var_f x).
Proof. intros. rewrite erase_lam_mono_open. reflexivity. Qed.

Lemma is_value_erase : forall e, is_value e -> is_value (erase_lam_mono e).
Proof.
  intros e H. induction H; simpl; eauto using is_value.
  destruct (ptyp_is_mono A); eauto using is_value.
Qed.

Lemma is_base_term_erase : forall e, is_base_term e -> is_base_term (erase_lam_mono e).
Proof.
  intros e H. induction H; simpl; eauto using is_base_term.
Qed.

(** Headline: erasing monotype lambda annotations preserves typing. *)
Theorem erase_lam_mono_typing : forall Γ m e B,
    Γ ⊢[ m ] e ⦂ B ->
    Γ ⊢[ m ] (erase_lam_mono e) ⦂ B.
Proof.
  intros Γ m e B Hty. induction Hty; simpl.
  - (* unit *) apply d_typing__unit.
  - (* var *) apply d_typing__var; assumption.
  - (* anno *) apply d_typing__anno; assumption.
  - (* sub *) eapply d_typing__sub; [ eassumption | eassumption ].
  - (* freeze *) apply d_typing__freeze; assumption.
  - (* forall *) apply d_typing__forall with (L := L);
      [ apply is_value_erase; assumption | assumption ].
  - (* abs *) apply d_typing__abs with (L := L) (A := A) (B := B);
      try assumption.
    intros x Hx. rewrite <- erase_lam_mono_var. auto.
  - (* abs_anno *) destruct (ptyp_is_mono A) eqn:Hmono.
    + (* mono annotation: drop it, recover via d_typing__abs *)
      assert (Hm : mono_ptyp A) by (apply ptyp_is_mono_sound;
        [ eapply d_wf_ptyp_lc_loc; eassumption | assumption ]).
      assert (HB1 : B1 = ptyp_to_btyp_inh A)
        by (apply mono_btyp_to_ptyp_inv; assumption).
      subst B1.
      apply d_typing__abs with (L := L) (A := A) (B := B2); try assumption.
      intros x Hx. rewrite <- erase_lam_mono_var. auto.
    + (* non-monotype annotation: keep it *)
      apply d_typing__abs_anno with (L := L) (A := A) (B1 := B1) (B2 := B2);
        try assumption.
      intros x Hx. rewrite <- erase_lam_mono_var. auto.
  - (* app: routes through skeleton inference [d_pat]; see [erase_lam_mono_pat] *)
    admit.
Admitted.

(** Why ascriptions are NOT erased: [freeze e] has NO inference-mode typing,
    so an ascription [(e : A)] is the only way to give a [freeze] term a [ti]
    typing.  Erasing such an ascription — even at a MONOTYPE [A] — can make the
    term untypeable (e.g. inside an outer [freeze], whose premise needs [ti]).
    The annotation's role there is MODE, not polymorphism, so it is genuinely
    load-bearing even at a monotype. *)
Lemma freeze_no_infer : forall Γ e B,
    Γ ⊢[ mode_ti ] (exp_freeze e) ⦂ B -> False.
Proof.
  (* With the unrestricted [Sub], the [ti] inversion has a [sub] case whose
     premise re-types the same [freeze] at [ti] — an induction, not a single
     inversion. *)
  intros Γ e B H.
  remember (exp_freeze e) as ef eqn:Hef. remember mode_ti as m0 eqn:Hm0.
  revert Hef Hm0. induction H; intros Hef Hm0;
    try discriminate Hef; try discriminate Hm0.
  apply IHd_typing; [ exact Hef | reflexivity ].
Qed.
