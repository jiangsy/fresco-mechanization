(** Fresco — "only polytypes need annotation" (annotation-erasure property).

    [erase_lam_mono] drops every MONOTYPE annotation on a lambda binder
    ([λᴬ.e ↦ λ.e] when [A] monotype), recursing through the whole term.  The
    headline is that this preserves typing at the SAME mode and type:

      {{ Γ ⊢[m] e ⦂ B }}d  →  {{ Γ ⊢[m] (erase_lam_mono e) ⦂ B }}d.

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

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_shallow.

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

(* RESTART NOTE: the pre-restart [erase_lam_mono_typing] ("erasing monotype
   lambda annotations preserves typing") lived here with an admitted [app]
   case (needs bespoke skeleton lemmas).  Dropped per the no-admits policy —
   see prop_annotation.v history / PROGRESS.md; re-prove it with the
   paper-faithful skeleton machinery if the claim returns to the paper. *)

(** Why ascriptions are NOT erased: [freeze e] has NO inference-mode typing,
    so an ascription [(e : A)] is the only way to give a [freeze] term a [ti]
    typing.  Erasing such an ascription — even at a MONOTYPE [A] — can make the
    term untypeable (e.g. inside an outer [freeze], whose premise needs [ti]).
    The annotation's role there is MODE, not polymorphism, so it is genuinely
    load-bearing even at a monotype. *)
Lemma freeze_no_infer : forall Γ e B,
    {{ Γ ⊢[ mode_ti ] (exp_freeze e) ⦂ B }}d -> False.
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
