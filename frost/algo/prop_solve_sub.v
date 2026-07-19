(** BASICS for the constraint-SOLVING layer ([a_solve_sub] / [a_solve_eq]),
    docs/DESIGN-subtyping.md §3.3(2).  These are the undecorated shadows of
    the decorated tag-solving ([a_solvetag_sub]/[a_solvetag_eq]); the
    subtyping-decoration lemmas invert [a_sub]'s Extract = look ∘ solve ∘ guess
    into a [solve]/[solvetag] pair, so [solve]'s outputs must be well-behaved.

    First: solving preserves local closure — a locally-closed problem has a
    locally-closed solution. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.

Set Implicit Arguments.

Scheme a_solve_sub_mutind := Induction for a_solve_sub Sort Prop
  with a_solve_eq_mutind  := Induction for a_solve_eq  Sort Prop.
Combined Scheme a_solve_sub_eq_mutind
  from a_solve_sub_mutind, a_solve_eq_mutind.

(** A guarded skeleton is locally closed. *)
Lemma guarded_pskl_lc : forall P, guarded_pskl P -> lc_pskl P.
Proof. intros P H; inversion H; subst; constructor; assumption. Qed.

Lemma lc_pskl_arrow_inv : forall P1 P2,
  lc_pskl (pskl_arrow P1 P2) -> lc_pskl P1 /\ lc_pskl P2.
Proof. intros P1 P2 H; inversion H; auto. Qed.

Lemma lc_pskl_tophole_inv : forall P,
  lc_pskl (pskl_tophole P) -> lc_pskl P.
Proof. intros P H; inversion H; auto. Qed.

Lemma lc_pskl_all_syn_inv : forall P,
  lc_pskl (pskl_all_syn P) ->
  forall X, lc_pskl (open_pskl_wrt_pskl P (pskl_var_f X)).
Proof. intros P H; inversion H; auto. Qed.

(** Solving preserves local closure. *)
Lemma a_solve_sub_eq_lc :
  (forall Θ m P Q P', Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
     lc_pskl P -> lc_pskl Q -> lc_pskl P') /\
  (forall Θ P Q P', Θ ⊢ₑ P ∼ Q ⤳ P' ->
     lc_pskl P -> lc_pskl Q -> lc_pskl P').
Proof.
  apply a_solve_sub_eq_mutind; intros;
    (* peel structured, non-binder inputs *)
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_tophole _) |- _ => apply lc_pskl_tophole_inv in H
    | H : guarded_pskl _           |- _ => apply guarded_pskl_lc in H
    end;
    (* discharge every case with a non-binder output *)
    try solve
      [ assumption
      | eauto
      | constructor; eauto
      | apply lc_pskl_tophole; eauto
      | apply lc_pskl_tophole; constructor; eauto ].
  (* remaining: binder cases (∀-input and/or ∀-output). *)
  - (* SS-ForallL : ∀P ≼ Q ⤳ ∀P' *)
    pick fresh β for L. apply (lc_pskl_all_syn_exists β).
    match goal with
    | HP : lc_pskl (pskl_all_syn _),
      IH : forall a, a `notin` L -> _ -> _ -> _ |- _ =>
        apply IH; [ auto | apply (lc_pskl_all_syn_inv HP) | assumption ]
    end.
  - (* SS-ForallR : A ≼ ∀B ⤳ P' (output unchanged) *)
    pick fresh β for L.
    match goal with
    | HQ : lc_pskl (pskl_all_syn _),
      IH : forall a, a `notin` L -> _ -> _ -> _ |- _ =>
        eapply IH; [ auto | eassumption | apply (lc_pskl_all_syn_inv HQ) ]
    end.
  - (* SE-Forall : ∀P ∼ ∀Q ⤳ ∀P' *)
    pick fresh β for L. apply (lc_pskl_all_syn_exists β).
    match goal with
    | HP : lc_pskl (pskl_all_syn ?p), HQ : lc_pskl (pskl_all_syn ?q),
      IH : forall a, a `notin` L -> _ -> _ -> _ |- _ =>
        apply IH; [ auto | apply (lc_pskl_all_syn_inv HP)
                  | apply (lc_pskl_all_syn_inv HQ) ]
    end.
  - (* SE-GhostForall : ⫯P ∼ ∀Q ⤳ ∀P' *)
    pick fresh β for L. apply (lc_pskl_all_syn_exists β).
    match goal with
    | HQ : lc_pskl (pskl_all_syn _),
      IH : forall a, a `notin` L -> _ -> _ -> _ |- _ =>
        apply IH; [ auto | apply lc_pskl_tophole; assumption
                  | apply (lc_pskl_all_syn_inv HQ) ]
    end.
  - (* SE-ForallGhost : ∀P ∼ ⫯Q ⤳ ∀P' *)
    pick fresh β for L. apply (lc_pskl_all_syn_exists β).
    match goal with
    | HP : lc_pskl (pskl_all_syn _),
      IH : forall a, a `notin` L -> _ -> _ -> _ |- _ =>
        apply IH; [ auto | apply (lc_pskl_all_syn_inv HP)
                  | apply lc_pskl_tophole; assumption ]
    end.
Qed.

Lemma a_solve_sub_lc : forall Θ m P Q P',
  Θ ⊢ₛ P ≼[ m ] Q ⤳ P' -> lc_pskl P -> lc_pskl Q -> lc_pskl P'.
Proof. intros; eapply (proj1 a_solve_sub_eq_lc); eauto. Qed.

Lemma a_solve_eq_lc : forall Θ P Q P',
  Θ ⊢ₑ P ∼ Q ⤳ P' -> lc_pskl P -> lc_pskl Q -> lc_pskl P'.
Proof. intros; eapply (proj2 a_solve_sub_eq_lc); eauto. Qed.

(** Solving a GUARDED subject yields a guarded solution: a guarded LHS only
    matches rules whose output is again guarded (no ghost/tophole/∀ can be
    introduced on the left).  Needed for the tophole cases of output
    well-formedness. *)
Lemma a_solve_sub_eq_guarded :
  (forall Θ m P Q P', Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
     lc_pskl P -> lc_pskl Q -> guarded_pskl P -> guarded_pskl P') /\
  (forall Θ P Q P', Θ ⊢ₑ P ∼ Q ⤳ P' ->
     lc_pskl P -> lc_pskl Q -> guarded_pskl P -> guarded_pskl P').
Proof.
  apply a_solve_sub_eq_mutind; intros;
    (* a non-guarded subject makes the case vacuous *)
    try solve [ match goal with H : guarded_pskl _ |- _ => inversion H end ];
    (* peel lc of the arrow / tophole subject/rhs *)
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ => apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_tophole _) |- _ => apply lc_pskl_tophole_inv in H
    end;
    try solve
      [ assumption
      | eauto
      | constructor; eauto using a_solve_sub_lc, a_solve_eq_lc ].
  - (* SS-ForallR : guarded LHS [A] carried through the ∀-RHS opening *)
    pick fresh β for L.
    match goal with
    | HQ : lc_pskl (pskl_all_syn _),
      IH : forall a, a `notin` L -> _ -> _ -> _ -> _ |- _ =>
        eapply IH;
          [ auto | assumption | apply (lc_pskl_all_syn_inv HQ) | assumption ]
    end.
Qed.

Lemma a_solve_sub_guarded : forall Θ m P Q P',
  Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
  lc_pskl P -> lc_pskl Q -> guarded_pskl P -> guarded_pskl P'.
Proof. intros; eapply (proj1 a_solve_sub_eq_guarded); eauto. Qed.
