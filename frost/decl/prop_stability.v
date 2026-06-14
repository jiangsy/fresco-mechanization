(** Frost — structural declarative-typing properties (order irrelevance,
    stability). *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.

Set Implicit Arguments.

(** A curried function type [A1 → … → An → R] built from a list of
    (argument-type, argument-term) pairs (a spine). *)
Definition curry_ptyp (args : list (ptyp * exp)) (R : ptyp) : ptyp :=
  fold_right (fun ae acc => ptyp_arrow (fst ae) acc) R args.

(** The curried application [f e1 … en]. *)
Definition curry_exp (f : exp) (args : list (ptyp * exp)) : exp :=
  fold_left (fun g ae => exp_app g (snd ae)) args f.

(** A prefix of [n] universal quantifiers [∀…∀. A]. *)
Fixpoint ptyp_forall_prefix (n : nat) (A : ptyp) : ptyp :=
  match n with
  | O => A
  | S n' => ptyp_all (ptyp_forall_prefix n' A)
  end.

(** * Order irrelevance of argument permutation.

    Permuting the arguments of a function-typed variable — and its argument
    types accordingly — does not affect typability.  Each entry of [args]
    pairs an argument type with its term, so one [Permutation] permutes both
    together; the function type carries an arbitrary [n]-quantifier prefix
    ([ptyp_forall_prefix]) and an arbitrary codomain [R]; the result [R'] at
    mode [m] is arbitrary.  The n-ary, polymorphic, full-permutation
    strengthening of the old [d_typing_order_irrel_adj].
    (TODO: generalise the head [exp_var_f x] to an arbitrary term.)
    Proof deferred. *)
Lemma d_typing_order_irrel : forall Γ m n x y args args' R R',
    Permutation args args' ->
    binds x (dbind_typ (ptyp_forall_prefix n (curry_ptyp args R))) Γ ->
    binds y (dbind_typ (ptyp_forall_prefix n (curry_ptyp args' R))) Γ ->
    Γ ⊢[ m ] curry_exp (exp_var_f x) args ⦂ R' ->
    Γ ⊢[ m ] curry_exp (exp_var_f y) args' ⦂ R'.
Proof.
Admitted.
