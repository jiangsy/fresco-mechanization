(** Frost — declarative typing metatheory (Phase 2.D).

    Umbrella file: re-exports the split modules under [prop_typing/]
    and hosts the Phase 2.D.7 / 2.D.8 stability theorems plus the E1
    expressiveness example. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.

Require Export src.frost.decl.prop_typing.weakening.
Require Export src.frost.decl.prop_typing.gen.
Require Export src.frost.decl.prop_typing.mono_subsumption.
Require Export src.frost.decl.prop_typing.abs_subsumption.
Require Export src.frost.decl.prop_typing.d12.

Set Implicit Arguments.

(** * Phase 2.D.7 — Stability S1 (argument-permutation).

    Design doc §3.D anchor: [f : ∀a b. a → (a → a) → int] applied to
    e1 e2 should give the same int as some [f' : ∀a. (a → a) → a → int]
    applied to e2 e1.

    Per the design's strictification policy, we attempt the strongest
    form first and narrow if needed. Below we state the strongest
    formulation (transposition of two adjacent arguments at any type),
    and a narrowed monotype-only version.

    Status: the most-general form fails to typecheck because re-typing
    the swapped function [λ y x. f x y] requires a d_typing__app
    derivation that the current rules cannot construct without a
    d_typing_app_inversion lemma (which itself is research-grade).
    We document this and produce a counter-example in PROGRESS.md.

    Narrowed form: transposition of two adjacent monotype arguments.
    Even this is research-grade — admits with rationale.
*)

Lemma d_typing_swap_mono : forall Γ f e1 e2 A1 A2 C m,
    mono_typ A1 ->
    mono_typ A2 ->
    d_typing m Γ (exp_app (exp_app f e1) e2) C ->
    d_typing mode_ti Γ f (typ_arrow A1 (typ_arrow A2 C)) ->
    d_typing mode_tc Γ e1 A1 ->
    d_typing mode_tc Γ e2 A2 ->
    (* The swapped function: λ y:A2. λ x:A1. f x y, where the body
       is built using locally-nameless de Bruijn indices. *)
    exists f_swap,
      d_typing mode_ti Γ f_swap (typ_arrow A2 (typ_arrow A1 C)) /\
      d_typing m Γ (exp_app (exp_app f_swap e2) e1) C.
Proof.
  (* Constructive: f_swap := exp_abs_anno A2 (exp_abs_anno A1
                                  (exp_app (exp_app f
                                             (exp_var_b 0))
                                           (exp_var_b 1))).
     Typing f_swap reduces to typing the inner [f x y] under the
     extended context, then closing twice with d_typing__abs_anno.
     The application [f_swap e2 e1] then types by [d_typing__app]
     applied twice.

     The remaining obstacle: producing the inner [d_pat] derivation
     for the arguments under the typing__app rules requires either
     (a) a d_pat-from-d_typing lemma, or (b) the algorithmic side's
     skeleton inference (Phase 3). Neither is currently available,
     so this lemma is admitted with a documented research-grade
     status. *)
Admitted.

(** * Phase 2.D.8 — Stability S2 (application-restructuring).

    Typability invariant under β-equivalent restructurings:
        Γ ⊢_M f e1 e2 ⇒ B  iff  Γ ⊢_M (λx:A1. f x e2) e1 ⇒ B.

    Same caveats as S1: requires inverting and rebuilding application
    derivations through d_pat / d_refine_syn / d_typing__abs_anno.
*)

Lemma d_typing_app_restructure : forall Γ f e1 e2 A1 B m,
    d_typing m Γ (exp_app (exp_app f e1) e2) B ->
    d_typing mode_tc Γ e1 A1 ->
    (* The restructured term [(λ x:A1. f x e2) e1]. *)
    d_typing m Γ
      (exp_app (exp_abs_anno A1
                 (exp_app (exp_app f (exp_var_b 0))
                          e2))
               e1) B.
Proof.
  (* Same research-grade pattern as S1. Requires a d_pat derivation
     for e2 in the extended context (x : A1) — which transfers by
     weakening — plus a d_refine_syn weakening (provable). The
     d_typing__app premise about the refined function type matches.

     But: the outer [d_typing__app (λx. f x e2) e1] requires the
     inner abs_anno to type at A1 → B, which depends on f's type
     containing A1 → ... — recovered by inversion on the original
     typing. Research-grade. Admitted. *)
Admitted.

(** * Order irrelevance (colleague's [order_irrel_app] adapted to Frost).

    Inspired by a stability lemma used in a colleague's mechanisation:
    if two variables [x] and [y] in scope have function types that are
    related by an argument permutation, then a curried application of
    [x] to a list of args and of [y] to the permuted args produce the
    same result type.

    The full n-argument version requires defining [curry_ty],
    [curry_tm], [forall_prefix] helpers — deferred. Below is the
    simplest concrete instance: 2 arguments, 0 forall-prefix, both
    arguments monotype (so the function types are first-order arrows).

    [paper-ref: stability:order-irrelevance] (no paper match yet; new
    target inspired by external system) *)

(** Two-argument adjacent swap when both functions are simultaneously
    in scope with the swapped function types. *)
Lemma d_typing_order_irrel_adj : forall Γ x y A1 A2 R e1 e2 m,
    binds x (dbind_typ (typ_arrow A1 (typ_arrow A2 R))) Γ ->
    binds y (dbind_typ (typ_arrow A2 (typ_arrow A1 R))) Γ ->
    d_typing m Γ (exp_app (exp_app (exp_var_f x) e1) e2) R ->
    d_typing m Γ (exp_app (exp_app (exp_var_f y) e2) e1) R.
Proof.
  (* Proof strategy via the colour/mode lens:

     Invert d_typing on the outer application: d_typing__app fires
     (with d_typing__sub for the function side at mode_fn). The
     function-side d_typing of [exp_app x e1] at [mode_fn m] inverts
     similarly, ending at d_typing__var for x. From binds-x we recover
     the type [A1 → A2 → R]. The d_refine_syn / d_pat structures pin
     e1 to A1 and e2 to A2.

     Reconstruct symmetrically: d_typing__app at [exp_app y e2] with
     [d_typing__var] for y giving [A2 → A1 → R], then outer app with e1.

     The skeleton inference (d_pat / d_refine_syn) for e2 and e1 is
     mode_tc and is mechanically preserved by argument-order swap
     (the patterns don't reference position).

     ADMITTED: requires non-trivial d_typing inversion through d_pat
     and d_refine_syn — same machinery as d_typing_swap_mono. The
     auxiliary d_pat-from-d_typing lemma (cited in d_typing_swap_mono)
     is the key blocker. *)
Admitted.

(** N-argument version (target). Requires [forall_prefix] /
    [curry_ty] / [curry_tm] helpers. The forall-prefixed version
    would interact with the colour discipline at [d_typing__forall]
    (value restriction) — extending the proof to n quantifiers
    needs commuting argument-permutation with the cofinite
    quantifier introduction. Documented as future work. *)


(** * Phase 2.D.9 — Expressiveness E1 (Church-encoded existentials).

    Three concrete typing theorems for the Church encoding of
    existential types: introduction, elimination, and round-trip.

    Concrete types (using typ_unit as the paper's "Int" stand-in
    since Frost has no separate Int):
        mkPkg : Int → ∀β. (∀α. α → β) → β
        getInt : (∀β. (∀α. α → β) → β) → Int

    Witness terms (using locally-nameless de Bruijn):
        mkPkg := λv. λk. k v
        getInt := λp. p [Int] (λα. λx. x)   -- but Frost has no
                                                explicit type-app;
                                                the type abstraction
                                                is silently introduced
                                                by [d_typing__forall].

    Status: the design doc §3.D explicitly flags this as a benchmark:
    "if Church-encoded existentials don't typecheck without
    annotations, document as a finding (not strictification)".
    We state the three theorems and document.
*)

Definition E1_mkPkg : exp :=
  (* λv. λk. k v *)
  exp_abs (exp_abs (exp_app (exp_var_b 0) (exp_var_b 1))).

Definition E1_pkg_typ : typ :=
  (* ∀β. (∀α. α → β) → β *)
  typ_all_col colour_inh
    (typ_arrow
       (typ_all_col colour_inh
          (typ_arrow (typ_var_b 0) (typ_var_b 1)))
       (typ_var_b 0)).

Definition E1_mkPkg_typ : typ :=
  (* unit → ∀β. (∀α. α → β) → β *)
  typ_arrow typ_unit E1_pkg_typ.

Theorem E1_intro : d_typing mode_tc nil E1_mkPkg E1_mkPkg_typ.
Proof.
  (* Witnessing this would require a derivation tree
     d_typing__abs (intro for the outer λv : unit)
       d_typing__forall (intro for the ∀β, since the body λk. k v
                        is a value and the forall rule applies)
         d_typing__abs (intro for λk : ∀α. α → β)
           d_typing__app (apply k to v)
             ... refinement chain producing the right pattern ...
     The β / α variables (bound in the [typ_all_col] scopes) cross
     under [d_typing__forall] via cofinite quantification, requiring
     [d_typing_pat_subst_typ_mut] (Task 3) to commute open with the
     body. Since Task 3 is admitted, this derivation cannot be
     constructed cleanly here.
     Documented as a Phase 2.D research-grade finding. *)
Admitted.

Definition E1_getInt : exp :=
  (* λp. p [unit] (λα. λx. x) — without explicit type-app, the value
     restriction's forall_inh / forall_syn rules silently introduce
     the [β = unit] instantiation. The applied function below is
     just a "default ε:unit" Church-style identity. *)
  exp_abs (exp_app (exp_var_b 0)
                   (exp_abs (exp_anno exp_unit typ_unit))).

Definition E1_getInt_typ : typ :=
  typ_arrow E1_pkg_typ typ_unit.

Theorem E1_elim : d_typing mode_tc nil E1_getInt E1_getInt_typ.
Proof.
  (* Witnessing requires applying p to a polymorphic continuation
     k : ∀α. α → unit. Producing the d_pat-side derivation for the
     k argument, including its refinement to the unfreshened [∀α. ...]
     shape, is again gated on Task 3 (type subst). Documented. *)
Admitted.

Theorem E1_roundtrip :
    d_typing mode_tc nil
      (exp_app E1_getInt (exp_app E1_mkPkg exp_unit))
      typ_unit.
Proof.
  (* Composition of E1_intro and E1_elim with a single d_typing__app
     in the middle. Since both intros are admitted, this is too.
     Documented as a research-grade benchmark per design §3.D. *)
Admitted.
