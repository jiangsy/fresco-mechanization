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

Require Export src.frost.decl.typing.prop_weakening.
Require Export src.frost.decl.typing.def_gen.
Require Export src.frost.decl.typing.prop_subsumption_aux.
Require Export src.frost.decl.typing.prop_general_subsumption.

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

(** ** Helpers for [d_typing_order_irrel_adj].

    The key proof-debugging observation (colour/mode lens — see
    [DESIGN.md] Part 2): typing a [d_typing] application term
    [exp_app f e] is rigid because [exp_app] is NOT [is_base_term]
    and NOT [is_value], so only [d_typing__app] can fire. Similarly,
    typing [exp_var_f x] at [mode_fn m] (which is neither [mode_ti]
    nor [mode_tc]) can only use [d_typing__sub] — [__var] requires
    [mode_ti], [__forall] requires [mode_tc].
*)

(** A [mode_ti] typing of a variable factors through its binding,
    either by literal equality (the [__var] base case) or by a
    [d_consis] derivation (collapsed [__sub] chain — [d_sub] at
    [mode_ti] is [__infer], i.e. wrapped [d_consis]). *)
Lemma d_typing_var_ti_to_consis_or_eq : forall Γ x A B,
    uniq Γ ->
    binds x (dbind_typ A) Γ ->
    d_wf_typ Γ A ->                          (* NEW Phase 1.I: needed by
                                                [d_consis_compose] which now
                                                requires d_wf_typ on LHS. *)
    Γ ⊢[ mode_ti ] (exp_var_f x) ⇒ B ->
    A = B \/ nil ⨟ Γ ⊨ A ≈ B.
Proof.
  intros Γ x A B Huniq Hb HwfA Htyp.
  remember (exp_var_f x) as evx. remember mode_ti as m_ti.
  induction Htyp; subst; try discriminate.
  - (* __var: B = A0, with binds x A0. Use uniq to conclude A = A0. *)
    inversion Heqevx; subst x0.
    left.
    assert (Hdbeq : dbind_typ A = dbind_typ A0)
      by (eapply binds_unique; eauto).
    inversion Hdbeq; reflexivity.
  - (* __sub at mode_ti: only d_sub__infer fires (mode = mode_ti).
       [discriminate] kills the mode-constructor mismatches (__check,
       __forall_r, __arg). [congruence] kills [__forall_l_tagged]
       whose [m <> mode_ti] premise becomes [mode_ti <> mode_ti]. *)
    match goal with
    | Hsub : d_sub mode_ti nil _ _ _ |- _ =>
        inversion Hsub; subst; try discriminate; try congruence
    end.
    edestruct IHHtyp as [Heq | Hcons]; auto.
    + (* IH: A = A0; subst A. The goal collapses to the inversion's
         d_consis (the only d_consis in scope after subst). *)
      subst A. right.
      match goal with
      | Hc_inv : d_consis nil _ (syn_color _) (syn_color _) |- _ => exact Hc_inv
      end.
    + (* IH: d_consis nil Γ A A0 = d_consis nil Γ A (syn_color T_rule).
         Inversion gives d_consis nil Γ (syn_color T_rule) (syn_color A_rule).
         Compose. The (syn_color _) (syn_color _) pattern picks the
         inverted hypothesis (Hcons's LHS [A] is a variable, not syn_color). *)
      right.
      match goal with
      | Hc_inv : d_consis nil _ (syn_color _) (syn_color _) |- _ =>
          edestruct (d_consis_compose (Δa := @nil atom) (Δb := @nil atom))
            as [Δc [Hperm Hccompose]];
            [ exact Hcons | exact Hc_inv | apply list_disjoint_nil_l
            | exact HwfA |];
          simpl in Hperm; apply Permutation_sym, Permutation_nil in Hperm;
          subst Δc; exact Hccompose
      end.
Qed.

(** A [mode_fn _] typing of a variable factors through its binding
    via a [d_sub] derivation. Combines [d_typing_var_ti_to_consis_or_eq]
    with [d_consis_sub_trans_nil] (the latter requires [d_wf_typ Γ A]). *)
Lemma d_typing_var_at_fn_to_d_sub : forall Γ x A B m,
    uniq Γ ->
    binds x (dbind_typ A) Γ ->
    d_wf_typ Γ A ->
    Γ ⊢[ mode_fn m ] (exp_var_f x) ⇒ B ->
    Γ ⊢[ mode_fn m ; nil ] A ⊑ B.
Proof.
  intros Γ x A B m Huniq Hb Hwf Htyp.
  remember (exp_var_f x) as evx. remember (mode_fn m) as m_fn.
  induction Htyp; subst; try discriminate; try congruence.
  - (* __sub: only surviving case (other cases fail on mode or exp
       shape; __forall would require mode_tc, ruled out by [try congruence]
       on the mode equation).
       After [subst], the rule's [e] became [exp_var_f x] directly
       (Heqevx was consumed). Apply the [mode_ti] helper to the inner
       d_typing, then compose with the outer d_sub. *)
    edestruct d_typing_var_ti_to_consis_or_eq
      as [Heq | Hcons]; [exact Huniq | exact Hb | exact Hwf | exact Htyp | | ].
    + subst A0.
      match goal with
      | Hsub : d_sub (mode_fn _) nil Γ A B |- _ => exact Hsub
      end.
    + eapply d_consis_sub_trans_nil; eauto.
Qed.

(** Two-argument adjacent swap when both functions are simultaneously
    in scope with the swapped function types.

    We additionally require [d_wf_denv Γ] — used both to derive [uniq Γ]
    (so the variable rule's binding is unique) and to derive [d_wf_typ]
    of the bindings (needed by [d_consis_sub_trans_nil] inside
    [d_typing_var_at_fn_to_d_sub]). *)
Lemma d_typing_order_irrel_adj : forall Γ x y A1 A2 R e1 e2 m,
    d_wf_denv Γ ->
    binds x (dbind_typ (typ_arrow A1 (typ_arrow A2 R))) Γ ->
    binds y (dbind_typ (typ_arrow A2 (typ_arrow A1 R))) Γ ->
    Γ ⊢[ m ] (exp_app (exp_app (exp_var_f x) e1) e2) ⇒ R ->
    Γ ⊢[ m ] (exp_app (exp_app (exp_var_f y) e2) e1) ⇒ R.
Proof.
  intros Γ x y A1 A2 R e1 e2 m Hwfd Hbx Hby Htyp.
  assert (Huniq : uniq Γ) by (clear - Hwfd; induction Hwfd; auto).
  assert (Hwfx : d_wf_typ Γ (typ_arrow A1 (typ_arrow A2 R)))
    by (eapply d_wf_denv_binds_typ; eauto).
  assert (Hwfy : d_wf_typ Γ (typ_arrow A2 (typ_arrow A1 R)))
    by (eapply d_wf_denv_binds_typ; eauto).
  (* Outer __app inversion. [exp_app] is not [is_base_term] and not
     [is_value]; only [d_typing__app] fires. Name the surviving case's
     existentials and premises explicitly. *)
  inversion Htyp as
    [ | | | | | | | |
      Γ_o m_o e1_o e2_o P2 P2' B_o
      Hpat_e2 Href_e2 Hfn He2_tc ];
    subst; clear Htyp;
    try discriminate;
    try (match goal with H : is_base_term (exp_app _ _) |- _ => inversion H end);
    try (match goal with H : is_value (exp_app _ _) |- _ => inversion H end).
  (* Inner __app inversion on [Hfn : d_typing (mode_fn m) Γ (exp_app x e1) _]. *)
  inversion Hfn as
    [ | | | | | | | |
      Γ_i m_i e1_i e2_i P1 P1' B_i
      Hpat_e1 Href_e1 Hx_typ He1_tc ];
    subst; clear Hfn;
    try discriminate;
    try (match goal with H : is_base_term (exp_app _ _) |- _ => inversion H end);
    try (match goal with H : is_value (exp_app _ _) |- _ => inversion H end).
  (* Rebuild for [y] via [d_typing__app] twice. *)
  eapply d_typing__app with (P := P1) (P' := P1');
    [ exact Hpat_e1 | exact Href_e1 | | exact He1_tc ].
  eapply d_typing__app with (P := P2) (P' := P2');
    [ exact Hpat_e2 | exact Href_e2 | | exact He2_tc ].
  (* Goal: d_typing (mode_fn (mode_fn m)) Γ y (typ_arrow P2' (typ_arrow P1' R)). *)
  assert (Hxsub : Γ ⊢[ mode_fn (mode_fn m) ; nil ]
            (typ_arrow A1 (typ_arrow A2 R)) ⊑ (typ_arrow P1' (typ_arrow P2' R)))
    by (eapply d_typing_var_at_fn_to_d_sub; eauto).
  (* Invert [Hxsub]: only [d_sub__arg] fires (mode_fn _, arrow LHS).
     [discriminate] kills mode-mismatch cases; [congruence] kills
     [__forall_l_tagged]'s [m <> mode_ti] premise specialised to
     [mode_fn _]. *)
  inversion Hxsub as
    [ | | | Δa Δb Γ_s ms T1 T2 A1' A2' Hca Hsub_rest | | ];
    subst; clear Hxsub; try discriminate; try congruence.
  (* Δa ++ Δb = nil → Δa = Δb = nil. *)
  match goal with
  | Heq : ?Δa' ++ ?Δb' = nil |- _ =>
      apply app_eq_nil in Heq as [-> ->]
  end.
  (* Invert [Hsub_rest] : d_sub (mode_fn m) nil Γ (typ_arrow A2 R) (typ_arrow P2' R). *)
  inversion Hsub_rest as
    [ | | | Δa' Δb' Γ_s' ms' T1' T2' A1'' A2'' Hcb Hsub_R | | ];
    subst; clear Hsub_rest; try discriminate; try congruence.
  match goal with
  | Heq : ?Δa' ++ ?Δb' = nil |- _ =>
      apply app_eq_nil in Heq as [-> ->]
  end.
  (* Now [Hca : d_consis nil Γ A1 P1'], [Hcb : d_consis nil Γ A2 P2'],
     [Hsub_R : d_sub m nil Γ R R]. Build [y]'s typing. *)
  eapply d_typing__sub with (A := typ_arrow A2 (typ_arrow A1 R)).
  - apply is_base_term__var.
  - apply d_typing__var. exact Hby.
  - rewrite_env (@nil atom ++ @nil atom).
    apply d_sub__arg; [exact Hcb |].
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub__arg; [exact Hca | exact Hsub_R].
Qed.

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
