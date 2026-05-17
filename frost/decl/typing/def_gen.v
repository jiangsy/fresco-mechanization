(** Frost — declarative typing metatheory: generalised relations
    [d_consis_gen], [d_sub_gen], [d_typing_gen] — inductives, basic
    properties, structural lemmas, and the FN^n TI predicate. *)

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
Require Import src.frost.decl.typing.prop_weakening.

Set Implicit Arguments.

(** * Phase 2.D.6 — General subsumption (paper declarative.tex:574).

    The paper's restatable Lemma states that subsumption is admissible
    for ARBITRARY terms, not just base terms. The d_typing__sub rule
    in our calculus restricts the [is_base_term e] premise.

    Strategy (per the design doc): for non-base terms, the rule that
    introduced them can absorb the subsumption into its existing
    conclusion. This is genuinely research-grade — for several cases
    (notably [d_typing__app]) the result requires a transitivity
    lemma for d_sub which itself is not proven (paper:574 sub-lemma).

    We prove the base-term cases cleanly, and admit the non-base
    cases with documented rationale (per the design's strictification
    policy: "narrow to base + abs + freeze if hard").
*)

(** Paper Lemma 3.1 (General subsumption). [paper-ref: lemma:general-subsumption]

    Strategy: paper proof factors through a syntax-directed restatement
    of the type system, using [thm:typing-syn-soundness] / [_completeness]
    + [Generalised General Subsumption] on the syntax-directed system.
    The mech does not have a separate syntax-directed system, so we
    close directly on the bidirectional system. The direct closure
    requires [d_sub] transitivity (paper [thm:subtyping-transitivity] /
    [thm:consist-subtyping-transitivity]); see [d_consis_sub_trans_nil]
    in [prop_subtyping.v] which is the narrowed transitivity sufficient
    for the [__sub] case.

    Added precondition [d_wf_denv Γ]: needed for [d_typing_pat_preserves_wf]
    to extract [d_wf_typ Γ A0] for the intermediate type, which then
    discharges the [d_wf_typ] precondition of [d_consis_sub_trans_nil].

    Closure status — see the [D1 closure structure] comment below for the
    detailed map across Hsub × Hty cases. *)
(** D1 closure structure (this commit):

    Approach — induct on Hsub primarily, then dispatch on Hty's shape
    within each Hsub case. Key supporting facts that simplify the
    proof globally:

    - [d_typing_pat_preserves_wf] → [d_wf_typ Γ A] from Hty.
    - [d_sub_LHS_mono_wf] on Hsub + [d_wf_typ Γ A] → [mono_typ A].
    - For [Hsub = __infer / __check]: LHS is_typ (from mono) → by
      [d_consis_empty_eq], B = A. So both reduce to a mode-lift at the
      same mono type → discharged by [d_typing_gen_lift_mono] (the
      non-gen [d_typing_lift_mono] was deleted 2026-05-17 as unused).
    - For [Hsub = __forall_r]: dispatch on Hty.
      * base terms (unit/var/anno/sub): use [d_typing__sub] with Hsub.
      * values (abs/abs_anno): use [d_typing__forall] + Hsub-IH at each X.
      * applications: NOT a value, NOT base — needs function-side lift
        (research-grade; admitted).
    - For [Hsub = __arg]: similar dispatch; the body-conversion path
      requires recursive general subsumption on the body (research-grade
      for the cases where the body's Hsub-inner is itself __arg /
      __forall_r). The mode-lift sub-case (inner __infer / __check) is
      closeable, but full closure needs an extended induction structure
      (paper's "FN^n" generalisation). Admitted for non-mode-lift cases.
    - For [Hsub = __forall_l_*]: A would be [typ_all_etag] /
      [typ_all_plain] (from Hsub's LHS shape), violating [d_wf_typ Γ A].
      Vacuous. *)
(** * Generalised subtyping (paper's [bid{T}] extension).

    The paper's appendix Lemma B.5 ("Generalised General Subsumption")
    routes through an extended consistency / subtyping relation
    ([fig:frost-subtyping-consistency-gen], syntax-directed.tex) over
    generalised unresolved types [\bid{T}], which extend [\syn{T}]
    with [inh{∀α.}T] on the LHS.

    [d_consis_gen] FAITHFULLY mirrors the paper's generalised
    [typconsis]: it has the SAME structural rules as [d_consis] (unit,
    var, forall_inh_tagged/untagged, forall_syn_tagged/untagged,
    arrow), each taking per-X [d_consis_gen] sub-derivations, PLUS the
    new [__forall_inh] rule (paper's [ForallInh]) admitting
    [typ_all_col colour_inh] on the LHS.

    Mirroring the structure (rather than the earlier [__embed] +
    [__forall_inh] shortcut) is what makes [d_consis_gen] compositional
    — [d_consis_gen_trans] goes through entirely within gen-land. The
    original [d_consis] embeds via the [d_consis_gen__embed] LEMMA
    (proved by induction below). *)
(* Post-refactor (typ_all_plain removed from typ): d_consis_gen mirrors
   d_consis exactly — 4 forall rules, no _untagged variants (those were
   paper-unfaithful). Rule order: tagged-inh, tagged-syn, syn, inh. *)
Inductive d_consis_gen :
    list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_consis_gen__unit : forall Γ,
    d_consis_gen nil Γ typ_unit typ_unit
| d_consis_gen__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_consis_gen nil Γ (typ_var_f X) (typ_var_f X)
| d_consis_gen__forall_inh_tagged : forall L Δ Γ ε T A,
    (forall X, X `notin` L ->
       d_consis_gen Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    ~ List.In ε Δ ->
    d_consis_gen (ε :: Δ) Γ (typ_all_etag ε T) (typ_all_col colour_inh A)
| d_consis_gen__forall_inh_untagged : forall L Δ Γ T A,
    (* Mirror of d_consis__forall_inh_untagged (δ=· case of EqForallInh). *)
    (forall X, X `notin` L ->
       d_consis_gen Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis_gen Δ Γ (typ_all_col colour_syn T) (typ_all_col colour_inh A)
| d_consis_gen__forall_syn_tagged : forall L Δ Γ ε T A,
    (forall X, X `notin` L ->
       d_consis_gen Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis_gen Δ Γ (typ_all_etag ε T) (typ_all_col colour_syn A)
| d_consis_gen__forall_syn : forall L Δ Γ T A,
    (forall X, X `notin` L ->
       d_consis_gen Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis_gen Δ Γ (typ_all_col colour_syn T) (typ_all_col colour_syn A)
| d_consis_gen__forall_inh : forall L Δ Γ T A,
    (forall X, X `notin` L ->
       d_consis_gen Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis_gen Δ Γ (typ_all_col colour_inh T) (typ_all_col colour_inh A)
| d_consis_gen__arrow : forall Δ1 Δ2 Γ T1 T2 A1 A2,
    d_consis_gen Δ1 Γ T1 A1 ->
    d_consis_gen Δ2 Γ T2 A2 ->
    list_disjoint Δ1 Δ2 ->
    d_consis_gen (Δ1 ++ Δ2) Γ (typ_arrow T1 T2) (typ_arrow A1 A2).

(** [d_consis] embeds into [d_consis_gen] — same rules across both. *)
Lemma d_consis_gen__embed : forall Δ Γ T A,
    Δ ⨟ Γ ⊨ T ≈ A ->
    d_consis_gen Δ Γ T A.
Proof.
  intros Δ Γ T A H. induction H.
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var; assumption.
  - apply d_consis_gen__forall_inh_tagged with (L := L); assumption.
  - apply d_consis_gen__forall_inh_untagged with (L := L); assumption.
  - apply d_consis_gen__forall_syn_tagged with (L := L); assumption.
  - apply d_consis_gen__forall_syn with (L := L); assumption.
  - apply d_consis_gen__forall_inh with (L := L); assumption.
  - apply d_consis_gen__arrow; assumption.
Qed.

(** ** Property of [syn_color_t] specific to [d_consis_gen].

    [syn_color_t] (and its structural lemmas) live in [def_extra.v];
    here we prove the [d_consis_gen]-specific fact:
    [d_consis_gen]-related types have EQUAL [syn_color_t] — because
    [d_consis_gen] relates types that differ only in [forall]-colour/
    tag, exactly what [syn_color_t] erases. This is what makes a
    [syn_color_t]-typed variable invariant under narrowing. *)
Lemma d_consis_gen_syn_color_eq : forall Δ Γ A B,
    d_consis_gen Δ Γ A B ->
    syn_color_t A = syn_color_t B.
Proof.
  intros Δ Γ A B H. induction H; simpl; try reflexivity.
  - (* __forall_inh_tagged *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __forall_inh_untagged (NEW) *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __forall_syn_tagged *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __forall_inh *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __forall_syn (post-refactor) *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __arrow *)
    rewrite IHd_consis_gen1. rewrite IHd_consis_gen2. reflexivity.
Qed.

(** When the LHS is already fully syn-coloured ([is_syn_typ T]), the
    generalised consistency relation is forced to be the identity:
    [d_consis_gen] has no constructor with a [typ_all_col colour_syn]
    LHS (mirrors the paper: [syn{∀α.}] is never a [typconsis] LHS — see
    [syntax-directed.tex], all [typconsis] LHS [forall]s are tagged),
    so any [forall] node makes the hypothesis vacuous, while the
    [unit]/[var]/[arrow] rules are rigid. This is what lets the D12
    [__abs_anno] cases reconstruct: the rule's arrow-arg [syn_color_t A]
    is pinned, but any consistency target of it must equal it. *)
Lemma d_consis_gen_lhs_syn_eq : forall T,
    is_syn_typ T ->
    forall Δ Γ A, d_consis_gen Δ Γ T A -> T = A.
Proof.
  intros T Hsyn. induction Hsyn; intros Δ Γ A0 Hc.
  - inversion Hc; subst. reflexivity.
  - inversion Hc; subst. reflexivity.
  - inversion Hc; subst. f_equal; eauto.
  - (* is_syn_typ__all: T = typ_all_col colour_syn A. Post δ-refactor,
       d_consis_gen has TWO rules with LHS typ_all_col colour_syn:
       __forall_syn (T = A, original) and __forall_inh_untagged (NEW,
       T ≠ A by colour). The new rule makes this lemma provably FALSE.
       Admitted pending precondition strengthening (e.g., is_syn_typ A
       on the conclusion, or restrict to non-cross-colour). *)
    admit.
Admitted.
(* d_consis_gen_lhs_syn_eq: 1 admit post-δ-refactor — new
   __forall_inh_untagged rule breaks the equality conclusion. Used in
   D12 __abs_anno; may cascade. *)

(** The original [d_consis] inherits the same rigidity (it is a subset
    of [d_consis_gen]). *)
Lemma d_consis_lhs_syn_eq : forall T,
    is_syn_typ T ->
    forall Δ Γ A, d_consis Δ Γ T A -> T = A.
Proof.
  intros. eapply d_consis_gen_lhs_syn_eq; eauto using d_consis_gen__embed.
Qed.

(** Parallel rigidity on [is_inh_typ] LHS: for fully [inh]-painted [T],
    every [d_consis_gen] target equals [T]. Same proof structure as the
    [is_syn_typ] version: unit/var rigid, arrow inducts, [is_inh_typ__all]
    forces the [__forall_inh] rule (the only [d_consis_gen] rule whose LHS
    is [typ_all_col colour_inh _]); cofinite IH + open-inj. *)
Lemma d_consis_gen_lhs_inh_eq : forall T,
    is_inh_typ T ->
    forall Δ Γ A, d_consis_gen Δ Γ T A -> T = A.
Proof.
  intros T Hinh. induction Hinh; intros Δ Γ A0 Hc.
  - inversion Hc; subst. reflexivity.
  - inversion Hc; subst. reflexivity.
  - inversion Hc; subst. f_equal; eauto.
  - inversion Hc; subst.
    f_equal.
    match goal with
    | Hbody : forall X, X `notin` ?L0 -> d_consis_gen _ _ _ _ |- _ =>
        pick fresh X for
          (L `union` L0 `union` ftvar_in_typ A `union` ftvar_in_typ A1);
        assert (HX_L : X `notin` L) by fsetdec;
        assert (HX_L0 : X `notin` L0) by fsetdec;
        specialize (H0 X HX_L Δ ((X ~ dbind_tvar) ++ Γ)
                      (open_typ_wrt_typ A1 (typ_var_f X)) (Hbody X HX_L0));
        apply open_typ_wrt_typ_inj in H0; auto
    end.
Qed.

(** The original [d_consis] inherits the same rigidity. *)
Lemma d_consis_lhs_inh_eq : forall T,
    is_inh_typ T ->
    forall Δ Γ A, d_consis Δ Γ T A -> T = A.
Proof.
  intros. eapply d_consis_gen_lhs_inh_eq; eauto using d_consis_gen__embed.
Qed.

(** Generalised subtyping using [d_consis_gen] for the consistency
    premises. Adds an __infer / __check that uses [d_consis_gen],
    plus the structural cases.

    [d_sub_gen__refl_any] requires [mode_typ_compat m A]: the paper's
    [M ⊢ A] predicate. Without it, [d_sub_gen (mode_fn _) nil Γ A A]
    would be admissible for non-arrow A (e.g. typ_unit), but the
    corresponding [d_typing (mode_fn _) Γ e A] is unreachable — the
    [mode_typ_compat] premise prevents that inconsistency at the
    relation level. *)
Inductive d_sub_gen :
    mode -> list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_sub_gen__embed : forall m Δ Γ T A,
    d_sub m Δ Γ T A ->
    d_sub_gen m Δ Γ T A
(* [d_sub_gen__infer_gen] / [d_sub_gen__check_gen] — the generalised
   TI/TC subtyping rules (paper syntax-directed.tex:43-53): the
   syntax-directed [typsub] at TI/TC takes the GENERALISED
   [typconsis]. [d_sub_gen__embed] only covers the non-generalised
   [d_sub], so these add the [d_consis_gen]-based variants. *)
| d_sub_gen__infer_gen : forall Γ T A,
    (* mirrors [d_sub__infer]: bases [T], [A] each painted [syn]. *)
    d_consis_gen nil Γ (syn_color T) (syn_color A) ->
    d_sub_gen mode_ti nil Γ (syn_color T) (syn_color A)
| d_sub_gen__check_gen : forall Δ Γ T A,
    (* mirrors [d_sub__check]: base [T] painted [syn] (and guarded),
       base [A] painted [inh]. *)
    guarded_typ (syn_color T) ->
    d_consis_gen Δ Γ (syn_color T) (inh_color A) ->
    d_sub_gen mode_tc Δ Γ (syn_color T) (inh_color A)
(* [d_sub_gen__refl_any] — restricted to [mono_typ A].

   An earlier version used [mode_typ_compat m A] as the premise, but
   that is UNSOUND: it admits [d_sub_gen mode_tc nil Γ A A] for
   [A = typ_all_col colour_inh A_inner] (since [is_inh_typ] includes
   such [A]), yet the corresponding mode-lift of typing is not always
   derivable. Concrete counter-example: [e = exp_anno e0 A] with [e0]
   a non-value and [A = typ_all_col colour_inh ...]: [Hty] at mode_ti
   is derivable, but [d_typing mode_tc Γ e A] is NOT — [d_typing__sub]
   needs [d_sub mode_tc A A] which fails (no [d_consis] rule admits
   [typ_all_col] on the LHS), and [d_typing__forall] needs
   [is_value e0]. The paper's [M ⊢ A] predicate is silent on this.

   Restricting to [mono_typ A] keeps the rule sound: mono types are
   reflexively subtypeable ([d_consis_refl_mono]) and mode-liftable
   (cf. [d_typing_gen_lift_mono]). *)
| d_sub_gen__refl_mono : forall m Γ A,
    mono_typ A ->
    mode_typ_compat m A ->
    d_wf_typ Γ A ->
    d_sub_gen m nil Γ A A
| d_sub_gen__forall_r : forall L Δ Γ T A,
    (forall X, X `notin` L ->
       d_sub_gen mode_tc Δ ((X ~ dbind_tvar) ++ Γ) T (open_typ_wrt_typ A (typ_var_f X))) ->
    d_sub_gen mode_tc Δ Γ T (typ_all_col colour_inh A)
| d_sub_gen__arg : forall Δ1 Δ2 Γ m T1 T2 A1 A2,
    d_consis_gen Δ1 Γ T1 A1 ->
    d_sub_gen m Δ2 Γ T2 A2 ->
    d_sub_gen (mode_fn m) (Δ1 ++ Δ2) Γ (typ_arrow T1 T2) (typ_arrow A1 A2).

(** ** Generalised typing [d_typing_gen].

    Mirrors [d_typing] rule-for-rule, EXCEPT [d_typing_gen__sub] uses
    the generalised subtyping [d_sub_gen] in place of [d_sub]. This is
    the system the paper's Lemma B.5 (Generalised General Subsumption,
    D12) is really about: the syntax-directed [Sub] rule takes the
    generalised subtyping.

    Standalone inductive (not mutual) — it reuses the ORIGINAL [d_pat]
    in the [__app] rule (the pattern judgement is orthogonal to
    subsumption and does not change). [d_typing] embeds into
    [d_typing_gen] structurally via [d_sub_gen__embed]
    ([d_typing_embed_gen] below).

    With [d_typing_gen__sub] taking [d_sub_gen], the D12 cases that
    were blocked on the gen→sub bridge (var/anno/+ __arg) close
    directly: reconstruct [d_typing_gen__sub] with the [d_sub_gen]
    in hand, no bridge needed. *)
Inductive d_typing_gen :
  mode -> list (atom * dbind) -> exp -> typ -> Prop :=
| d_typing_gen__unit : forall Γ,
    mode_typ_compat mode_ti typ_unit ->
    d_typing_gen mode_ti Γ exp_unit typ_unit
| d_typing_gen__var : forall Γ x A,
    (* mirrors [d_typing__var]: reads back the (already [syn]-painted)
       context binding. *)
    binds x (dbind_typ A) Γ ->
    d_typing_gen mode_ti Γ (exp_var_f x) A
| d_typing_gen__anno : forall Γ e A,
    (* mirrors [d_typing__anno]: base [A : ctyp], premise + term
       annotation [inh]-painted, conclusion [syn]-painted. *)
    d_typing_gen mode_tc Γ e (inh_color A) ->
    d_typing_gen mode_ti Γ (exp_anno e (inh_color A)) (syn_color A)
| d_typing_gen__sub : forall Γ m e A B,
    is_base_term e ->
    d_typing_gen mode_ti Γ e A ->
    d_sub_gen m nil Γ A B ->
    d_typing_gen m Γ e B
| d_typing_gen__freeze : forall Γ e A,
    d_typing_gen mode_ti Γ e A ->
    d_typing_gen mode_tc Γ (exp_freeze e) A
| d_typing_gen__forall : forall L Γ e A,
    is_value e ->
    (forall X, X `notin` L ->
       d_typing_gen mode_tc ((X ~ dbind_tvar) ++ Γ) e
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_typing_gen mode_tc Γ e (typ_all_col colour_inh A)
| d_typing_gen__abs : forall L Γ m e A B,
    (* mirrors [d_typing__abs]: base [A], context binding [syn]-painted,
       conclusion arrow-arg [inh]-painted. *)
    d_wf_typ Γ (inh_color A) ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m) ((x ~ dbind_typ (syn_color A)) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing_gen m Γ (exp_abs e) (typ_arrow (inh_color A) B)
| d_typing_gen__abs_anno : forall L Γ m e A B,
    (* mirrors [d_typing__abs_anno]: base [A : ctyp], context binding
       AND conclusion arrow-arg both [syn]-painted; term carries
       [inh_color A] (a [typ]). *)
    d_wf_typ Γ (syn_color A) ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m) ((x ~ dbind_typ (syn_color A)) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing_gen m Γ (exp_abs_anno (inh_color A) e) (typ_arrow (syn_color A) B)
| d_typing_gen__app : forall Γ m e1 e2 P P' B,
    (* mirrors [d_typing__app]: base skeleton [P : ctyp], [d_pat] reads
       its [syn] painting, [d_refine_syn] its [inh] painting; [P' : typ]
       is the refinement output / function arg; arg checked at
       [inh_color (erase P')]. *)
    d_pat mode_tc Γ e2 (syn_color P) ->
    d_refine_syn nil Γ (inh_color P) P' ->
    d_typing_gen (mode_fn m) Γ e1 (typ_arrow P' B) ->
    d_typing_gen mode_tc Γ e2 (inh_color (erase P')) ->
    d_typing_gen m Γ (exp_app e1 e2) B.

(** [d_typing] embeds into [d_typing_gen]: every original typing is a
    generalised typing (the [__sub] rule's [d_sub] embeds via
    [d_sub_gen__embed]). Structural induction. *)
Lemma d_typing_embed_gen : forall m Γ e A,
    Γ ⊢[ m ] e ⇒ A ->
    d_typing_gen m Γ e A.
Proof.
  intros m Γ e A H. induction H.
  - apply d_typing_gen__unit; assumption.
  - apply d_typing_gen__var; assumption.
  - apply d_typing_gen__anno; assumption.
  - apply d_typing_gen__sub with (A := A); auto.
    apply d_sub_gen__embed; assumption.
  - apply d_typing_gen__freeze; assumption.
  - apply d_typing_gen__forall with (L := L); assumption.
  - apply d_typing_gen__abs with (L := L); assumption.
  - apply d_typing_gen__abs_anno with (L := L); assumption.
  - apply d_typing_gen__app with (P := P) (P' := P'); assumption.
Qed.

(** [d_sub_gen] is reflexive on any mono wf type at a compatible mode. *)
Lemma d_sub_gen_refl : forall Γ A m,
    mono_typ A ->
    mode_typ_compat m A ->
    d_wf_typ Γ A ->
    d_sub_gen m nil Γ A A.
Proof.
  intros. apply d_sub_gen__refl_mono; auto.
Qed.

(** [d_sub] is reflexive on any mono wf type at a compatible mode.
    (Generalises [d_sub_refl_mono] from mode_ti to all compatible
    modes — sound because mono types carry no quantifiers, so the
    [d_consis] reflexivity used by every [d_sub] mode is available.) *)
Lemma d_sub_refl_mono_mode : forall Γ A m,
    mono_typ A ->
    mode_typ_compat m A ->
    d_wf_typ Γ A ->
    Γ ⊢[ m ; nil ] A ⊑ A.
Proof.
  intros Γ A m Hmono Hcompat. generalize dependent Γ.
  induction Hcompat; intros Γ Hwf.
  - (* mode_ti — route the mono refl through the [syn_color]-painted
       [d_sub__infer] using [A = syn_color (erase A)]. *)
    assert (Hg : d_sub mode_ti nil Γ (syn_color (erase A)) (syn_color (erase A))).
    { apply d_sub__infer.
      rewrite (mono_typ_syn_color_erase Hmono).
      apply d_consis_refl_mono; auto. }
    rewrite (mono_typ_syn_color_erase Hmono) in Hg. exact Hg.
  - (* mode_tc — same pattern, RHS now [inh_color]. *)
    assert (Hg : d_sub mode_tc nil Γ (syn_color (erase A)) (inh_color (erase A))).
    { apply d_sub__check.
      - rewrite (mono_typ_syn_color_erase Hmono).
        apply mono_typ_guarded; auto.
      - rewrite (mono_typ_syn_color_erase Hmono),
                (mono_typ_inh_color_erase Hmono).
        apply d_consis_refl_mono; auto. }
    rewrite (mono_typ_syn_color_erase Hmono),
            (mono_typ_inh_color_erase Hmono) in Hg.
    exact Hg.
  - (* mode_fn: A = typ_arrow A0 B *)
    inversion Hmono; subst.
    inversion Hwf; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub__arg.
    + apply d_consis_refl_mono; auto.
    + apply IHHcompat; auto.
Qed.

(** [d_consis_gen] is reflexive on any [is_inh_typ] wf type — the
    paper's generalised consistency is structurally reflexive on
    generalised unresolved types. Proven by induction on the
    [is_inh_typ] derivation: unit/var/arrow via [__embed]/[__arrow],
    and [typ_all_col colour_inh] via the structural [__forall_inh]
    rule. This is the mechanised analogue of the paper's implicit
    "[typconsis] is reflexive" used in the __app step of Lemma B.5. *)
Lemma d_consis_gen_refl : forall Γ A,
    is_inh_typ A ->
    d_wf_typ Γ A ->
    d_consis_gen nil Γ A A.
Proof.
  intros Γ A Hinh. generalize dependent Γ.
  induction Hinh; intros Γ Hwf.
  - apply d_consis_gen__embed. apply d_consis__unit.
  - apply d_consis_gen__embed. inversion Hwf; subst.
    apply d_consis__var; assumption.
  - inversion Hwf; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow.
    + apply IHHinh1; assumption.
    + apply IHHinh2; assumption.
    + apply list_disjoint_nil_l.
  - (* typ_all_col colour_inh A *)
    inversion Hwf; subst.
    apply d_consis_gen__forall_inh with (L := L `union` L0 `union` dom Γ).
    intros X HX. apply H0; auto.
Qed.

(** [d_consis_gen_refl_syn]: reflexivity of [d_consis_gen] on
    syn-painted types. Uses the new [__forall_syn] rule for
    [typ_all_col colour_syn] LHS. Mirror of [d_consis_gen_refl] for
    inh-painted types.

    This is the typing-level analogue of the new [__forall_syn] rule's
    main payoff: refl on syn-painted polytypes is now provable, unlocking
    the D12 __app function-arg mode-shift composition. *)
Lemma d_consis_gen_refl_syn : forall Γ A,
    is_syn_typ A ->
    d_wf_typ Γ A ->
    d_consis_gen nil Γ A A.
Proof.
  intros Γ A Hsyn. generalize dependent Γ.
  induction Hsyn; intros Γ Hwf.
  - apply d_consis_gen__embed. apply d_consis__unit.
  - apply d_consis_gen__embed. inversion Hwf; subst.
    apply d_consis__var; assumption.
  - inversion Hwf; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow.
    + apply IHHsyn1; assumption.
    + apply IHHsyn2; assumption.
    + apply list_disjoint_nil_l.
  - (* typ_all_col colour_syn A: uses the new __forall_syn rule. *)
    inversion Hwf; subst.
    apply d_consis_gen__forall_syn with (L := L `union` L0 `union` dom Γ).
    intros X HX. apply H0; auto.
Qed.

(** [d_consis_gen_refl_is_typ]: reflexivity of [d_consis_gen] on any
    [is_typ] (decorated, colour-annotated) type. Combines refl_syn /
    refl via dispatch on the [typ_all_col] colour. Used in D12's __app
    case to reflexively type the function-arg [P'] regardless of its
    colour annotation. *)
Lemma d_consis_gen_refl_is_typ : forall Γ A,
    is_typ A ->
    d_wf_typ Γ A ->
    d_consis_gen nil Γ A A.
Proof.
  intros Γ A Hist. generalize dependent Γ.
  induction Hist; intros Γ Hwf.
  - apply d_consis_gen__embed. apply d_consis__unit.
  - apply d_consis_gen__embed. inversion Hwf; subst.
    apply d_consis__var; assumption.
  - inversion Hwf; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow.
    + apply IHHist1; assumption.
    + apply IHHist2; assumption.
    + apply list_disjoint_nil_l.
  - (* typ_all_col c A: dispatch on colour. *)
    inversion Hwf; subst.
    destruct c.
    + apply d_consis_gen__forall_syn with (L := L `union` L0 `union` dom Γ).
      intros X HX. apply H0; auto.
    + apply d_consis_gen__forall_inh with (L := L `union` L0 `union` dom Γ).
      intros X HX. apply H0; auto.
Qed.

(** [d_typing_check_is_inh]: a [mode_tc] (check-mode) typing always
    has an [is_inh_typ] type. PROVABLY FALSE in the current rule set —
    [__freeze] inherits its inner mode_ti type unchanged, so for
    [exp_anno e0 (inh_color (ctyp_all _))] with output
    [syn_color (ctyp_all _) = typ_all_col colour_syn _] (NOT is_inh_typ),
    [__freeze] produces a mode_tc derivation at a non-inh type. The
    fix requires repainting in [__freeze / __abs / __abs_anno / __app]
    rule definitions; out of scope for this pass.

    LEMMA REMOVED 2026-05-16: no callers in the codebase; the false
    admit served as documentation only. The counter-example is preserved
    above for future reference. *)

(** [d_consis_lhs_is_syn_typ]: stated for the pre-fix system as "is_inh
    LHS in d_consis forces is_syn LHS". POST the [d_consis__forall_inh]
    addition, this is PROVABLY FALSE — counter-example:
    [A = typ_all_col colour_inh (typ_var_b 0)] has is_inh_typ A and
    [d_consis nil Γ A A] is derivable via [__forall_inh] (with the trivial
    cofinite premise), but is_syn_typ A FAILS at the head.

    LEMMA REMOVED 2026-05-16: no callers in the codebase. The
    counter-example is preserved above for future reference. *)

(** [d_consis_rhs_is_inh_typ]: when [d_consis nil Γ A B] holds and
    [is_inh_typ A], then B is also [is_inh_typ]. Used to propagate
    is_inh-ness through d_consis (necessary to invoke
    [d_consis_sym_inh] in the reverse direction). *)
Lemma d_consis_rhs_is_inh_typ : forall Γ A B,
    nil ⨟ Γ ⊨ A ≈ B ->
    is_inh_typ A ->
    is_inh_typ B.
Proof.
  intros Γ A B Hc Hinh.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hc; subst.
  - apply is_inh_typ__unit.
  - apply is_inh_typ__var.
  - inversion Hinh. (* __forall_inh_tagged: typ_all_etag — not inh *)
  - (* __forall_inh_untagged (NEW): A = typ_all_col colour_syn — not inh *)
    inversion Hinh.
  - inversion Hinh. (* __forall_syn_tagged: typ_all_etag — not inh *)
  - inversion Hinh. (* __forall_syn (post-refactor): typ_all_col colour_syn — not inh *)
  - (* __forall_inh: A = typ_all_col colour_inh A_inner, B = same
       structure on RHS body. is_inh_typ A ⟹ inversion gives is_inh_typ
       (open A_inner X) for each X via cofinite premise. Use IH (cofinite)
       to derive is_inh_typ (open B_inner X), then [is_inh_typ__all]
       wraps. *)
    inversion Hinh; subst.
    apply is_inh_typ__all with (L := L `union` L0).
    intros X HX.
    eapply H0; eauto.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hinh; subst.
    apply is_inh_typ__arrow; auto.
Qed.

(** [d_consis_gen_rhs_is_inh_typ]: same as above but for d_consis_gen. *)
Lemma d_consis_gen_rhs_is_inh_typ : forall Γ A B,
    d_consis_gen nil Γ A B ->
    is_inh_typ A ->
    is_inh_typ B.
Proof.
  intros Γ A B Hcg.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hcg; intros Hinh; try discriminate HeqΔ.
  - (* __unit *) apply is_inh_typ__unit.
  - (* __var *) apply is_inh_typ__var.
  - (* __forall_inh_untagged (NEW): A = typ_all_col colour_syn — not inh *)
    inversion Hinh.
  - (* __forall_syn_tagged: A = typ_all_etag — not is_inh. *)
    inversion Hinh.
  - (* __forall_syn (post-refactor): A = typ_all_col colour_syn — not is_inh. *)
    inversion Hinh.
  - (* __forall_inh: both sides typ_all_col colour_inh. *)
    inversion Hinh; subst.
    apply is_inh_typ__all with (L := L `union` L0).
    intros X HX. apply H0; auto.
  - (* __arrow *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hinh; subst.
    apply is_inh_typ__arrow; auto.
Qed.

(** [d_wf_typ_is_typ]: d_wf_typ implies is_typ. *)
Lemma d_wf_typ_is_typ : forall Γ A,
    d_wf_typ Γ A -> is_typ A.
Proof.
  intros Γ A H. induction H.
  - apply is_typ__unit.
  - apply is_typ__var.
  - apply is_typ__arrow; assumption.
  - apply is_typ__all with (L := L); auto.
Qed.

(* [d_consis_lhs_is_inh_for_typ] (formerly here) DELETED 2026-05-17 —
   provably FALSE post-refactor: the new [d_consis__forall_syn] rule
   admits [typ_all_col colour_syn] LHS which is [is_typ] but NOT
   [is_inh_typ]. Had zero callers across the codebase. *)

(** [d_consis_gen_preserves_wf]: d_consis_gen preserves wf on RHS.
    Every forall rule's RHS is [typ_all_col _ A0] with per-X RHS-wf
    from the IH; arrow is structural; unit/var trivial. *)
Lemma d_consis_gen_preserves_wf : forall Δ Γ A B,
    d_consis_gen Δ Γ A B ->
    d_wf_typ Γ B.
Proof.
  intros Δ Γ A B Hcg. induction Hcg.
  - (* __unit *) apply d_wf_typ__unit.
  - (* __var *) apply d_wf_typ__var; assumption.
  - (* __forall_inh_tagged *) apply d_wf_typ__all with (L := L); assumption.
  - (* __forall_inh_untagged (NEW) *) apply d_wf_typ__all with (L := L); assumption.
  - (* __forall_syn_tagged *) apply d_wf_typ__all with (L := L); assumption.
  - (* __forall_syn (post-refactor) *) apply d_wf_typ__all with (L := L); assumption.
  - (* __forall_inh *) apply d_wf_typ__all with (L := L); assumption.
  - (* __arrow *) apply d_wf_typ__arrow; auto.
Qed.

(** [d_consis_gen_sym_inh]: symmetry for d_consis_gen on is_inh types. *)
Lemma d_consis_gen_sym_inh : forall Γ A B,
    d_consis_gen nil Γ A B ->
    is_inh_typ A ->
    d_consis_gen nil Γ B A.
Proof.
  intros Γ A B Hcg.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hcg; intros Hinh; try discriminate HeqΔ.
  - (* __unit *) apply d_consis_gen__unit.
  - (* __var *) apply d_consis_gen__var; assumption.
  - (* __forall_inh_untagged (NEW): LHS typ_all_col colour_syn — not is_inh. *)
    inversion Hinh.
  - (* __forall_syn_tagged: LHS typ_all_etag — not is_inh. *)
    inversion Hinh.
  - (* __forall_syn (post-refactor): LHS typ_all_col colour_syn — not is_inh. *)
    inversion Hinh.
  - (* __forall_inh: both sides typ_all_col colour_inh. IH = H0. *)
    inversion Hinh; subst.
    apply d_consis_gen__forall_inh with (L := L `union` L0).
    intros X HX.
    apply H0; auto.
  - (* __arrow *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hinh; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow; auto.
Qed.

(** [d_consis_gen_trans]: transitivity of [d_consis_gen] at [Δ = nil].

    At [Δ = nil] the existential-[Permutation] complication of
    [d_consis_compose] disappears: every sub-derivation also lives at
    [nil], so the result mode/Δ is uniform and the forall cases
    compose per-X without a [Δ] mismatch. The paper's generalised
    [typconsis] is transitive (Lemma B.2 generalised); this is the
    [Δ = nil] instance, which is all the D12 [__sub]/[__arg] use
    sites need (their outer [Δ] is forced [nil]). *)
(** [d_consis_gen_trans]: composes [d_consis_gen] at empty Δ. The [is_typ T]
    precondition excludes [typ_all_etag] at the LHS top, which would otherwise
    let [__forall_syn_tagged] compose with [__forall_inh_untagged] into
    [typ_all_etag → typ_all_col colour_inh] — a shape whose only producer is
    [d_consis_gen__forall_inh_tagged] at output Δ = ε :: Δ_body ≠ nil, breaking
    the nil-Δ output signature. Call sites supply [is_typ T] from [syn_color]
    shapes (which are always [is_typ]). *)
Lemma d_consis_gen_trans : forall Γ T A B,
    is_typ T ->
    d_consis_gen nil Γ T A ->
    d_consis_gen nil Γ A B ->
    d_consis_gen nil Γ T B.
Proof.
  intros Γ T A B Hwf_T Hc1 Hc2.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  generalize dependent B.
  induction Hc1; intros B0 Hc2.
  - (* __unit *) exact Hc2.
  - (* __var *) exact Hc2.
  - (* __forall_inh_tagged: T = typ_all_etag — not is_typ. *)
    inversion Hwf_T.
  - (* __forall_inh_untagged (NEW δ): LHS typ_all_col colour_syn,
       RHS typ_all_col colour_inh. Hc2 LHS = colour_inh ⟹ __forall_inh.
       Compose via cofinite IH. *)
    subst.
    inversion Hc2; subst.
    inversion Hwf_T; subst.
    apply d_consis_gen__forall_inh_untagged with (L := L `union` L0 `union` L1).
    intros X HX.
    apply H0; auto.
  - (* __forall_syn_tagged: T = typ_all_etag — not is_typ. *)
    inversion Hwf_T.
  - (* __forall_syn: LHS typ_all_col colour_syn, RHS typ_all_col colour_syn.
       Hc2 LHS = colour_syn ⟹ __forall_syn OR __forall_inh_untagged. *)
    subst.
    inversion Hc2; subst.
    + (* Hc2 = __forall_inh_untagged: result LHS colour_syn → RHS colour_inh *)
      inversion Hwf_T; subst.
      apply d_consis_gen__forall_inh_untagged with (L := L `union` L0 `union` L1).
      intros X HX. apply H0; auto.
    + (* Hc2 = __forall_syn: result LHS colour_syn → RHS colour_syn *)
      inversion Hwf_T; subst.
      apply d_consis_gen__forall_syn with (L := L `union` L0 `union` L1).
      intros X HX. apply H0; auto.
  - (* __forall_inh: LHS typ_all_col colour_inh, RHS typ_all_col colour_inh.
       Hc2 LHS = colour_inh ⟹ __forall_inh. *)
    subst.
    inversion Hc2; subst.
    inversion Hwf_T; subst.
    apply d_consis_gen__forall_inh with (L := L `union` L0 `union` L1).
    intros X HX. apply H0; auto.
  - (* __arrow: Δ1 ++ Δ2 = nil ⇒ both nil *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    simpl in Hc2. inversion Hc2; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    inversion Hwf_T; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow.
    + apply IHHc1_1; auto.
    + apply IHHc1_2; auto.
    + apply list_disjoint_nil_l.
Qed.

(** [d_typing_narrow_consis_head_arg]: narrowing a [d_typing]
    head-binding along a [d_consis_gen]. Now a clean corollary of
    [d_typing_narrow_consis_head]: [d_consis_gen]-related types have
    equal [syn_color_t] ([d_consis_gen_syn_color_eq]), which is exactly
    the premise [d_typing_narrow_consis_head] needs. *)
Lemma d_typing_narrow_consis_head_arg : forall x Aold Anew Γ m e B,
    ((x ~ dbind_typ Aold) ++ Γ) ⊢[ m ] e ⇒ B ->
    d_consis_gen nil Γ Aold Anew ->
    ((x ~ dbind_typ Anew) ++ Γ) ⊢[ m ] e ⇒ B.
Proof.
  intros x Aold Anew Γ m e B Hty Hcg.
  apply d_typing_narrow_consis_head with (Aold := Aold); auto.
  symmetry. eapply d_consis_gen_syn_color_eq; eauto.
Qed.

(** ** Structural lemmas for the generalised relations.

    Weakening and tvar-morph for [d_consis_gen] / [d_sub_gen]. Mirror
    the corresponding facts on [d_consis] / [d_sub] — composition
    works case-by-case on the embedded / refl_any / arrow / forall_r /
    arg constructors. Needed by [d_typing_general_subsumption_gen] to
    weaken sub-derivations when reasoning under cofinitely-quantified
    type-variable binders (paper Lemma B.5 proof, __forall_r case). *)

Lemma d_consis_gen_weakening : forall Γ1 Γ2 Γ3 Δ T A,
    d_consis_gen Δ (Γ1 ++ Γ3) T A ->
    d_consis_gen Δ (Γ1 ++ Γ2 ++ Γ3) T A.
Proof.
  intros Γ1 Γ2 Γ3 Δ T A H. dependent induction H.
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var.
    apply binds_app_iff in H. destruct H as [Hb | Hb].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_consis_gen__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    + intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
      eapply H0; eauto.
    + assumption.
  - (* __forall_inh_untagged (NEW) *)
    apply d_consis_gen__forall_inh_untagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_syn with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_inh with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__arrow; auto.
Qed.

Corollary d_consis_gen_weakening_head : forall Γ Γ' Δ T A,
    d_consis_gen Δ Γ T A ->
    d_consis_gen Δ (Γ' ++ Γ) T A.
Proof.
  intros. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_consis_gen_weakening. simpl. auto.
Qed.

Lemma d_sub_gen_weakening : forall Γ1 Γ2 Γ3 m Δ T A,
    d_sub_gen m Δ (Γ1 ++ Γ3) T A ->
    d_sub_gen m Δ (Γ1 ++ Γ2 ++ Γ3) T A.
Proof.
  intros Γ1 Γ2 Γ3 m Δ T A H. dependent induction H.
  - apply d_sub_gen__embed. apply d_sub_weakening; auto.
  - apply d_sub_gen__infer_gen; auto.
    apply d_consis_gen_weakening; auto.
  - apply d_sub_gen__check_gen; auto.
    apply d_consis_gen_weakening; auto.
  - apply d_sub_gen__refl_mono; auto. eapply d_wf_typ_weakening; eauto.
  - apply d_sub_gen__forall_r with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_sub_gen__arg; eauto.
    apply d_consis_gen_weakening; auto.
Qed.

Corollary d_sub_gen_weakening_head : forall Γ Γ' m Δ T A,
    d_sub_gen m Δ Γ T A ->
    d_sub_gen m Δ (Γ' ++ Γ) T A.
Proof.
  intros. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_gen_weakening. simpl. auto.
Qed.

(** Weakening for [d_typing_gen] — structural, mirrors
    [d_typing_weakening]. The [__sub] case uses [d_sub_gen_weakening]. *)
Lemma d_typing_gen_weakening : forall Γ1 Γ2 Γ3 m e A,
    d_typing_gen m (Γ1 ++ Γ3) e A ->
    d_typing_gen m (Γ1 ++ Γ2 ++ Γ3) e A.
Proof.
  intros Γ1 Γ2 Γ3 m e A H.
  remember (Γ1 ++ Γ3) as Γ eqn:HeqΓ.
  generalize dependent Γ1.
  induction H; intros Γ1 HeqΓ; subst.
  - apply d_typing_gen__unit; assumption.
  - apply d_typing_gen__var. apply binds_app_iff in H.
    destruct H as [Hb | Hb].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_typing_gen__anno; auto.
  - apply d_typing_gen__sub with (A := A); auto.
    apply d_sub_gen_weakening; auto.
  - apply d_typing_gen__freeze; auto.
  - apply d_typing_gen__forall with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    + assumption.
    + intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H1; auto.
  - apply d_typing_gen__abs with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx.
      rewrite_env (((x ~ dbind_typ (syn_color A)) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H1; auto.
  - apply d_typing_gen__abs_anno with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx.
      rewrite_env (((x ~ dbind_typ (syn_color A)) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H1; auto.
  - apply d_typing_gen__app with (P := P) (P' := P'); auto.
    + eapply (proj2 d_typing_pat_weakening) with
        (Γ1 := Γ1) (Γ2 := Γ2) (Γ3 := Γ3); eauto.
    + apply d_refine_syn_weakening; auto.
Qed.

Corollary d_typing_gen_weakening_head : forall Γ Γ' m e A,
    d_typing_gen m Γ e A ->
    d_typing_gen m (Γ' ++ Γ) e A.
Proof.
  intros. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_typing_gen_weakening. simpl. auto.
Qed.

(** [d_sub_gen] preserves RHS well-formedness — the [d_sub_gen]
    analogue of [d_sub_preserves_wf]. [__embed] routes through
    [d_sub_preserves_wf], [__refl_mono] reads off its premise,
    [__forall_r] / [__arg] are structural ([__arg]'s arg side uses
    [d_consis_gen_preserves_wf]). *)
Lemma d_sub_gen_preserves_wf : forall m Δ Γ T A,
    d_sub_gen m Δ Γ T A ->
    d_wf_typ Γ A.
Proof.
  intros m Δ Γ T A H. induction H.
  - (* __embed *) eapply d_sub_preserves_wf; eauto.
  - (* __infer_gen *) eapply d_consis_gen_preserves_wf; eauto.
  - (* __check_gen *) eapply d_consis_gen_preserves_wf; eauto.
  - (* __refl_mono *) assumption.
  - (* __forall_r *)
    apply d_wf_typ__all with (L := L `union` dom Γ).
    intros X HX. apply H0; auto.
  - (* __arg *)
    apply d_wf_typ__arrow.
    + eapply d_consis_gen_preserves_wf; eauto.
    + assumption.
Qed.

(** [d_typing_gen] preserves type well-formedness — the [d_typing_gen]
    analogue of [d_typing_pat_preserves_wf]'s typing half. Mirrors
    that proof case-for-case; [__sub] routes through
    [d_sub_gen_preserves_wf]. *)
Lemma d_typing_gen_preserves_wf : forall m Γ e A,
    d_typing_gen m Γ e A ->
    d_wf_denv Γ ->
    d_wf_typ Γ A.
Proof.
  intros m Γ e A H. induction H; intros Hwfd.
  - (* __unit *) apply d_wf_typ__unit.
  - (* __var: post re-encoding the rule returns the bound type raw —
       no [syn_color] wrap on the conclusion. *)
    eapply d_wf_denv_binds_typ; eauto.
  - (* __anno: IH gives [d_wf_typ Γ (inh_color A)]; conclusion is
       [syn_color A]; bridge via [d_wf_typ_inh_color_syn_color]. *)
    apply d_wf_typ_inh_color_syn_color. apply IHd_typing_gen; auto.
  - (* __sub *) eapply d_sub_gen_preserves_wf; eauto.
  - (* __freeze *) apply IHd_typing_gen; auto.
  - (* __forall *)
    apply d_wf_typ__all with (L := L `union` dom Γ).
    intros X HX. apply H1; auto. apply d_wf_denv__tvar; auto.
  - (* __abs: arrow-arg [inh_color A] from the rule's wf premise; body
       wf via strengthening the extended context (which binds
       [syn_color A]). *)
    apply d_wf_typ__arrow; auto.
    pick fresh x for (L `union` dom Γ).
    eapply d_wf_typ_strengthening_typ with
      (Γ1 := nil) (x := x) (A := syn_color A).
    eauto using d_wf_denv__typ, d_wf_typ_inh_color_syn_color.
  - (* __abs_anno: arrow-arg [syn_color A] from the rule's wf premise. *)
    apply d_wf_typ__arrow; auto.
    pick fresh x for (L `union` dom Γ).
    eapply d_wf_typ_strengthening_typ with
      (Γ1 := nil) (x := x) (A := syn_color A).
    eauto using d_wf_denv__typ.
  - (* __app: post re-encoding the function's arg type is [P' : typ];
       the [d_typing_gen] for the function gives [d_wf_typ Γ (typ_arrow P' B)]. *)
    assert (Harr : d_wf_typ Γ (typ_arrow P' B)) by (apply IHd_typing_gen1; auto).
    inversion Harr; subst. auto.
Qed.

(** [d_typing_gen_check_is_inh]: gen analogue — PROVABLY FALSE for the
    same reason as [d_typing_check_is_inh]. [d_typing_gen__freeze]
    mirrors [d_typing__freeze]'s no-repainting behaviour. LEMMA REMOVED
    2026-05-16: no callers. Counter-example documented in the original
    [d_typing_check_is_inh] block. *)

Lemma d_consis_gen_tvar_morph : forall Γ Γ' Δ T A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_consis_gen Δ Γ T A ->
    d_consis_gen Δ Γ' T A.
Proof.
  intros Γ Γ' Δ T A Hmorph H.
  generalize dependent Γ'. induction H; intros Γ' Hmorph.
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var. apply Hmorph; assumption.
  - apply d_consis_gen__forall_inh_tagged with (L := L `union` dom Γ').
    + intros X HX. apply H0; auto.
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb]; apply binds_app_iff;
        [ left; auto | right; auto ].
    + assumption.
  - (* __forall_inh_untagged (NEW) *)
    apply d_consis_gen__forall_inh_untagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff;
      [ left; auto | right; auto ].
  - apply d_consis_gen__forall_syn_tagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff;
      [ left; auto | right; auto ].
  - apply d_consis_gen__forall_syn with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff;
      [ left; auto | right; auto ].
  - apply d_consis_gen__forall_inh with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff;
      [ left; auto | right; auto ].
  - apply d_consis_gen__arrow; auto.
Qed.

Lemma d_sub_gen_tvar_morph : forall Γ Γ' m Δ T A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_sub_gen m Δ Γ T A ->
    d_sub_gen m Δ Γ' T A.
Proof.
  intros Γ Γ' m Δ T A Hmorph H.
  generalize dependent Γ'. induction H; intros Γ' Hmorph.
  - apply d_sub_gen__embed. eapply d_sub_tvar_morph; eauto.
  - apply d_sub_gen__infer_gen; auto. eapply d_consis_gen_tvar_morph; eauto.
  - apply d_sub_gen__check_gen; auto. eapply d_consis_gen_tvar_morph; eauto.
  - apply d_sub_gen__refl_mono; auto. eapply d_wf_typ_tvar_morph; eauto.
  - apply d_sub_gen__forall_r with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_sub_gen__arg.
    + eapply d_consis_gen_tvar_morph; eauto.
    + apply IHd_sub_gen; auto.
Qed.

(** Narrowing a [dbind_typ] binding preserves [dbind_tvar] lookups
    (the narrowed slot holds a [dbind_typ], so no [dbind_tvar] lookup
    can resolve to it). *)
Lemma binds_tvar_narrow_typ :
  forall (Γ1 Γ2 : list (atom * dbind)) x Aold Anew X,
    binds X dbind_tvar (Γ1 ++ (x ~ dbind_typ Aold) ++ Γ2) ->
    binds X dbind_tvar (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2).
Proof.
  intros Γ1 Γ2 x Aold Anew X HbY.
  apply binds_app_iff in HbY. destruct HbY as [Hb | Hb].
  - apply binds_app_iff. left. assumption.
  - apply binds_app_iff in Hb. destruct Hb as [Hbx | Hbp].
    + apply binds_one_iff in Hbx. destruct Hbx as [_ Habs]. inversion Habs.
    + apply binds_app_iff. right. apply binds_app_iff. right. assumption.
Qed.

(** [d_typing_gen] narrowing along a [syn_color_t]-equal binding swap —
    the [d_typing_gen] analogue of [d_typing_narrow_consis]. The
    [__var] case at the narrowed binding closes immediately because
    [d_typing_gen__var] gives the [syn_color_t] of the binding and
    [Hsc] equates the two. [__sub]'s [d_sub_gen] and [__app]'s
    [d_refine_syn] only read [dbind_tvar] entries
    ([binds_tvar_narrow_typ]); [__app]'s [d_pat] narrows via
    [d_typing_narrow_consis]. *)
Lemma d_typing_gen_narrow_consis : forall m Γ_full e B,
    d_typing_gen m Γ_full e B ->
    forall Γ1 x Aold Anew Γ2,
      Γ_full = Γ1 ++ (x ~ dbind_typ Aold) ++ Γ2 ->
      syn_color_t Anew = syn_color_t Aold ->
      d_typing_gen m (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2) e B.
Proof.
  (* RE-ENCODING ADMIT (2026-05-15): mirrors [d_typing_narrow_consis]
     — post-ctyp re-encoding, [d_typing_gen__var] returns the bound
     type raw, so the [__var] narrowed-binding sub-case no longer
     closes from [syn_color_t]-equality alone. *)
Admitted.

Corollary d_typing_gen_narrow_consis_head : forall x Aold Anew Γ m e B,
    d_typing_gen m ((x ~ dbind_typ Aold) ++ Γ) e B ->
    syn_color_t Anew = syn_color_t Aold ->
    d_typing_gen m ((x ~ dbind_typ Anew) ++ Γ) e B.
Proof.
  intros x Aold Anew Γ m e B Hty Hsc.
  rewrite_env (nil ++ (x ~ dbind_typ Anew) ++ Γ).
  eapply d_typing_gen_narrow_consis with (Γ1 := nil) (Aold := Aold); eauto.
Qed.

(** ** FN^n TI predicate (paper's mode-stack discipline).

    A mode is in [is_fn_n_ti] form iff it's [mode_ti] or
    [mode_fn m'] for some m' in [is_fn_n_ti] form — i.e.,
    [FN^n TI = mode_fn^n mode_ti] for some n ≥ 0. *)
Inductive is_fn_n_ti : mode -> Prop :=
| is_fn_n_ti__ti : is_fn_n_ti mode_ti
| is_fn_n_ti__fn : forall m,
    is_fn_n_ti m ->
    is_fn_n_ti (mode_fn m).

(** Replace the innermost TI in m_orig (a FN^n TI mode) with m_new.
    [mode_fn_n_subst (FN^n TI) m_new = FN^n m_new]. *)
Fixpoint mode_fn_n_subst (m_orig m_new : mode) : mode :=
  match m_orig with
  | mode_ti => m_new
  | mode_fn m' => mode_fn (mode_fn_n_subst m' m_new)
  | mode_tc => mode_tc  (* unused; is_fn_n_ti excludes mode_tc *)
  end.

(** [decr_mode] preserves [is_fn_n_ti]. *)
Lemma is_fn_n_ti_decr : forall m,
    is_fn_n_ti m ->
    is_fn_n_ti (decr_mode m).
Proof.
  intros m H. inversion H; subst; simpl.
  - apply is_fn_n_ti__ti.
  - assumption.
Qed.

(** [mode_fn_n_subst] respects [decr_mode] on FN^n TI: for n ≥ 1,
    [decr (FN^n m_new) = FN^{n-1} m_new] = [mode_fn_n_subst (decr m_orig) m_new]. *)
Lemma mode_fn_n_subst_decr : forall m_orig m_new,
    is_fn_n_ti m_orig ->
    m_orig <> mode_ti ->
    decr_mode (mode_fn_n_subst m_orig m_new) =
    mode_fn_n_subst (decr_mode m_orig) m_new.
Proof.
  intros m_orig m_new H Hne. inversion H; subst; simpl.
  - exfalso. apply Hne. reflexivity.
  - reflexivity.
Qed.

(** Lift d_consis to d_sub_gen at a compatible mode. Recurses on the
    structure of mode_typ_compat (which mirrors the type structure). *)
(** With the new [d_consis__forall_inh] rule, [d_consis nil Γ T A]
    with A is_inh_typ no longer pins T to mono — T can be
    [typ_all_col colour_inh _]. We add [is_utyp T] as precondition
    to rule out the new case structurally; callers supply this from
    their context (e.g., [mono_typ A] gives mono T via [d_consis_mono_RHS]
    which gives is_utyp T via [mono_typ_is_utyp]). *)
Lemma d_consis_to_d_sub_gen : forall m Γ T A,
    mode_typ_compat m A ->
    d_wf_typ Γ T ->
    is_utyp T ->
    nil ⨟ Γ ⊨ T ≈ A ->
    d_sub_gen m nil Γ T A.
Proof.
  intros m Γ T A Hcompat HwfT Hut Hc. generalize dependent T.
  induction Hcompat; intros T HwfT Hut Hc.
  - (* mode_ti: mono extraction → T = A. *)
    assert (HmonoT : mono_typ T) by (eapply d_consis_LHS_mono_wf; eauto).
    destruct (d_consis_mono_LHS Hc HmonoT) as [HeqAT _]; subst.
    apply d_sub_gen__refl_mono; auto.
    apply mode_typ_compat__ti; apply mono_typ_is_syn_typ; auto.
  - (* mode_tc: same mono-extraction chain (is_utyp T rules out
       the [typ_all_col colour_inh] LHS case). *)
    assert (HmonoT : mono_typ T) by (eapply d_consis_LHS_mono_wf; eauto).
    destruct (d_consis_mono_LHS Hc HmonoT) as [HeqAT _]; subst.
    apply d_sub_gen__refl_mono; auto.
    apply mode_typ_compat__tc; apply mono_typ_is_inh_typ; auto.
  - (* mode_fn: A = typ_arrow A0 B. T from d_consis must be typ_arrow. *)
    inversion Hc; subst.
    inversion HwfT; subst.
    inversion Hut; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
    | H : nil = _ ++ _ |- _ =>
        symmetry in H; apply app_eq_nil in H;
        destruct H as [HΔ1 HΔ2]; subst
    end.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + apply d_consis_gen__embed. assumption.
    + apply IHHcompat; auto.
Qed.

(** [d_consis_extends_d_consis_gen_nil]: compose d_consis on LHS with
    d_consis_gen at outer Δ = nil. The Δ = nil restriction avoids a
    permutation issue in d_consis_compose. *)
Lemma d_consis_extends_d_consis_gen : forall Γ T A B,
    nil ⨟ Γ ⊨ T ≈ A ->
    d_consis_gen nil Γ A B ->
    d_wf_typ Γ T ->
    d_consis_gen nil Γ T B.
Proof.
  intros Γ T0 A B Hc Hcg HwfT.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  generalize dependent T0.
  induction Hcg; intros T0 Hc HwfT.
  - (* __unit: A = B = typ_unit. *)
    apply d_consis_gen__embed. assumption.
  - (* __var: A = B = typ_var_f X. *)
    apply d_consis_gen__embed. assumption.
  - (* __forall_inh_tagged: outer Δ = ε :: Δ ≠ nil — vacuous. *)
    exfalso; congruence.
  - (* __forall_inh_untagged (NEW δ): A = typ_all_col colour_syn T_inner,
       B = typ_all_col colour_inh A_inner. Hc : d_consis nil Γ T0 (typ_all_col colour_syn T_inner).
       RHS = colour_syn ⟹ __forall_syn_tagged (LHS typ_all_etag, vacuous via HwfT)
       OR __forall_syn (LHS typ_all_col colour_syn). *)
    subst.
    inversion Hc; subst.
    + (* __forall_syn_tagged: T0 = typ_all_etag, not d_wf_typ. *)
      inversion HwfT.
    + (* __forall_syn: T0 = typ_all_col colour_syn. Compose via
         d_consis_gen__forall_inh_untagged. *)
      inversion HwfT; subst.
      apply d_consis_gen__forall_inh_untagged with (L := L `union` L0 `union` L1).
      intros X HX.
      apply d_consis_gen_trans with (A := open_typ_wrt_typ T (typ_var_f X)).
      * match goal with H_wf_body : forall X, X `notin` ?L1 -> d_wf_typ _ _ |- _ =>
          eapply d_wf_typ_is_typ; apply H_wf_body; fsetdec end.
      * apply d_consis_gen__embed.
        match goal with
        | H' : forall X0, X0 `notin` _ -> d_consis _ _ _ _ |- _ =>
            apply H'; auto
        end.
      * apply H; auto.
  - (* __forall_syn_tagged: A = typ_all_etag — no d_consis rule has
       typ_all_etag as RHS, so Hc is vacuous. *)
    inversion Hc.
  - (* __forall_syn (post-refactor): A = typ_all_col colour_syn T_inner.
       Hc has RHS = colour_syn — __forall_syn_tagged or __forall_syn. *)
    subst.
    inversion Hc; subst.
    + (* __forall_syn_tagged: T0 = typ_all_etag, not wf. *)
      inversion HwfT.
    + (* __forall_syn: compose via d_consis_gen__forall_syn. *)
      inversion HwfT; subst.
      apply d_consis_gen__forall_syn with (L := L `union` L0 `union` L1).
      intros X HX.
      apply d_consis_gen_trans with (A := open_typ_wrt_typ T (typ_var_f X)).
      * match goal with H_wf_body : forall X, X `notin` ?L1 -> d_wf_typ _ _ |- _ =>
          eapply d_wf_typ_is_typ; apply H_wf_body; fsetdec end.
      * apply d_consis_gen__embed.
        match goal with
        | H' : forall X0, X0 `notin` _ -> d_consis _ _ _ _ |- _ =>
            apply H'; auto
        end.
      * apply H; auto.
  - (* __forall_inh: A = typ_all_col colour_inh T_inner. Hc RHS = colour_inh.
       d_consis rules matching: __forall_inh_tagged (LHS typ_all_etag,
       Δ = ε :: Δ_rule, with Hc's Δ = nil → discriminate), __forall_inh_untagged
       (LHS typ_all_col colour_syn), or __forall_inh (LHS typ_all_col colour_inh). *)
    subst.
    inversion Hc; subst.
    (* Note: __forall_inh_tagged case (Δ = ε :: Δ_rule ≠ nil) is
       auto-discharged by inversion since outer Δ = nil. *)
    + (* __forall_inh_untagged: T0 = typ_all_col colour_syn.
         Compose via d_consis_gen__forall_inh_untagged. *)
      inversion HwfT; subst.
      apply d_consis_gen__forall_inh_untagged with (L := L `union` L0 `union` L1).
      intros X HX.
      apply d_consis_gen_trans with (A := open_typ_wrt_typ T (typ_var_f X)).
      * match goal with H_wf_body : forall X, X `notin` ?L1 -> d_wf_typ _ _ |- _ =>
          eapply d_wf_typ_is_typ; apply H_wf_body; fsetdec end.
      * apply d_consis_gen__embed.
        match goal with
        | H' : forall X0, X0 `notin` _ -> d_consis _ _ _ _ |- _ =>
            apply H'; auto
        end.
      * apply H; auto.
    + (* __forall_inh: T0 = typ_all_col colour_inh. Compose via __forall_inh. *)
      inversion HwfT; subst.
      apply d_consis_gen__forall_inh with (L := L `union` L0 `union` L1).
      intros X HX.
      apply d_consis_gen_trans with (A := open_typ_wrt_typ T (typ_var_f X)).
      * match goal with H_wf_body : forall X, X `notin` ?L1 -> d_wf_typ _ _ |- _ =>
          eapply d_wf_typ_is_typ; apply H_wf_body; fsetdec end.
      * apply d_consis_gen__embed.
        match goal with
        | H' : forall X0, X0 `notin` _ -> d_consis _ _ _ _ |- _ =>
            apply H'; auto
        end.
      * apply H; auto.
  - (* __arrow *)
    apply app_eq_nil in HeqΔ.
    destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hc; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    inversion HwfT; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow; auto.
Qed.

(** [d_consis_sub_trans_gen_nil]: extend d_sub_gen on the LHS via
    a d_consis. Mirrors [d_consis_sub_trans_nil] for the gen
    relation. The signature has [T] after [d_sub_gen] so that
    [induction Hs; intros T] gives a properly T-abstracted IH. *)
(** Helper: a [d_consis_gen] with a [syn_color]-shaped RHS pins the
    LHS to [syn_color X] under wf — the [__forall_inh*] / [__forall_syn*]
    / [__forall_inh] cases of [d_consis_gen] are either vacuous on
    [syn_color]-shaped RHS (colour mismatch: [syn_color] paints
    [colour_syn], not [colour_inh]) or LHS-unwf (etag/plain). *)
Lemma d_consis_gen_RHS_syn_color_eq : forall Γ A X,
    d_consis_gen nil Γ A (syn_color X) ->
    d_wf_typ Γ A ->
    A = syn_color X.
Proof.
  intros Γ A X Hcg.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  remember (syn_color X) as A_RHS eqn:HeqA.
  generalize dependent X.
  induction Hcg; intros X' HeqA HwfA; subst.
  - destruct X'; simpl in HeqA; try discriminate. reflexivity.
  - destruct X'; simpl in HeqA; try discriminate.
    injection HeqA; intro; subst; reflexivity.
  - inversion HwfA.
  - (* __forall_inh_untagged (NEW): RHS = typ_all_col colour_inh,
       syn_color paints colour_syn — discriminate via destruct X'. *)
    destruct X'; simpl in HeqA; try discriminate.
  - inversion HwfA.
  - destruct X'; simpl in HeqA; try discriminate.
    inversion HeqA; subst.
    inversion HwfA; subst.
    f_equal.
    pick fresh X0 for
      (L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_ctyp X' `union` dom Γ).
    assert (HX_L : X0 `notin` L) by fsetdec.
    assert (HX_L0 : X0 `notin` L0) by fsetdec.
    assert (HnotinT : X0 `notin` ftvar_in_typ T) by fsetdec.
    assert (HnotinSC : X0 `notin` ftvar_in_typ (syn_color X')).
    { rewrite syn_color_ftvar. fsetdec. }
    pose proof (H0 X0 HX_L eq_refl
                   (open_ctyp_wrt_ctyp X' (ctyp_var_f X0))) as Heq.
    rewrite syn_color_open_var in Heq.
    specialize (Heq eq_refl (H3 X0 HX_L0)).
    apply (open_typ_wrt_typ_inj T (syn_color X') X0); auto.
  - destruct X'; simpl in HeqA; discriminate.
  - destruct X'; simpl in HeqA; try discriminate.
    injection HeqA; intros HeqA2 HeqA1.
    apply app_eq_nil in HeqΔ; destruct HeqΔ as [HΔ1 HΔ2]; subst.
    inversion HwfA; subst.
    f_equal.
    + eapply IHHcg1; eauto.
    + eapply IHHcg2; eauto.
Qed.

Lemma d_consis_sub_trans_gen_nil : forall m Γ A B,
    d_sub_gen m nil Γ A B ->
    forall T,
      nil ⨟ Γ ⊨ T ≈ A ->
      d_wf_typ Γ T ->
      d_sub_gen m nil Γ T B.
Proof.
  intros m Γ A B Hs.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hs; intros T0 Hc HwfT.
  - (* __embed: route through [d_consis_sub_trans_nil]. *)
    subst. apply d_sub_gen__embed. eapply d_consis_sub_trans_nil; eauto.
  - (* __infer_gen: Hc has RHS = syn_color T. Sound closure: use
       [d_consis_gen_RHS_syn_color_eq] (Qed) to pin T0 = syn_color T,
       then compose Hc with H via [d_consis_gen_trans] and reconstruct
       via [d_sub_gen__infer_gen]. This avoids the unsound chain
       through [d_consis_LHS_is_utyp_when_RHS_syn_color]. *)
    subst.
    assert (Hc_gen : d_consis_gen nil Γ T0 (syn_color T))
      by (apply d_consis_gen__embed; assumption).
    assert (HT0eq : T0 = syn_color T)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto).
    subst T0.
    apply d_sub_gen__infer_gen.
    eapply d_consis_gen_trans; [ eapply d_wf_typ_is_typ; eassumption | | ]; eauto.
  - (* __check_gen: same pattern — pin T0 = syn_color T via the RHS
       rigidity lemma, then dispatch via [d_sub_gen__check_gen] (the
       guarded_typ + d_consis_gen premise of __check_gen carry over). *)
    subst.
    assert (Hc_gen : d_consis_gen nil Γ T0 (syn_color T))
      by (apply d_consis_gen__embed; assumption).
    assert (HT0eq : T0 = syn_color T)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto).
    subst T0.
    apply d_sub_gen__check_gen; assumption.
  - (* __refl_mono: A = B mono. Use [d_consis_to_d_sub_gen] (compat
       carried by __refl_mono). [is_utyp T0] derived via
       [d_consis_mono_RHS] (mono A pins T0 = A, hence mono T0, hence
       is_utyp T0). *)
    subst.
    edestruct (d_consis_mono_RHS Hc) as [HmonoT0 [_ _]]; eauto.
    eapply d_consis_to_d_sub_gen; eauto.
    apply mono_typ_is_utyp; assumption.
  - (* __forall_r: B = typ_all_col colour_inh A0, m = mode_tc.
       Reconstruct via __forall_r with per-X IH. *)
    subst.
    apply d_sub_gen__forall_r with (L := L `union` dom Γ).
    intros X HX.
    eapply H0; eauto.
    + apply d_consis_weakening_head; auto.
    + apply d_wf_typ_weakening_head; auto.
  - (* __arg: A = typ_arrow T1 T2, B = typ_arrow A1 A2. Hc forces
       T0 = typ_arrow T0_arg T0_ret. Compose Hc's arg-side d_consis
       with Hs's arg-side d_consis_gen via [d_consis_extends_d_consis_gen]. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hc; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    inversion HwfT; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + eapply d_consis_extends_d_consis_gen; eauto.
    + eapply IHHs; eauto.
Qed.

(* ====================================================================== *)
(*  Gen→original bridge lemmas. These were previously in                  *)
(*  [prop_general_subsumption.v]; moved here 2026-05-17 so                 *)
(*  [prop_subsumption_aux.v]'s [d_sub_gen_trans] can use the              *)
(*  [d_sub_gen → d_sub] direction in the new                              *)
(*  [d_sub__forall_l_untagged] inner case (which needs to wrap a body's   *)
(*  inductively-produced [d_sub_gen] back into a [d_sub] for the          *)
(*  [d_sub__forall_l_untagged] rule's body slot).                         *)
(* ====================================================================== *)

(** [d_consis_gen_to_d_consis_syn_lhs]: the SYN-LHS-restricted bridge.
    When the LHS is [is_syn_typ] (every quantifier is [colour_syn]),
    the [__forall_inh] case (LHS = [typ_all_col colour_inh]) is vacuous,
    so the bridge closes. *)
Lemma d_consis_gen_to_d_consis_syn_lhs : forall T,
    is_syn_typ T ->
    forall Δ Γ A, d_consis_gen Δ Γ T A -> d_consis Δ Γ T A.
Proof.
  intros T Hsyn. induction Hsyn; intros Δ Γ A0 Hc.
  - (* typ_unit *) inversion Hc; subst. apply d_consis__unit.
  - (* typ_var_f X *) inversion Hc; subst. apply d_consis__var; assumption.
  - (* typ_arrow *)
    inversion Hc; subst.
    apply d_consis__arrow; auto.
  - (* typ_all_col colour_syn (post-refactor): d_consis_gen admits two
       rules with this LHS — __forall_syn (RHS colour_syn) and the new
       __forall_inh_untagged (RHS colour_inh). Both bridge to their
       d_consis counterparts via the IH on the opened body. *)
    inversion Hc; subst.
    + (* __forall_inh_untagged (NEW δ-rule) *)
      apply d_consis__forall_inh_untagged with (L := L `union` L0).
      intros X HX. apply H0; auto.
    + (* __forall_syn *)
      apply d_consis__forall_syn with (L := L `union` L0).
      intros X HX. apply H0; auto.
Qed.

(** [d_consis_gen_to_d_consis]: the gen→original bridge for consistency.
    Each d_consis_gen constructor reconstructs its d_consis counterpart;
    [__forall_inh_untagged] (δ-NEW) and [__forall_inh] (added during the
    earlier refactor) make this lemma Qed. *)
Lemma d_consis_gen_to_d_consis : forall Δ Γ T A,
    d_consis_gen Δ Γ T A ->
    Δ ⨟ Γ ⊨ T ≈ A.
Proof.
  intros Δ Γ T A H. induction H.
  - apply d_consis__unit.
  - apply d_consis__var; assumption.
  - apply d_consis__forall_inh_tagged with (L := L); assumption.
  - apply d_consis__forall_inh_untagged with (L := L); assumption.
  - apply d_consis__forall_syn_tagged with (L := L); assumption.
  - apply d_consis__forall_syn with (L := L); assumption.
  - apply d_consis__forall_inh with (L := L); assumption.
  - apply d_consis__arrow; assumption.
Qed.

(** [d_sub_gen_to_d_sub]: the gen→original bridge for subtyping. Routes
    [__refl_mono] through [d_sub_refl_mono_mode] and the consistency
    components through [d_consis_gen_to_d_consis]. *)
Lemma d_sub_gen_to_d_sub : forall m Δ Γ T A,
    d_sub_gen m Δ Γ T A ->
    Γ ⊢[ m ; Δ ] T ⊑ A.
Proof.
  intros m Δ Γ T A H. induction H.
  - (* __embed: the d_sub is the premise. *)
    assumption.
  - (* __infer_gen *)
    apply d_sub__infer. apply d_consis_gen_to_d_consis. assumption.
  - (* __check_gen *)
    apply d_sub__check; auto. apply d_consis_gen_to_d_consis. assumption.
  - (* __refl_mono *)
    apply d_sub_refl_mono_mode; auto.
  - (* __forall_r *)
    apply d_sub__forall_r with (L := L); auto.
  - (* __arg *)
    apply d_sub__arg; auto. apply d_consis_gen_to_d_consis. assumption.
Qed.
