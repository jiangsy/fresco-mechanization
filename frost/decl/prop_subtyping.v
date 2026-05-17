(** Frost — declarative subtyping metatheory (Phase 2.C).

    Umbrella file: re-exports the split modules under [prop_subtyping/]
    and defines [d_typing_sub_compose], the only top-level lemma that
    must live here (its callers in [prop_typing.v] expect
    [Require Import src.frost.decl.prop_subtyping] to bring it into
    scope). *)

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

Require Export src.frost.decl.subtyping.prop_basics.
Require Export src.frost.decl.subtyping.prop_consis_trans.
Require Export src.frost.decl.subtyping.prop_consis_sub_trans.
Require Export src.frost.decl.subtyping.prop_sub_sound.

Set Implicit Arguments.

(** * Composing the [d_typing__sub] step with an outer subsumption.

    This is the helper that extends paper Lemma 3.1 (general subsumption,
    [d_typing_general_subsumption] in [prop_typing.v]) to its [__sub]
    case at mode_ti. Lives here (not in prop_typing.v) because it
    routes through [d_consis_sub_trans] which lives in the
    [consis_extends] split above. *)
Lemma d_typing_sub_compose : forall Γ e A_prev A B m,
    is_base_term e ->
    Γ ⊢[ mode_ti ] e ⇒ A_prev ->
    Γ ⊢[ mode_ti ; nil ] A_prev ⊑ A ->
    Γ ⊢[ m ; nil ] A ⊑ B ->
    d_wf_denv Γ ->
    Γ ⊢[ m ] e ⇒ B.
Proof.
  intros Γ e A_prev A B m Hbase Hty_inner Hsub_inner Hsub Hwfdenv.
  (* Invert the [mode_ti] [d_sub]: only [__infer] survives (the
     [__forall_l_*] cases carry [mode_ti <> mode_ti]); it pins
     [A_prev] / [A] to [syn_color] paintings of [ctyp] bases. *)
  inversion Hsub_inner; subst;
    try (match goal with H : ?m0 <> ?m0 |- _ => exfalso; apply H; reflexivity end).
  match goal with
  | Hconsis : d_consis nil Γ (syn_color ?Tin) (syn_color ?Ain) |- _ =>
      (* [d_consis_sub_trans] requires [d_wf_typ Γ (syn_color Tin)];
         derive it via [d_typing_pat_preserves_wf] on Hty_inner. *)
      assert (Hwf_lhs : d_wf_typ Γ (syn_color Tin))
        by (eapply (proj1 d_typing_pat_preserves_wf); eauto);
      edestruct d_consis_sub_trans as [Δc [Hperm Hsub_composed]];
        [ exact Hconsis | exact Hsub | apply list_disjoint_nil_l
        | intros _; reflexivity
        | exact Hwf_lhs
        | ];
      simpl in Hperm; apply Permutation_sym in Hperm;
      apply Permutation_nil in Hperm; subst Δc;
      apply d_typing__sub with (A := syn_color Tin);
      [ exact Hbase | exact Hty_inner | exact Hsub_composed ]
  end.
Qed.
