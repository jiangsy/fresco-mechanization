(** Frost — algorithmic system soundness vs. declarative (Phase 3.B).

    Paper reference: [paper/sections/proofs.tex] §"Type Inference".

    For each algorithmic judgment from Phase 3.A we state and prove
    that it implies its declarative counterpart on the "transferred"
    output context.  The transfer meta-function [a_transfers] erases
    the flex-mono / flex-poly machinery from an [aenv] to obtain a
    [denv].

    The bulk of these soundness proofs are research-grade in scale
    (each algorithmic rule has a declarative analogue that requires
    threading information-increase + the corresponding declarative
    weakening / stability lemma from Phase 2.{B,C,D,E}).  We state
    the headline theorems and admit the proofs with case-by-case
    rationales pointing to the missing upstream ingredients; the
    declarative lemmas that *are* available (Phase 2 exports) are
    cited inline. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.notations.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.prop_typing.
Require Import src.frost.decl.prop_skeleton.

Set Implicit Arguments.


(* ===================================================================== *)
(*  Transfer: aenv → denv (as a relation).                                *)
(* ===================================================================== *)

(** [a_transfers Θ Γ] — paper's transfer meta-function from algorithmic
    contexts to declarative contexts.  It is *partial* on aenvs whose
    flex-mono entries are still undeclared ([abind_flex_mono] with no
    definition), so we encode it as an inductive relation rather than a
    [Fixpoint].

    Cases:
    - rigid type variable     [α]        ↦  [α : dbind_tvar]
    - term binding            [x : A]    ↦  [x : dbind_typ A]
    - flex-mono definition    [α̂ ≜ τ]   ↦  *erased* (the entry is
                                            existentially closed by τ;
                                            the paper transfer replaces
                                            uses of [α̂] by [τ], so the
                                            entry itself disappears)
    - flex-poly definition    [α̌ ≜ P]   ↦  *erased* (similar; treated
                                            via the witness [P])
    - marker [⊳]                          ↦  erased
    - bare flex-mono (no def)             — no transfer exists.

    This is the "identity-metasubstitution" simplification of the
    paper's transfer: we *do not* perform the substitution into [Γ]
    here; we leave that to a separate substitution-respect lemma.
    Stating it this way keeps stability lemmas closer to their paper
    formulation. *)

Inductive a_transfers : aenv -> denv -> Prop :=
| a_transfers__nil :
    a_transfers nil nil
| a_transfers__tvar : forall a Θ Γ,
    a_transfers Θ Γ ->
    a_transfers ((a ~ abind_tvar) ++ Θ) ((a ~ dbind_tvar) ++ Γ)
| a_transfers__var_typ : forall a A Θ Γ,
    a_transfers Θ Γ ->
    a_transfers ((a ~ abind_var_typ A) ++ Θ) ((a ~ dbind_typ A) ++ Γ)
| a_transfers__flex_mono_def : forall a τ Θ Γ,
    a_transfers Θ Γ ->
    a_transfers ((a ~ abind_flex_mono_def τ) ++ Θ) Γ
| a_transfers__flex_poly_def : forall a P Θ Γ,
    a_transfers Θ Γ ->
    a_transfers ((a ~ abind_flex_poly_def P) ++ Θ) Γ
| a_transfers__marker : forall a Θ Γ,
    a_transfers Θ Γ ->
    a_transfers ((a ~ abind_marker) ++ Θ) Γ.

Notation "Θ ⤳ Γ" := (a_transfers Θ Γ)
  (at level 75, no associativity) : type_scope.

(** Basic functional properties. *)

Lemma a_transfers_deterministic : forall Θ Γ1 Γ2,
    a_transfers Θ Γ1 ->
    a_transfers Θ Γ2 ->
    Γ1 = Γ2.
Proof.
  intros Θ Γ1 Γ2 H1. revert Γ2.
  induction H1; intros Γ2 H2; inversion H2; subst; auto;
    try (f_equal; auto).
Qed.

Lemma a_transfers_nil_inv : forall Γ,
    a_transfers nil Γ -> Γ = nil.
Proof. intros Γ H; inversion H; reflexivity. Qed.

(** Transfer factors through list concatenation. *)
Lemma a_transfers_app : forall Ξ Θ Γ,
    a_transfers (Ξ ++ Θ) Γ ->
    exists ΓΞ ΓΘ, Γ = ΓΞ ++ ΓΘ /\ a_transfers Ξ ΓΞ /\ a_transfers Θ ΓΘ.
Proof.
  intros Ξ. induction Ξ as [|[a b] Ξ' IH]; intros Θ Γ H.
  - simpl in H. exists nil, Γ. simpl. split; auto.
    split; [apply a_transfers__nil | exact H].
  - simpl in H. inversion H; subst.
    + (* abind_tvar *)
      match goal with
      | [Hrest : a_transfers (Ξ' ++ Θ) ?G |- _] =>
          apply IH in Hrest; destruct Hrest as [ΓΞ [ΓΘ [Eq [HΞ HΘ]]]]
      end.
      exists ((a ~ dbind_tvar) ++ ΓΞ), ΓΘ.
      split; [rewrite Eq; simpl; reflexivity|].
      split; [apply a_transfers__tvar; exact HΞ | exact HΘ].
    + (* abind_var_typ *)
      match goal with
      | [Hrest : a_transfers (Ξ' ++ Θ) ?G |- _] =>
          apply IH in Hrest; destruct Hrest as [ΓΞ [ΓΘ [Eq [HΞ HΘ]]]]
      end.
      eexists ((a ~ dbind_typ _) ++ ΓΞ), ΓΘ.
      split; [rewrite Eq; simpl; reflexivity|].
      split; [apply a_transfers__var_typ; exact HΞ | exact HΘ].
    + (* abind_flex_mono_def *)
      match goal with
      | [Hrest : a_transfers (Ξ' ++ Θ) ?G |- _] =>
          apply IH in Hrest; destruct Hrest as [ΓΞ [ΓΘ [Eq [HΞ HΘ]]]]
      end.
      exists ΓΞ, ΓΘ.
      split; [exact Eq|].
      split; [apply a_transfers__flex_mono_def; exact HΞ | exact HΘ].
    + (* abind_flex_poly_def *)
      match goal with
      | [Hrest : a_transfers (Ξ' ++ Θ) ?G |- _] =>
          apply IH in Hrest; destruct Hrest as [ΓΞ [ΓΘ [Eq [HΞ HΘ]]]]
      end.
      exists ΓΞ, ΓΘ.
      split; [exact Eq|].
      split; [apply a_transfers__flex_poly_def; exact HΞ | exact HΘ].
    + (* abind_marker *)
      match goal with
      | [Hrest : a_transfers (Ξ' ++ Θ) ?G |- _] =>
          apply IH in Hrest; destruct Hrest as [ΓΞ [ΓΘ [Eq [HΞ HΘ]]]]
      end.
      exists ΓΞ, ΓΘ.
      split; [exact Eq|].
      split; [apply a_transfers__marker; exact HΞ | exact HΘ].
Qed.

(** A suffix Ξ all of whose flex-mono entries are *defined* transfers
    to nil: every entry in [a_suffix_binding] is either erased
    ([flex_mono_def] / [flex_poly_def] / [flex_mono] — but the latter
    has no transfer rule, so we'd have to assume that case absent). *)
Lemma a_transfers_suffix_inv : forall Ξ Γ,
    a_suffix Ξ ->
    a_transfers Ξ Γ ->
    Γ = nil.
Proof.
  intros Ξ Γ Hsuf. revert Γ.
  induction Hsuf; intros Γ Htr.
  - inversion Htr; reflexivity.
  - inversion H; subst.
    + (* abind_flex_mono: no transfer rule for bare flex_mono.
         Inversion of Htr on the consed entry yields no constructor. *)
      inversion Htr.
    + (* abind_flex_mono_def *)
      inversion Htr; subst. eapply IHHsuf; eauto.
    + (* abind_flex_poly_def *)
      inversion Htr; subst. eapply IHHsuf; eauto.
Qed.


(* ===================================================================== *)
(*  Stability of declarative judgments under information-increase.        *)
(* ===================================================================== *)

(** Paper's "stability" lemma family (proofs.tex §1): every declarative
    judgment that holds in the source context's transfer also holds in
    the target context's transfer, when [Θ₀ ⊑ Θ₁].

    For the identity-metasubstitution variant of [aenv_extends] (the
    only one we mechanise), each flex-mono / flex-poly variable in
    [Θ₀] is preserved in [Θ₁] (its sort may strengthen from
    declaration to definition).  Erasing flex-variables to obtain the
    declarative context [Γᵢ = transfer Θᵢ] then yields *Γ₀ ⊆ Γ₁* up
    to permutation of weakening entries (insertions of fresh
    rigid/term/marker bindings) — and Phase 2.{B,C,D,E} all furnish
    weakening lemmas.

    We expose the stability lemmas individually so downstream
    soundness proofs can call them without re-deriving the weakening
    skeleton.  Each is admitted with the rationale "follows by
    induction on [Θ₀ ⊑ Θ₁]; uses the Phase 2.X weakening lemma".
*)

Lemma stability_d_wf_typ : forall Θ0 Θ1 Γ0 Γ1 A,
    aenv_extends Θ0 Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_wf_typ Γ0 A ->
    d_wf_typ Γ1 A.
Proof.
  intros Θ0 Θ1 Γ0 Γ1 A Hext. revert Γ0 Γ1 A.
  induction Hext; intros Γ0 Γ1 A Htr0 Htr1 Hwf.
  - (* aenv_extends__empty: Θ0 = nil, Θ1 = Ξ. *)
    apply a_transfers_nil_inv in Htr0. subst Γ0.
    pose proof (a_transfers_suffix_inv H Htr1) as Eq. subst Γ1.
    exact Hwf.
  - (* flex_mono_keep: bare flex_mono has no transfer rule. *)
    inversion Htr0.
  - (* flex_mono_solve: source has bare flex_mono, no transfer rule. *)
    inversion Htr0.
  - (* flex_mono_def: both sides erase. *)
    inversion Htr0; subst. inversion Htr1; subst.
    eapply IHHext; eauto.
  - (* flex_poly_def: source erases; target's prefix Ξ also erases,
       then the flex_poly_def erases. *)
    inversion Htr0; subst.
    apply a_transfers_app in Htr1.
    destruct Htr1 as [ΓΞ [ΓΘ' [Eq [HΞ HΘ']]]].
    pose proof (a_transfers_suffix_inv H HΞ) as EqΞ. subst ΓΞ. simpl in Eq.
    subst Γ1.
    inversion HΘ'; subst.
    eapply IHHext; eauto.
  - (* var_typ: source ↦ (a, dbind_typ P) :: Γ0'; target ↦ Ξ-prefix +
       (a, dbind_typ P) :: Γ1'.  The Ξ-prefix erases by suffix_inv. *)
    inversion Htr0; subst.
    apply a_transfers_app in Htr1.
    destruct Htr1 as [ΓΞ [ΓΘ' [Eq [HΞ HΘ']]]].
    pose proof (a_transfers_suffix_inv H HΞ) as EqΞ. subst ΓΞ. simpl in Eq.
    subst Γ1.
    inversion HΘ'; subst.
    rewrite_env (nil ++ (a ~ dbind_typ P) ++ Γ) in Hwf.
    apply d_wf_typ_strengthening_typ in Hwf. simpl in Hwf.
    apply d_wf_typ_weakening_head with (Γ := Γ0) (Γ' := a ~ dbind_typ P).
    eapply IHHext; eauto.
  - (* tvar: rigid type variable; transfer keeps it on both sides. *)
    inversion Htr0; subst.
    apply a_transfers_app in Htr1.
    destruct Htr1 as [ΓΞ [ΓΘ' [Eq [HΞ HΘ']]]].
    pose proof (a_transfers_suffix_inv H HΞ) as EqΞ. subst ΓΞ. simpl in Eq.
    subst Γ1.
    inversion HΘ'; subst.
    rewrite_env ((a ~ dbind_tvar) ++ Γ) in Hwf.
    rewrite_env ((a ~ dbind_tvar) ++ Γ0).
    eapply d_wf_typ_tvar_morph; [|exact Hwf].
    intros Y HbY. apply binds_app_iff in HbY.
    apply binds_app_iff. destruct HbY as [Hin | Hin].
    + left. exact Hin.
    + right.
      assert (Hwf_var : d_wf_typ Γ (typ_var_f Y)) by (apply d_wf_typ__var; auto).
      apply IHHext with (Γ1 := Γ0) in Hwf_var; auto.
      inversion Hwf_var; subst; auto.
  - (* marker: erases on both sides. *)
    inversion Htr0; subst.
    apply a_transfers_app in Htr1.
    destruct Htr1 as [ΓΞ [ΓΘ' [Eq [HΞ HΘ']]]].
    pose proof (a_transfers_suffix_inv H HΞ) as EqΞ. subst ΓΞ. simpl in Eq.
    subst Γ1.
    inversion HΘ'; subst.
    eapply IHHext; eauto.
Qed.

Lemma stability_d_consis : forall Θ0 Θ1 Γ0 Γ1 Δ T A,
    aenv_extends Θ0 Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_consis Δ Γ0 T A ->
    d_consis Δ Γ1 T A.
Proof.
  (* Admitted: by induction on [Θ0 ⊑ Θ1]; uses [d_consis_weakening]
     from prop_subtyping.v.  Same shape as [stability_d_wf_typ]. *)
Admitted.

Lemma stability_d_sub : forall Θ0 Θ1 Γ0 Γ1 m Δ A B,
    aenv_extends Θ0 Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_sub m Δ Γ0 A B ->
    d_sub m Δ Γ1 A B.
Proof.
  (* Admitted: by induction on [Θ0 ⊑ Θ1]; uses [d_sub_weakening]
     from prop_typing.v. *)
Admitted.

Lemma stability_d_pat_consis : forall Θ0 Θ1 Γ0 Γ1 Δ S P,
    aenv_extends Θ0 Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_pat_consis Δ Γ0 S P ->
    d_pat_consis Δ Γ1 S P.
Proof.
  (* Admitted: by induction on [Θ0 ⊑ Θ1]; uses
     [d_pat_consis_weakening] from prop_typing.v. *)
Admitted.

Lemma stability_d_pat_sub : forall Θ0 Θ1 Γ0 Γ1 m Δ S P,
    aenv_extends Θ0 Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_pat_sub m Δ Γ0 S P ->
    d_pat_sub m Δ Γ1 S P.
Proof.
  (* Admitted: by induction on [Θ0 ⊑ Θ1]; uses
     [d_pat_sub_weakening] from prop_typing.v. *)
Admitted.

Lemma stability_d_refine : forall Θ0 Θ1 Γ0 Γ1 Ψ P Q,
    aenv_extends Θ0 Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_refine Ψ Γ0 P Q ->
    d_refine Ψ Γ1 P Q.
Proof.
  (* Admitted: by induction on [Θ0 ⊑ Θ1]; uses a Phase 2.B
     [d_refine_weakening]-style lemma (not currently exported; would
     be one of d_wf_skel_psi_*-flavoured helpers). *)
Admitted.

Lemma stability_d_refine_syn : forall Θ0 Θ1 Γ0 Γ1 Ψ P Q,
    aenv_extends Θ0 Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_refine_syn Ψ Γ0 P Q ->
    d_refine_syn Ψ Γ1 P Q.
Proof.
  (* Admitted: by induction on [Θ0 ⊑ Θ1]; same shape as
     [stability_d_refine]. *)
Admitted.

Lemma stability_d_typing : forall Θ0 Θ1 Γ0 Γ1 m e A,
    aenv_extends Θ0 Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_typing m Γ0 e A ->
    d_typing m Γ1 e A.
Proof.
  (* Admitted: by induction on [Θ0 ⊑ Θ1]; uses [d_typing_weakening]
     from prop_typing.v.  Phase 2.D weakening covers this directly. *)
Admitted.

Lemma stability_d_pat : forall Θ0 Θ1 Γ0 Γ1 m e P,
    aenv_extends Θ0 Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_pat m Γ0 e P ->
    d_pat m Γ1 e P.
Proof.
  (* Admitted: by induction on [Θ0 ⊑ Θ1]; uses [d_pat_weakening]
     from prop_typing.v. *)
Admitted.


(* ===================================================================== *)
(*  Soundness of algorithmic subtyping.                                   *)
(* ===================================================================== *)

(** [a_sub_sound]: if [Θ₀ ⊢ T ⊑ A ⊣ Θ₁] holds algorithmically and the
    two contexts both transfer to declarative contexts [Γ₀], [Γ₁],
    then the declarative subtyping [Γ₁ ⊢ T ⊑ A] holds in mode TC with
    no tag context (the algorithmic system tracks the tag context
    inside [Θ]; the transferred declarative form uses an empty Δ).

    By induction on [a_sub].  Each constructor case unfolds to a
    [a_broom] derivation; the structural rules (arrow, ∀-right, …)
    mirror the declarative [d_sub] constructors directly, the
    flex-mono/flex-poly cases reduce to applying the corresponding
    declarative substitution lemma after a transfer round-trip. *)

Theorem a_sub_sound : forall NM m P0 Θ0 T A Θ1 Γ0 Γ1,
    a_sub NM m P0 Θ0 T A Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_sub m nil Γ1 T A.
Proof.
  (* Admitted: research-grade.  Skeleton of the proof:

     - By induction on [a_sub NM m P0 Θ0 T A Θ1].
     - Each of the 2 [a_sub] constructors triggers a [a_broom]
       sub-induction.  The [a_broom] constructors are:
         * [infer] / [check]  → match [d_sub__infer] / [d_sub__check]
                                via [a_consis_sound] (not yet built).
         * [arg]              → match [d_sub__arg]; uses unification
                                soundness for the argument leg.
         * [forall_l]         → match [d_sub__forall_l_*] via
                                [a_assign]-based instantiation
                                witnesses; this is the case that needs
                                the deepest auxiliary lemmas
                                (paper proofs.tex Lemma "instantiation
                                ranges over the right shape").
         * [forall_r] / [univ_ghost_r] / [univ_ghost_l] / [ghost]
                              → match the corresponding [d_sub] rule
                                or are absorbed by [stability_d_sub].
         * [flex_mono] / [flex_poly]
                              → require a substitution-respect lemma
                                from Phase 3.A (not yet exported)
                                relating [a_unify_var] / [a_assign] to
                                an existential witness in [d_sub].
     - The outer [a_sub] rule consumes a [a_guess_mono_suffix] and a
       [a_meta_subst]; both translate to an [open_typ_wrt_typ]-style
       composition on the declarative side.

     The auxiliary lemmas required but not currently mechanised:

       (i)   [a_consis_sound]  — consistency soundness;
       (ii)  [a_unify_sound]   — unification soundness;
       (iii) [a_assign_sound]  — flex-mono / flex-poly assignment;
       (iv)  [a_pre_sub_sound] — pre-subtyping erases to ≤ on shapes.

     Each is on the order of one auxiliary file's worth of work.  The
     full proof tree mirrors paper proofs.tex §Type Inference Lemma
     "Subtyping is sound". *)
Admitted.


(* ===================================================================== *)
(*  Soundness of algorithmic skeleton inference + typing (mutual).        *)
(* ===================================================================== *)

(** [a_pat_sound] / [a_typing_sound] are genuinely mutual due to the
    App rule, which threads the function-side typing through a
    skeleton-side argument inference.  We state both then admit the
    mutual proof with a single shared rationale block. *)

Theorem a_pat_sound : forall m Θ0 P0 e P Θ1 Γ0 Γ1,
    a_pat m Θ0 P0 e P Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_pat m Γ1 e P.
Proof.
  (* Admitted: research-grade.  See [a_typing_sound] for the joint
     skeleton.  Specifically [a_pat]'s cases:

     - [unit] / [var] / [anno] / [freeze]
                                       → mirror [d_pat__*] directly
                                         after [a_sub_sound] dispatch
                                         on the pat-mode variant.
     - [abs_check] / [abs_anno_check]  → mirror [d_pat__abs_check] /
                                         [d_pat__abs_anno_check]; these
                                         are the same shapes that
                                         carry Phase 2.B "tophole hole"
                                         tensions, see PROGRESS.md
                                         §"Paper-level tensions".
     - [abs] / [abs_anno]              → mirror [d_pat__abs] /
                                         [d_pat__abs_anno]; consume
                                         [a_split] (which we'd erase
                                         to an identity on the
                                         non-flex case; the flex-mono
                                         case introduces fresh
                                         declarative variables via the
                                         transfer of the new context).
     - [app]                           → cross-references [a_typing]
                                         soundness; closed by mutual
                                         IH. *)
Admitted.

Theorem a_typing_sound : forall m Θ0 P0 e A Θ1 Γ0 Γ1,
    a_typing m Θ0 P0 e A Θ1 ->
    a_transfers Θ0 Γ0 ->
    a_transfers Θ1 Γ1 ->
    d_typing m Γ1 e A.
Proof.
  (* Admitted: research-grade.  Joint mutual induction with
     [a_pat_sound] using a [Scheme a_typing_pat_mut] (not yet
     generated; would mirror [d_typing_pat_mut] from prop_basic.v).

     Cases of [a_typing] map to [d_typing] cases:

     - [unit]                          → [d_typing__unit] then
                                         [d_typing__sub] for the
                                         subtyping leg.
     - [var]                           → [d_typing__var] then
                                         [d_typing__sub]; requires
                                         that the transfer of [Θ]
                                         preserves the [binds] of x
                                         (true by construction of
                                         [a_transfers__var_typ]).
     - [anno]                          → [d_typing__anno] then sub.
     - [freeze]                        → [d_typing__freeze].
     - [abs_check] / [forall_check] /
       [abs_anno_check]                → [d_typing__abs] /
                                         [d_typing__forall] /
                                         [d_typing__abs_anno] in TC
                                         mode.
     - [abs] / [abs_anno]              → same in TI / fn-mode after
                                         the [a_split] erasure.
     - [app]                           → [d_typing__app]; cross-
                                         references [a_pat_sound] for
                                         the argument skeleton.

     Aside from the missing soundness of [a_consis] / [a_unify] /
     [a_assign] (cf. [a_sub_sound] above), the typing-side proof
     needs:

       (a) [a_split_sound]: under [a_transfers Θ0 Γ0] /
           [a_transfers Θ1 Γ1], [a_split Θ0 P0 P Q Θ1] implies P0 is
           an arrow shape modulo the introduced flex-monos; on the
           declarative side this is a no-op (P0 is preserved verbatim
           or hidden behind a new fresh tvar);
       (b) [a_guess_mono_sound]: the meta-output of [a_guess_mono] is
           well-formed after transfer.

     Each of (a) and (b) is one short lemma's work but blocked on the
     unification-soundness chain above. *)
Admitted.


(* ===================================================================== *)
(*  Sanity check.                                                         *)
(* ===================================================================== *)

(** Smoke test: the transfer relation typechecks on [nil] both ways. *)
Lemma a_transfers_nil_smoke : a_transfers nil nil.
Proof. apply a_transfers__nil. Qed.
