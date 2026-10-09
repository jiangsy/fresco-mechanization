(** CONSERVATIVITY: the paper's declarative judgements over an algorithmic
    context Θ, at a FLEXIBLE-FREE Θ, are exactly the declarative judgements
    over the corresponding declarative context Γ.

    ⭐ WHAT THIS IS FOR.  Section D's four theorems are stated against the
    decl-in-algo layer ([ad_pat] / [ad_sd_typing], algo_decl/
    def_typing.v) because that is where the algorithm's output
    context lives.  The CLOSED-PROGRAM corollaries (prop_closed.v) want the
    PURELY declarative system instead — a reader of the paper's §declarative
    figure has never met Θ.  This file is the missing translation.

    ⚠️ [paper-gap] THE PAPER NEVER CONNECTS THE TWO SYSTEMS.
    [app:decl-in-algo-context] (full-algo-spec.tex:97-115) only asserts the
    extension — *"it is easy to extend them to algorithmic contexts Θ … other
    rules simply switch from Γ to Θ"* — and states no conservativity lemma in
    either direction.  What follows is the prose-completion of that sentence;
    docs/PAPER-GAPS.md.

    THE SHAPE.  A [denv] embeds into an [aenv] by [denv_to_aenv] (§0): a
    declarative context IS an algorithmic one with no flexible variables.  Each
    judgement's [ad_] version is then its [d_] version plus the
    flexible-lookup rows, and those rows are VACUOUS in the image — no
    [abind_flex_mono] / [abind_flex_mono_def] is ever produced — so every
    translation is a plain induction whose flex cases are discharged by
    [denv_to_aenv_no_flex_def].

    TWO ASYMMETRIES between the systems that the translations have to absorb:

    - the [ad] layer has ONE consistency and ONE subtyping relation, indexed by
      the sort [N ∈ {TY, SK}], where the declarative system has TWO of each
      ([d_consis] / [d_sub] over [utyp]/[btyp], [d_pat_consis] / [d_pat_sub]
      over [uskl]/[bskl]).  At the TY sort the [ad] subject is the sort
      inclusion [utyp_to_uskl C] of a type, which is GHOST-FREE, so all the
      ghost rows are excluded by their subject and what is left matches the
      type-sorted judgement rule for rule (§4, §8).
    - the ∀-scope context Δ is an [atoms] on both sides, so the two systems
      share it (§0b).

    ⚙ WHY IT LIVES HERE.  It relates the DECLARATIVE system to the
    decl-in-algo one, and [algo_decl/] is where the decl-in-algo layer lives,
    so this is its home.  ⚠️ It was filed under [algo/typing/] when it was
    written, on the theory that needing [btyp_to_bskl_open]
    (algo/pat/prop_soundness_pat.v) and [guarded_pskl_lc]
    (algo/sub/prop_solve_sub.v) would invert the layering.  It does not: the
    DEFINITION layers point one way ([algo/def_*] -> [algo_decl/def_*] and
    [deco_algo/def_*], never back), while the PROOF layers already interleave —
    [deco_algo/prop_soundness_sub.v] reaches into
    [algo/consis/prop_soundness_consis.v], [algo/prop_pat_sub.v],
    [algo/prop_refine.v] and [algo/prop_stability.v].  Moved to the (then
    undivided) decorated-algo layer 2026-08-11, and to [algo_decl/] when that
    layer was split into [algo_decl/] (the `ad_*` decl-in-algo judgements) and
    [deco_algo/] (the paper's `da` decorated-algorithmic system).

    ⚙ NO [Set Implicit Arguments] HERE, deliberately.  Every translation
    threads its context as an EQUATION ([Θ = denv_to_aenv Γ]) so that the
    induction can be on the [ad] derivation, and under the flag the context
    variable would become strictly implicit — making every explicit
    application in this file read one argument out of step. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_general_subsumption.  (* ptyp_to_btyp_inh_mono_syn *)
Require Import src.fresco.decl.prop_wellformed.           (* d_wf_utyp_lc *)
Require Import src.fresco.decl.prop_syntax_directed.       (* ftvar_btyp_to_bskl *)
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.def_typing.
Require Import src.fresco.algo_decl.prop_ctx_mono.   (* aenv_tbinds_le *)
Require Import src.fresco.algo.prop_pat_sub.   (* uskl_ghost_free_open_gen *)
Require Import src.fresco.algo.prop_refine.
Require Import src.fresco.algo.consis.prop_soundness_consis.
Require Import src.fresco.algo.sub.prop_solve_sub.
Require Import src.fresco.algo.sub.prop_soundness_subtag.
Require Import src.fresco.algo.pat.prop_soundness_pat.
Require Import src.fresco.algo.prop_suffix_erase.
Require Import src.fresco.algo.prop_normal.
Require Import src.fresco.algo.prop_basic.

(* ===================================================================== *)
(*  §0  THE CONTEXT EMBEDDING                                             *)
(*                                                                        *)
(*  ⚙ No notation, deliberately — like [ad_pat_sub_v] this is a           *)
(*  mech-internal device, not a paper judgement, and the paper's own       *)
(*  ⌈·⌉ brackets are already taken.                                        *)
(* ===================================================================== *)

Definition abind_of_dbind (d : dbind) : abind :=
  match d with
  | dbind_tvar => abind_tvar
  | dbind_typ A => abind_var_typ A
  | dbind_skl P => abind_var_skl P
  end.

Definition denv_to_aenv (Γ : denv) : aenv :=
  List.map (fun e => (fst e, abind_of_dbind (snd e))) Γ.

Lemma binds_denv_to_aenv : forall x d Γ,
  binds x d Γ -> binds x (abind_of_dbind d) (denv_to_aenv Γ).
Proof.
  intros x d Γ. induction Γ as [ | [y d'] Γ' IH ]; simpl; [ contradiction | ].
  intros [ Heq | Hin ]; [ inversion Heq; subst; left; reflexivity | ].
  right; apply IH; exact Hin.
Qed.

Lemma binds_denv_to_aenv_inv : forall x b Γ,
  binds x b (denv_to_aenv Γ) ->
  exists d, binds x d Γ /\ b = abind_of_dbind d.
Proof.
  intros x b Γ. induction Γ as [ | [y d'] Γ' IH ]; simpl; [ contradiction | ].
  intros [ Heq | Hin ].
  - inversion Heq; subst. exists d'.
    split; [ left; reflexivity | reflexivity ].
  - destruct (IH Hin) as [d [Hb Heq]]. exists d.
    split; [ right; exact Hb | exact Heq ].
Qed.

(** ⭐ THE ONE FACT THAT MAKES EVERY FLEX ROW VACUOUS: the image of a
    declarative context has no flexible variables at all. *)
Lemma denv_to_aenv_no_flex_def : forall α τ Γ,
  binds α (abind_flex_mono_def τ) (denv_to_aenv Γ) -> False.
Proof.
  intros α τ Γ Hb.
  destruct (binds_denv_to_aenv_inv α (abind_flex_mono_def τ) Γ Hb) as [d [_ Heq]].
  destruct d; discriminate.
Qed.

Lemma a_binds_tvar_denv_to_aenv : forall α Γ,
  a_binds_tvar α (denv_to_aenv Γ) -> binds α dbind_tvar Γ.
Proof.
  intros α Γ [ Hb | [ Hb | [τ Hb] ] ];
    [ destruct (binds_denv_to_aenv_inv α abind_tvar Γ Hb) as [d [Hd Heq]]
    | destruct (binds_denv_to_aenv_inv α abind_flex_mono Γ Hb) as [d [Hd Heq]]
    | destruct (binds_denv_to_aenv_inv α (abind_flex_mono_def τ) Γ Hb)
        as [d [Hd Heq]] ];
    destruct d; try discriminate Heq; exact Hd.
Qed.

Lemma a_binds_tvar_of_denv : forall α Γ,
  binds α dbind_tvar Γ -> a_binds_tvar α (denv_to_aenv Γ).
Proof.
  intros α Γ Hb. left. exact (binds_denv_to_aenv α dbind_tvar Γ Hb).
Qed.

Lemma abind_to_pskl_of_dbind : forall d,
  abind_to_pskl (abind_of_dbind d) = dbind_to_pskl d.
Proof. destruct d; reflexivity. Qed.

(* ===================================================================== *)
(*  §0b  THE ∀-SCOPE CONTEXT Δ.  It is an [atoms] on BOTH sides, so the   *)
(*  two systems share it verbatim.  Every rule that touches Δ only ever   *)
(*  ADDS one atom (∀) or CLEARS it (∀◇, whose body is read at Γ∖Δ — the   *)
(*  embedding commutes with that, [denv_to_aenv_minus]).                  *)
(* ===================================================================== *)

(** The paper's [Γ∖Δ] commutes with the embedding: removing the Δ-vars
    before or after translating the context gives the same [aenv]. *)
Lemma denv_to_aenv_minus : forall Γ Δ,
  denv_to_aenv (denv_minus Γ Δ) = aenv_minus (denv_to_aenv Γ) Δ.
Proof.
  intros Γ Δ. induction Γ as [ | [x d] Γ' IH ]; [ reflexivity | ].
  unfold denv_minus, aenv_minus in *. simpl.
  destruct (AtomSetImpl.mem x Δ); simpl; [ exact IH | f_equal; exact IH ].
Qed.

(* ===================================================================== *)
(*  §1  TYPE EQUIVALENCE COLLAPSES.  The paper adds [Θ ⊢ A ≡ B] premises  *)
(*  to four rules "because of the existence of flexible variables"        *)
(*  (full-algo-spec.tex:104-106).  With no flexible to unfold, the        *)
(*  equational theory IS syntactic identity — which is exactly why the    *)
(*  declarative figure can leave those premises out.                      *)
(* ===================================================================== *)

Lemma a_tyequiv_denv_eq : forall Θ A B,
  a_tyequiv Θ A B -> forall Γ, Θ = denv_to_aenv Γ -> A = B.
Proof.
  intros Θ A B H; induction H; intros Γ0 HΘ; subst.
  - reflexivity.
  - symmetry. exact (IHa_tyequiv Γ0 eq_refl).
  - rewrite (IHa_tyequiv1 Γ0 eq_refl). exact (IHa_tyequiv2 Γ0 eq_refl).
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
  - rewrite (IHa_tyequiv1 Γ0 eq_refl), (IHa_tyequiv2 Γ0 eq_refl). reflexivity.
  - f_equal.
    pick fresh α for (L `union` ftvar_in_ptyp A `union` ftvar_in_ptyp B).
    apply open_ptyp_wrt_ptyp_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | ].
    exact (H0 α ltac:(clear - Fr; fsetdec) Γ0 eq_refl).
Qed.

(* ===================================================================== *)
(*  §2  WELL-FORMEDNESS, both directions.                                 *)
(* ===================================================================== *)

Lemma a_wf_ptyp_to_d : forall Θ A,
  a_wf_ptyp Θ A -> forall Γ, Θ = denv_to_aenv Γ -> d_wf_ptyp Γ A.
Proof.
  intros Θ A H; induction H; intros Γ0 HΘ; subst.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. apply a_binds_tvar_denv_to_aenv; assumption.
  - apply d_wf_ptyp__arrow;
      [ exact (IHa_wf_ptyp1 Γ0 eq_refl) | exact (IHa_wf_ptyp2 Γ0 eq_refl) ].
  - apply d_wf_ptyp__all with (L := L). intros α Hα.
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
Qed.

Lemma d_wf_ptyp_to_a : forall Γ A,
  d_wf_ptyp Γ A -> a_wf_ptyp (denv_to_aenv Γ) A.
Proof.
  intros Γ A H; induction H.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply a_binds_tvar_of_denv; assumption.
  - apply a_wf_ptyp__arrow; assumption.
  - apply a_wf_ptyp__all with (L := L). intros α Hα. exact (H0 α Hα).
Qed.

(** ⭐ The DECLARATIVE side of the problem definition's "M wf" — the
    [a_wf_exp] judgement (algo/pat/prop_soundness_pat.v §1) verbatim, with
    [d_wf_ptyp] reading the annotations.  It exists so the paper-facing
    corollaries (prop_run_corollaries.v §5/§6) can state their subject
    hypothesis in the DECLARATIVE system; the two bridges below make it
    interchangeable with [{{ denv_to_aenv Γ ⊢ᵉ e }}a] — at the closed
    entry point, with [{{ nil ⊢ᵉ e }}a]. *)

Reserved Notation "{{ Γ ⊢ᵉ e }}d"
  (at level 0, e at level 74, format "'{{'  Γ  ⊢ᵉ  e  '}}d'").

Inductive d_wf_exp : denv -> exp -> Prop :=
| d_wf_exp__unit : forall Γ,
    {{ Γ ⊢ᵉ exp_unit }}d
| d_wf_exp__var : forall Γ x,
    {{ Γ ⊢ᵉ (exp_var_f x) }}d
| d_wf_exp__anno : forall Γ e A,
    d_wf_ptyp Γ A ->
    {{ Γ ⊢ᵉ e }}d ->
    {{ Γ ⊢ᵉ (exp_anno e A) }}d
| d_wf_exp__freeze : forall Γ e,
    {{ Γ ⊢ᵉ e }}d ->
    {{ Γ ⊢ᵉ (exp_freeze e) }}d
| d_wf_exp__abs : forall L Γ e,
    (forall x, x `notin` L ->
       {{ Γ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}d) ->
    {{ Γ ⊢ᵉ (exp_abs e) }}d
| d_wf_exp__abs_anno : forall L Γ A e,
    d_wf_ptyp Γ A ->
    (forall x, x `notin` L ->
       {{ Γ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}d) ->
    {{ Γ ⊢ᵉ (exp_abs_anno A e) }}d
| d_wf_exp__app : forall Γ e1 e2,
    {{ Γ ⊢ᵉ e1 }}d ->
    {{ Γ ⊢ᵉ e2 }}d ->
    {{ Γ ⊢ᵉ (exp_app e1 e2) }}d
where "{{ Γ ⊢ᵉ e }}d" := (d_wf_exp Γ e) : fresco_d_scope.

Lemma d_wf_exp_to_a : forall Γ e,
  {{ Γ ⊢ᵉ e }}d -> {{ (denv_to_aenv Γ) ⊢ᵉ e }}a.
Proof.
  intros Γ e H; induction H.
  - apply a_wf_exp__unit.
  - apply a_wf_exp__var.
  - apply a_wf_exp__anno; [ apply d_wf_ptyp_to_a; assumption | assumption ].
  - apply a_wf_exp__freeze; assumption.
  - apply a_wf_exp__abs with (L := L); assumption.
  - apply a_wf_exp__abs_anno with (L := L);
      [ apply d_wf_ptyp_to_a; assumption | assumption ].
  - apply a_wf_exp__app; assumption.
Qed.

Lemma a_wf_pskl_to_d : forall Θ Δ P,
  a_wf_pskl Θ Δ P ->
  forall Γ, Θ = denv_to_aenv Γ -> d_wf_pskl Γ Δ P.
Proof.
  intros Θ Δ P H; induction H; intros Γ0 HΘ; subst.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. apply a_binds_tvar_denv_to_aenv; exact H.
  - apply d_wf_pskl__arrow;
      [ exact (IHa_wf_pskl1 Γ0 eq_refl) | exact (IHa_wf_pskl2 Γ0 eq_refl) ].
  - apply d_wf_pskl__all with (L := L). intros α Hα.
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole;
      [ exact H
      | exact (IHa_wf_pskl (denv_minus Γ0 Δ)
                 (eq_sym (denv_to_aenv_minus Γ0 Δ))) ].
Qed.

Lemma d_wf_pskl_to_a : forall Γ Δ P,
  d_wf_pskl Γ Δ P -> a_wf_pskl (denv_to_aenv Γ) Δ P.
Proof.
  intros Γ Δ P H; induction H.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. apply a_binds_tvar_of_denv; exact H.
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L). intros α Hα. exact (H0 α Hα).
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; [ exact H | ].
    rewrite <- (denv_to_aenv_minus Γ Δ). exact IHd_wf_pskl.
Qed.

(* ===================================================================== *)
(*  §3  SKELETON CONSISTENCY  [ad_pat_consis] ⇄ [d_pat_consis].           *)
(*  Rule for rule, plus the two lookup rows FlexL / FlexR.                *)
(* ===================================================================== *)

Lemma ad_pat_consis_to_d : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q -> forall Γ, Θ = denv_to_aenv Γ -> d_pat_consis Ψ Γ R Q.
Proof.
  intros Ψ Θ R Q H; induction H; intros Γ0 HΘ; subst.
  - apply d_pat_consis__unit; assumption.
  - apply d_pat_consis__var;
      [ assumption | apply a_binds_tvar_denv_to_aenv; assumption ].
  - apply d_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ exact (IHad_pat_consis1 Γ0 eq_refl) | exact (IHad_pat_consis2 Γ0 eq_refl)
      | assumption ].
  - apply d_pat_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0);
      [ | assumption ].
    intros α Hα. exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_pat_consis__forall_inh_untagged with (L := L).
    intros α Hα. exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_pat_consis__forall_syn_tagged with (L := L).
    intros α Hα. exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_pat_consis__forall_syn with (L := L).
    intros α Hα. exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_pat_consis__ghostg; assumption.
  - apply d_pat_consis__topholeg. exact (IHad_pat_consis Γ0 eq_refl).
  - apply d_pat_consis__hole;
      [ assumption
      | exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty P H0 Γ0 eq_refl) ].
  - apply d_pat_consis__tophole. exact (IHad_pat_consis Γ0 eq_refl).
  - apply d_pat_consis__tophole_inh with (L := L).
    intros α Hα. exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_pat_consis__tophole_drop. exact (IHad_pat_consis Γ0 eq_refl).
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
Qed.

Lemma d_pat_consis_to_ad : forall Ψ Γ R Q,
  d_pat_consis Ψ Γ R Q -> ad_pat_consis Ψ (denv_to_aenv Γ) R Q.
Proof.
  intros Ψ Γ R Q H; induction H.
  - apply ad_pat_consis__unit; assumption.
  - apply ad_pat_consis__var;
      [ assumption | apply a_binds_tvar_of_denv; assumption ].
  - apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
  - apply ad_pat_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0); assumption.
  - apply ad_pat_consis__forall_inh_untagged with (L := L); assumption.
  - apply ad_pat_consis__forall_syn_tagged with (L := L); assumption.
  - apply ad_pat_consis__forall_syn with (L := L); assumption.
  - apply ad_pat_consis__ghostg; assumption.
  - apply ad_pat_consis__topholeg; assumption.
  - apply ad_pat_consis__hole;
      [ assumption | exact (d_wf_pskl_to_a Γ empty P H0) ].
  - apply ad_pat_consis__tophole; assumption.
  - apply ad_pat_consis__tophole_inh with (L := L); assumption.
  - apply ad_pat_consis__tophole_drop; assumption.
Qed.

(* ===================================================================== *)
(*  §4  TYPE CONSISTENCY.  At the TY sort the [ad] subject is the sort    *)
(*  inclusion of a type, hence ghost-free, so every ghost row is excluded *)
(*  by its subject and what is left is [d_consis] rule for rule.          *)
(* ===================================================================== *)

Lemma ad_pat_consis_ty_to_d : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q ->
  forall Γ, Θ = denv_to_aenv Γ ->
  forall C B, R = utyp_to_uskl C -> Q = btyp_to_bskl B ->
  d_consis Ψ Γ C B.
Proof.
  intros Ψ Θ R Q H; induction H; intros Γ0 HΘ C0 B0 HR HQ; subst.
  - destruct C0; simpl in HR; try discriminate HR.
    destruct B0; simpl in HQ; try discriminate HQ.
    apply d_consis__unit; assumption.
  - destruct C0; simpl in HR; try discriminate HR.
    destruct B0; simpl in HQ; try discriminate HQ.
    inversion HR; inversion HQ; subst.
    apply d_consis__var;
      [ apply a_binds_tvar_denv_to_aenv; assumption | assumption ].
  - destruct C0; simpl in HR; try discriminate HR.
    destruct B0; simpl in HQ; try discriminate HQ.
    inversion HR; inversion HQ; subst.
    apply d_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ exact (IHad_pat_consis1 Γ0 eq_refl C0_1 B0_1 eq_refl eq_refl)
      | exact (IHad_pat_consis2 Γ0 eq_refl C0_2 B0_2 eq_refl eq_refl)
      | assumption ].
  - destruct C0; simpl in HR; try discriminate HR.
    destruct B0; simpl in HQ; try discriminate HQ.
    inversion HR; inversion HQ; subst.
    apply d_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0); [ | assumption ].
    intros α Hα.
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl
             (open_utyp_wrt_utyp C0 (utyp_var_f α))
             (open_btyp_wrt_btyp B0 (btyp_var_f α))
             ltac:(symmetry; apply utyp_to_uskl_open_var)
             ltac:(rewrite btyp_to_bskl_open; reflexivity)).
  - destruct C0; simpl in HR; try discriminate HR.
    destruct B0; simpl in HQ; try discriminate HQ.
    inversion HR; inversion HQ; subst.
    apply d_consis__forall_inh_untagged with (L := L).
    intros α Hα.
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl
             (open_utyp_wrt_utyp C0 (utyp_var_f α))
             (open_btyp_wrt_btyp B0 (btyp_var_f α))
             ltac:(symmetry; apply utyp_to_uskl_open_var)
             ltac:(rewrite btyp_to_bskl_open; reflexivity)).
  - destruct C0; simpl in HR; try discriminate HR.
    destruct B0; simpl in HQ; try discriminate HQ.
    inversion HR; inversion HQ; subst.
    apply d_consis__forall_syn_tagged with (L := L).
    intros α Hα.
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl
             (open_utyp_wrt_utyp C0 (utyp_var_f α))
             (open_btyp_wrt_btyp B0 (btyp_var_f α))
             ltac:(symmetry; apply utyp_to_uskl_open_var)
             ltac:(rewrite btyp_to_bskl_open; reflexivity)).
  - destruct C0; simpl in HR; try discriminate HR.
    destruct B0; simpl in HQ; try discriminate HQ.
    inversion HR; inversion HQ; subst.
    apply d_consis__forall_syn with (L := L).
    intros α Hα.
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl
             (open_utyp_wrt_utyp C0 (utyp_var_f α))
             (open_btyp_wrt_btyp B0 (btyp_var_f α))
             ltac:(symmetry; apply utyp_to_uskl_open_var)
             ltac:(rewrite btyp_to_bskl_open; reflexivity)).
  - destruct C0; simpl in HR; discriminate HR.
  - destruct C0; simpl in HR; discriminate HR.
  - destruct C0; simpl in HR; discriminate HR.
  - destruct C0; simpl in HR; discriminate HR.
  - destruct C0; simpl in HR; discriminate HR.
  - destruct C0; simpl in HR; discriminate HR.
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
Qed.

Lemma d_consis_to_ad : forall Ψ Γ C B,
  d_consis Ψ Γ C B ->
  ad_pat_consis Ψ (denv_to_aenv Γ) (utyp_to_uskl C) (btyp_to_bskl B).
Proof.
  intros Ψ Γ C B H; induction H; simpl.
  - apply ad_pat_consis__unit; assumption.
  - apply ad_pat_consis__var;
      [ assumption | apply a_binds_tvar_of_denv; assumption ].
  - apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
  - apply ad_pat_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0);
      [ | assumption ].
    intros α Hα. pose proof (H0 α Hα) as Hx.
    rewrite utyp_to_uskl_open_var, (btyp_to_bskl_open B (btyp_var_f α)) in Hx.
    exact Hx.
  - apply ad_pat_consis__forall_inh_untagged with (L := L).
    intros α Hα. pose proof (H0 α Hα) as Hx.
    rewrite utyp_to_uskl_open_var, (btyp_to_bskl_open B (btyp_var_f α)) in Hx.
    exact Hx.
  - apply ad_pat_consis__forall_syn_tagged with (L := L).
    intros α Hα. pose proof (H0 α Hα) as Hx.
    rewrite utyp_to_uskl_open_var, (btyp_to_bskl_open B (btyp_var_f α)) in Hx.
    exact Hx.
  - apply ad_pat_consis__forall_syn with (L := L).
    intros α Hα. pose proof (H0 α Hα) as Hx.
    rewrite utyp_to_uskl_open_var, (btyp_to_bskl_open B (btyp_var_f α)) in Hx.
    exact Hx.
Qed.

(* ===================================================================== *)
(*  §5  SKELETON REFINEMENT  [ad_refine_syn] ⇄ [d_refine_syn].            *)
(* ===================================================================== *)

Lemma ad_refine_syn_to_d : forall Θ Δ Q Q',
  ad_refine_syn Θ Δ Q Q' ->
  forall Γ, Θ = denv_to_aenv Γ -> d_refine_syn Γ Δ Q Q'.
Proof.
  intros Θ Δ Q Q' H; induction H; intros Γ0 HΘ; subst.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var.
  - apply d_refine_syn__arrow;
      [ exact H | exact (IHad_refine_syn1 Γ0 eq_refl)
      | exact (IHad_refine_syn2 Γ0 eq_refl) ].
  - apply d_refine_syn__all with (L := L); [ exact H | ]. intros α Hα.
    exact (H1 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_refine_syn__hole. exact H.
  - apply d_refine_syn__tophole_remove;
      [ exact H | exact (IHad_refine_syn Γ0 eq_refl) ].
  - apply d_refine_syn__tophole_fill with (L := L); [ exact H | ]. intros α Hα.
    exact (H1 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_refine_syn__tophole_keep;
      [ exact H | exact (IHad_refine_syn Γ0 eq_refl) ].
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
Qed.

Lemma d_refine_syn_to_ad : forall Γ Δ Q Q',
  d_refine_syn Γ Δ Q Q' -> ad_refine_syn (denv_to_aenv Γ) Δ Q Q'.
Proof.
  intros Γ Δ Q Q' H; induction H.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
  - apply ad_refine_syn__arrow; assumption.
  - apply ad_refine_syn__all with (L := L); [ exact H | ]. intros α Hα.
    exact (H1 α Hα).
  - apply ad_refine_syn__hole. exact H.
  - apply ad_refine_syn__tophole_remove; assumption.
  - apply ad_refine_syn__tophole_fill with (L := L); [ exact H | ]. intros α Hα.
    exact (H1 α Hα).
  - apply ad_refine_syn__tophole_keep; assumption.
Qed.

(** ⭐ THE UNCOLOURED TWINS.  Same eight rows; needed because the paper's
    presupposition on skeleton consistency (declarative.tex:2074) is stated at
    the uncoloured sort, so it is [d_refine_pskl] / [ad_refine_pskl] that the
    subtyping rows now carry and that this file has to move across. *)
Lemma ad_refine_pskl_to_d : forall Θ Δ P P',
  ad_refine_pskl Θ Δ P P' ->
  forall Γ, Θ = denv_to_aenv Γ -> d_refine_pskl Γ Δ P P'.
Proof.
  intros Θ Δ P P' H; induction H; intros Γ0 HΘ; subst.
  - apply d_refine_pskl__unit.
  - apply d_refine_pskl__var.
  - apply d_refine_pskl__arrow;
      [ exact (IHad_refine_pskl1 Γ0 eq_refl)
      | exact (IHad_refine_pskl2 Γ0 eq_refl) ].
  - apply d_refine_pskl__all with (L := L). intros α Hα.
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_refine_pskl__hole. exact H.
  - apply d_refine_pskl__tophole_remove.
    exact (IHad_refine_pskl Γ0 eq_refl).
  - apply d_refine_pskl__tophole_fill with (L := L). intros α Hα.
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_refine_pskl__tophole_keep. exact (IHad_refine_pskl Γ0 eq_refl).
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
Qed.

Lemma d_refine_pskl_to_ad : forall Γ Δ P P',
  d_refine_pskl Γ Δ P P' -> ad_refine_pskl (denv_to_aenv Γ) Δ P P'.
Proof.
  intros Γ Δ P P' H; induction H.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var.
  - apply ad_refine_pskl__arrow; auto.
  - apply ad_refine_pskl__all with (L := L). intros α Hα. exact (H0 α Hα).
  - apply ad_refine_pskl__hole. exact H.
  - apply ad_refine_pskl__tophole_remove; auto.
  - apply ad_refine_pskl__tophole_fill with (L := L). intros α Hα.
    exact (H0 α Hα).
  - apply ad_refine_pskl__tophole_keep; auto.
Qed.

(** the two shapes the subtyping rows actually use: Δ empty on both sides *)
Lemma ad_refine_pskl_to_d_closed : forall Γ P P',
  ad_refine_pskl (denv_to_aenv Γ) empty P P' -> d_refine_pskl Γ empty P P'.
Proof.
  intros Γ P P' H.
  exact (ad_refine_pskl_to_d (denv_to_aenv Γ) empty P P' H Γ eq_refl).
Qed.

Lemma d_refine_pskl_to_ad_closed : forall Γ P P',
  d_refine_pskl Γ empty P P' -> ad_refine_pskl (denv_to_aenv Γ) empty P P'.
Proof.
  intros Γ P P' H. exact (d_refine_pskl_to_ad Γ empty P P' H).
Qed.

(** The JOIN crosses in both directions, because both of its halves do. *)
Lemma ad_consis_join_to_d : forall Ψ Θ R Q,
  ad_consis_join Ψ Θ R Q -> forall Γ, Θ = denv_to_aenv Γ -> d_consis_join Ψ Γ R Q.
Proof.
  intros Ψ Θ R Q [Hc Hr] Γ0 HΘ; subst. split.
  - exact (ad_pat_consis_to_d Ψ (denv_to_aenv Γ0) R Q Hc Γ0 eq_refl).
  - apply ad_refine_pskl_to_d_closed; assumption.
Qed.

Lemma d_consis_join_to_ad : forall Ψ Γ R Q,
  d_consis_join Ψ Γ R Q -> ad_consis_join Ψ (denv_to_aenv Γ) R Q.
Proof.
  intros Ψ Γ R Q [Hc Hr]. split.
  - apply d_pat_consis_to_ad; assumption.
  - apply d_refine_pskl_to_ad_closed; assumption.
Qed.

(* ===================================================================== *)
(*  §6  THE ForallL INSTANTIATION.  Both systems require the instantiated *)
(*  ψ to be well-scoped and tagged, but they say it in different sorts:   *)
(*  the [ad] side scopes ⌊ψ⌋ˢ with [a_wf_pskl], the [d] side scopes ψ     *)
(*  itself with [d_wf_uskl] (skeletons) or its RETRACTION with            *)
(*  [d_wf_utyp] (types).  ⌊·⌋ˢ is not injective — it collapses the ε tag  *)
(*  and the dotted ghosts — so these go by induction on the DERIVATION    *)
(*  with the erasure threaded as an equation.                             *)
(* ===================================================================== *)

Lemma d_wf_uskl_of_a_wf_pskl : forall Θ Δ P,
  a_wf_pskl Θ Δ P ->
  forall ψ, P = uskl_to_pskl ψ ->
  forall Γ, Θ = denv_to_aenv Γ -> d_wf_uskl Γ Δ ψ.
Proof.
  intros Θ Δ P H; induction H; intros ψ Hψ Γ0 HΘ; subst;
    destruct ψ; simpl in Hψ; try discriminate Hψ.
  - apply d_wf_uskl__unit.
  - inversion Hψ; subst. apply d_wf_uskl__var.
    apply a_binds_tvar_denv_to_aenv; exact H.
  - inversion Hψ; subst. apply d_wf_uskl__arrow;
      [ exact (IHa_wf_pskl1 _ eq_refl Γ0 eq_refl)
      | exact (IHa_wf_pskl2 _ eq_refl Γ0 eq_refl) ].
  - inversion Hψ; subst. apply d_wf_uskl__all_syn with (L := L). intros α Hα.
    exact (H0 α Hα (open_uskl_wrt_uskl ψ (uskl_var_f α))
             ltac:(symmetry; apply uskl_to_pskl_open)
             ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - inversion Hψ; subst. apply d_wf_uskl__all_tag with (L := L) (ε := ε).
    intros α Hα.
    exact (H0 α Hα (open_uskl_wrt_uskl ψ (uskl_var_f α))
             ltac:(symmetry; apply uskl_to_pskl_open)
             ((α ~ dbind_tvar) ++ Γ0) eq_refl).
  - apply d_wf_uskl__hole.
  - apply d_wf_uskl__holeg.
  - inversion Hψ; subst. apply d_wf_uskl__tophole;
      [ apply guarded_uskl_of_uskl_to_pskl; exact H
      | exact (IHa_wf_pskl _ eq_refl (denv_minus Γ0 Δ)
                 (eq_sym (denv_to_aenv_minus Γ0 Δ))) ].
  - inversion Hψ; subst. apply d_wf_uskl__topholeg;
      [ apply guarded_uskl_of_uskl_to_pskl; exact H
      | exact (IHa_wf_pskl _ eq_refl (denv_minus Γ0 Δ)
                 (eq_sym (denv_to_aenv_minus Γ0 Δ))) ].
Qed.

Lemma a_wf_pskl_of_d_wf_uskl : forall Γ Δ ψ,
  d_wf_uskl Γ Δ ψ ->
  a_wf_pskl (denv_to_aenv Γ) Δ (uskl_to_pskl ψ).
Proof.
  intros Γ Δ ψ H; induction H; simpl.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. apply a_binds_tvar_of_denv; exact H.
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L). intros α Hα.
    pose proof (H0 α Hα) as Hx.
    rewrite uskl_to_pskl_open in Hx. exact Hx.
  - apply a_wf_pskl__all with (L := L). intros α Hα.
    pose proof (H0 α Hα) as Hx.
    rewrite uskl_to_pskl_open in Hx. exact Hx.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole.
    + apply guarded_pskl_uskl_to_pskl; assumption.
    + rewrite <- (denv_to_aenv_minus Γ Δ). exact IHd_wf_uskl.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole.
    + apply guarded_pskl_uskl_to_pskl; assumption.
    + rewrite <- (denv_to_aenv_minus Γ Δ). exact IHd_wf_uskl.
Qed.

(** The ghost-free part of [uskl] IS [utyp]: the retraction is a section
    there, and it transports tagged-ness, the tag count and well-scopedness. *)
Lemma uskl_ghost_free_utyp_to_uskl : forall R,
  uskl_ghost_free R -> utyp_to_uskl (uskl_to_utyp R) = R.
Proof.
  intros R H; induction H; simpl; try reflexivity.
  - rewrite IHuskl_ghost_free1, IHuskl_ghost_free2. reflexivity.
  - f_equal.
    pick fresh α for (L `union` ftvar_in_uskl R
                        `union` ftvar_in_uskl (utyp_to_uskl (uskl_to_utyp R))).
    apply open_uskl_wrt_uskl_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | ].
    rewrite <- utyp_to_uskl_open_var, <- uskl_to_utyp_open_var.
    exact (H0 α ltac:(clear - Fr; fsetdec)).
  - f_equal.
    pick fresh α for (L `union` ftvar_in_uskl R
                        `union` ftvar_in_uskl (utyp_to_uskl (uskl_to_utyp R))).
    apply open_uskl_wrt_uskl_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | ].
    rewrite <- utyp_to_uskl_open_var, <- uskl_to_utyp_open_var.
    exact (H0 α ltac:(clear - Fr; fsetdec)).
Qed.

Lemma is_ttyp_uskl_to_utyp : forall ψ,
  is_tskl ψ -> uskl_ghost_free ψ -> is_ttyp (uskl_to_utyp ψ).
Proof.
  intros ψ H; induction H; intros Hgf; simpl.
  - apply is_ttyp__unit.
  - apply is_ttyp__var.
  - inversion Hgf; subst. apply is_ttyp__arrow; auto.
  - inversion Hgf as [ | | | L0 ε0 R0 Hgf0 | ]; subst.
    apply is_ttyp__all_tag with (L := L `union` L0). intros α Hα.
    rewrite <- uskl_to_utyp_open_var.
    apply H0; [ clear - Hα; fsetdec | apply Hgf0; clear - Hα; fsetdec ].
  - inversion Hgf.
  - inversion Hgf.
Qed.

Lemma d_tags_uskl_to_utyp : forall Ψ ψ,
  d_tags_skl Ψ ψ -> uskl_ghost_free ψ -> d_tags Ψ (uskl_to_utyp ψ).
Proof.
  intros Ψ ψ H; induction H; intros Hgf; simpl.
  - apply d_tags__unit; assumption.
  - apply d_tags__var; assumption.
  - inversion Hgf; subst. apply d_tags__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); auto.
  - inversion Hgf as [ | | | L0 ε0 R0 Hgf0 | ]; subst.
    apply d_tags__all_tag with (L := L `union` L0) (Ψ0 := Ψ0);
      [ | assumption | assumption ].
    intros α Hα. rewrite <- uskl_to_utyp_open_var.
    apply H0; [ clear - Hα; fsetdec | apply Hgf0; clear - Hα; fsetdec ].
  - inversion Hgf.
  - inversion Hgf.
Qed.

(** A ∀ binds its variable in Γ as well as Δ, so the retraction is already
    well-formed over Γ alone. *)
Lemma d_wf_utyp_of_d_wf_uskl : forall Γ Δ ψ,
  d_wf_uskl Γ Δ ψ -> uskl_ghost_free ψ -> d_wf_utyp Γ (uskl_to_utyp ψ).
Proof.
  intros Γ Δ ψ H; induction H; intros Hgf; simpl.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var. exact H.
  - inversion Hgf; subst. apply d_wf_utyp__arrow; auto.
  - inversion Hgf as [ | | | | L0 R0 Hgf0 ]; subst.
    apply d_wf_utyp__all_syn with (L := L `union` L0). intros α Hα.
    rewrite <- uskl_to_utyp_open_var.
    exact (H0 α ltac:(clear - Hα; fsetdec)
             (Hgf0 α ltac:(clear - Hα; fsetdec))).
  - inversion Hgf as [ | | | L0 ε0 R0 Hgf0 | ]; subst.
    apply d_wf_utyp__all_tag with (L := L `union` L0) (ε := ε). intros α Hα.
    rewrite <- uskl_to_utyp_open_var.
    exact (H0 α ltac:(clear - Hα; fsetdec)
             (Hgf0 α ltac:(clear - Hα; fsetdec))).
  - inversion Hgf.
  - inversion Hgf.
  - inversion Hgf.
  - inversion Hgf.
Qed.

(* ===================================================================== *)
(*  §7  SKELETON SUBTYPING  [ad_pat_sub] at N = SK ⇄ [d_pat_sub].         *)
(* ===================================================================== *)

(** ⚠️⚠️ THE SOURCE IS THE LEAF-VALID MIRROR, not the plain join, and it has to
    be.  Since 2026-08-11 [d_pat_sub]'s three consistency-bearing rows carry the
    paper's presupposition on skeleton consistency (declarative.tex:2074), which
    [ad_pat_sub] itself supplies since 2026-08-12, at exactly those rows.  ⚙ It
    used to be statable only over the fuelled mirror, because the plain
    relation did not carry the datum (cex/cex_ad_pat_join_not_leaf_valid.v)
    — the fuel was never what the proof needed, only the datum was. *)
Lemma ad_pat_sub_sk_to_d : forall NM M Ψ Θ R Q,
  ad_pat_sub NM M Ψ Θ R Q -> NM = a_sub_mode_sk ->
  forall Γ, Θ = denv_to_aenv Γ -> d_pat_sub M Ψ Γ R Q.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros HNM Γ0 HΘ;
    try discriminate HNM; subst.
  - (* Infer *) apply d_pat_sub__infer;
      [ assumption
      | eapply ad_consis_join_to_d; [ exact H0 | reflexivity ]
      | assumption ].
  - (* UnivGhostR *) apply d_pat_sub__univ_ghost_r;
      [ assumption | assumption | assumption | assumption
      | eapply ad_consis_join_to_d; [ exact H3 | reflexivity ] ].
  - (* Arrow *) apply d_pat_sub__arg with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ eapply ad_consis_join_to_d; [ exact H | reflexivity ]
      | exact (IHad_pat_sub eq_refl Γ0 eq_refl) | assumption ].
  - (* ForallL, tagged *) inversion H2; subst.
    apply d_pat_sub__forall_l_tagged with (Ψ' := Ψ') (psi := ψ);
      [ assumption | assumption
      | (* the two judgements now read `fresh Ψ'` the SAME way, so the
           hygiene premise travels verbatim *) assumption | assumption
      | exact (d_wf_uskl_of_a_wf_pskl (denv_to_aenv Γ0) empty (uskl_to_pskl ψ)
                 H3 ψ eq_refl Γ0 eq_refl)
      | assumption | exact (IHad_pat_sub eq_refl Γ0 eq_refl) ].
  - (* ForallL, untagged *) inversion H2; subst.
    apply d_pat_sub__forall_l_untagged with (Ψ' := Ψ') (psi := ψ);
      [ assumption | assumption
      | (* the two judgements now read `fresh Ψ'` the SAME way, so the
           hygiene premise travels verbatim *) assumption | assumption
      | exact (d_wf_uskl_of_a_wf_pskl (denv_to_aenv Γ0) empty (uskl_to_pskl ψ)
                 H3 ψ eq_refl Γ0 eq_refl)
      | assumption | exact (IHad_pat_sub eq_refl Γ0 eq_refl) ].
  - (* Ghost *) apply d_pat_sub__ghost;
      [ assumption
      | exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty P H0 Γ0 eq_refl)
      | assumption ].
  - (* GhostG *) apply d_pat_sub__ghostg; assumption.
  - (* UnivGhostL *) apply d_pat_sub__univ_ghost_l;
      [ assumption | exact (IHad_pat_sub eq_refl Γ0 eq_refl) ].
  - (* UnivGhostLG *) apply d_pat_sub__univ_ghost_lg;
      [ assumption | exact (IHad_pat_sub eq_refl Γ0 eq_refl) ].
  - (* FlexMono *) exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
Qed.

(** ⭐ THE DIRECTION THE COMPLETENESS BRIDGE NEEDS, at the SK sort: a
    declarative skeleton join IS a LEAF-VALID one.  Since 2026-08-11 there is
    nothing to recover — the leaf datum is the paper's presupposition, carried
    on the rule, so it crosses by [d_refine_pskl_to_ad_closed] and the only
    work left is COLLECTING the fuel.

    ⚙ And the fuel is easy HERE, unlike §13's type-sorted twin: [d_pat_sub] has
    no cofinite row (its ForallR is a TY-only rule), so one [n] per premise
    suffices and no renaming is needed. *)

Lemma d_pat_sub_to_ad : forall M Ψ Γ R Q,
  d_pat_sub M Ψ Γ R Q -> ad_pat_sub a_sub_mode_sk M Ψ (denv_to_aenv Γ) R Q.
Proof.
  intros M Ψ Γ R Q H; induction H.
  - apply ad_pat_sub__infer;
      [ assumption | apply d_consis_join_to_ad; assumption | assumption ].
  - apply ad_pat_sub__univ_ghost_r;
      [ assumption | assumption | assumption | assumption
      | apply d_consis_join_to_ad; assumption ].
  - apply ad_pat_sub__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ apply d_consis_join_to_ad; assumption
      | assumption | assumption ].
  - apply ad_pat_sub__forall_l_tagged with (Ψ' := Ψ') (ψ := psi);
      [ assumption | assumption | assumption
      | apply a_tags_sort__sk; assumption
      | exact (a_wf_pskl_of_d_wf_uskl Γ empty psi H3)
      | assumption ].
  - apply ad_pat_sub__forall_l_untagged with (Ψ' := Ψ') (ψ := psi);
      [ assumption | assumption | assumption
      | apply a_tags_sort__sk; assumption
      | exact (a_wf_pskl_of_d_wf_uskl Γ empty psi H3)
      | assumption ].
  - apply ad_pat_sub__ghost;
      [ assumption
      | exact (d_wf_pskl_to_a Γ empty P H0)
      | assumption ].
  - apply ad_pat_sub__univ_ghost_l; assumption.
  - apply ad_pat_sub__ghostg; assumption.
  - apply ad_pat_sub__univ_ghost_lg; assumption.
Qed.

(* ===================================================================== *)
(*  §8  TYPE SUBTYPING  [ad_pat_sub] at N = TY ⇄ [d_sub].                 *)
(*                                                                        *)
(*  The colour-discipline premises the declarative rules state and the    *)
(*  fused figure leaves to the sort ([is_styp] on Infer, [is_ityp] and    *)
(*  guardedness on Check, [is_ityp] on ForallR) are all RECOVERED here    *)
(*  rather than assumed: at the TY sort the [ad] target is a [btyp]'s     *)
(*  skeleton, and a skeleton predicate on it transports back.             *)
(* ===================================================================== *)

Lemma is_ityp_of_btyp_to_bskl : forall Q,
  is_iskl Q -> forall B, Q = btyp_to_bskl B -> is_ityp B.
Proof.
  intros Q H; induction H; intros B0 HQ;
    destruct B0; simpl in HQ; try discriminate HQ; inversion HQ; subst.
  - apply is_ityp__unit.
  - apply is_ityp__var.
  - apply is_ityp__arrow; [ apply IHis_iskl1 | apply IHis_iskl2 ]; reflexivity.
  - apply is_ityp__all with (L := L). intros α Hα.
    apply (H0 α Hα (open_btyp_wrt_btyp B0 (btyp_var_f α))).
    rewrite btyp_to_bskl_open; reflexivity.
Qed.

Lemma lc_utyp_of_lc_uskl_incl : forall R,
  lc_uskl R -> forall C, R = utyp_to_uskl C -> lc_utyp C.
Proof.
  intros R H; induction H; intros C0 HR;
    destruct C0; simpl in HR; try discriminate HR; inversion HR; subst;
    try solve [ constructor ].
  - apply lc_utyp_arrow; [ apply IHlc_uskl1 | apply IHlc_uskl2 ]; reflexivity.
  - apply lc_utyp_all_syn. intros α.
    apply (H0 α (open_utyp_wrt_utyp C0 (utyp_var_f α))).
    symmetry; apply utyp_to_uskl_open_var.
  - apply lc_utyp_all_tag. intros α.
    apply (H0 α (open_utyp_wrt_utyp C0 (utyp_var_f α))).
    symmetry; apply utyp_to_uskl_open_var.
Qed.

Lemma guarded_utyp_of_guarded_uskl_incl : forall C,
  guarded_uskl (utyp_to_uskl C) -> guarded_utyp C.
Proof.
  intros C H; destruct C; simpl in H; inversion H; subst.
  - apply guarded_utyp__unit.
  - apply guarded_utyp__var.
  - apply guarded_utyp__arrow;
      [ apply (lc_utyp_of_lc_uskl_incl (utyp_to_uskl C1));
          [ assumption | reflexivity ]
      | apply (lc_utyp_of_lc_uskl_incl (utyp_to_uskl C2));
          [ assumption | reflexivity ] ].
Qed.

(** [Check]'s target: an inherited painting that is also a [btyp]'s skeleton
    determines the [btyp]'s colour discipline AND its guardedness. *)
Lemma inh_paint_btyp : forall P B,
  guarded_pskl P -> btyp_to_bskl B = pskl_to_bskl_inh P ->
  is_ityp B /\ guarded_btyp B.
Proof.
  intros P B Hg Heq.
  assert (Hi : is_ityp B).
  { apply (is_ityp_of_btyp_to_bskl (pskl_to_bskl_inh P));
      [ apply is_iskl_pskl_to_bskl_inh; apply guarded_pskl_lc; exact Hg
      | symmetry; exact Heq ]. }
  split; [ exact Hi | ].
  pose proof (is_ityp_lc Hi) as Hlc.
  destruct P; inversion Hg; subst;
    destruct B; simpl in Heq; try discriminate Heq.
  - apply guarded_btyp__unit.
  - apply guarded_btyp__var.
  - inversion Hlc; subst. apply guarded_btyp__arrow; assumption.
Qed.

(** At [N = TY, M = TC] the target is always inherited — the declarative
    [ForallR]'s [is_ityp] premise, recovered by induction rather than
    assumed. *)
Lemma ad_pat_sub_ty_tc_target_ityp : forall NM M Ψ Θ R Q,
  ad_pat_sub NM M Ψ Θ R Q -> NM = a_sub_mode_ty -> M = mode_tc ->
  forall B, Q = btyp_to_bskl B -> is_ityp B.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros HNM HM B0 HQ;
    try discriminate HNM; try discriminate HM; subst.
  - (* Check *) exact (proj1 (inh_paint_btyp B B0 H0 (eq_sym HQ))).
  - (* ForallR *) destruct B0; simpl in HQ; try discriminate HQ.
    inversion HQ; subst.
    apply is_ityp__all with (L := L). intros α Hα.
    exact (H0 α Hα eq_refl eq_refl (open_btyp_wrt_btyp B0 (btyp_var_f α))
             ltac:(rewrite btyp_to_bskl_open; reflexivity)).
  - (* ForallL, tagged *) exact (IHad_pat_sub eq_refl eq_refl B0 eq_refl).
  - (* ForallL, untagged *) exact (IHad_pat_sub eq_refl eq_refl B0 eq_refl).
Qed.

Lemma ad_pat_sub_ty_to_d : forall NM M Ψ Θ R Q,
  ad_pat_sub NM M Ψ Θ R Q -> NM = a_sub_mode_ty ->
  forall Γ, Θ = denv_to_aenv Γ ->
  forall C B, R = utyp_to_uskl C -> Q = btyp_to_bskl B ->
  d_sub M Ψ Γ C B.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros HNM Γ0 HΘ C0 B0 HR HQ;
    try discriminate HNM; subst.
  - (* Infer *) apply d_sub__infer;
      [ exact (ad_pat_consis_ty_to_d empty (denv_to_aenv Γ0) (utyp_to_uskl C0)
                 (btyp_to_bskl B0) (ad_consis_join_consis H0)
                 Γ0 eq_refl C0 B0 eq_refl eq_refl)
      | exact (is_styp_of_btyp_to_bskl (btyp_to_bskl B0) H1 B0 eq_refl)
      | assumption ].
  - (* Check *)
    destruct (inh_paint_btyp B B0 H0 (eq_sym HQ)) as [Hi Hgb].
    apply d_sub__check;
      [ apply guarded_utyp_of_guarded_uskl_incl; exact H
      | exact Hgb
      | exact (ad_pat_consis_ty_to_d Ψ (denv_to_aenv Γ0) (utyp_to_uskl C0)
                 (btyp_to_bskl B0)
                 ltac:(rewrite <- HQ; exact (ad_consis_join_consis H1))
                 Γ0 eq_refl C0 B0 eq_refl eq_refl)
      | exact Hi ].
  - (* ForallR *) destruct B0; simpl in HQ; try discriminate HQ.
    inversion HQ; subst.
    apply d_sub__forall_r with (L := L).
    + apply is_ityp__all with (L := L). intros α Hα.
      eapply ad_pat_sub_ty_tc_target_ityp;
        [ exact (H α Hα) | reflexivity | reflexivity
        | rewrite btyp_to_bskl_open; reflexivity ].
    + intros α Hα.
      exact (H0 α Hα eq_refl ((α ~ dbind_tvar) ++ Γ0) eq_refl C0
               (open_btyp_wrt_btyp B0 (btyp_var_f α)) eq_refl
               ltac:(rewrite btyp_to_bskl_open; reflexivity)).
  - (* Arrow *)
    destruct C0; simpl in HR; try discriminate HR.
    destruct B0; simpl in HQ; try discriminate HQ.
    inversion HR; inversion HQ; subst.
    apply d_sub__arg with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ exact (ad_pat_consis_ty_to_d Ψ1 (denv_to_aenv Γ0) (utyp_to_uskl C0_1)
                 (btyp_to_bskl B0_1) (ad_consis_join_consis H)
                 Γ0 eq_refl C0_1 B0_1 eq_refl eq_refl)
      | exact (IHad_pat_sub eq_refl Γ0 eq_refl C0_2 B0_2 eq_refl eq_refl)
      | assumption ].
  - (* ForallL, tagged *)
    destruct C0; simpl in HR; try discriminate HR.
    inversion HR; subst. inversion H2; subst.
    apply d_sub__forall_l_tagged with (Ψ' := Ψ') (ph := uskl_to_utyp ψ);
      [ assumption | assumption
      | (* the hygiene premise crosses the SORTS: the inclusion
           [utyp_to_uskl] keeps every tag.  ⚙ No explicit argument — the ∀'s
           own tag was substituted away by [inversion HR; subst]. *)
        rewrite <- ftag_utyp_to_uskl; simpl in H1 |- *; exact H1
      | apply d_tags_uskl_to_utyp; assumption
      | exact (d_wf_utyp_of_d_wf_uskl Γ0 empty ψ
                 (d_wf_uskl_of_a_wf_pskl (denv_to_aenv Γ0) empty
                    (uskl_to_pskl ψ) H3 ψ eq_refl Γ0 eq_refl) H7)
      | apply is_ttyp_uskl_to_utyp; assumption
      | exact (IHad_pat_sub eq_refl Γ0 eq_refl
                 (open_utyp_wrt_utyp C0 (uskl_to_utyp ψ)) B0
                 ltac:(rewrite utyp_to_uskl_open;
                       rewrite (uskl_ghost_free_utyp_to_uskl ψ H7);
                       reflexivity)
                 eq_refl) ].
  - (* ForallL, untagged *)
    destruct C0; simpl in HR; try discriminate HR.
    inversion HR; subst. inversion H2; subst.
    apply d_sub__forall_l_untagged with (Ψ' := Ψ') (ph := uskl_to_utyp ψ);
      [ assumption | assumption
      | (* the hygiene premise crosses the SORTS: the inclusion
           [utyp_to_uskl] keeps every tag.  ⚙ No explicit argument — the ∀'s
           own tag was substituted away by [inversion HR; subst]. *)
        rewrite <- ftag_utyp_to_uskl; simpl in H1 |- *; exact H1
      | apply d_tags_uskl_to_utyp; assumption
      | exact (d_wf_utyp_of_d_wf_uskl Γ0 empty ψ
                 (d_wf_uskl_of_a_wf_pskl (denv_to_aenv Γ0) empty
                    (uskl_to_pskl ψ) H3 ψ eq_refl Γ0 eq_refl) H7)
      | apply is_ttyp_uskl_to_utyp; assumption
      | exact (IHad_pat_sub eq_refl Γ0 eq_refl
                 (open_utyp_wrt_utyp C0 (uskl_to_utyp ψ)) B0
                 ltac:(rewrite utyp_to_uskl_open;
                       rewrite (uskl_ghost_free_utyp_to_uskl ψ H7);
                       reflexivity)
                 eq_refl) ].
  - (* FlexMono *) exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
Qed.

(** The two forms in which the base rows of [ad_pat] / [ad_sd_typing] carry
    their join: the LEAF-VALID [ad_pat_sub_v], whose extra data the plain
    declarative rules do not ask for and which is therefore simply forgotten
    ([ad_pat_sub_of_fuel]). *)
(* ===================================================================== *)
(*  §9  SKELETON INFERENCE  [ad_pat] -> [d_pat].                          *)
(* ===================================================================== *)

Lemma ad_pat_to_d : forall M Θ e Q,
  ad_pat M Θ e Q -> forall Γ, Θ = denv_to_aenv Γ -> d_pat M Γ e Q.
Proof.
  intros M Θ e Q H; induction H; intros Γ0 HΘ; subst Θ.
  - (* P-Unit *) apply d_pat__unit;
      [ exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty (bskl_to_pskl Q) H Γ0 eq_refl)
      | eapply ad_pat_sub_sk_to_d; [ eassumption | reflexivity | reflexivity ] ].
  - (* P-Var *)
    destruct (binds_denv_to_aenv_inv x b Γ0 H) as [d [Hd Heq]]; subst.
    apply d_pat__var with (P := P) (d := d);
      [ exact Hd
      | rewrite <- abind_to_pskl_of_dbind; exact H0
      | exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty (bskl_to_pskl Q) H1 Γ0 eq_refl)
      | eapply ad_pat_sub_sk_to_d; [ eassumption | reflexivity | reflexivity ] ].
  - (* P-Anno *) apply d_pat__anno;
      [ exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H Γ0 eq_refl)
      | exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty (bskl_to_pskl Q) H0 Γ0 eq_refl)
      | eapply ad_pat_sub_sk_to_d; [ eassumption | reflexivity | reflexivity ] ].
  - (* P-Freeze *) apply d_pat__freeze. exact (IHad_pat Γ0 eq_refl).
  - (* P-Abs *) apply d_pat__abs with (L := L);
      [ assumption
      | exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty P H0 Γ0 eq_refl)
      | assumption
      | intros x Hx; exact (H3 x Hx ((x ~ dbind_skl P) ++ Γ0) eq_refl) ].
  - (* P-AbsAnno *) apply d_pat__abs_anno with (L := L) (B := B);
      [ assumption
      | exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H0 Γ0 eq_refl)
      | assumption | assumption
      | intros x Hx; exact (H4 x Hx ((x ~ dbind_typ A) ++ Γ0) eq_refl) ].
  - (* P-App *) apply d_pat__app with (P := P) (Q1 := Q1);
      [ exact (IHad_pat1 Γ0 eq_refl)
      | exact (ad_refine_syn_to_d (denv_to_aenv Γ0) empty
                 (pskl_to_bskl_inh P) Q1 H0 Γ0 eq_refl)
      | exact (IHad_pat2 Γ0 eq_refl) ].
  - (* P-AbsCheck *) apply d_pat__abs_check with (L := L). intros x Hx.
    exact (H0 x Hx ((x ~ dbind_skl pskl_hole) ++ Γ0) eq_refl).
  - (* P-AbsAnnoCheck *) apply d_pat__abs_anno_check with (L := L);
      [ exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H Γ0 eq_refl)
      | intros x Hx; exact (H1 x Hx ((x ~ dbind_typ A) ++ Γ0) eq_refl) ].
Qed.

(* ===================================================================== *)
(*  §10  SYNTAX-DIRECTED TYPING  [ad_sd_typing] -> [d_sd_typing].         *)
(*                                                                        *)
(*  ⭐ The four explicit type-equivalence premises the appendix adds       *)
(*  (Freeze, AbsAnnoCheck, AbsAnno, App) all collapse to EQUALITY here     *)
(*  (§1) — which is what makes the declarative figure's silent reuse of    *)
(*  an annotation legitimate once the flexibles are gone.                  *)
(* ===================================================================== *)

Lemma ad_sd_typing_to_d : forall M Θ e B,
  ad_sd_typing M Θ e B -> forall Γ, Θ = denv_to_aenv Γ -> d_sd_typing M Γ e B.
Proof.
  intros M Θ e B H; induction H; intros Γ0 HΘ; subst Θ.
  - (* sd-Unit *) apply d_sd_typing__unit.
    eapply ad_pat_sub_ty_to_d;
      [ eassumption | reflexivity | reflexivity | | reflexivity ];
    unfold ptyp_to_uskl_syn; symmetry; apply utyp_to_uskl_ptyp_to_utyp_syn.
  - (* sd-Var *)
    destruct (binds_denv_to_aenv_inv x (abind_var_typ A) Γ0 H) as [d [Hd Heq]].
    destruct d as [ | A1 | P1 ]; simpl in Heq; try discriminate Heq.
    assert (HA : A = A1) by (injection Heq; auto). subst A1.
    apply d_sd_typing__var with (A := A);
      [ exact Hd
      | eapply ad_pat_sub_ty_to_d;
          [ eassumption | reflexivity | reflexivity | | reflexivity ];
        unfold ptyp_to_uskl_syn; symmetry; apply utyp_to_uskl_ptyp_to_utyp_syn ].
  - (* sd-Anno *) apply d_sd_typing__anno with (A := A);
      [ exact (IHad_sd_typing Γ0 eq_refl)
      | eapply ad_pat_sub_ty_to_d;
          [ eassumption | reflexivity | reflexivity | | reflexivity ];
        unfold ptyp_to_uskl_syn; symmetry; apply utyp_to_uskl_ptyp_to_utyp_syn ].
  - (* sd-Freeze *)
    rewrite (a_tyequiv_denv_eq (denv_to_aenv Γ0) B A H0 Γ0 eq_refl) in *.
    apply d_sd_typing__freeze. exact (IHad_sd_typing Γ0 eq_refl).
  - (* sd-AbsCheck (∀) *) apply d_sd_typing__abs_check_step with (L := L);
      [ assumption
      | intros α Hα; exact (H1 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl) ].
  - (* sd-AbsCheck (→) *) apply d_sd_typing__abs_check_base with (L := L);
      [ exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H Γ0 eq_refl)
      | assumption
      | intros x Hx; exact (H2 x Hx ((x ~ dbind_typ A) ++ Γ0) eq_refl) ].
  - (* sd-AbsAnnoCheck (∀) *)
    apply d_sd_typing__abs_anno_check_step with (L := L);
      [ assumption
      | intros α Hα; exact (H1 α Hα ((α ~ dbind_tvar) ++ Γ0) eq_refl) ].
  - (* sd-AbsAnnoCheck (→) *)
    rewrite <- (a_tyequiv_denv_eq (denv_to_aenv Γ0) A A' H0 Γ0 eq_refl).
    apply d_sd_typing__abs_anno_check_base with (L := L);
      [ exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H Γ0 eq_refl)
      | assumption
      | intros x Hx; exact (H3 x Hx ((x ~ dbind_typ A) ++ Γ0) eq_refl) ].
  - (* sd-Abs *) apply d_sd_typing__abs with (L := L);
      [ assumption
      | exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H0 Γ0 eq_refl)
      | assumption
      | intros x Hx; exact (H3 x Hx ((x ~ dbind_typ A) ++ Γ0) eq_refl) ].
  - (* sd-AbsAnno *)
    apply d_sd_typing__abs_anno with (L := L);
      [ assumption
      | exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H0 Γ0 eq_refl)
      | rewrite H2; symmetry;
        exact (a_tyequiv_denv_eq (denv_to_aenv Γ0) A A' H1 Γ0 eq_refl)
      | assumption
      | intros x Hx; exact (H5 x Hx ((x ~ dbind_typ A) ++ Γ0) eq_refl) ].
  - (* sd-App *)
    assert (HA2 : btyp_to_ptyp B1 = A2)
      by exact (a_tyequiv_denv_eq (denv_to_aenv Γ0) (btyp_to_ptyp B1) A2
                  H2 Γ0 eq_refl).
    apply d_sd_typing__app with (P := P) (B1 := B1);
      [ exact (ad_pat_to_d mode_tc (denv_to_aenv Γ0) e2
                 (pskl_to_bskl_syn P) H Γ0 eq_refl)
      | exact (ad_refine_syn_to_d (denv_to_aenv Γ0) empty
                 (pskl_to_bskl_inh P) (btyp_to_bskl B1) H0 Γ0 eq_refl)
      | exact (IHad_sd_typing1 Γ0 eq_refl)
      | rewrite HA2; exact (IHad_sd_typing2 Γ0 eq_refl) ].
Qed.

(* ===================================================================== *)
(*  §11  CLOSING OFF THE RUN'S OUTPUT CONTEXT.                            *)
(*                                                                        *)
(*  Soundness delivers its declarative derivation at the run's OUTPUT     *)
(*  context Θ1, which normally still holds flexibles — [fun x -> x] at    *)
(*  the empty context returns [α̂ → α̂] with [Θ1 = α̂].  §0-§10 need a       *)
(*  flexible-FREE context, so the flexibles must first be instantiated:   *)
(*  the run started at [·], so [Θ1] is a pure SUFFIX and every one of its *)
(*  entries can be solved into its own tail ([solves_flex_of_wf_head]).   *)
(*  Peeling the suffix with [ad_sd_typing_subst_mid] and accumulating the *)
(*  solutions gives a metasubstitution [ζ ∷ Θ1 ⊑ ·] together with the     *)
(*  derivation at [·] — which is also, and independently, a proof that a  *)
(*  closing metasubstitution EXISTS, so the corollary is not vacuous.     *)
(*                                                                        *)
(*  ⚙ [msubst_btyp] had no facts anywhere before this section — it is     *)
(*  DEFINED in algo/def_meta.v and was used by no proof — so the three    *)
(*  below are its only home.                                              *)
(* ===================================================================== *)

Lemma msubst_btyp_nil : forall B, msubst_btyp nil B = B.
Proof. induction B; simpl; congruence. Qed.

Lemma msubst_btyp_ptyp_to_btyp_syn : forall ζ A,
  msubst_btyp ζ (ptyp_to_btyp_syn A) = ptyp_to_btyp_syn (msubst_ptyp ζ A).
Proof. induction A; simpl; congruence. Qed.

(** [ζ] instantiates every variable by a MONOTYPE.  Needed for the INHERITED
    painting only: [msubst_btyp] paints an image SYNTHESISED, and a monotype
    is the one shape whose two paintings coincide. *)
Definition msubst_mono (ζ : metasubst) : Prop :=
  forall α, mono_ptyp (msubst_lookup ζ α).

Lemma msubst_btyp_ptyp_to_btyp_inh : forall ζ A,
  msubst_mono ζ ->
  msubst_btyp ζ (ptyp_to_btyp_inh A) = ptyp_to_btyp_inh (msubst_ptyp ζ A).
Proof.
  intros ζ A Hm. induction A; simpl; try congruence.
  symmetry. apply ptyp_to_btyp_inh_mono_syn. apply Hm.
Qed.

Lemma msubst_btyp_cons_subst : forall ζ β τ B,
  msubst_btyp ((β, msubst_ptyp ζ τ) :: ζ) B
  = msubst_btyp ζ (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) β B).
Proof.
  intros ζ β τ B. induction B; try (simpl; congruence).
  (* the only interesting case: a free variable, where the two [if]s test
     the same atoms through DIFFERENT decision procedures ([==] in
     [msubst_lookup], lngen's [eq_var] in [subst_btyp_in_btyp]) *)
  cbn [subst_btyp_in_btyp]. destruct (α == β) as [ Heq | Hne ].
  - subst α. destruct (eq_var β β) as [ _ | Hc ]; [ | contradiction ].
    cbn [msubst_btyp]. rewrite msubst_lookup_cons_eq.
    symmetry. apply msubst_btyp_ptyp_to_btyp_syn.
  - destruct (eq_var α β) as [ Hc | _ ]; [ contradiction | ].
    cbn [msubst_btyp]. rewrite msubst_lookup_cons_neq by exact Hne.
    reflexivity.
Qed.

(** …and every type variable of [Θ] by a CLOSED one. *)
Definition msubst_closes (ζ : metasubst) (Θ : aenv) : Prop :=
  forall α, a_binds_tvar α Θ -> a_wf_ptyp nil (msubst_lookup ζ α).

Lemma a_binds_tvar_strengthen_cons : forall α β b Θ,
  α <> β -> a_binds_tvar α ((β ~ b) ++ Θ) -> a_binds_tvar α Θ.
Proof.
  intros α β b Θ Hne [ Hb | [ Hb | [τ Hb] ] ]; simpl in Hb;
    (destruct Hb as [ Heq | Hb ];
     [ inversion Heq; subst; contradiction | ]);
    [ left | right; left | right; right; exists τ ]; exact Hb.
Qed.

Lemma msubst_closes_ptyp : forall ζ Θ τ,
  msubst_mono ζ -> msubst_closes ζ Θ -> a_wf_ptyp Θ τ -> mono_ptyp τ ->
  mono_ptyp (msubst_ptyp ζ τ) /\ a_wf_ptyp nil (msubst_ptyp ζ τ).
Proof.
  intros ζ Θ τ Hmo Hc Hwf Hm. revert Hwf. induction Hm; intros Hwf; simpl.
  - split; [ apply mono_ptyp__unit | apply a_wf_ptyp__unit ].
  - inversion Hwf; subst.
    match goal with Hb : a_binds_tvar _ _ |- _ => exact (conj (Hmo _) (Hc _ Hb)) end.
  - inversion Hwf; subst.
    match goal with
    | Hw1 : a_wf_ptyp _ A1, Hw2 : a_wf_ptyp _ A2 |- _ =>
        destruct (IHHm1 Hw1) as [Hm1' Hw1']; destruct (IHHm2 Hw2) as [Hm2' Hw2']
    end.
    split; [ apply mono_ptyp__arrow | apply a_wf_ptyp__arrow ]; assumption.
Qed.

Lemma msubst_mono_nil : msubst_mono nil.
Proof. intros α. simpl. apply mono_ptyp__var. Qed.

Lemma msubst_mono_cons : forall ζ β σ,
  msubst_mono ζ -> mono_ptyp σ -> msubst_mono ((β, σ) :: ζ).
Proof.
  intros ζ β σ Hmo Hm α. simpl.
  destruct (α == β) as [ -> | Hne ]; [ exact Hm | apply Hmo ].
Qed.

Lemma msubst_closes_cons : forall ζ Θ β b σ,
  msubst_closes ζ Θ -> a_wf_ptyp nil σ ->
  msubst_closes ((β, σ) :: ζ) ((β ~ b) ++ Θ).
Proof.
  intros ζ Θ β b σ Hc Hw α Ha. simpl.
  destruct (α == β) as [ -> | Hne ]; [ exact Hw | ].
  apply Hc. exact (a_binds_tvar_strengthen_cons α β b Θ Hne Ha).
Qed.

Lemma a_inc_nil_suffix : forall κ Θ, κ ∷ nil ⊑ Θ -> a_suffix Θ.
Proof. intros κ Θ H. inversion H; subst. assumption. Qed.

(** ⭐ THE CLOSING.  Every entry of a well-formed suffix is solvable into its
    own tail, so peeling it top-down instantiates the whole context at once. *)
Lemma ad_sd_typing_close_suffix : forall Ξ,
  a_suffix Ξ -> {{ ⊢ Ξ }}a ->
  forall M e B, ad_sd_typing M Ξ e B ->
  ftvar_in_exp e [<=] empty ->
  exists ζ, ζ ∷ Ξ ⊑ nil /\ msubst_mono ζ /\ msubst_closes ζ Ξ
         /\ ad_sd_typing M nil e (msubst_btyp ζ B).
Proof.
  induction Ξ as [ | [β b] Ξ' IH ]; intros Hsuf Hwf M e B Hd He.
  - exists nil. repeat split.
    + apply a_inc__empty. apply a_suffix__nil.
    + apply msubst_mono_nil.
    + intros α [ Hb | [ Hb | [τ Hb] ] ]; contradiction.
    + rewrite msubst_btyp_nil. exact Hd.
  - inversion Hsuf as [ | ? ? ? Hsuf' Hbind ]; subst.
    simpl_env in Hwf.
    destruct (solves_flex_of_wf_head Hbind Hwf) as [τs Hs].
    assert (Hwf' : {{ ⊢ Ξ' }}a) by (inversion Hwf; subst; assumption).
    assert (Hβd : β `notin` dom Ξ') by (inversion Hwf; subst; assumption).
    pose proof (@ad_sd_typing_subst_mid _ _ _ _ Hd τs β b nil Ξ'
                  ltac:(simpl_env; reflexivity) Hs
                  ltac:(simpl_env; apply a_wf_aenv_uniq; exact Hwf)) as Hx.
    simpl_env in Hx.
    assert (Hdd : ftvar_in_aenv Ξ' [<=] dom Ξ')
      by (apply a_wf_aenv_ftv_dom; exact Hwf').
    rewrite subst_aenv_fresh_eq in Hx by (clear - Hβd Hdd; fsetdec).
    rewrite subst_ptyp_in_exp_fresh_eq in Hx by (clear - He; fsetdec).
    destruct (IH Hsuf' Hwf' M e _ Hx He) as [ζ' [Hinc' [Hmo' [Hcl' Htd]]]].
    assert (Hmw : mono_ptyp (msubst_ptyp ζ' τs)
                  /\ a_wf_ptyp nil (msubst_ptyp ζ' τs))
      by (eapply msubst_closes_ptyp;
            [ exact Hmo' | exact Hcl' | eapply solves_flex_wf; exact Hs
            | eapply solves_flex_mono; exact Hs ]).
    destruct Hmw as [Hmono Hwfc].
    exists ((β, msubst_ptyp ζ' τs) :: ζ'). repeat split.
    + destruct Hs as [_ [_ [_ [Hb | Hb]]]]; subst b;
        [ apply a_inc__flex; assumption
        | apply a_inc__flex_def;
            [ assumption | assumption | assumption
            | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmono ] ].
    + apply msubst_mono_cons; assumption.
    + apply msubst_closes_cons; assumption.
    + rewrite msubst_btyp_cons_subst. exact Htd.
Qed.

(* ===================================================================== *)
(*  §12  THE COMPLETENESS DIRECTION: how far it reaches, and where it     *)
(*  stops.                                                                *)
(*                                                                        *)
(*  ⚠️ [paper-gap] The [d_] → [ad_] direction — what a completeness        *)
(*  corollary stated over [d_sd_typing] would need — is NOT closed.  Two  *)
(*  obstructions were recorded here; ⭐ (B) IS NOW GONE (2026-08-11), so   *)
(*  what remains is (A) alone:                                            *)
(*                                                                        *)
(*  (A) THE LEAF-VALID DATUM.  [ad_pat] / [ad_sd_typing] embed            *)
(*      [ad_pat_sub_v], whose consistency leaves additionally carry the   *)
(*      subject's refinement [{{ Θ ⨟ ∅ ⊢ᵣₚ ⌊R⌋ˢ ⊳ ⌊Q⌋ }}ad]; [d_pat] /    *)
(*      [d_sd_typing] embed the PLAIN join, from which the datum is not   *)
(*      recoverable in general — the capture configuration (subject       *)
(*      [∀X.◇], counterpart [∀ˢX.X]) has a plain join and provably no     *)
(*      leaf-valid one (cex/cex_ad_pat_join_not_leaf_valid.v).            *)
(*      ⭐ [d_pat_consis_subject_refine_ghost_free] below settles the      *)
(*      OPEN half of that question: at a GHOST-FREE subject the datum IS  *)
(*      derivable, from consistency alone.  Since [ad_sd_typing]'s three  *)
(*      base rows join [ptyp_to_uskl_syn A] — the painting of a [ptyp],   *)
(*      which has no ghosts — TYPING's own base rows are never the        *)
(*      obstruction.  What is left is exactly [ad_pat]'s P-Var at a       *)
(*      SKELETON entry [x : P] with a ghost under a ∀, which [ad_pat__abs]*)
(*      may introduce with any well-formed [P] and which [d_sd_typing]    *)
(*      reaches through its App rule's [d_pat] premise.                   *)
(*                                                                        *)
(*  (B) TAG HYGIENE — ✅ RESOLVED 2026-08-11, and it used to be the       *)
(*      DEEPER of the two.  The paper's prose "fresh Ψ'" means GLOBAL     *)
(*      freshness (fresh from the SUBJECT's syntactic tags, not only from *)
(*      the tag context — the two come apart at the Arrow split, and      *)
(*      precision-substitution is FALSE over the weak reading).  Only the *)
(*      fuel mirrors used to say so; now [d_sub], [d_pat_sub] and         *)
(*      [ad_pat_sub] carry the same premise, so both sorts line up and    *)
(*      the [ad_pat_sub_sk_to_d] / [ad_pat_sub_ty_to_d] rows above        *)
(*      transport it verbatim (across the sorts via [ftag_utyp_to_uskl]). *)
(*      What paid for it: decl/prop_tag_swap.v §4-§5 — collect a         *)
(*      derivation's instantiation tags into ONE bound, then move them    *)
(*      wholesale by transposition — which is what CST                    *)
(*      ([d_consis_sub_trans_mid]) needs, its ForallL case transporting   *)
(*      along [utyp_tag_refines] where the subject GAINS tags.            *)
(*      ⚠️ WHAT IS STILL OWED in this neighbourhood is a FUEL question,    *)
(*      not a hygiene one: [ad_pat_sub] → [ad_pat_sub_fuel].                *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §13  THE LEAF-VALID UPGRADE.                                          *)
(*                                                                        *)
(*  ⚙ RETIRED 2026-08-12.  This section used to hold [ad_pat_sub_ty_to_v], *)
(*  which upgraded a plain join to the leaf-valid one at [N = TY] over a   *)
(*  DECLARATIVE context and a GHOST-FREE subject — three hypotheses it     *)
(*  needed only because it had to RECOVER the leaf datum at every leaf     *)
(*  ([d_pat_consis_subject_refine_closed]), and the SK sort was left open  *)
(*  (obstruction (A) of docs/HANDOFF-closed-corollaries-declarative.md).   *)
(*                                                                        *)
(*  ⭐ ALL THREE HYPOTHESES ARE GONE, and with them the obstruction: since  *)
(*  [ad_pat_sub] carries the leaf presupposition itself, the datum is a    *)
(*  PREMISE of the row that needs it, and the upgrade is                   *)
(*  [ad_pat_sub_to_fuel] (algo/sub/prop_soundness_subtag.v) — UNCONDITIONAL, at  *)
(*  either sort, over any Θ.  Only the fuel is left to collect.            *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §14  THE OTHER DIRECTION AT THE TYPE SORT:  [d_sub] -> [ad_pat_sub].  *)
(*                                                                        *)
(*  ⚙ §8 goes [ad] -> [d] by RETRACTING [uskl_to_utyp], which needs the   *)
(*  subject ghost-free at every step.  This direction uses the INCLUSION  *)
(*  [utyp_to_uskl] instead, so nothing has to be recovered: a [utyp] has  *)
(*  no ghost slot to begin with, and every side condition the algorithmic *)
(*  rule adds over the declarative one is discharged by transporting the  *)
(*  declarative premise along the inclusion.                              *)
(* ===================================================================== *)

(** ⚠️ [lc_utyp] is not decoration: [uskl_ghost_free] has no [uskl_var_b] row,
    so it fails outright on an open body — the inclusion of a [utyp] is
    ghost-free exactly when the [utyp] is locally closed. *)
Lemma uskl_ghost_free_incl : forall C,
  lc_utyp C -> uskl_ghost_free (utyp_to_uskl C).
Proof.
  intros C H; induction H; simpl; try solve [ constructor ].
  - apply uskl_ghost_free__arrow; assumption.
  - apply uskl_ghost_free__all_syn with (L := empty). intros α _.
    rewrite <- utyp_to_uskl_open_var. auto.
  - apply uskl_ghost_free__all_tag with (L := empty). intros α _.
    rewrite <- utyp_to_uskl_open_var. auto.
Qed.

Lemma is_sskl_of_is_styp : forall B, is_styp B -> is_sskl (btyp_to_bskl B).
Proof.
  intros B H; induction H; simpl; try solve [ constructor; auto ].
  apply is_sskl__all with (L := L). intros α Hα.
  change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
  rewrite <- btyp_to_bskl_open. auto.
Qed.

Lemma guarded_uskl_incl : forall C,
  guarded_utyp C -> guarded_uskl (utyp_to_uskl C).
Proof.
  intros C H; inversion H; subst; simpl;
    [ apply guarded_uskl__unit | apply guarded_uskl__var
    | apply guarded_uskl__arrow; apply lc_utyp_to_uskl; assumption ].
Qed.

Lemma d_tags_skl_incl : forall Ψ C,
  d_tags Ψ C -> d_tags_skl Ψ (utyp_to_uskl C).
Proof.
  intros Ψ C H; induction H; simpl.
  - apply d_tags_skl__unit; assumption.
  - apply d_tags_skl__var; assumption.
  - apply d_tags_skl__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
  - apply d_tags_skl__all_tag with (L := L) (Ψ0 := Ψ0);
      [ | assumption | assumption ].
    intros α Hα. rewrite <- utyp_to_uskl_open_var. auto.
Qed.

(** Both well-scopedness judgements push a ∀-bound variable into Γ (the
    skeleton one ALSO into Δ, which only the ∀◇ rule reads, and the
    inclusion of a [utyp] has no ∀◇), so the transport only needs every tvar
    of the source context to be a tvar of the target, at any Δ. *)
Lemma d_wf_uskl_incl_gen : forall Γ C,
  d_wf_utyp Γ C ->
  forall Γ' Δ,
    (forall α, binds α dbind_tvar Γ -> binds α dbind_tvar Γ') ->
    d_wf_uskl Γ' Δ (utyp_to_uskl C).
Proof.
  intros Γ C H; induction H; intros Γ' Δ0 Hvis; simpl.
  - apply d_wf_uskl__unit.
  - apply d_wf_uskl__var. apply Hvis; assumption.
  - apply d_wf_uskl__arrow;
      [ apply IHd_wf_utyp1 | apply IHd_wf_utyp2 ]; exact Hvis.
  - apply d_wf_uskl__all_syn with (L := L). intros α Hα.
    rewrite <- utyp_to_uskl_open_var. apply (H0 α Hα).
    intros β Hb. apply binds_app_iff in Hb. apply binds_app_iff.
    destruct Hb as [ Hb | Hb ]; [ left; exact Hb | right; apply Hvis, Hb ].
  - apply d_wf_uskl__all_tag with (L := L) (ε := ε). intros α Hα.
    rewrite <- utyp_to_uskl_open_var. apply (H0 α Hα).
    intros β Hb. apply binds_app_iff in Hb. apply binds_app_iff.
    destruct Hb as [ Hb | Hb ]; [ left; exact Hb | right; apply Hvis, Hb ].
Qed.

Lemma d_wf_uskl_incl : forall Γ C,
  d_wf_utyp Γ C -> d_wf_uskl Γ empty (utyp_to_uskl C).
Proof.
  intros Γ C H. apply (d_wf_uskl_incl_gen Γ C H Γ empty).
  intros α Hb. exact Hb.
Qed.


Lemma lc_pskl_of_lc_btyp : forall B,
  lc_btyp B -> lc_pskl (bskl_to_pskl (btyp_to_bskl B)).
Proof.
  intros B H; induction H; simpl;
    try solve [ constructor; assumption ].
  - apply lc_pskl_all_syn. intro α.
    rewrite <- bskl_to_pskl_open.
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
    rewrite <- btyp_to_bskl_open. auto.
  - apply lc_pskl_all_syn. intro α.
    rewrite <- bskl_to_pskl_open.
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
    rewrite <- btyp_to_bskl_open. auto.
Qed.

(** An INHERITED [btyp] paints as an inherited [pskl]: every ∀ it has is
    [btyp_all_inh], and [pskl_to_bskl_inh] paints every ∀ that way. *)
Lemma inh_paint_bskl : forall B,
  is_ityp B ->
  btyp_to_bskl B = pskl_to_bskl_inh (bskl_to_pskl (btyp_to_bskl B)).
Proof.
  intros B H; induction H; simpl; try reflexivity.
  - f_equal; assumption.
  - (* ⚙ the ∀ row's binder is the RULE's [A], not the statement's [B] *)
    f_equal.
    pick fresh α for (L `union` ftvar_in_btyp A
                      `union` ftvar_in_bskl
                                (pskl_to_bskl_inh
                                   (bskl_to_pskl (btyp_to_bskl A)))).
    apply open_bskl_wrt_bskl_inj with (α1 := α);
      [ rewrite ftvar_btyp_to_bskl; clear - Fr; fsetdec
      | clear - Fr; fsetdec | ].
    (* push the opening through the two paintings on the RIGHT, then the
       goal IS the cofinite hypothesis *)
    rewrite <- pskl_to_bskl_inh_open, <- bskl_to_pskl_open.
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
    rewrite <- btyp_to_bskl_open.
    exact (H0 α ltac:(clear - Fr; fsetdec)).
Qed.

(** [Check]'s target on the [ad] side is spelt [inh{B'}] for a [pskl] [B'];
    an INHERITED, GUARDED [btyp] is exactly such a painting. *)
Lemma guarded_ityp_inh_paint : forall B,
  is_ityp B -> guarded_btyp B ->
  btyp_to_bskl B = pskl_to_bskl_inh (bskl_to_pskl (btyp_to_bskl B))
  /\ guarded_pskl (bskl_to_pskl (btyp_to_bskl B)).
Proof.
  intros B Hi Hg. split; [ apply inh_paint_bskl; exact Hi | ].
  inversion Hg; subst; simpl;
    [ apply guarded_pskl__unit | apply guarded_pskl__var
    | apply guarded_pskl__arrow; apply lc_pskl_of_lc_btyp; assumption ].
Qed.

(** ⭐ THE TY-SORT BRIDGE, [d] -> [ad].  Every premise the algorithmic rule
    adds is the declarative one pushed along [utyp_to_uskl]: the hygiene by
    [ftag_utyp_to_uskl] (the inclusion keeps every tag), the ForallL
    instantiation's sort data by [is_tskl_utyp_to_uskl] / [d_tags_skl_incl] /
    [uskl_ghost_free_incl] — the last of which is what [a_tags_sort__ty]
    demands and what makes this sort easy. *)
(** ⭐ THE LEAF PRESUPPOSITION AT THE TY SORT IS REFLEXIVITY.  [ad_pat_sub]
    demands the refinement at every consistency leaf (2026-08-12), and at
    [N = TY] it costs nothing: consistency preserves the plain erasure
    ([d_consis_btyp_erase]) and both sort inclusions agree with it
    (prop_coercions.v), so the two sides of the refinement are the SAME
    skeleton and [ad_refine_pskl_refl] closes it.

    ⚙ Its scope premise is the paper's usual EXTERNAL well-formedness
    (docs/WF-SIDE-CONDITIONS.md): [ad_refine_pskl_refl] is stated under the
    paper's presupposition that the refined skeleton is well-formed, and
    [d_sub] states no well-formedness of its own. *)
Lemma d_consis_refine_ty : forall Ψ Γ C B,
  {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
  {{ (denv_to_aenv Γ) ⨟ empty ⊢ₚₛ (uskl_to_pskl (utyp_to_uskl C)) }}a ->
  {{ (denv_to_aenv Γ) ⨟ empty ⊢ᵣₚ (uskl_to_pskl (utyp_to_uskl C))
     ⊳ (bskl_to_pskl (btyp_to_bskl B)) }}ad.
Proof.
  intros Ψ Γ C B Hc Hwf.
  rewrite bskl_to_pskl_btyp_to_bskl.
  rewrite <- (d_consis_btyp_erase Hc).
  rewrite <- uskl_to_pskl_utyp_to_uskl.
  apply ad_refine_pskl_refl; exact Hwf.
Qed.

(** The SCOPE side condition of [d_consis_refine_ty], in the shape every leaf
    row hands it: a well-scoped [utyp] is a well-scoped [pskl] once pushed
    along the two sort inclusions (at [Δ = ∅] on both). *)
Lemma a_wf_pskl_of_d_wf_utyp : forall Γ C,
  d_wf_utyp Γ C ->
  {{ (denv_to_aenv Γ) ⨟ empty ⊢ₚₛ (uskl_to_pskl (utyp_to_uskl C)) }}a.
Proof.
  intros Γ C H.
  exact (a_wf_pskl_of_d_wf_uskl Γ empty (utyp_to_uskl C)
           (d_wf_uskl_incl Γ C H)).
Qed.

(** ⭐ THE TYPE SORT HAS NO DECLARATIVE JOIN OF ITS OWN: [d_consis] carries no
    refinement datum (there are no holes at the type sort, so there is nothing
    for refinement to fill).  The bridge MANUFACTURES the [ad] half — the
    refinement is REFLEXIVE at a type, given scope — so the join is
    [d_consis_to_ad] paired with [d_consis_refine_ty].  This is the one place
    in the tree where a join is built from a consistency that did not come
    with one. *)
Lemma d_consis_join_ty : forall Ψ Γ C B,
  {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
  {{ (denv_to_aenv Γ) ⨟ empty ⊢ₚₛ (uskl_to_pskl (utyp_to_uskl C)) }}a ->
  {{ Ψ ⨟ (denv_to_aenv Γ) ⊢ˢ (utyp_to_uskl C) ∼ᵣ (btyp_to_bskl B) }}ad.
Proof.
  intros Ψ Γ C B Hc Hwf. split.
  - apply d_consis_to_ad; assumption.
  - eapply d_consis_refine_ty; eassumption.
Qed.

(** ⚙ The [d_wf_utyp] premise is new with the leaf presupposition
    (2026-08-12): §14's leaf rows now owe the refinement, and
    [d_consis_refine_ty] discharges it by reflexivity given SCOPE.  It is the
    paper's usual external well-formedness, and the one call site
    ([base_row] below) has it — its subjects are paintings. *)
Lemma d_sub_to_ad : forall M Ψ Γ C B,
  d_sub M Ψ Γ C B ->
  d_wf_utyp Γ C ->
  ad_pat_sub a_sub_mode_ty M Ψ (denv_to_aenv Γ)
    (utyp_to_uskl C) (btyp_to_bskl B).
Proof.
  intros M Ψ Γ C B H; induction H; intros Hwf; simpl.
  - (* infer *) apply ad_pat_sub__infer;
      [ assumption
      | eapply d_consis_join_ty;
          [ eassumption | apply a_wf_pskl_of_d_wf_utyp; assumption ]
      | apply is_sskl_of_is_styp; assumption ].
  - (* check *)
    destruct (guarded_ityp_inh_paint B ltac:(assumption) ltac:(assumption))
      as [ Heq Hgp ].
    (* ⚙ the rule's [pskl] target is [bskl_to_pskl (btyp_to_bskl B)], which is
       ALSO what [d_consis_refine_ty] concludes over — so the leaf premise is
       that lemma verbatim, with no retraction step. *)
    rewrite Heq. apply ad_pat_sub__check;
      [ apply guarded_uskl_incl; assumption | exact Hgp | ].
    apply ad_consis_join_inh_intro.
    + rewrite <- Heq. apply d_consis_to_ad; assumption.
    + eapply d_consis_refine_ty;
        [ eassumption | apply a_wf_pskl_of_d_wf_utyp; assumption ].
  - (* forall_r *)
    apply ad_pat_sub__forall_r with (L := L `union` dom Γ). intros α Hα.
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
    rewrite <- btyp_to_bskl_open.
    apply H1; [ clear - Hα; fsetdec
              | apply (d_wf_utyp_weakening_head ((α ~ dbind_tvar) ++ nil)); assumption ].
  - (* arg *)
    inversion Hwf; subst.
    apply ad_pat_sub__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ eapply d_consis_join_ty;
          [ eassumption | apply a_wf_pskl_of_d_wf_utyp; assumption ]
      | apply IHd_sub; assumption
      | assumption ].
  - (* forall_l, tagged *)
    apply ad_pat_sub__forall_l_tagged with
      (Ψ' := Ψ') (ψ := utyp_to_uskl ph);
      [ assumption | assumption
      | (* the hygiene crosses the sorts: the inclusion keeps every tag *)
        rewrite (ftag_utyp_to_uskl (utyp_all_tag ε C)); assumption
      | apply a_tags_sort__ty;
          [ apply is_tskl_utyp_to_uskl; assumption
          | apply d_tags_skl_incl; assumption
          | apply uskl_ghost_free_incl; eapply d_wf_utyp_lc; eassumption ]
      | exact (a_wf_pskl_of_d_wf_uskl Γ empty (utyp_to_uskl ph)
                 (d_wf_uskl_incl Γ ph ltac:(assumption)))
      | rewrite <- utyp_to_uskl_open; apply IHd_sub;
        inversion Hwf; subst; eapply d_wf_utyp_open; eassumption ].
  - (* forall_l, untagged *)
    apply ad_pat_sub__forall_l_untagged with
      (Ψ' := Ψ') (ψ := utyp_to_uskl ph);
      [ assumption | assumption
      | rewrite (ftag_utyp_to_uskl (utyp_all_syn C)); assumption
      | apply a_tags_sort__ty;
          [ apply is_tskl_utyp_to_uskl; assumption
          | apply d_tags_skl_incl; assumption
          | apply uskl_ghost_free_incl; eapply d_wf_utyp_lc; eassumption ]
      | exact (a_wf_pskl_of_d_wf_uskl Γ empty (utyp_to_uskl ph)
                 (d_wf_uskl_incl Γ ph ltac:(assumption)))
      | rewrite <- utyp_to_uskl_open; apply IHd_sub;
        inversion Hwf; subst; eapply d_wf_utyp_open; eassumption ].
Qed.

(* ===================================================================== *)
(*  §15  THE TYPING BRIDGE, [d_sd_typing] -> [ad_sd_typing], REDUCED TO   *)
(*  SKELETON INFERENCE.                                                   *)
(*                                                                        *)
(*  ⭐ Every rule but App goes through.  What the algorithmic rules ask    *)
(*  for beyond the declarative ones is:                                   *)
(*   - the LEAF-VALID join, which §13-§14 supply at [N = TY];             *)
(*   - the appendix's four type-EQUIVALENCE premises, which are           *)
(*     [a_tyequiv__refl] over a flexible-free Θ (§1) and so need only     *)
(*     [lc_ptyp] — [d_sd_typing_target_lc], decl/prop_syntax_directed.v;  *)
(*   - [a_wf_ptyp Θ A] on [sd-Anno].  ⚠️ [d_sd_typing__anno] states NO     *)
(*     well-formedness (its four type-carrying siblings do), so this one  *)
(*     is NOT recoverable from the derivation.  It is carried as the      *)
(*     paper's ambient "all inputs are well-formed", in exactly the shape *)
(*     the [ad] side EXHIBITS ([ad_sd_typing_wf_exp]).                    *)
(*     docs/WF-SIDE-CONDITIONS.md.                                        *)
(*                                                                        *)
(*  ⭐ STATED OVER AN ARBITRARY Γ, deliberately.  At [Γ = ·] both side     *)
(*  conditions above are free, so a closed-only statement would hide      *)
(*  them — and the [sd-Anno] one is a real finding about the paper's      *)
(*  §declarative figure, not bookkeeping.                                 *)
(*                                                                        *)
(*  ⭐ App WAS THE ONE HOLE, and it is now closed.  It used to carry the    *)
(*  pointwise [d_pat] -> [ad_pat] bridge as a HYPOTHESIS, which is FALSE   *)
(*  (cex/cex_d_pat_bridges_false.v at commit 09a1f0b) — so the lemma it    *)
(*  guarded was vacuous.  What made the bridge false was the mechanisation *)
(*  deferring the paper's presupposition on skeleton consistency; with     *)
(*  that presupposition on the rules (decl/def_rules.v, 2026-08-11) the    *)
(*  bridge is a rule-for-rule induction — [d_pat_to_ad] below.             *)
(* ===================================================================== *)

(** ⭐ THE BRIDGE THAT USED TO BE ASSUMED.  No hypothesis: with both of the
    paper's presuppositions on the rules, [d_pat]'s rows and [ad_pat]'s match
    one for one, and each premise crosses by the §0-§7 translations. *)
Lemma d_pat_to_ad : forall M Γ e Q,
  d_pat M Γ e Q -> ad_pat M (denv_to_aenv Γ) e Q.
Proof.
  intros M Γ e Q H; induction H.
  - (* P-Unit *) apply ad_pat__unit;
      [ exact (d_wf_pskl_to_a Γ empty (bskl_to_pskl Q) H)
      | apply d_pat_sub_to_ad; assumption ].
  - (* P-Var *) apply ad_pat__var with (P := P) (b := abind_of_dbind d);
      [ apply binds_denv_to_aenv; assumption
      | rewrite abind_to_pskl_of_dbind; assumption
      | exact (d_wf_pskl_to_a Γ empty (bskl_to_pskl Q) H1)
      | apply d_pat_sub_to_ad; assumption ].
  - (* P-Anno *) apply ad_pat__anno;
      [ exact (d_wf_ptyp_to_a Γ A H)
      | exact (d_wf_pskl_to_a Γ empty (bskl_to_pskl Q) H0)
      | apply d_pat_sub_to_ad; assumption ].
  - (* P-Freeze *) apply ad_pat__freeze; assumption.
  - (* P-Abs *) apply ad_pat__abs with (L := L);
      [ assumption
      | exact (d_wf_pskl_to_a Γ empty P H0)
      | assumption
      (* ⚙ the cofinite premise is [H2]; its IH — what we need — is [H3] *)
      | intros x Hx; exact (H3 x Hx) ].
  - (* P-AbsAnno *) apply ad_pat__abs_anno with (L := L) (B := B);
      [ assumption | exact (d_wf_ptyp_to_a Γ A H0) | assumption | assumption
      | intros x Hx; exact (H4 x Hx) ].
  - (* P-App *) apply ad_pat__app with (P := P) (Q1 := Q1);
      [ assumption
      | exact (d_refine_syn_to_ad Γ empty (pskl_to_bskl_inh P) Q1 H0)
      | assumption ].
  - (* P-AbsCheck *) apply ad_pat__abs_check with (L := L).
    intros x Hx; exact (H0 x Hx).
  - (* P-AbsAnnoCheck *) apply ad_pat__abs_anno_check with (L := L);
      [ exact (d_wf_ptyp_to_a Γ A H) | intros x Hx; exact (H1 x Hx) ].
Qed.

Lemma aenv_tbinds_le_weaken_cons : forall Θ x (b : abind),
  aenv_tbinds_le Θ ((x ~ b) ++ Θ).
Proof. intros Θ x b y c Hc Hy. apply binds_app_3; exact Hy. Qed.

(** The three base rows all read the same way: the embedded [d_sub] becomes an
    [ad_pat_sub] at the TY sort (§14), and its subject is a PAINTING, hence
    ghost-free — but that no longer matters: [ad_pat_sub_to_fuel] collects the
    fuel with no side condition at all (§13).

    ⚙ [wftac] is what §14's leaf presupposition costs here, and it costs
    nothing: the subject is the painting of a [ptyp] the row already has
    well-formed, so [d_wf_utyp_painting_syn] carries it across.  ⚙ The
    second tactic argument — the subject's LOCAL CLOSURE, which the retired
    ghost-freeness branch needed — went with §13. *)
Ltac base_row wftac :=
  (* ⚙ [ptyp_to_uskl_syn] is a Definition, so the goal never displays the
     [bskl_to_uskl (pskl_to_bskl_syn …)] form the coercion lemma rewrites *)
  unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn;
  rewrite <- utyp_to_uskl_ptyp_to_utyp_syn;
  apply d_sub_to_ad;
    [ eassumption | apply d_wf_utyp_painting_syn; wftac ].

Lemma d_sd_typing_to_ad : forall M Γ e B,
  d_sd_typing M Γ e B ->
  d_wf_denv Γ ->
  {{ (denv_to_aenv Γ) ⊢ᵉ e }}a ->
  ad_sd_typing M (denv_to_aenv Γ) e B.
Proof.
  intros M Γ e B H; induction H; intros Hwf Hwfe.
  - (* sd-Unit *)
    apply ad_sd_typing__unit.
    base_row ltac:(apply d_wf_ptyp__unit).
  - (* sd-Var *)
    apply ad_sd_typing__var with (A := A);
      [ apply binds_denv_to_aenv with (d := dbind_typ A); assumption | ].
    base_row ltac:(eapply d_wf_denv_binds_ptyp; eassumption).
  - (* sd-Anno: the annotation's wf is the AMBIENT hypothesis, not the rule's *)
    inversion Hwfe as [ | | Θ0 e0 A0 Hwfa Hwfe0 | | | | ]; subst.
    apply ad_sd_typing__anno with (A := A);
      [ exact Hwfa | apply IHd_sd_typing; assumption | ].
    base_row ltac:(eapply a_wf_ptyp_to_d; [ eassumption | reflexivity ]).
  - (* sd-Freeze: the appendix's equivalence premise is REFLEXIVITY here *)
    inversion Hwfe as [ | | | Θ0 e0 Hwfe0 | | | ]; subst.
    apply ad_sd_typing__freeze with (B := A);
      [ apply IHd_sd_typing; assumption
      | apply a_tyequiv__refl; apply lc_ptyp_of_lc_btyp_syn;
        eapply d_sd_typing_target_lc; eassumption ].
  - (* sd-AbsCheck (∀) *)
    apply ad_sd_typing__abs_check_step with (L := L `union` dom Γ);
      [ assumption | ].
    intros α Hα.
    exact (H1 α ltac:(clear - Hα; solve_notin_auto)
             ltac:(apply d_wf_denv__tvar;
                     [ exact Hwf | clear - Hα; solve_notin_auto ])
             ltac:(apply (a_wf_exp_mono Hwfe);
                   apply aenv_tbinds_le_weaken_cons)).
  - (* sd-AbsCheck (→) *)
    inversion Hwfe as [ | | | | L0 Θ0 e0 Hbody | | ]; subst.
    apply ad_sd_typing__abs_check_base
      with (L := L `union` L0 `union` dom Γ) (A := A);
      [ apply d_wf_ptyp_to_a; assumption | assumption | ].
    intros x Hx.
    exact (H2 x ltac:(clear - Hx; solve_notin_auto)
             ltac:(apply d_wf_denv__typ;
                     [ exact Hwf | clear - Hx; solve_notin_auto | assumption ])
             ltac:(apply (a_wf_exp_mono
                            (Hbody x ltac:(clear - Hx; solve_notin_auto)));
                   apply aenv_tbinds_le_weaken_cons)).
  - (* sd-AbsAnnoCheck (∀) *)
    apply ad_sd_typing__abs_anno_check_step with (L := L `union` dom Γ);
      [ assumption | ].
    intros α Hα.
    exact (H1 α ltac:(clear - Hα; solve_notin_auto)
             ltac:(apply d_wf_denv__tvar;
                     [ exact Hwf | clear - Hα; solve_notin_auto ])
             ltac:(apply (a_wf_exp_mono Hwfe);
                   apply aenv_tbinds_le_weaken_cons)).
  - (* sd-AbsAnnoCheck (→) *)
    inversion Hwfe as [ | | | | | L0 Θ0 A0 e0 Hwfa Hbody | ]; subst.
    apply ad_sd_typing__abs_anno_check_base
      with (L := L `union` L0 `union` dom Γ) (A := A);
      [ exact Hwfa
      | apply a_tyequiv__refl; eapply d_wf_ptyp_lc; eassumption
      | assumption | ].
    intros x Hx.
    exact (H2 x ltac:(clear - Hx; solve_notin_auto)
             ltac:(apply d_wf_denv__typ;
                     [ exact Hwf | clear - Hx; solve_notin_auto | assumption ])
             ltac:(apply (a_wf_exp_mono
                            (Hbody x ltac:(clear - Hx; solve_notin_auto)));
                   apply aenv_tbinds_le_weaken_cons)).
  - (* sd-Abs *)
    inversion Hwfe as [ | | | | L0 Θ0 e0 Hbody | | ]; subst.
    apply ad_sd_typing__abs with (L := L `union` L0 `union` dom Γ) (A := A);
      [ assumption | apply d_wf_ptyp_to_a; assumption | assumption | ].
    intros x Hx.
    exact (H3 x ltac:(clear - Hx; solve_notin_auto)
             ltac:(apply d_wf_denv__typ;
                     [ exact Hwf | clear - Hx; solve_notin_auto | assumption ])
             ltac:(apply (a_wf_exp_mono
                            (Hbody x ltac:(clear - Hx; solve_notin_auto)));
                   apply aenv_tbinds_le_weaken_cons)).
  - (* sd-AbsAnno *)
    inversion Hwfe as [ | | | | | L0 Θ0 A0 e0 Hwfa Hbody | ]; subst.
    (* ⚙ [subst] used [btyp_to_ptyp B1 = A] to eliminate [A] itself *)
    apply ad_sd_typing__abs_anno
      with (L := L `union` L0 `union` dom Γ)
           (A := btyp_to_ptyp B1) (A' := btyp_to_ptyp B1) (B1 := B1);
      [ assumption | exact Hwfa
      | apply a_tyequiv__refl; eapply d_wf_ptyp_lc; eassumption
      | reflexivity | assumption | ].
    intros x Hx.
    exact (H4 x ltac:(clear - Hx; solve_notin_auto)
             ltac:(apply d_wf_denv__typ;
                     [ exact Hwf | clear - Hx; solve_notin_auto | assumption ])
             ltac:(apply (a_wf_exp_mono
                            (Hbody x ltac:(clear - Hx; solve_notin_auto)));
                   apply aenv_tbinds_le_weaken_cons)).
  - (* sd-App: ⚠️ the ONE hole — its skeleton-inference premise *)
    inversion Hwfe as [ | | | | | | Θ0 e10 e20 Hwf1 Hwf2 ]; subst.
    apply ad_sd_typing__app with (P := P) (A2 := btyp_to_ptyp B1) (B1 := B1);
      [ exact (d_pat_to_ad mode_tc Γ e2 (pskl_to_bskl_syn P) H)
      | eapply d_refine_syn_to_ad; eassumption
      | apply IHd_sd_typing1; assumption
      | apply a_tyequiv__refl; apply lc_ptyp_btyp_to_ptyp;
        (* [lc_btyp B1] from the FUNCTION premise's arrow target *)
        match goal with
        | Hf : {{ _ ⊢ˢᵈ[ mode_fn _ ] _ ⦂ (btyp_arrow _ _) }}d |- _ =>
            let Ha := fresh "Ha" in
            assert (Ha : lc_btyp (btyp_arrow B1 B2))
              by (eapply d_sd_typing_target_lc; eassumption);
            inversion Ha; subst; assumption
        end
      | apply IHd_sd_typing2; assumption ].
Qed.
