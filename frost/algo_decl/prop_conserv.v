(** CONSERVATIVITY: the paper's declarative judgements over an algorithmic
    context Θ, at a FLEXIBLE-FREE Θ, are exactly the declarative judgements
    over the corresponding declarative context Γ.

    ⭐ WHAT THIS IS FOR.  Section D's four theorems are stated against the
    decl-in-algo layer ([ad_pat] / [ad_sd_typing], algo_decl/
    def_decl_algo_typing.v) because that is where the algorithm's output
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
    - the ∀-scope context Δ is an [atoms] on the [ad] side and a [list atom] on
      the [d] side; they are related by membership rather than converted (§0b).

    ⚙ WHY IT LIVES HERE.  It relates the DECLARATIVE system to the
    decl-in-algo one, and [algo_decl/] is where the decl-in-algo layer lives,
    so this is its home.  ⚠️ It was filed under [algo/typing/] when it was
    written, on the theory that needing [btyp_to_bskl_open]
    (algo/pat/prop_soundness_pat.v) and [guarded_pskl_lc]
    (algo/sub/prop_solve_sub.v) would invert the layering.  It does not: the
    DEFINITION layers point one way ([algo/def_*] -> [algo_decl/def_*] and
    [deco_algo/def_*], never back), while the PROOF layers already interleave —
    [deco_algo/prop_decorate_key.v] reaches into
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

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_general_subsumption.  (* mono_ptyp_inh_eq_syn *)
Require Import src.frost.decl.prop_wellformed.           (* d_wf_utyp_lc *)
Require Import src.frost.decl.prop_syntax_directed.       (* ftvar_btyp_to_bskl *)
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_decl_algo.
Require Import src.frost.algo_decl.def_decl_algo_sub.
Require Import src.frost.algo_decl.def_decl_algo_typing.
Require Import src.frost.algo_decl.prop_ctx_mono.   (* aenv_tbinds_le *)
Require Import src.frost.algo.prop_pat_sub.   (* uskl_ghost_free_open_gen *)
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import src.frost.algo.sub.prop_soundness_sub.
Require Import src.frost.algo.pat.prop_soundness_pat.
Require Import src.frost.algo.prop_suffix_erase.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_flex.

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

Lemma denv_to_aenv_cons : forall x d Γ,
  denv_to_aenv ((x ~ d) ++ Γ) = (x ~ abind_of_dbind d) ++ denv_to_aenv Γ.
Proof. reflexivity. Qed.

Lemma denv_to_aenv_dom : forall Γ, dom (denv_to_aenv Γ) [=] dom Γ.
Proof. induction Γ as [ | [x d] Γ' IH ]; simpl; fsetdec. Qed.

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
(*  §0b  THE ∀-SCOPE CONTEXT Δ.  It is an [atoms] on the [ad] side and a  *)
(*  [list atom] on the [d] side, so the two are related by MEMBERSHIP     *)
(*  rather than converted; every rule that touches Δ only ever ADDS one   *)
(*  atom or CLEARS it, and both operations respect the relation.          *)
(* ===================================================================== *)

Definition delta_agree (Δa : atoms) (Δd : list atom) : Prop :=
  forall α, α `in` Δa <-> List.In α Δd.

Lemma delta_agree_nil : delta_agree empty nil.
Proof. intros α. split; [ intros H; clear - H; fsetdec | contradiction ]. Qed.

Lemma delta_agree_cons : forall Δa Δd α,
  delta_agree Δa Δd -> delta_agree (add α Δa) (α :: Δd).
Proof.
  intros Δa Δd α H β. split.
  - intros Hin. destruct (β == α) as [ -> | Hne ]; [ left; reflexivity | ].
    right. apply H. clear - Hin Hne; fsetdec.
  - intros [ Heq | Hin ]; [ subst; clear; fsetdec | ].
    apply H in Hin. clear - Hin; fsetdec.
Qed.

#[local] Hint Resolve delta_agree_nil : core.

(** The Δ-vars as an ordinary tvar context — what the TYPE-sorted
    well-formedness [d_wf_utyp] wants, since its ∀ rule extends Γ where the
    skeleton-sorted one extends Δ. *)
Fixpoint tvars_denv (Δ : list atom) : denv :=
  match Δ with
  | nil => nil
  | α :: Δ' => (α ~ dbind_tvar) ++ tvars_denv Δ'
  end.

Lemma binds_tvars_denv : forall α Δ,
  List.In α Δ -> binds α dbind_tvar (tvars_denv Δ).
Proof.
  intros α Δ. induction Δ as [ | β Δ' IH ]; simpl; [ contradiction | ].
  intros [ Heq | Hin ]; [ subst; left; reflexivity | right; apply IH; exact Hin ].
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

Lemma a_wf_pskl_to_d : forall Θ Δa P,
  a_wf_pskl Θ Δa P ->
  forall Γ Δd, Θ = denv_to_aenv Γ -> delta_agree Δa Δd -> d_wf_pskl Γ Δd P.
Proof.
  intros Θ Δa P H; induction H; intros Γ0 Δd HΘ HΔ; subst.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [ HΔα | Hb ];
      [ left; apply HΔ; exact HΔα
      | right; apply a_binds_tvar_denv_to_aenv; exact Hb ].
  - apply d_wf_pskl__arrow;
      [ exact (IHa_wf_pskl1 Γ0 Δd eq_refl HΔ)
      | exact (IHa_wf_pskl2 Γ0 Δd eq_refl HΔ) ].
  - apply d_wf_pskl__all with (L := L). intros α Hα.
    exact (H0 α Hα Γ0 (α :: Δd) eq_refl (delta_agree_cons _ _ α HΔ)).
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole;
      [ exact H | exact (IHa_wf_pskl Γ0 nil eq_refl delta_agree_nil) ].
Qed.

Lemma d_wf_pskl_to_a : forall Γ Δd P,
  d_wf_pskl Γ Δd P ->
  forall Δa, delta_agree Δa Δd -> a_wf_pskl (denv_to_aenv Γ) Δa P.
Proof.
  intros Γ Δd P H; induction H; intros Δa HΔ.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. destruct H as [ HΔα | Hb ];
      [ left; apply HΔ; exact HΔα | right; apply a_binds_tvar_of_denv; exact Hb ].
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L). intros α Hα.
    exact (H0 α Hα (add α Δa) (delta_agree_cons _ _ α HΔ)).
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole;
      [ exact H | exact (IHd_wf_pskl empty delta_agree_nil) ].
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
      | exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty P H0 Γ0 nil eq_refl
                 delta_agree_nil) ].
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
      [ assumption | exact (d_wf_pskl_to_a Γ nil P H0 empty delta_agree_nil) ].
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

Lemma ad_refine_syn_to_d : forall Θ Δa Q P,
  ad_refine_syn Θ Δa Q P ->
  forall Γ Δd, Θ = denv_to_aenv Γ -> delta_agree Δa Δd -> d_refine_syn Γ Δd Q P.
Proof.
  intros Θ Δa Q P H; induction H; intros Γ0 Δd HΘ HΔ; subst.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [ HΔα | Hb ];
      [ left; apply HΔ; exact HΔα
      | right; apply a_binds_tvar_denv_to_aenv; exact Hb ].
  - apply d_refine_syn__arrow;
      [ exact (IHad_refine_syn1 Γ0 Δd eq_refl HΔ)
      | exact (IHad_refine_syn2 Γ0 Δd eq_refl HΔ) ].
  - apply d_refine_syn__all with (L := L). intros α Hα.
    exact (H0 α Hα Γ0 (α :: Δd) eq_refl (delta_agree_cons _ _ α HΔ)).
  - apply d_refine_syn__hole.
    exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty P H Γ0 nil eq_refl
             delta_agree_nil).
  - apply d_refine_syn__tophole_remove.
    exact (IHad_refine_syn Γ0 Δd eq_refl HΔ).
  - apply d_refine_syn__tophole_fill with (L := L). intros α Hα.
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) Δd eq_refl HΔ).
  - apply d_refine_syn__tophole_keep;
      [ assumption | exact (IHad_refine_syn Γ0 Δd eq_refl HΔ) ].
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
Qed.

Lemma d_refine_syn_to_ad : forall Γ Δd Q P,
  d_refine_syn Γ Δd Q P ->
  forall Δa, delta_agree Δa Δd -> ad_refine_syn (denv_to_aenv Γ) Δa Q P.
Proof.
  intros Γ Δd Q P H; induction H; intros Δa HΔ.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var. destruct H as [ HΔα | Hb ];
      [ left; apply HΔ; exact HΔα | right; apply a_binds_tvar_of_denv; exact Hb ].
  - apply ad_refine_syn__arrow; auto.
  - apply ad_refine_syn__all with (L := L). intros α Hα.
    exact (H0 α Hα (add α Δa) (delta_agree_cons _ _ α HΔ)).
  - apply ad_refine_syn__hole.
    exact (d_wf_pskl_to_a Γ nil P H empty delta_agree_nil).
  - apply ad_refine_syn__tophole_remove; auto.
  - apply ad_refine_syn__tophole_fill with (L := L). intros α Hα.
    exact (H0 α Hα Δa HΔ).
  - apply ad_refine_syn__tophole_keep; auto.
Qed.

(** ⭐ THE UNCOLOURED TWINS.  Same eight rows; needed because the paper's
    presupposition on skeleton consistency (declarative.tex:2074) is stated at
    the uncoloured sort, so it is [d_refine_pskl] / [ad_refine_pskl] that the
    subtyping rows now carry and that this file has to move across. *)
Lemma ad_refine_pskl_to_d : forall Θ Δa P Q,
  ad_refine_pskl Θ Δa P Q ->
  forall Γ Δd, Θ = denv_to_aenv Γ -> delta_agree Δa Δd -> d_refine_pskl Γ Δd P Q.
Proof.
  intros Θ Δa P Q H; induction H; intros Γ0 Δd HΘ HΔ; subst.
  - apply d_refine_pskl__unit.
  - apply d_refine_pskl__var. destruct H as [ HΔα | Hb ];
      [ left; apply HΔ; exact HΔα
      | right; apply a_binds_tvar_denv_to_aenv; exact Hb ].
  - apply d_refine_pskl__arrow;
      [ exact (IHad_refine_pskl1 Γ0 Δd eq_refl HΔ)
      | exact (IHad_refine_pskl2 Γ0 Δd eq_refl HΔ) ].
  - apply d_refine_pskl__all with (L := L). intros α Hα.
    exact (H0 α Hα Γ0 (α :: Δd) eq_refl (delta_agree_cons _ _ α HΔ)).
  - apply d_refine_pskl__hole.
    exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty Q H Γ0 nil eq_refl
             delta_agree_nil).
  - apply d_refine_pskl__tophole_remove.
    exact (IHad_refine_pskl Γ0 Δd eq_refl HΔ).
  - apply d_refine_pskl__tophole_fill with (L := L). intros α Hα.
    exact (H0 α Hα ((α ~ dbind_tvar) ++ Γ0) Δd eq_refl HΔ).
  - apply d_refine_pskl__tophole_keep;
      [ assumption | exact (IHad_refine_pskl Γ0 Δd eq_refl HΔ) ].
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
  - exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
Qed.

Lemma d_refine_pskl_to_ad : forall Γ Δd P Q,
  d_refine_pskl Γ Δd P Q ->
  forall Δa, delta_agree Δa Δd -> ad_refine_pskl (denv_to_aenv Γ) Δa P Q.
Proof.
  intros Γ Δd P Q H; induction H; intros Δa HΔ.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var. destruct H as [ HΔα | Hb ];
      [ left; apply HΔ; exact HΔα | right; apply a_binds_tvar_of_denv; exact Hb ].
  - apply ad_refine_pskl__arrow; auto.
  - apply ad_refine_pskl__all with (L := L). intros α Hα.
    exact (H0 α Hα (add α Δa) (delta_agree_cons _ _ α HΔ)).
  - apply ad_refine_pskl__hole.
    exact (d_wf_pskl_to_a Γ nil Q H empty delta_agree_nil).
  - apply ad_refine_pskl__tophole_remove; auto.
  - apply ad_refine_pskl__tophole_fill with (L := L). intros α Hα.
    exact (H0 α Hα Δa HΔ).
  - apply ad_refine_pskl__tophole_keep; auto.
Qed.

(** the two shapes the subtyping rows actually use: Δ empty on both sides *)
Lemma ad_refine_pskl_to_d_closed : forall Γ P Q,
  ad_refine_pskl (denv_to_aenv Γ) empty P Q -> d_refine_pskl Γ nil P Q.
Proof.
  intros Γ P Q H.
  exact (ad_refine_pskl_to_d (denv_to_aenv Γ) empty P Q H Γ nil eq_refl
           delta_agree_nil).
Qed.

Lemma d_refine_pskl_to_ad_closed : forall Γ P Q,
  d_refine_pskl Γ nil P Q -> ad_refine_pskl (denv_to_aenv Γ) empty P Q.
Proof.
  intros Γ P Q H. exact (d_refine_pskl_to_ad Γ nil P Q H empty delta_agree_nil).
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

Lemma lc_uskl_of_lc_pskl_erase : forall P,
  lc_pskl P -> forall R, P = uskl_to_pskl R -> lc_uskl R.
Proof.
  intros P H; induction H; intros R HR;
    destruct R; simpl in HR; try discriminate HR; inversion HR; subst;
    try solve [ constructor ].
  - apply lc_uskl_arrow; [ apply IHlc_pskl1 | apply IHlc_pskl2 ]; reflexivity.
  - apply lc_uskl_all_syn. intros α.
    apply (H0 α (open_uskl_wrt_uskl R (uskl_var_f α)));
      symmetry; apply uskl_to_pskl_open.
  - apply lc_uskl_all_tag. intros α.
    apply (H0 α (open_uskl_wrt_uskl R (uskl_var_f α)));
      symmetry; apply uskl_to_pskl_open.
  - apply lc_uskl_tophole. apply IHlc_pskl; reflexivity.
  - apply lc_uskl_topholeg. apply IHlc_pskl; reflexivity.
Qed.

Lemma guarded_uskl_of_guarded_pskl_erase : forall R,
  guarded_pskl (uskl_to_pskl R) -> guarded_uskl R.
Proof.
  intros R H; destruct R; simpl in H; inversion H; subst.
  - apply guarded_uskl__unit.
  - apply guarded_uskl__var.
  - apply guarded_uskl__arrow;
      [ apply (lc_uskl_of_lc_pskl_erase (uskl_to_pskl R1));
          [ assumption | reflexivity ]
      | apply (lc_uskl_of_lc_pskl_erase (uskl_to_pskl R2));
          [ assumption | reflexivity ] ].
Qed.

Lemma guarded_pskl_of_guarded_uskl_erase : forall R,
  guarded_uskl R -> guarded_pskl (uskl_to_pskl R).
Proof.
  intros R H; inversion H; subst; simpl;
    [ apply guarded_pskl__unit | apply guarded_pskl__var
    | apply guarded_pskl__arrow; apply lc_uskl_to_pskl; assumption ].
Qed.

Lemma d_wf_uskl_of_a_wf_pskl : forall Θ Δa P,
  a_wf_pskl Θ Δa P ->
  forall ψ, P = uskl_to_pskl ψ ->
  forall Γ Δd, Θ = denv_to_aenv Γ -> delta_agree Δa Δd -> d_wf_uskl Γ Δd ψ.
Proof.
  intros Θ Δa P H; induction H; intros ψ Hψ Γ0 Δd HΘ HΔ; subst;
    destruct ψ; simpl in Hψ; try discriminate Hψ.
  - apply d_wf_uskl__unit.
  - inversion Hψ; subst. apply d_wf_uskl__var.
    destruct H as [ HΔα | Hb ];
      [ left; apply HΔ; exact HΔα
      | right; apply a_binds_tvar_denv_to_aenv; exact Hb ].
  - inversion Hψ; subst. apply d_wf_uskl__arrow;
      [ exact (IHa_wf_pskl1 _ eq_refl Γ0 Δd eq_refl HΔ)
      | exact (IHa_wf_pskl2 _ eq_refl Γ0 Δd eq_refl HΔ) ].
  - inversion Hψ; subst. apply d_wf_uskl__all_syn with (L := L). intros α Hα.
    exact (H0 α Hα (open_uskl_wrt_uskl ψ (uskl_var_f α))
             ltac:(symmetry; apply uskl_to_pskl_open)
             Γ0 (α :: Δd) eq_refl (delta_agree_cons _ _ α HΔ)).
  - inversion Hψ; subst. apply d_wf_uskl__all_tag with (L := L) (ε := ε).
    intros α Hα.
    exact (H0 α Hα (open_uskl_wrt_uskl ψ (uskl_var_f α))
             ltac:(symmetry; apply uskl_to_pskl_open)
             Γ0 (α :: Δd) eq_refl (delta_agree_cons _ _ α HΔ)).
  - apply d_wf_uskl__hole.
  - apply d_wf_uskl__holeg.
  - inversion Hψ; subst. apply d_wf_uskl__tophole;
      [ apply guarded_uskl_of_guarded_pskl_erase; exact H
      | exact (IHa_wf_pskl _ eq_refl Γ0 nil eq_refl delta_agree_nil) ].
  - inversion Hψ; subst. apply d_wf_uskl__topholeg;
      [ apply guarded_uskl_of_guarded_pskl_erase; exact H
      | exact (IHa_wf_pskl _ eq_refl Γ0 nil eq_refl delta_agree_nil) ].
Qed.

Lemma a_wf_pskl_of_d_wf_uskl : forall Γ Δd ψ,
  d_wf_uskl Γ Δd ψ ->
  forall Δa, delta_agree Δa Δd ->
  a_wf_pskl (denv_to_aenv Γ) Δa (uskl_to_pskl ψ).
Proof.
  intros Γ Δd ψ H; induction H; intros Δa HΔ; simpl.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. destruct H as [ HΔα | Hb ];
      [ left; apply HΔ; exact HΔα | right; apply a_binds_tvar_of_denv; exact Hb ].
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L). intros α Hα.
    pose proof (H0 α Hα (add α Δa) (delta_agree_cons _ _ α HΔ)) as Hx.
    rewrite uskl_to_pskl_open in Hx. exact Hx.
  - apply a_wf_pskl__all with (L := L). intros α Hα.
    pose proof (H0 α Hα (add α Δa) (delta_agree_cons _ _ α HΔ)) as Hx.
    rewrite uskl_to_pskl_open in Hx. exact Hx.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole.
    + apply guarded_pskl_of_guarded_uskl_erase; assumption.
    + exact (IHd_wf_uskl empty delta_agree_nil).
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole.
    + apply guarded_pskl_of_guarded_uskl_erase; assumption.
    + exact (IHd_wf_uskl empty delta_agree_nil).
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

Lemma d_wf_utyp_of_d_wf_uskl : forall Γ Δd ψ,
  d_wf_uskl Γ Δd ψ -> uskl_ghost_free ψ ->
  d_wf_utyp (tvars_denv Δd ++ Γ) (uskl_to_utyp ψ).
Proof.
  intros Γ Δd ψ H; induction H; intros Hgf; simpl.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var. destruct H as [ HΔ | Hb ];
      [ apply binds_app_2; apply binds_tvars_denv; exact HΔ
      | apply binds_app_3; exact Hb ].
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
    a PLAIN [ad_pat_sub] does not supply — and provably cannot
    (cex/cex_ad_pat_join_not_leaf_valid.v).  [ad_pat_sub_gv] does supply it, at
    exactly those rows, and it is what [ad_pat] / [ad_sd_typing] embed, so
    nothing is lost.  ⚙ RESTART NOTE: the previous [ad_pat_sub_sk_to_d], from
    the plain judgement, is DELETED — it is false as stated now. *)
Lemma ad_pat_sub_gv_sk_to_d : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q -> NM = a_sub_mode_sk ->
  forall Γ, Θ = denv_to_aenv Γ -> d_pat_sub M Ψ Γ R Q.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; intros HNM Γ0 HΘ;
    try discriminate HNM; subst.
  - (* Infer *) apply d_pat_sub__infer;
      [ assumption
      | exact (ad_pat_consis_to_d empty (denv_to_aenv Γ0) R Q H0 Γ0 eq_refl)
      | assumption
      | apply ad_refine_pskl_to_d_closed; assumption ].
  - (* UnivGhostR *) apply d_pat_sub__univ_ghost_r;
      [ assumption | assumption | assumption | assumption
      | exact (ad_pat_consis_to_d empty (denv_to_aenv Γ0) R Q H3 Γ0 eq_refl)
      | apply ad_refine_pskl_to_d_closed; assumption ].
  - (* Arrow *) apply d_pat_sub__arg with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ exact (ad_pat_consis_to_d Ψ1 (denv_to_aenv Γ0) R1 Q1 H Γ0 eq_refl)
      | apply ad_refine_pskl_to_d_closed; assumption
      | exact (IHad_pat_sub_gv eq_refl Γ0 eq_refl) | assumption ].
  - (* ForallL, tagged *) inversion H2; subst.
    apply d_pat_sub__forall_l_tagged with (Ψ' := Ψ') (psi := ψ);
      [ assumption | assumption
      | (* the two judgements now read `fresh Ψ'` the SAME way, so the
           hygiene premise travels verbatim *) assumption | assumption
      | exact (d_wf_uskl_of_a_wf_pskl (denv_to_aenv Γ0) empty (uskl_to_pskl ψ)
                 H3 ψ eq_refl Γ0 nil eq_refl delta_agree_nil)
      | assumption | exact (IHad_pat_sub_gv eq_refl Γ0 eq_refl) ].
  - (* ForallL, untagged *) inversion H2; subst.
    apply d_pat_sub__forall_l_untagged with (Ψ' := Ψ') (psi := ψ);
      [ assumption | assumption
      | (* the two judgements now read `fresh Ψ'` the SAME way, so the
           hygiene premise travels verbatim *) assumption | assumption
      | exact (d_wf_uskl_of_a_wf_pskl (denv_to_aenv Γ0) empty (uskl_to_pskl ψ)
                 H3 ψ eq_refl Γ0 nil eq_refl delta_agree_nil)
      | assumption | exact (IHad_pat_sub_gv eq_refl Γ0 eq_refl) ].
  - (* Ghost *) apply d_pat_sub__ghost;
      [ assumption
      | exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty P H0 Γ0 nil eq_refl
                 delta_agree_nil)
      | assumption ].
  - (* GhostG *) apply d_pat_sub__ghostg; assumption.
  - (* UnivGhostL *) apply d_pat_sub__univ_ghost_l;
      [ assumption | exact (IHad_pat_sub_gv eq_refl Γ0 eq_refl) ].
  - (* UnivGhostLG *) apply d_pat_sub__univ_ghost_lg;
      [ assumption | exact (IHad_pat_sub_gv eq_refl Γ0 eq_refl) ].
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
Lemma d_pat_sub_to_ad_gv : forall M Ψ Γ R Q,
  d_pat_sub M Ψ Γ R Q ->
  exists n, ad_pat_sub_gv n a_sub_mode_sk M Ψ (denv_to_aenv Γ) R Q.
Proof.
  intros M Ψ Γ R Q H; induction H.
  - (* Infer *) exists 0. apply ad_pat_sub_gv__infer;
      [ assumption | apply d_pat_consis_to_ad; assumption | assumption
      | apply d_refine_pskl_to_ad_closed; assumption ].
  - (* UnivGhostR *) exists 0. apply ad_pat_sub_gv__univ_ghost_r;
      [ assumption | assumption | assumption | assumption
      | apply d_pat_consis_to_ad; assumption
      | apply d_refine_pskl_to_ad_closed; assumption ].
  - (* Arrow *) destruct IHd_pat_sub as [ n Hn ]. exists (S n).
    apply ad_pat_sub_gv__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ apply d_pat_consis_to_ad; assumption
      | apply d_refine_pskl_to_ad_closed; assumption
      | exact Hn | assumption ].
  - (* ForallL, tagged *) destruct IHd_pat_sub as [ n Hn ]. exists (S n).
    apply ad_pat_sub_gv__forall_l_tagged with (Ψ' := Ψ') (ψ := psi);
      [ assumption | assumption | assumption
      | apply a_tags_sort__sk; assumption
      | exact (a_wf_pskl_of_d_wf_uskl Γ nil psi H3 empty delta_agree_nil)
      | exact Hn ].
  - (* ForallL, untagged *) destruct IHd_pat_sub as [ n Hn ]. exists (S n).
    apply ad_pat_sub_gv__forall_l_untagged with (Ψ' := Ψ') (ψ := psi);
      [ assumption | assumption | assumption
      | apply a_tags_sort__sk; assumption
      | exact (a_wf_pskl_of_d_wf_uskl Γ nil psi H3 empty delta_agree_nil)
      | exact Hn ].
  - (* Ghost *) exists 0. apply ad_pat_sub_gv__ghost;
      [ assumption
      | exact (d_wf_pskl_to_a Γ nil P H0 empty delta_agree_nil)
      | assumption ].
  - (* UnivGhostL *) destruct IHd_pat_sub as [ n Hn ]. exists n.
    apply ad_pat_sub_gv__univ_ghost_l; [ assumption | exact Hn ].
  - (* GhostG *) exists 0. apply ad_pat_sub_gv__ghostg; assumption.
  - (* UnivGhostLG *) destruct IHd_pat_sub as [ n Hn ]. exists n.
    apply ad_pat_sub_gv__univ_ghost_lg; [ assumption | exact Hn ].
Qed.

Lemma d_pat_sub_to_ad_v : forall M Ψ Γ R Q,
  d_pat_sub M Ψ Γ R Q -> ad_pat_sub_v a_sub_mode_sk M Ψ (denv_to_aenv Γ) R Q.
Proof. intros M Ψ Γ R Q H. exact (d_pat_sub_to_ad_gv M Ψ Γ R Q H). Qed.

Lemma d_pat_sub_to_ad : forall M Ψ Γ R Q,
  d_pat_sub M Ψ Γ R Q -> ad_pat_sub a_sub_mode_sk M Ψ (denv_to_aenv Γ) R Q.
Proof.
  intros M Ψ Γ R Q H; induction H.
  - apply ad_pat_sub__infer;
      [ assumption | apply d_pat_consis_to_ad; assumption | assumption ].
  - apply ad_pat_sub__univ_ghost_r;
      [ assumption | assumption | assumption | assumption
      | apply d_pat_consis_to_ad; assumption ].
  - apply ad_pat_sub__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ apply d_pat_consis_to_ad; assumption | assumption | assumption ].
  - apply ad_pat_sub__forall_l_tagged with (Ψ' := Ψ') (ψ := psi);
      [ assumption | assumption | assumption
      | apply a_tags_sort__sk; assumption
      | exact (a_wf_pskl_of_d_wf_uskl Γ nil psi H3 empty delta_agree_nil)
      | assumption ].
  - apply ad_pat_sub__forall_l_untagged with (Ψ' := Ψ') (ψ := psi);
      [ assumption | assumption | assumption
      | apply a_tags_sort__sk; assumption
      | exact (a_wf_pskl_of_d_wf_uskl Γ nil psi H3 empty delta_agree_nil)
      | assumption ].
  - apply ad_pat_sub__ghost;
      [ assumption
      | exact (d_wf_pskl_to_a Γ nil P H0 empty delta_agree_nil)
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

Lemma is_styp_of_btyp_to_bskl : forall Q,
  is_sskl Q -> forall B, Q = btyp_to_bskl B -> is_styp B.
Proof.
  intros Q H; induction H; intros B0 HQ;
    destruct B0; simpl in HQ; try discriminate HQ; inversion HQ; subst.
  - apply is_styp__unit.
  - apply is_styp__var.
  - apply is_styp__arrow; [ apply IHis_sskl1 | apply IHis_sskl2 ]; reflexivity.
  - apply is_styp__all with (L := L). intros α Hα.
    apply (H0 α Hα (open_btyp_wrt_btyp B0 (btyp_var_f α))).
    rewrite btyp_to_bskl_open; reflexivity.
Qed.

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

Lemma is_iskl_pskl_to_bskl_inh : forall P,
  lc_pskl P -> is_iskl (pskl_to_bskl_inh P).
Proof.
  intros P Hlc; induction Hlc; simpl; try solve [ constructor; auto ].
  apply is_iskl__all with (L := {}). intros α _.
  rewrite <- pskl_to_bskl_inh_open. auto.
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
                 (btyp_to_bskl B0) H0 Γ0 eq_refl C0 B0 eq_refl eq_refl)
      | exact (is_styp_of_btyp_to_bskl (btyp_to_bskl B0) H1 B0 eq_refl)
      | assumption ].
  - (* Check *)
    destruct (inh_paint_btyp B B0 H0 (eq_sym HQ)) as [Hi Hgb].
    apply d_sub__check;
      [ apply guarded_utyp_of_guarded_uskl_incl; exact H
      | exact Hgb
      | exact (ad_pat_consis_ty_to_d Ψ (denv_to_aenv Γ0) (utyp_to_uskl C0)
                 (btyp_to_bskl B0) ltac:(rewrite <- HQ; exact H1) Γ0 eq_refl
                 C0 B0 eq_refl eq_refl)
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
                 (btyp_to_bskl B0_1) H Γ0 eq_refl C0_1 B0_1 eq_refl eq_refl)
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
      | exact (d_wf_utyp_of_d_wf_uskl Γ0 nil ψ
                 (d_wf_uskl_of_a_wf_pskl (denv_to_aenv Γ0) empty
                    (uskl_to_pskl ψ) H3 ψ eq_refl Γ0 nil eq_refl
                    delta_agree_nil) H7)
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
      | exact (d_wf_utyp_of_d_wf_uskl Γ0 nil ψ
                 (d_wf_uskl_of_a_wf_pskl (denv_to_aenv Γ0) empty
                    (uskl_to_pskl ψ) H3 ψ eq_refl Γ0 nil eq_refl
                    delta_agree_nil) H7)
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
    ([ad_pat_sub_of_v]). *)
Lemma ad_pat_sub_v_sk_to_d : forall m Ψ Γ R Q,
  ad_pat_sub_v a_sub_mode_sk m Ψ (denv_to_aenv Γ) R Q -> d_pat_sub m Ψ Γ R Q.
Proof.
  intros m Ψ Γ R Q [ n Hn ].
  exact (ad_pat_sub_gv_sk_to_d n a_sub_mode_sk m Ψ (denv_to_aenv Γ) R Q
           Hn eq_refl Γ eq_refl).
Qed.

Lemma ad_pat_sub_v_ty_to_d : forall m Ψ Γ A B,
  ad_pat_sub_v a_sub_mode_ty m Ψ (denv_to_aenv Γ)
    (ptyp_to_uskl_syn A) (btyp_to_bskl B) ->
  d_sub m Ψ Γ (ptyp_to_utyp_syn A) B.
Proof.
  intros m Ψ Γ A B Hv.
  eapply ad_pat_sub_ty_to_d;
    [ exact (ad_pat_sub_of_v Hv) | reflexivity | reflexivity | | reflexivity ].
  unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  symmetry. apply utyp_to_uskl_ptyp_to_utyp_syn.
Qed.

(* ===================================================================== *)
(*  §9  SKELETON INFERENCE  [ad_pat] -> [d_pat].                          *)
(* ===================================================================== *)

Lemma ad_pat_to_d : forall M Θ e Q,
  ad_pat M Θ e Q -> forall Γ, Θ = denv_to_aenv Γ -> d_pat M Γ e Q.
Proof.
  intros M Θ e Q H; induction H; intros Γ0 HΘ; subst Θ.
  - (* P-Unit *) apply d_pat__unit;
      [ exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty (bskl_to_pskl Q) H Γ0 nil
                 eq_refl delta_agree_nil)
      | apply ad_pat_sub_v_sk_to_d; assumption ].
  - (* P-Var *)
    destruct (binds_denv_to_aenv_inv x b Γ0 H) as [d [Hd Heq]]; subst.
    apply d_pat__var with (P := P) (d := d);
      [ exact Hd
      | rewrite <- abind_to_pskl_of_dbind; exact H0
      | exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty (bskl_to_pskl Q) H1 Γ0 nil
                 eq_refl delta_agree_nil)
      | apply ad_pat_sub_v_sk_to_d; assumption ].
  - (* P-Anno *) apply d_pat__anno;
      [ exact (a_wf_ptyp_to_d (denv_to_aenv Γ0) A H Γ0 eq_refl)
      | exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty (bskl_to_pskl Q) H0 Γ0 nil
                 eq_refl delta_agree_nil)
      | apply ad_pat_sub_v_sk_to_d; assumption ].
  - (* P-Freeze *) apply d_pat__freeze. exact (IHad_pat Γ0 eq_refl).
  - (* P-Abs *) apply d_pat__abs with (L := L);
      [ assumption
      | exact (a_wf_pskl_to_d (denv_to_aenv Γ0) empty P H0 Γ0 nil eq_refl
                 delta_agree_nil)
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
                 (pskl_to_bskl_inh P) Q1 H0 Γ0 nil eq_refl delta_agree_nil)
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
    apply ad_pat_sub_v_ty_to_d; assumption.
  - (* sd-Var *)
    destruct (binds_denv_to_aenv_inv x (abind_var_typ A) Γ0 H) as [d [Hd Heq]].
    destruct d as [ | A1 | P1 ]; simpl in Heq; try discriminate Heq.
    assert (HA : A = A1) by (injection Heq; auto). subst A1.
    apply d_sd_typing__var with (A := A);
      [ exact Hd | apply ad_pat_sub_v_ty_to_d; assumption ].
  - (* sd-Anno *) apply d_sd_typing__anno with (A := A);
      [ exact (IHad_sd_typing Γ0 eq_refl) | apply ad_pat_sub_v_ty_to_d; assumption ].
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
                 (pskl_to_bskl_inh P) (btyp_to_bskl B1) H0 Γ0 nil eq_refl
                 delta_agree_nil)
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
  symmetry. apply mono_ptyp_inh_eq_syn. apply Hm.
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
(*      not a hygiene one: [ad_pat_sub] → [ad_pat_sub_g].                 *)
(* ===================================================================== *)

Lemma binds_tvars_denv_inv : forall α Δ,
  binds α dbind_tvar (tvars_denv Δ) -> List.In α Δ.
Proof.
  intros α Δ. induction Δ as [ | β Δ' IH ]; simpl; [ contradiction | ].
  intros [ Heq | Hb ];
    [ inversion Heq; subst; left; reflexivity | right; apply IH; exact Hb ].
Qed.

(** ⭐ (A)'s POSITIVE HALF.  A ghost-free subject has nothing to capture, so
    its refinement into the counterpart is READ OFF the consistency
    derivation: the ∀ rows line up (consistency pushes the rigid into Γ,
    refinement into Δ — the [tvars_denv Δd] split below is exactly that
    correspondence), and every rule that could fill a ghost with a
    binder-bound variable is excluded by the subject. *)
Lemma d_pat_consis_subject_refine_ghost_free : forall Ψ Γ R Q,
  d_pat_consis Ψ Γ R Q -> uskl_ghost_free R ->
  forall Γ0 Δd Δa, Γ = tvars_denv Δd ++ Γ0 -> delta_agree Δa Δd ->
  ad_refine_pskl (denv_to_aenv Γ0) Δa (uskl_to_pskl R) (bskl_to_pskl Q).
Proof.
  intros Ψ Γ R Q H; induction H; intros Hgf Γ0 Δd Δa HΓ HΔ; subst;
    try solve [ inversion Hgf ].
  - (* unit *) apply ad_refine_pskl__unit.
  - (* var *) apply ad_refine_pskl__var.
    apply binds_app_1 in H0 as [ Hb | Hb ];
      [ left; apply HΔ; apply binds_tvars_denv_inv; exact Hb
      | right; apply a_binds_tvar_of_denv; exact Hb ].
  - (* arrow *) inversion Hgf; subst. apply ad_refine_pskl__arrow;
      [ exact (IHd_pat_consis1 ltac:(assumption) Γ0 Δd Δa eq_refl HΔ)
      | exact (IHd_pat_consis2 ltac:(assumption) Γ0 Δd Δa eq_refl HΔ) ].
  - (* ∀^ε ~ ∀ⁱ *)
    inversion Hgf as [ | | | L0 ε0 R0 Hgf0 | ]; subst.
    apply ad_refine_pskl__all with (L := L `union` L0). intros α Hα.
    rewrite <- uskl_to_pskl_open, <- bskl_to_pskl_open.
    apply (H0 α ltac:(clear - Hα; solve_notin_auto)
             (Hgf0 α ltac:(clear - Hα; solve_notin_auto))
             Γ0 (α :: Δd) (add α Δa));
      [ simpl_env; reflexivity | apply delta_agree_cons; exact HΔ ].
  - (* ∀ˢ ~ ∀ⁱ *)
    inversion Hgf as [ | | | | L0 R0 Hgf0 ]; subst.
    apply ad_refine_pskl__all with (L := L `union` L0). intros α Hα.
    rewrite <- uskl_to_pskl_open, <- bskl_to_pskl_open.
    apply (H0 α ltac:(clear - Hα; solve_notin_auto)
             (Hgf0 α ltac:(clear - Hα; solve_notin_auto))
             Γ0 (α :: Δd) (add α Δa));
      [ simpl_env; reflexivity | apply delta_agree_cons; exact HΔ ].
  - (* ∀^ε ~ ∀ˢ *)
    inversion Hgf as [ | | | L0 ε0 R0 Hgf0 | ]; subst.
    apply ad_refine_pskl__all with (L := L `union` L0). intros α Hα.
    rewrite <- uskl_to_pskl_open, <- bskl_to_pskl_open.
    apply (H0 α ltac:(clear - Hα; solve_notin_auto)
             (Hgf0 α ltac:(clear - Hα; solve_notin_auto))
             Γ0 (α :: Δd) (add α Δa));
      [ simpl_env; reflexivity | apply delta_agree_cons; exact HΔ ].
  - (* ∀ˢ ~ ∀ˢ *)
    inversion Hgf as [ | | | | L0 R0 Hgf0 ]; subst.
    apply ad_refine_pskl__all with (L := L `union` L0). intros α Hα.
    rewrite <- uskl_to_pskl_open, <- bskl_to_pskl_open.
    apply (H0 α ltac:(clear - Hα; solve_notin_auto)
             (Hgf0 α ltac:(clear - Hα; solve_notin_auto))
             Γ0 (α :: Δd) (add α Δa));
      [ simpl_env; reflexivity | apply delta_agree_cons; exact HΔ ].
Qed.

(** …and at the top level, which is the shape [ad_pat_sub_gv]'s leaf rows
    ask for: [ad_sd_typing]'s base rows join the painting of a [ptyp], so
    their subject is ghost-free and their leaf datum is free. *)
Corollary d_pat_consis_subject_refine_closed : forall Ψ Γ R Q,
  d_pat_consis Ψ Γ R Q -> uskl_ghost_free R ->
  ad_refine_pskl (denv_to_aenv Γ) empty (uskl_to_pskl R) (bskl_to_pskl Q).
Proof.
  intros Ψ Γ R Q H Hgf.
  exact (d_pat_consis_subject_refine_ghost_free Ψ Γ R Q H Hgf Γ nil empty
           eq_refl delta_agree_nil).
Qed.

(* ===================================================================== *)
(*  §13  THE LEAF-VALID UPGRADE AT THE TYPE SORT.                         *)
(*                                                                        *)
(*  ⭐ What §12 leaves open is a question about GHOSTS, and at [N = TY]   *)
(*  there are none to worry about: [a_tags_sort__ty] forces every ForallL *)
(*  instantiation ghost-free BY RULE, so a join whose ROOT subject is     *)
(*  ghost-free has a ghost-free subject at every leaf, and                *)
(*  [d_pat_consis_subject_refine_closed] hands the leaf datum over.       *)
(*                                                                        *)
(*  ⚙ The other half of [ad_pat_sub_v] is the FUEL, which is a plain      *)
(*  collection: only Arrow / ForallR / ForallL increment, so the          *)
(*  derivation's own height serves.  ⚠️ [__forall_r] is COFINITE, so one  *)
(*  fuel has to serve infinitely many α — the IH is taken at ONE fresh α  *)
(*  and regenerated by [ad_pat_sub_gv_rename_tvar], the same shape as     *)
(*  [d_sub_to_tagsin] in decl/prop_tag_swap.v §3.                        *)
(*                                                                        *)
(*  ⚠️ THE SK SORT IS NOT THIS.  There [a_tags_sort__sk] permits a GHOSTY  *)
(*  instantiation, and [ad_pat]'s P-Var reads a possibly-ghosty [P] out   *)
(*  of the context — that is obstruction (A) proper, still open.          *)
(* ===================================================================== *)

Lemma ad_pat_sub_ty_to_v : forall M Ψ Θ R Q,
  ad_pat_sub a_sub_mode_ty M Ψ Θ R Q ->
  forall Γ, Θ = denv_to_aenv Γ ->
  uskl_ghost_free R ->
  ad_pat_sub_v a_sub_mode_ty M Ψ (denv_to_aenv Γ) R Q.
Proof.
  intros M Ψ Θ R Q H.
  remember a_sub_mode_ty as NM eqn:HNM.
  induction H; intros Γ0 HΘ Hgf; subst; try discriminate HNM.
  - (* Infer: the leaf datum is the subject's refinement, read off consistency *)
    exists 0. apply ad_pat_sub_gv__infer;
      [ assumption | assumption | assumption
      | apply (d_pat_consis_subject_refine_closed empty Γ0 R Q);
          [ exact (ad_pat_consis_to_d empty (denv_to_aenv Γ0) R Q
                     ltac:(assumption) Γ0 eq_refl)
          | exact Hgf ] ].
  - (* Check (TY) *)
    exists 0. apply ad_pat_sub_gv__check;
      [ assumption | assumption | assumption | ].
    rewrite <- (bskl_to_pskl_pskl_to_bskl_inh B).
    apply (d_pat_consis_subject_refine_closed Ψ Γ0 T (pskl_to_bskl_inh B));
      [ exact (ad_pat_consis_to_d Ψ (denv_to_aenv Γ0) T (pskl_to_bskl_inh B)
                 ltac:(assumption) Γ0 eq_refl)
      | exact Hgf ].
  - (* ForallR (TY): ONE fuel for the whole cofinite family, via renaming *)
    pick fresh α for (L `union` dom Γ0 `union` ftvar_in_uskl T
                      `union` ftvar_in_bskl B).
    destruct (H0 α ltac:(clear - Fr; solve_notin_auto) eq_refl
                ((α ~ dbind_tvar) ++ Γ0) eq_refl Hgf) as [ n Hn ].
    exists (S n).
    apply ad_pat_sub_gv__forall_r with
      (L := L `union` dom Γ0 `union` ftvar_in_uskl T `union` ftvar_in_bskl B
            `union` singleton α).
    intros β Hβ.
    rewrite (subst_bskl_in_bskl_intro α B (bskl_var_f β))
      by (clear - Fr; fsetdec).
    rewrite <- (subst_uskl_in_uskl_fresh_eq T (uskl_var_f β) α)
      by (clear - Fr; fsetdec).
    rewrite_env (nil ++ (β ~ abind_tvar) ++ denv_to_aenv Γ0).
    eapply ad_pat_sub_gv_rename_tvar with (Θ1 := nil) (α := α).
    + exact Hn.
    + simpl. rewrite denv_to_aenv_dom. clear - Fr; fsetdec.
    + intros β0 τ Hb. exfalso. simpl in Hb.
      eapply denv_to_aenv_no_flex_def; eassumption.
  - (* Arrow: the DOMAIN is a consistency leaf too, so it carries the datum *)
    inversion Hgf as [ | | R1' R2' Hgf1 Hgf2 | | ]; subst.
    destruct (IHad_pat_sub eq_refl Γ0 eq_refl Hgf2) as [ n Hn ].
    exists (S n).
    apply ad_pat_sub_gv__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ assumption
      | apply (d_pat_consis_subject_refine_closed Ψ1 Γ0 R1 Q1);
          [ exact (ad_pat_consis_to_d Ψ1 (denv_to_aenv Γ0) R1 Q1
                     ltac:(assumption) Γ0 eq_refl)
          | exact Hgf1 ]
      | exact Hn | assumption ].
  - (* ForallL, tagged: [a_tags_sort__ty] hands over the instantiation's
       ghost-freeness, which is exactly what keeps the body ghost-free *)
    match goal with Ht : a_tags_sort a_sub_mode_ty Ψ' ψ |- _ =>
      inversion Ht as [ | Ψ'' ψ'' Htsk Htag Hgfψ ]; subst end.
    destruct (IHad_pat_sub eq_refl Γ0 eq_refl
                (uskl_ghost_free_open_gen_tag Hgf Hgfψ
                   (is_tskl_lc Htsk))) as [ n Hn ].
    exists (S n).
    apply ad_pat_sub_gv__forall_l_tagged with (Ψ' := Ψ') (ψ := ψ);
      [ assumption | assumption | assumption | assumption | assumption
      | exact Hn ].
  - (* ForallL, untagged *)
    match goal with Ht : a_tags_sort a_sub_mode_ty Ψ' ψ |- _ =>
      inversion Ht as [ | Ψ'' ψ'' Htsk Htag Hgfψ ]; subst end.
    destruct (IHad_pat_sub eq_refl Γ0 eq_refl
                (uskl_ghost_free_open_gen Hgf Hgfψ
                   (is_tskl_lc Htsk))) as [ n Hn ].
    exists (S n).
    apply ad_pat_sub_gv__forall_l_untagged with (Ψ' := Ψ') (ψ := ψ);
      [ assumption | assumption | assumption | assumption | assumption
      | exact Hn ].
  - (* FlexMono: vacuous over a declarative context *)
    exfalso. eapply denv_to_aenv_no_flex_def; eassumption.
Qed.

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

(** ⚠️ The two well-scopedness judgements do NOT track a ∀-bound variable in
    the same place: [d_wf_utyp]'s ∀ rows push it into Γ, [d_wf_uskl]'s into Δ.
    So the transport threads a VISIBILITY condition — every tvar of the source
    context is visible on the target side, in Δ or in Γ' — exactly as
    [d_pat_consis_subject_refine_ghost_free] threads [delta_agree]. *)
Lemma d_wf_uskl_incl_gen : forall Γ C,
  d_wf_utyp Γ C ->
  forall Γ' Δ,
    (forall α, binds α dbind_tvar Γ ->
       List.In α Δ \/ binds α dbind_tvar Γ') ->
    d_wf_uskl Γ' Δ (utyp_to_uskl C).
Proof.
  intros Γ C H; induction H; intros Γ' Δ0 Hvis; simpl.
  - apply d_wf_uskl__unit.
  - apply d_wf_uskl__var. apply Hvis; assumption.
  - apply d_wf_uskl__arrow;
      [ apply IHd_wf_utyp1 | apply IHd_wf_utyp2 ]; exact Hvis.
  - apply d_wf_uskl__all_syn with (L := L). intros α Hα.
    rewrite <- utyp_to_uskl_open_var. apply (H0 α Hα).
    intros β Hb. destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [ [ Heq _ ] | Hb' ];
      [ subst; left; simpl; left; reflexivity | ].
    destruct (Hvis β Hb') as [ HΔ | HΓ ];
      [ left; simpl; right; exact HΔ | right; exact HΓ ].
  - apply d_wf_uskl__all_tag with (L := L) (ε := ε). intros α Hα.
    rewrite <- utyp_to_uskl_open_var. apply (H0 α Hα).
    intros β Hb. destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [ [ Heq _ ] | Hb' ];
      [ subst; left; simpl; left; reflexivity | ].
    destruct (Hvis β Hb') as [ HΔ | HΓ ];
      [ left; simpl; right; exact HΔ | right; exact HΓ ].
Qed.

Lemma d_wf_uskl_incl : forall Γ C,
  d_wf_utyp Γ C -> d_wf_uskl Γ nil (utyp_to_uskl C).
Proof.
  intros Γ C H. apply (d_wf_uskl_incl_gen Γ C H Γ nil).
  intros α Hb. right; exact Hb.
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
Lemma d_sub_to_ad : forall M Ψ Γ C B,
  d_sub M Ψ Γ C B ->
  ad_pat_sub a_sub_mode_ty M Ψ (denv_to_aenv Γ)
    (utyp_to_uskl C) (btyp_to_bskl B).
Proof.
  intros M Ψ Γ C B H; induction H; simpl.
  - (* infer *) apply ad_pat_sub__infer;
      [ assumption | apply d_consis_to_ad; assumption
      | apply is_sskl_of_is_styp; assumption ].
  - (* check *)
    destruct (guarded_ityp_inh_paint B ltac:(assumption) ltac:(assumption))
      as [ Heq Hgp ].
    rewrite Heq. apply ad_pat_sub__check;
      [ apply guarded_uskl_incl; assumption | exact Hgp | ].
    rewrite <- Heq. apply d_consis_to_ad; assumption.
  - (* forall_r *)
    apply ad_pat_sub__forall_r with (L := L). intros α Hα.
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
    rewrite <- btyp_to_bskl_open. exact (H1 α Hα).
  - (* arg *)
    apply ad_pat_sub__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ apply d_consis_to_ad; assumption | assumption | assumption ].
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
      | exact (a_wf_pskl_of_d_wf_uskl Γ nil (utyp_to_uskl ph)
                 (d_wf_uskl_incl Γ ph ltac:(assumption)) empty
                 delta_agree_nil)
      | rewrite <- utyp_to_uskl_open; assumption ].
  - (* forall_l, untagged *)
    apply ad_pat_sub__forall_l_untagged with
      (Ψ' := Ψ') (ψ := utyp_to_uskl ph);
      [ assumption | assumption
      | rewrite (ftag_utyp_to_uskl (utyp_all_syn C)); assumption
      | apply a_tags_sort__ty;
          [ apply is_tskl_utyp_to_uskl; assumption
          | apply d_tags_skl_incl; assumption
          | apply uskl_ghost_free_incl; eapply d_wf_utyp_lc; eassumption ]
      | exact (a_wf_pskl_of_d_wf_uskl Γ nil (utyp_to_uskl ph)
                 (d_wf_uskl_incl Γ ph ltac:(assumption)) empty
                 delta_agree_nil)
      | rewrite <- utyp_to_uskl_open; assumption ].
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
(*  that presupposition on the rules (decl/def_extra.v, 2026-08-11) the    *)
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
      [ exact (d_wf_pskl_to_a Γ nil (bskl_to_pskl Q) H empty delta_agree_nil)
      | apply d_pat_sub_to_ad_v; assumption ].
  - (* P-Var *) apply ad_pat__var with (P := P) (b := abind_of_dbind d);
      [ apply binds_denv_to_aenv; assumption
      | rewrite abind_to_pskl_of_dbind; assumption
      | exact (d_wf_pskl_to_a Γ nil (bskl_to_pskl Q) H1 empty delta_agree_nil)
      | apply d_pat_sub_to_ad_v; assumption ].
  - (* P-Anno *) apply ad_pat__anno;
      [ exact (d_wf_ptyp_to_a Γ A H)
      | exact (d_wf_pskl_to_a Γ nil (bskl_to_pskl Q) H0 empty delta_agree_nil)
      | apply d_pat_sub_to_ad_v; assumption ].
  - (* P-Freeze *) apply ad_pat__freeze; assumption.
  - (* P-Abs *) apply ad_pat__abs with (L := L);
      [ assumption
      | exact (d_wf_pskl_to_a Γ nil P H0 empty delta_agree_nil)
      | assumption
      (* ⚙ the cofinite premise is [H2]; its IH — what we need — is [H3] *)
      | intros x Hx; exact (H3 x Hx) ].
  - (* P-AbsAnno *) apply ad_pat__abs_anno with (L := L) (B := B);
      [ assumption | exact (d_wf_ptyp_to_a Γ A H0) | assumption | assumption
      | intros x Hx; exact (H4 x Hx) ].
  - (* P-App *) apply ad_pat__app with (P := P) (Q1 := Q1);
      [ assumption
      | exact (d_refine_syn_to_ad Γ nil (pskl_to_bskl_inh P) Q1 H0 empty
                 delta_agree_nil)
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
    ghost-free, so §13 upgrades it to the leaf-valid join the rule wants. *)
Ltac base_row lctac :=
  (* ⚙ [ptyp_to_uskl_syn] is a Definition, so the goal never displays the
     [bskl_to_uskl (pskl_to_bskl_syn …)] form the coercion lemma rewrites *)
  unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn;
  rewrite <- utyp_to_uskl_ptyp_to_utyp_syn;
  eapply ad_pat_sub_ty_to_v;
    [ apply d_sub_to_ad; eassumption | reflexivity
    | apply uskl_ghost_free_incl; apply lc_ptyp_to_utyp_syn; lctac ].

Lemma d_sd_typing_to_ad : forall M Γ e B,
  d_sd_typing M Γ e B ->
  d_wf_denv Γ ->
  {{ (denv_to_aenv Γ) ⊢ᵉ e }}a ->
  ad_sd_typing M (denv_to_aenv Γ) e B.
Proof.
  intros M Γ e B H; induction H; intros Hwf Hwfe.
  - (* sd-Unit *)
    apply ad_sd_typing__unit. base_row ltac:(apply lc_ptyp_unit).
  - (* sd-Var *)
    apply ad_sd_typing__var with (A := A);
      [ apply binds_denv_to_aenv with (d := dbind_typ A); assumption | ].
    base_row ltac:(eapply d_wf_ptyp_lc; eapply d_wf_denv_binds_ptyp;
                   eassumption).
  - (* sd-Anno: the annotation's wf is the AMBIENT hypothesis, not the rule's *)
    inversion Hwfe as [ | | Θ0 e0 A0 Hwfa Hwfe0 | | | | ]; subst.
    apply ad_sd_typing__anno with (A := A);
      [ exact Hwfa | apply IHd_sd_typing; assumption | ].
    base_row ltac:(apply lc_ptyp_of_lc_btyp_inh;
                   eapply d_sd_typing_target_lc; eassumption).
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
      | eapply d_refine_syn_to_ad; [ eassumption | apply delta_agree_nil ]
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
