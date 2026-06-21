(** Paper-finished properties of the algorithmic look / constraint-collection
    judgments (paper [subtyping-proofs.tex], the [☺️]-checked lemmas).

    These are support lemmas for the decoration argument, stated over the
    ORDINARY algorithmic judgments only (no decorated layer), so they close
    with NO admitted dependency.  Started per the "prove the paper-finished
    proofs first" plan. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.def_ott.
Require Import src.frost.prop_ln.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.

Set Implicit Arguments.

Scheme a_looksub_mut := Induction for a_looksub Sort Prop
  with a_lookeq_mut  := Induction for a_lookeq  Sort Prop.
Combined Scheme a_looksub_lookeq_mutind from a_looksub_mut, a_lookeq_mut.

(* Helper: if the searched variable [α] is absent from the source skeleton,
   constraint collection produces no fresh variables and no constraints.
   This discharges the "[Absent] for [Q]" subcases of the stability lemma. *)
Lemma a_look_absent_empty :
  (forall α m P P0 Ξ C, a_looksub α m P P0 Ξ C ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ C = nil) /\
  (forall α P P0 Ξ C, a_lookeq α P P0 Ξ C ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ C = nil).
Proof.
  apply a_looksub_lookeq_mutind; intros; simpl in *;
    try (split; reflexivity);
    try (exfalso; fsetdec).
  all: let b := fresh "b" in pick fresh b;
       repeat match goal with
       | [ H : forall x : atom, x `notin` ?L -> _ |- _ ] =>
           specialize (H b ltac:(fsetdec))
       end.
  all: repeat match goal with
       | [ H : ?a `notin` ftvar_in_pskl (open_pskl_wrt_pskl ?P (pskl_var_f ?b)) -> _ |- _ ] =>
           let Hu := fresh in
           pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b)) as Hu;
           simpl in Hu;
           let Hn := fresh in
           assert (Hn : a `notin` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f b)))
             by fsetdec;
           specialize (H Hn); clear Hu Hn
       | [ H : ?a `notin` ftvar_in_pskl ?P -> _ |- _ ] =>
           let Hn := fresh in
           assert (Hn : a `notin` ftvar_in_pskl P) by fsetdec;
           specialize (H Hn); clear Hn
       end.
  all: repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
       subst; simpl; auto.
Qed.

(* Guardedness is preserved by substituting for a NON-head variable. *)
Lemma guarded_pskl_subst : forall A Q β,
    guarded_pskl A -> lc_pskl Q -> A <> pskl_var_f β ->
    guarded_pskl (subst_pskl_in_pskl Q β A).
Proof.
  intros A Q β Hg Hlc Hne. inversion Hg; subst; simpl.
  - apply guarded_pskl__unit.
  - destruct (X == β); [ subst; contradiction | ]. apply guarded_pskl__var.
  - apply guarded_pskl__arrow; apply subst_pskl_in_pskl_lc_pskl; assumption.
Qed.

(* Stability of constraint collection (paper subtyping-proofs.tex,
   lemma:constraint-collection-stable-substitution, [☺️]).

   Mechanisation note: [lc_pskl Q] is required for the locally-nameless
   subst/open commutation in the quantifier cases; it is implicit in the
   paper's on-paper substitution. *)
Lemma a_look_stable_subst :
  (forall α m P P0 Ξ C, a_looksub α m P P0 Ξ C ->
     forall β Q, β <> α -> lc_pskl Q -> α `notin` ftvar_in_pskl Q ->
     a_looksub α m (subst_pskl_in_pskl Q β P) P0 Ξ C) /\
  (forall α P P0 Ξ C, a_lookeq α P P0 Ξ C ->
     forall β Q, β <> α -> lc_pskl Q -> α `notin` ftvar_in_pskl Q ->
     a_lookeq α (subst_pskl_in_pskl Q β P) P0 Ξ C).
Proof.
  (* Proof structure: mutual induction via [a_looksub_lookeq_mutind].  Per case,
     [simpl] the substitution on the LHS head, then:
     - structural cases (Var, Arrow, UnivGhost-rules): reconstruct with the
       same constructor, feeding the IHs (which already give the substituted
       sub-derivations); binder cases (ForallL/ForallR/ForallInh/ForallSyn/
       UnivGhost1) commute subst with open via
       [subst_pskl_in_pskl_open_pskl_wrt_pskl_var] (needs [β'<>β], [lc_pskl Q]);
     - guarded-LHS cases (Check) and any bare-variable LHS: sub-case on
       [LHS = pskl_var_f β].  When it is, [α∉ftv(LHS)] (β<>α), so
       [a_look_absent_empty] collapses the constraints to [nil] and
       [a_looksub__absent]/[a_lookeq__absent] rebuilds on [Q] (using
       [α∉ftv Q]); otherwise the head is preserved and we reconstruct.
     This is the paper's "since α∉ftv(Q) we can always use Absent for Q". *)
  destruct a_look_absent_empty as [Hsub_abs Heq_abs].
  apply a_looksub_lookeq_mutind.
  - (* LS-Var *)
    intros α m P Ξ P' Href β Q Hbne Hlc Hnotin.
    rewrite subst_pskl_in_pskl_fresh_eq by (simpl; fsetdec).
    apply a_looksub__var; assumption.
  - (* LS-Absent *)
    intros α m P P' Hnf β Q Hbne Hlc Hnotin.
    apply a_looksub__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P Q β) as Hu. fsetdec.
  - (* LS-Vacuous *)
    intros α m P P' β Q Hbne Hlc Hnotin. apply a_looksub__vacuous.
  - (* LS-Check *)
    intros α A B Ξ C HgA HgB Hlk IHlk β Q Hbne Hlc Hnotin.
    inversion HgA; subst.
    + apply a_looksub__check;
        [ apply guarded_pskl_subst; [ constructor | assumption | discriminate ]
        | assumption | apply IHlk; assumption ].
    + destruct (X == β).
      * subst. apply Heq_abs in Hlk; [ | simpl; fsetdec ]. destruct Hlk; subst.
        apply a_looksub__absent.
        pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper (pskl_var_f β) Q β) as Hu.
        simpl in Hu. fsetdec.
      * apply a_looksub__check;
          [ apply guarded_pskl_subst; [ constructor | assumption
            | intro Hc; inversion Hc; subst; contradiction ]
          | assumption | apply IHlk; assumption ].
    + apply a_looksub__check;
        [ apply guarded_pskl_subst; [ constructor; assumption | assumption | discriminate ]
        | assumption | apply IHlk; assumption ].
  - (* LS-ForallR *)
    intros L α A B Ξ C Hpr IHpr β Q Hbne Hlc Hnotin.
    apply a_looksub__forall_r with (L := L `union` singleton β `union` ftvar_in_pskl Q).
    intros β' Hβ'. apply IHpr; [ fsetdec | assumption | assumption | assumption ].
  - (* LS-Arrow *)
    intros α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hlk IHlk Hsub IHsub β Q Hbne Hlc Hnotin.
    simpl. apply a_looksub__arrow; [ apply IHlk | apply IHsub ]; assumption.
  - (* LS-ForallL *)
    intros L α m P P' Ξ C Hpr IHpr β Q Hbne Hlc Hnotin. simpl.
    apply a_looksub__forall_l with (L := L `union` singleton β `union` ftvar_in_pskl Q).
    intros β' Hβ'.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var by (first [ fsetdec | assumption ]).
    apply IHpr; [ fsetdec | assumption | assumption | assumption ].
  - (* LS-UnivGhostL *)
    intros α m P P' Ξ C Hpr IHpr β Q Hbne Hlc Hnotin. simpl.
    apply a_looksub__univ_ghost_l. apply IHpr; assumption.
  - (* LE-Var *)
    intros α P Ξ P' Href β Q Hbne Hlc Hnotin.
    rewrite subst_pskl_in_pskl_fresh_eq by (simpl; fsetdec).
    apply a_lookeq__var; assumption.
  - (* LE-Absent *)
    intros α P P' Hnf β Q Hbne Hlc Hnotin.
    apply a_lookeq__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P Q β) as Hu. fsetdec.
  - (* LE-Vacuous *)
    intros α P P' β Q Hbne Hlc Hnotin. apply a_lookeq__vacuous.
  - (* LE-FlexR *)
    intros α P β0 γ Hpne Hpin β Q Hbne Hlc Hnotin. simpl.
    apply a_lookeq__flex_r.
    + destruct P as [ | n | X | P1 P2 | P0 | | P0 ]; simpl; try discriminate.
      destruct (X == β); subst.
      * intro HQ. rewrite HQ in Hnotin. simpl in Hnotin. fsetdec.
      * intro HX. inversion HX; subst. congruence.
    + pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower P Q β) as Hl. fsetdec.
  - (* LE-Arrow *)
    intros α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hlk1 IHlk1 Hlk2 IHlk2 β Q Hbne Hlc Hnotin.
    simpl. apply a_lookeq__arrow; [ apply IHlk1 | apply IHlk2 ]; assumption.
  - (* LE-ForallInh *)
    intros L α P P' Ξ C Hpr IHpr β Q Hbne Hlc Hnotin. simpl.
    apply a_lookeq__forall_inh with (L := L `union` singleton β `union` ftvar_in_pskl Q).
    intros β' Hβ'.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var by (first [ fsetdec | assumption ]).
    apply IHpr; [ fsetdec | assumption | assumption | assumption ].
  - (* LE-ForallSyn *)
    intros L α P P' Ξ C Hpr IHpr β Q Hbne Hlc Hnotin. simpl.
    apply a_lookeq__forall_syn with (L := L `union` singleton β `union` ftvar_in_pskl Q).
    intros β' Hβ'.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var by (first [ fsetdec | assumption ]).
    apply IHpr; [ fsetdec | assumption | assumption | assumption ].
  - (* LE-UnivGhost *)
    intros α P P' Ξ C Hpr IHpr β Q Hbne Hlc Hnotin. simpl.
    apply a_lookeq__univ_ghost. apply IHpr; assumption.
  - (* LE-UnivGhost1 *)
    intros L α P P' Ξ C Hpr IHpr β Q Hbne Hlc Hnotin. simpl.
    apply a_lookeq__univ_ghost1 with (L := L `union` singleton β `union` ftvar_in_pskl Q).
    intros β' Hβ'. apply IHpr; [ fsetdec | assumption | assumption | assumption ].
  - (* LE-UnivGhost2 *)
    intros α P P' Ξ C HgP' Hpr IHpr β Q Hbne Hlc Hnotin. simpl.
    apply a_lookeq__univ_ghost2; [ assumption | apply IHpr; assumption ].
  - (* LE-UnivGhostR *)
    intros α P P' Ξ C Hpne HgP Hpr IHpr β Q Hbne Hlc Hnotin.
    inversion HgP; subst.
    + apply a_lookeq__univ_ghost_r;
        [ discriminate | constructor | apply IHpr; assumption ].
    + destruct (X == β).
      * subst. apply Heq_abs in Hpr; [ | simpl; fsetdec ]. destruct Hpr; subst.
        apply a_lookeq__vacuous.
      * apply a_lookeq__univ_ghost_r;
          [ rewrite subst_pskl_in_pskl_fresh_eq by (simpl; fsetdec);
            intro Hc; inversion Hc; subst; congruence
          | apply guarded_pskl_subst;
              [ constructor | assumption | intro Hc; inversion Hc; subst; congruence ]
          | apply IHpr; assumption ].
    + apply a_lookeq__univ_ghost_r;
        [ discriminate
        | apply guarded_pskl_subst; [ constructor; assumption | assumption | discriminate ]
        | apply IHpr; assumption ].
Qed.

(* Free-variable monotonicity of constraint SOLVING: the output skeleton's
   free variables come from the two inputs.  Building block for tracking
   freshness through [a_extract] (paper lemma:look-output-fresh). *)
Scheme a_solve_sub_mut := Minimality for a_solve_sub Sort Prop
  with a_solve_eq_mut  := Minimality for a_solve_eq  Sort Prop.
Combined Scheme a_solve_sub_eq_mutind from a_solve_sub_mut, a_solve_eq_mut.

Lemma a_solve_ftv :
  (forall Θ m P Q P', a_solve_sub Θ m P Q P' ->
     ftvar_in_pskl P' [<=] ftvar_in_pskl P `union` ftvar_in_pskl Q) /\
  (forall Θ P Q P', a_solve_eq Θ P Q P' ->
     ftvar_in_pskl P' [<=] ftvar_in_pskl P `union` ftvar_in_pskl Q).
Proof.
  apply a_solve_sub_eq_mutind; intros; simpl in *; try fsetdec.
  (* ForallR: instantiation by [⫯.□] contributes no free variable. *)
  all: try (
    match goal with
    | [ H : ftvar_in_pskl _ [<=] ftvar_in_pskl _
              `union` ftvar_in_pskl (open_pskl_wrt_pskl ?B (pskl_tophole pskl_hole)) |- _ ] =>
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_tophole pskl_hole)) as Hbr;
        simpl in Hbr
    end; fsetdec).
  (* Cofinite quantifier cases: open at a fresh [b], bound it away. *)
  all: (
    pick fresh b;
    repeat match goal with
    | [ H : forall x : atom, x `notin` ?L -> _ |- _ ] => specialize (H b ltac:(fsetdec))
    end;
    simpl in *;
    match goal with
    | [ |- ftvar_in_pskl ?P' [<=] ftvar_in_pskl ?P `union` ftvar_in_pskl ?Q ] =>
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P' (pskl_var_f b));
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b));
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f b))
    end;
    simpl in *; fsetdec).
Qed.
