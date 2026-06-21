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
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.

Set Implicit Arguments.

Scheme a_looksub_mut := Minimality for a_looksub Sort Prop
  with a_lookeq_mut  := Minimality for a_lookeq  Sort Prop.
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
  (* PLAN (next): mutual induction via [a_looksub_lookeq_mutind].  Per case,
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
Admitted.
