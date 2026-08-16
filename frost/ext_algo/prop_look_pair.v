(** ext_algo — THE b-CORE'S HOME (campaign §8c.9 §6b): the fused
    look-pair/fold-transport lemma over SUPPLY-THREADED looks, and its
    e-side prerequisites.

    §1 is the e-side look kit the pair induction leans on:

    §1a  the e-look's context is INERT (every freshness condition reads
         the SUPPLY), so derivations transport to ANY context — which is
         what replaces the a-side [a_looksub_ctx_exchange] surgery;
    §1b  the two supply indexes transport along [=] (the re-rootings
         re-associate [add]s, which is only a [=]-equality);
    §1c  the COLLECTION-PRESERVING re-rootings, e-side: R″
         ([e_looksub_strip_tophole_l] — outputs AND supplies exact) and
         R′ ([e_looksub_open_forall_l_first]) — ⭐ stated with an
         EXISTENTIAL opener, which kills the whole rebinding apparatus:
         in its ForallL case the premise IS the goal at the derivation's
         own opener (+ ctx_any), and in its ForallR case the IH's opener
         is reused below the rebuilt root (+ supply respect for the
         [add]-exchange) — so unlike the a-side R′
         (prop_look_equiv.v §6) NO swap is ever performed, and no e-side
         swap kit exists or is needed.

    §2 is the b-core KIT (fourth pass), §3 the b-core itself
    (forthcoming): the pair induction is RUNNER-SIDED — side 1 an
    arbitrary e-derivation (the Hhyg premise), side 2 the RUNNER's
    computation ([e_lookeq_impl]/[e_looksub_impl] = Some) — because the
    two-arbitrary-derivations form is FALSE
    (cex/probe_bcore_ug2_flexr.v: LE-FlexR × LE-UnivGhost2 overlap at a
    (⫯, var) node; a variable is [guarded_pskl]).  See
    HANDOFF-extractable-algo-encoding.md §8c.9, third + fourth passes.
    ⚙ §1c's R″/R′ are NOT consumed by the runner-sided b-core (the
    diagonals re-root SIDE 1 by §2c's ForallR-first instead); they stay
    as kit. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_ln.
Require Import src.frost.def_shapes.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.sub.prop_looksub.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.prop_look.
Require Import src.frost.ext_algo.prop_look_equiv.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.prop_solve.
Require Import src.frost.ext_algo.prop_solve_det.
Require Import src.frost.ext_algo.prop_solve_rel.
Require Import src.frost.ext_algo.prop_run_complete.

Set Implicit Arguments.

Open Scope frost_a_scope.
Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1a  The e-look's context is INERT                                    *)
(*                                                                        *)
(*  Every freshness side condition of the e-encoding reads the SUPPLY;    *)
(*  the context is carried only to mirror the a-shape (the projection     *)
(*  [e_looksub_sound] reintroduces context-freshness from coverage).  So  *)
(*  a derivation transports to ANY context — the re-rootings below lean   *)
(*  on this where the a-side versions needed [a_looksub_ctx_exchange].    *)
(* ===================================================================== *)

Lemma e_looksub_lookeq_ctx_any :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     forall Θ', {{ S0 ↝ S1 ⊨ Θ' ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     forall Θ', {{ S0 ↝ S1 ⊨ Θ' ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e).
Proof.
  apply (e_looksub_lookeq_mutind
           (fun S0 Θ α m P P' S1 Ξ C _ =>
              forall Θ', {{ S0 ↝ S1 ⊨ Θ' ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e)
           (fun S0 Θ α P P' S1 Ξ C _ =>
              forall Θ', {{ S0 ↝ S1 ⊨ Θ' ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e));
    intros;
    eauto using e_looksub__var, e_looksub__absent, e_looksub__vacuous,
      e_looksub__check, e_looksub__forall_r, e_looksub__arrow,
      e_looksub__forall_l, e_looksub__univ_ghost_l,
      e_lookeq__var, e_lookeq__absent, e_lookeq__vacuous,
      e_lookeq__flex_r, e_lookeq__arrow, e_lookeq__forall_inh,
      e_lookeq__forall_syn, e_lookeq__univ_ghost, e_lookeq__univ_ghost1,
      e_lookeq__univ_ghost2, e_lookeq__univ_ghost_r.
Qed.

(* ===================================================================== *)
(*  §1b  Supply respect: the two supply indexes transport along [=]       *)
(* ===================================================================== *)

Lemma e_looksub_lookeq_supply_respect :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e).
Proof.
  apply (e_looksub_lookeq_mutind
           (fun S0 Θ α m P P' S1 Ξ C _ =>
              forall S0', S0' [=] S0 ->
              exists S1', S1' [=] S1 /\
                {{ S0' ↝ S1' ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e)
           (fun S0 Θ α P P' S1 Ξ C _ =>
              forall S0', S0' [=] S0 ->
              exists S1', S1' [=] S1 /\
                {{ S0' ↝ S1' ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e)).
  - (* LS-Var *)
    intros * Heq. eexists. split; [ exact Heq | ].
    apply e_looksub__var.
  - (* LS-Absent *)
    intros * Habs * Heq. eexists. split; [ exact Heq | ].
    apply e_looksub__absent. exact Habs.
  - (* LS-Vacuous *)
    intros * Heq. eexists. split; [ exact Heq | ].
    apply e_looksub__vacuous.
  - (* LS-Check *)
    intros * Hgf Hne HgA HgB Hd IH S0' Heq.
    destruct (IH S0' Heq) as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_looksub__check; assumption.
  - (* LS-ForallR *)
    intros * Hgf Hβ Hd IH S0' Heq.
    destruct (IH (add β S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_looksub__forall_r with (β := β);
      [ assumption | rewrite Heq; assumption | exact Hd' ].
  - (* LS-Arrow *)
    intros * Hd1 IH1 Hd2 IH2 S0' Heq.
    destruct (IH1 S0' Heq) as [S1' [Heq1 Hd1']].
    destruct (IH2 S1' Heq1) as [S2' [Heq2 Hd2']].
    exists S2'. split; [ exact Heq2 | ].
    eapply e_looksub__arrow; [ exact Hd1' | exact Hd2' ].
  - (* LS-ForallL *)
    intros * Hβ Hd IH S0' Heq.
    destruct (IH (add β S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_looksub__forall_l with (β := β);
      [ rewrite Heq; assumption | exact Hd' ].
  - (* LS-UnivGhostL *)
    intros * Hd IH S0' Heq.
    destruct (IH S0' Heq) as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_looksub__univ_ghost_l. exact Hd'.
  - (* LE-Var *)
    intros * Heq. eexists. split; [ exact Heq | ].
    apply e_lookeq__var.
  - (* LE-Absent *)
    intros * Habs * Heq. eexists. split; [ exact Heq | ].
    apply e_lookeq__absent. exact Habs.
  - (* LE-Vacuous *)
    intros * Heq. eexists. split; [ exact Heq | ].
    apply e_lookeq__vacuous.
  - (* LE-FlexR *)
    intros * Hα1 Hne Hocc S0' Heq.
    exists (add α1 S0'). split; [ rewrite Heq; reflexivity | ].
    apply e_lookeq__flex_r;
      [ rewrite Heq; assumption | assumption | assumption ].
  - (* LE-Arrow *)
    intros * Hd1 IH1 Hd2 IH2 S0' Heq.
    destruct (IH1 S0' Heq) as [S1' [Heq1 Hd1']].
    destruct (IH2 S1' Heq1) as [S2' [Heq2 Hd2']].
    exists S2'. split; [ exact Heq2 | ].
    eapply e_lookeq__arrow; [ exact Hd1' | exact Hd2' ].
  - (* LE-ForallInh *)
    intros * Hβ Hd IH S0' Heq.
    destruct (IH (add β S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__forall_inh with (β := β);
      [ rewrite Heq; assumption | exact Hd' ].
  - (* LE-ForallSyn *)
    intros * Hβ Hd IH S0' Heq.
    destruct (IH (add β S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__forall_syn with (β := β);
      [ rewrite Heq; assumption | exact Hd' ].
  - (* LE-UnivGhost *)
    intros * Hd IH S0' Heq.
    destruct (IH S0' Heq) as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__univ_ghost. exact Hd'.
  - (* LE-UnivGhost1 *)
    intros * Hβ Hd IH S0' Heq.
    destruct (IH (add β S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__univ_ghost1 with (β := β);
      [ rewrite Heq; assumption | exact Hd' ].
  - (* LE-UnivGhost2 *)
    intros * Hg Hd IH S0' Heq.
    destruct (IH S0' Heq) as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__univ_ghost2; [ assumption | exact Hd' ].
  - (* LE-UnivGhostR *)
    intros * Hne Hg Hd IH S0' Heq.
    destruct (IH S0' Heq) as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__univ_ghost_r; [ assumption | assumption | exact Hd' ].
Qed.

(* ===================================================================== *)
(*  §1c  The COLLECTION-PRESERVING re-rootings, e-side (R″ and R′)        *)
(*                                                                        *)
(*  Mirrors of prop_look_equiv.v §6, leaning on the inert context.  R′    *)
(*  is stated with an EXISTENTIAL opener: in its ForallL case the        *)
(*  premise IS the goal at the derivation's own opener, so no rebinding  *)
(*  (hence no e-swap kit) is ever needed.                                *)
(* ===================================================================== *)

(** R″ — strip a ⫯ subject to the front; outputs AND supplies exact. *)
Lemma e_looksub_strip_tophole_l : forall S0 Θ α m P0 P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole P0) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ P0 ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H.
  remember (pskl_tophole P0) as S eqn:HS.
  revert P0 HS.
  induction H; intros P0' HS; inversion HS; subst.
  - (* LS-Absent *)
    apply e_looksub__absent. simpl in *. assumption.
  - (* LS-Vacuous *)
    apply e_looksub__vacuous.
  - (* LS-Check: a ⫯ subject is not guarded *)
    match goal with
    | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
    end.
  - (* LS-ForallR *)
    apply e_looksub__forall_r with (β := β);
      [ assumption | assumption | ].
    apply IHe_looksub. reflexivity.
  - (* LS-UnivGhostL *)
    assumption.
Qed.

(** R′ — open a ∀ subject at the front, at SOME supply-fresh opener;
    outputs exact, the output supply exact up to [=] after inserting the
    opener.  Size induction on the TARGET (only LS-ForallR recurses). *)
Lemma e_looksub_open_forall_l_first_n : forall n S0 Θ α m P0 P' S1 Ξ C,
  size_pskl P' < n ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P0) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  exists γ S1',
    γ `notin` S0 /\
    {{ (add γ S0) ↝ S1' ⊨ ((γ ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P0 (pskl_var_f γ)) ≼[ α , m ] P'
       ⤳ Ξ ⨾ C }}e.
Proof.
  induction n as [ | n IH ]; intros * Hsz Hd;
    [ exfalso; clear - Hsz; lia | ].
  inversion Hd; subst.
  - (* LS-Absent — ⚙ the S ↝ S leaf merged the lemma's two supplies *)
    match goal with
    | |- exists _ _, _ `notin` ?SS /\ _ =>
        destruct (atom_fresh (add α SS)) as [γ Hγ];
        exists γ, (add γ SS)
    end.
    split; [ clear - Hγ; fsetdec | ].
    apply e_looksub__absent.
    match goal with
    | Ha : α `notin` ftvar_in_pskl (pskl_all_syn _) |- _ =>
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0
                      (pskl_var_f γ)) as Hup;
        simpl in Ha; clear - Ha Hγ Hup; simpl in *; fsetdec
    end.
  - (* LS-Vacuous — same merge *)
    match goal with
    | |- exists _ _, _ `notin` ?SS /\ _ =>
        destruct (atom_fresh (add α SS)) as [γ Hγ];
        exists γ, (add γ SS)
    end.
    split; [ clear - Hγ; fsetdec | ].
    apply e_looksub__vacuous.
  - (* LS-Check: a ∀ subject is not guarded *)
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  - (* LS-ForallR: recurse below at the premise, then exchange supplies *)
    match goal with
    | Hp : e_looksub (add ?b S0) _ _ _ _ _ _ _ _ |- _ =>
        rename Hp into Hprem; rename b into β1
    end.
    assert (Hszp : size_pskl (open_pskl_wrt_pskl B (pskl_var_f β1)) < n)
      by (rewrite size_pskl_open_pskl_wrt_pskl_var;
          clear - Hsz; simpl in *; lia).
    destruct (IH _ _ _ _ _ _ _ _ _ Hszp Hprem)
      as (γ & S1' & Hγ & Hd').
    destruct ((proj1 e_looksub_lookeq_supply_respect) _ _ _ _ _ _ _ _ _ Hd'
                (add β1 (add γ S0)) ltac:(clear; fsetdec))
      as [S1'' [Heq Hd'']].
    pose proof ((proj1 e_looksub_lookeq_ctx_any) _ _ _ _ _ _ _ _ _ Hd''
                  ((β1 ~ abind_tvar) ++ (γ ~ abind_tvar) ++ Θ)) as Hd3.
    exists γ, S1''.
    split; [ clear - Hγ; fsetdec | ].
    apply e_looksub__forall_r with (β := β1);
      [ assumption | clear - Hγ H0; fsetdec | exact Hd3 ].
  - (* LS-ForallL: the premise IS the goal at its own opener *)
    match goal with
    | Hp : e_looksub (add ?b S0) _ _ _ _ _ _ _ _ |- _ =>
        rename Hp into Hprem; rename b into β1
    end.
    exists β1, S1.
    split; [ assumption | ].
    exact ((proj1 e_looksub_lookeq_ctx_any) _ _ _ _ _ _ _ _ _ Hprem
             ((β1 ~ abind_tvar) ++ Θ)).
Qed.

(** R′, packaged. *)
Lemma e_looksub_open_forall_l_first : forall S0 Θ α m P0 P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P0) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  exists γ S1',
    γ `notin` S0 /\
    {{ (add γ S0) ↝ S1' ⊨ ((γ ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P0 (pskl_var_f γ)) ≼[ α , m ] P'
       ⤳ Ξ ⨾ C }}e.
Proof.
  intros * Hd.
  exact (@e_looksub_open_forall_l_first_n (S (size_pskl P'))
           S0 Θ α m P0 P' S1 Ξ C ltac:(lia) Hd).
Qed.

(* ===================================================================== *)
(*  §2  THE b-CORE KIT (campaign §8c.9, fourth pass)                      *)
(*                                                                        *)
(*  Support for the RUNNER-SIDED pair induction (see the handoff's        *)
(*  fourth pass, and cex/probe_bcore_ug2_flexr.v for why side 2 must be   *)
(*  the runner's computation):                                            *)
(*    §2a  flex_agree_rel extensions (iff-pair cons, one-sided rigid      *)
(*         pushes) — the agreement moves the pair cases make;             *)
(*    §2b  e-side collection structure (pure-eq, shape, α-free and        *)
(*         ◇-target collapses, the var-target inversion, the TIGHT        *)
(*         interval bound) — side 1's inversion tools;                    *)
(*    §2c  the DISJUNCTIVE e-ForallR-first re-rooting — side 1's move at  *)
(*         the (ForallL/UGL vs runner-ForallR) diagonals; its Var-bottom  *)
(*         disjunct legitimately CHANGES the final sub-constraint, paid   *)
(*         by §2g's keep-peel;                                            *)
(*    §2d  the fold at a VAR pattern is a fixed point (build + invert) —  *)
(*         what makes the eq-motive's yield HATCH harmless;               *)
(*    §2e  fold structure facts (generated-fresh, pure-eq ftv bound);     *)
(*    §2f  the JUNK-TARGET head transport — the (side-1 raw var target    *)
(*         vs runner fresh-flexible) divergence, rel-or-hatch;            *)
(*    §2g  the KEEP-variant of §6a's ∀-peel (conclusion at the consed     *)
(*         context — SS-ForallR's premise shape, no strip);               *)
(*    §2h  e-solve context equivalence — rigid entries are invisible, so  *)
(*         an e-fold weakens to the ENRICHED context (the assembly's      *)
(*         move; the b-core's scoping premises read the enriched Θf).     *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §2a  flex_agree_rel extensions                                        *)
(* ===================================================================== *)

Lemma flex_agree_rel_extend_pair_iff : forall ρ V Θ1 Θ2 a b,
  flex_agree_rel ρ V Θ1 Θ2 ->
  (a_flex_tvar Θ1 a <-> a_flex_tvar Θ2 b) ->
  flex_agree_rel ((a, b) :: ρ) V Θ1 Θ2.
Proof.
  intros * [HV Hp] Hiff. split; [ exact HV | ].
  intros x y [E | Hin]; [ inversion E; subst; exact Hiff | exact (Hp _ _ Hin) ].
Qed.

Lemma flex_agree_rel_push_tvar_l : forall ρ V Θ1 Θ2 β,
  flex_agree_rel ρ V Θ1 Θ2 ->
  β `notin` V ∪ cols_l ρ ->
  flex_agree_rel ρ V ((β ~ abind_tvar) ++ Θ1) Θ2.
Proof.
  intros * [HV Hp] Hβ. split.
  - intros x Hx.
    assert (Hne : x <> β) by (clear - Hx Hβ; fsetdec).
    rewrite (a_flex_tvar_cons_tvar_other Θ1 Hne). apply HV. exact Hx.
  - intros a b Hin.
    pose proof (cols_l_in _ _ _ Hin) as Hc.
    assert (Hne : a <> β) by (clear - Hc Hβ; fsetdec).
    rewrite (a_flex_tvar_cons_tvar_other Θ1 Hne). apply Hp. exact Hin.
Qed.

Lemma flex_agree_rel_push_tvar_r : forall ρ V Θ1 Θ2 β,
  flex_agree_rel ρ V Θ1 Θ2 ->
  β `notin` V ∪ cols_r ρ ->
  flex_agree_rel ρ V Θ1 ((β ~ abind_tvar) ++ Θ2).
Proof.
  intros * [HV Hp] Hβ. split.
  - intros x Hx.
    assert (Hne : x <> β) by (clear - Hx Hβ; fsetdec).
    rewrite (a_flex_tvar_cons_tvar_other Θ2 Hne). apply HV. exact Hx.
  - intros a b Hin.
    pose proof (cols_r_in _ _ _ Hin) as Hc.
    assert (Hne : b <> β) by (clear - Hc Hβ; fsetdec).
    rewrite (a_flex_tvar_cons_tvar_other Θ2 Hne). apply Hp. exact Hin.
Qed.

(* ===================================================================== *)
(*  §2b  e-side collection structure                                      *)
(* ===================================================================== *)

Lemma e_lookeq_cstrs_pure_eq : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  Forall a_cstr_is_eq C.
Proof.
  intros * H.
  induction H; try solve [ constructor ]; auto.
  - constructor; [ exists P; reflexivity | constructor ].
  - constructor; [ eexists; reflexivity | constructor ].
  - apply Forall_app; split; assumption.
Qed.

(** A looksub collection is a pure-eq prefix + at most one terminal sub. *)
Lemma e_looksub_cstrs_shape : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  exists Ce Cs, C = Ce ++ Cs /\ Forall a_cstr_is_eq Ce
    /\ (Cs = nil \/ exists m' Q, Cs = a_cstr_sub m' Q :: nil).
Proof.
  intros * H.
  induction H;
    try solve
      [ exists nil, nil; simpl; repeat split; [ constructor | left; reflexivity ] ];
    try solve [ assumption ].
  - (* LS-Var *)
    exists nil, (a_cstr_sub m P :: nil). simpl. repeat split;
      [ constructor | right; eauto ].
  - (* LS-Check: pure-eq *)
    exists C, nil. rewrite app_nil_r. repeat split;
      [ eapply e_lookeq_cstrs_pure_eq; eassumption | left; reflexivity ].
  - (* LS-Arrow *)
    destruct IHe_looksub as (Ce & Cs & -> & Hpe & Hcs).
    exists (C1 ++ Ce), Cs. repeat split.
    + solve [ apply app_assoc | symmetry; apply app_assoc ].
    + apply Forall_app. split;
        [ eapply e_lookeq_cstrs_pure_eq; eassumption | exact Hpe ].
    + exact Hcs.
Qed.

Lemma e_lookeq_subject_absent : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  α `in` S0 ->
  α `notin` ftvar_in_pskl P ->
  Ξ = nil /\ C = nil.
Proof.
  intros * H.
  induction H; intros HαS Habs; simpl in *;
    (* the two S ↝ S leaves *)
    try solve [ split; reflexivity ];
    (* the rows whose subject shares the premise's ftv (⫯-unfolds), and the
       binder rows — the IH's supply obligation closes by fsetdec *)
    try solve
      [ apply IHe_lookeq;
        [ solve [ exact HαS | clear - HαS; fsetdec ]
        | solve
            [ exact Habs
            | clear - Habs; fsetdec
            | match goal with
              | |- α `notin` ftvar_in_pskl
                     (open_pskl_wrt_pskl ?PP (pskl_var_f ?bb)) =>
                  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                PP (pskl_var_f bb)) as Hup;
                  match goal with
                  | Hfr : bb `notin` _ |- _ =>
                      clear - Habs Hfr Hup HαS; simpl in *; fsetdec
                  end
              end ] ] ].
  - (* LE-Var *) exfalso. clear - Habs. fsetdec.
  - (* LE-FlexR *)
    exfalso.
    match goal with
    | Hin : α `in` ftvar_in_pskl _ |- _ => clear - Habs Hin; fsetdec
    end.
  - (* LE-Arrow *)
    pose proof (e_lookeq_supply_grows H) as Hg.
    destruct IHe_lookeq1 as [-> ->];
      [ exact HαS | clear - Habs; fsetdec | ].
    destruct IHe_lookeq2 as [-> ->];
      [ clear - HαS Hg; fsetdec | clear - Habs; fsetdec | ].
    split; reflexivity.
Qed.

Lemma e_looksub_subject_absent : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  α `in` S0 ->
  α `notin` ftvar_in_pskl P ->
  Ξ = nil /\ C = nil.
Proof.
  intros * H.
  induction H; intros HαS Habs; simpl in *;
    (* the S ↝ S leaves *)
    try solve [ split; reflexivity ];
    (* LS-Var: the subject IS α *)
    try solve [ exfalso; clear - Habs; fsetdec ];
    (* LS-Check: drops into the eq layer *)
    try solve
      [ match goal with
        | He : e_lookeq _ _ _ _ _ _ _ _ |- _ =>
            eapply e_lookeq_subject_absent;
            [ exact He | exact HαS | exact Habs ]
        end ];
    (* ForallR / ForallL / UnivGhostL: one premise, subject material ⊆ *)
    try solve
      [ apply IHe_looksub;
        [ solve [ exact HαS | clear - HαS; fsetdec ]
        | solve
            [ exact Habs
            | clear - Habs; fsetdec
            | match goal with
              | |- α `notin` ftvar_in_pskl
                     (open_pskl_wrt_pskl ?PP (pskl_var_f ?bb)) =>
                  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                PP (pskl_var_f bb)) as Hup;
                  match goal with
                  | Hfr : bb `notin` _ |- _ =>
                      clear - Habs Hfr Hup HαS; simpl in *; fsetdec
                  end
              end ] ] ].
  (* LS-Arrow *)
  match goal with
  | He : e_lookeq _ _ _ ?A _ _ _ _ |- _ =>
      pose proof (e_lookeq_supply_grows He) as Hg;
      assert (Habs1 : α `notin` ftvar_in_pskl A)
        by (clear - Habs; fsetdec);
      destruct (e_lookeq_subject_absent He HαS Habs1) as [-> ->]
  end.
  destruct IHe_looksub as [-> ->];
    [ clear - HαS Hg; fsetdec | clear - Habs; fsetdec | ].
  split; reflexivity.
Qed.

Lemma e_lookeq_hole_target : forall S0 Θ α P S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] pskl_hole ⤳ Ξ ⨾ C }}e ->
  Ξ = nil /\ (C = nil \/ C = a_cstr_eq pskl_hole :: nil).
Proof.
  intros * H.
  inversion H; subst; auto.
  match goal with
  | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
  end.
Qed.

Lemma e_looksub_hole_target : forall S0 Θ α m P S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] pskl_hole ⤳ Ξ ⨾ C }}e ->
  Ξ = nil /\ (C = nil \/ C = a_cstr_sub m pskl_hole :: nil).
Proof.
  intros * H.
  remember pskl_hole as T eqn:HT.
  induction H; inversion HT; subst.
  - (* LS-Var *) split; [ reflexivity | right; reflexivity ].
  - (* LS-Absent *) auto.
  - (* LS-Vacuous *) auto.
  - (* LS-Check: guarded ◇ has no constructor *)
    match goal with
    | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
    end.
  - (* LS-ForallL *) apply IHe_looksub. reflexivity.
  - (* LS-UnivGhostL *) apply IHe_looksub. reflexivity.
Qed.

(** At a VAR target every derivation either retains the raw target or
    replaces it by one fresh flexible (LE-FlexR, possibly under UG2s). *)
Lemma e_lookeq_var_target_inv : forall S0 Θ α P t S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] (pskl_var_f t) ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl P ->
  (Ξ = nil /\ C = a_cstr_eq (pskl_var_f t) :: nil)
  \/ (exists α1, Ξ = (α1 ~ abind_flex_mono) ++ nil
        /\ C = a_cstr_eq (pskl_var_f α1) :: nil
        /\ α1 `in` S1 /\ α1 `notin` S0).
Proof.
  intros * H.
  remember (pskl_var_f t) as T eqn:HT.
  induction H; inversion HT; subst; intros Hα.
  - (* LE-Var *) left. auto.
  - (* LE-Absent *) exfalso. clear - Hα H. fsetdec.
  - (* LE-FlexR *)
    right. exists α1. repeat split; auto.
  - (* LE-UnivGhost2 *)
    apply IHe_lookeq; [ reflexivity | simpl in Hα; exact Hα ].
Qed.

(** The TIGHT collection bound: constraints mention only the supply
    INTERVAL and the two inputs' variables. *)
Lemma e_looksub_lookeq_cstr_ftvar_tight :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     ftvar_in_a_cstrs C
       [<=] (S1 ∖ S0) ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     ftvar_in_a_cstrs C
       [<=] (S1 ∖ S0) ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P').
Proof.
  apply (e_looksub_lookeq_mutind
           (fun S0 Θ α m P P' S1 Ξ C _ =>
              ftvar_in_a_cstrs C
                [<=] (S1 ∖ S0) ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P')
           (fun S0 Θ α P P' S1 Ξ C _ =>
              ftvar_in_a_cstrs C
                [<=] (S1 ∖ S0) ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P'));
    intros;
    repeat match goal with
           | H : e_looksub ?a _ _ _ _ _ ?b _ _ |- _ =>
               lazymatch goal with
               | _ : a [<=] b |- _ => fail
               | _ => pose proof (e_looksub_supply_grows H)
               end
           | H : e_lookeq ?a _ _ _ _ ?b _ _ |- _ =>
               lazymatch goal with
               | _ : a [<=] b |- _ => fail
               | _ => pose proof (e_lookeq_supply_grows H)
               end
           end;
    repeat match goal with
           | H : context [ ftvar_in_pskl (open_pskl_wrt_pskl ?P (pskl_var_f ?b)) ] |- _ =>
               lazymatch goal with
               | _ : ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
                       [<=] ftvar_in_pskl (pskl_var_f b) ∪ ftvar_in_pskl P |- _ => fail
               | _ => pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b))
               end
           end;
    repeat rewrite ftvar_in_a_cstrs_app;
    simpl in *; fsetdec.
Qed.

(* ===================================================================== *)
(*  §2c  the disjunctive e-ForallR-FIRST re-rooting (side 1's move)       *)
(* ===================================================================== *)

Lemma e_looksub_forall_r_first : forall S0 Θ α P B S1 Ξ C (Lβ : atoms),
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl P ->
  exists β1 S1' Ξ' C',
    β1 `notin` S0 /\ S1' [=] add β1 S1 /\
    {{ (add β1 S0) ↝ S1' ⊨ ((β1 ~ abind_tvar) ++ Θ)
       ⊢ P ≼[ α , mode_tc ] (open_pskl_wrt_pskl B (pskl_var_f β1))
       ⤳ Ξ' ⨾ C' }}e /\
    ( (β1 `in` S1 /\ Ξ' = Ξ /\ C' = C)
      \/ (β1 `notin` Lβ /\ Ξ = nil
          /\ C = a_cstr_sub mode_tc (pskl_all_syn B) :: nil
          /\ Ξ' = nil
          /\ C' = a_cstr_sub mode_tc
                    (open_pskl_wrt_pskl B (pskl_var_f β1)) :: nil) ).
Proof.
  intros * H.
  remember (pskl_all_syn B) as T eqn:HT.
  remember mode_tc as m0 eqn:Hm.
  revert B HT.
  induction H; intros B0 HT Hα; inversion HT; subst; subst.
  - (* LS-Var: the Var bottom — outputs change, disjunct 2 *)
    destruct (atom_fresh (S ∪ Lβ)) as [β1 Hβ1].
    exists β1, (add β1 S), nil,
      (a_cstr_sub mode_tc (open_pskl_wrt_pskl B0 (pskl_var_f β1)) :: nil).
    split; [ clear - Hβ1; fsetdec | ].
    split; [ reflexivity | ].
    split; [ apply e_looksub__var | ].
    right.
    split; [ clear - Hβ1; fsetdec | ].
    repeat (split; [ reflexivity | ]); reflexivity.
  - (* LS-Absent *)
    exfalso. clear - Hα H. fsetdec.
  - (* LS-Check: a ∀ target is not guarded *)
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  - (* LS-ForallR: done — the premise IS the re-rooted derivation *)
    match goal with
    | Hp : e_looksub (add β S0) _ _ _ _ _ S1 _ _ |- _ =>
        pose proof (e_looksub_supply_grows Hp) as Hg
    end.
    exists β, S1, Ξ, C.
    split; [ assumption | ].
    split; [ clear - Hg; fsetdec | ].
    split; [ assumption | ].
    left.
    split; [ clear - Hg; fsetdec | ].
    split; reflexivity.
  - (* LS-ForallL: recurse, exchange supplies/contexts, rebuild *)
    match goal with
    | Hfr : β `notin` S0, Hp : e_looksub (add β S0) _ _ _ _ _ _ _ _ |- _ =>
        rename Hfr into Hγfr; rename Hp into Hprem; rename β into γ
    end.
    assert (Hαo : α `in`
              ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f γ))).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f γ)) as Hlo.
      simpl in Hα. clear - Hα Hlo. fsetdec. }
    destruct (IHe_looksub eq_refl _ eq_refl Hαo)
      as (β1 & S1' & Ξ' & C' & Hβ1 & HS1' & Hd & Hdisj).
    destruct ((proj1 e_looksub_lookeq_supply_respect)
                _ _ _ _ _ _ _ _ _ Hd (add γ (add β1 S0))
                ltac:(clear; fsetdec))
      as [S1'' [HS1'' Hd']].
    pose proof ((proj1 e_looksub_lookeq_ctx_any) _ _ _ _ _ _ _ _ _ Hd'
                  ((γ ~ abind_tvar) ++ (β1 ~ abind_tvar) ++ Θ)) as Hd''.
    exists β1, S1'', Ξ', C'.
    split; [ clear - Hβ1; fsetdec | ].
    split; [ rewrite HS1''; exact HS1' | ].
    split.
    { apply e_looksub__forall_l with (β := γ);
        [ clear - Hγfr Hβ1; fsetdec | exact Hd'' ]. }
    destruct Hdisj as [ (HinS & -> & ->) | (HL & -> & -> & -> & ->) ].
    + left. split; [ assumption | ]. split; reflexivity.
    + right. split; [ assumption | ].
      repeat (split; [ reflexivity | ]); reflexivity.
  - (* LS-UnivGhostL: recurse and rebuild *)
    simpl in Hα.
    destruct (IHe_looksub eq_refl _ eq_refl Hα)
      as (β1 & S1' & Ξ' & C' & Hβ1 & HS1' & Hd & Hdisj).
    exists β1, S1', Ξ', C'.
    split; [ assumption | ].
    split; [ assumption | ].
    split; [ apply e_looksub__univ_ghost_l; exact Hd | ].
    destruct Hdisj as [ (HinS & -> & ->) | (HL & -> & -> & -> & ->) ].
    + left. split; [ assumption | ]. split; reflexivity.
    + right. split; [ assumption | ].
      repeat (split; [ reflexivity | ]); reflexivity.
Qed.

(* ===================================================================== *)
(*  §2d  the fold at a VAR pattern — a fixed point                        *)
(* ===================================================================== *)

Lemma a_solve_eq_var_subject_inv : forall Θ γ Q Ξ P',
  {{ Θ ⊢ₑ (pskl_var_f γ) ∼ Q ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = pskl_var_f γ.
Proof.
  intros * H.
  remember (pskl_var_f γ) as S eqn:HS.
  induction H; inversion HS; subst.
  - (* SE-Var *) auto.
  - (* SE-FlexR: guess of a var is the var *)
    match goal with
    | HG : a_guess_mono _ (pskl_var_f γ) _ _ |- _ => inversion HG; subst
    end.
    simpl. auto.
  - (* SE-VacuousR *) auto.
  - (* SE-GuardedGhost *) apply IHa_solve_eq. reflexivity.
Qed.

Lemma a_solve_cstr_var_subject_inv : forall C Θ γ Ξ Q,
  Forall a_cstr_is_eq C ->
  {{ Θ ⊩ C ⨾ (pskl_var_f γ) ⤳ Ξ ⨾ Q }}a ->
  Ξ = nil /\ Q = pskl_var_f γ.
Proof.
  induction C as [ | c C' IH ]; intros * Hpe Hd.
  - inversion Hd; subst. auto.
  - inversion Hpe as [ | ? ? [Q0 HQ0] Hpe' ]; subst.
    apply a_solve_cstr_eq_inv in Hd as (Ξ1 & Ξ2 & Pmid & -> & Hh & Ht).
    destruct (a_solve_eq_var_subject_inv Hh) as [-> ->].
    destruct (IH _ _ _ _ Hpe' Ht) as [-> ->].
    auto.
Qed.

Lemma a_solve_cstr_var_subject : forall C Θ γ,
  Forall a_cstr_is_eq C ->
  {{ Θ ⊩ C ⨾ (pskl_var_f γ) ⤳ nil ⨾ (pskl_var_f γ) }}a.
Proof.
  induction C as [ | c C' IH ]; intros * Hpe.
  - apply a_solve_cstr__empty.
  - inversion Hpe as [ | ? ? [Q0 HQ0] Hpe' ]; subst.
    replace (@nil (atom * abind))
      with (@nil (atom * abind) ++ @nil (atom * abind)) by reflexivity.
    eapply a_solve_cstr__eq.
    + apply a_solve_eq__var.
    + simpl. apply IH. exact Hpe'.
Qed.

Lemma a_solve_cstr_var_subject_sub : forall C Θ γ m Q,
  Forall a_cstr_is_eq C ->
  {{ Θ ⊩ (C ++ (a_cstr_sub m Q :: nil)) ⨾ (pskl_var_f γ)
     ⤳ nil ⨾ (pskl_var_f γ) }}a.
Proof.
  induction C as [ | c C' IH ]; intros * Hpe; simpl.
  - apply a_solve_cstr__sub. apply a_solve_sub__var.
  - inversion Hpe as [ | ? ? [Q0 HQ0] Hpe' ]; subst.
    replace (@nil (atom * abind))
      with (@nil (atom * abind) ++ @nil (atom * abind)) by reflexivity.
    eapply a_solve_cstr__eq.
    + apply a_solve_eq__var.
    + simpl. apply IH. exact Hpe'.
Qed.

(* ===================================================================== *)
(*  §2e  fold structure facts                                             *)
(* ===================================================================== *)

Lemma a_solve_cstr_generated_fresh_set : forall Θ C P Ξ P',
  {{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ P' }}a ->
  dom Ξ ∩ ftvar_in_aenv Θ [=] empty.
Proof.
  intros * H; induction H.
  - simpl. clear. fsetdec.
  - eapply (proj1 a_solve_sub_eq_generated_fresh_set). eassumption.
  - match goal with
    | He : a_solve_eq _ _ _ _ _ |- _ =>
        pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                      _ _ _ _ _ He) as Hh
    end.
    rewrite ftvar_in_aenv_app in IHa_solve_cstr.
    rewrite dom_app.
    clear - Hh IHa_solve_cstr. fsetdec.
Qed.

Lemma a_solve_cstr_pure_eq_ftv : forall Θ C P Ξ P',
  Forall a_cstr_is_eq C ->
  {{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ P' }}a ->
  ftvar_in_pskl P' [<=] ftvar_in_pskl P ∪ ftvar_in_a_cstrs C ∪ dom Ξ.
Proof.
  intros * Hpe Hd; induction Hd.
  - simpl. clear. fsetdec.
  - (* a sub head contradicts pure-eq *)
    inversion Hpe as [ | ? ? [? Heq] ]; subst. discriminate.
  - inversion Hpe as [ | ? ? _ Hpe' ]; subst.
    match goal with
    | He : a_solve_eq _ _ _ _ _ |- _ =>
        pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ _ He) as Hh
    end.
    specialize (IHHd Hpe').
    rewrite dom_app. simpl.
    clear - Hh IHHd. fsetdec.
Qed.

(* ===================================================================== *)
(*  §2f  the JUNK-TARGET head transport                                   *)
(* ===================================================================== *)

Lemma a_solve_eq_var_target_junk : forall Θ1 acc1 t1 Ξh mid1,
  {{ Θ1 ⊢ₑ acc1 ∼ (pskl_var_f t1) ⤳ Ξh ⨾ mid1 }}a ->
  forall Θ2 (L : atoms) acc2 t2 ρ V,
  rel_pskl ρ V acc1 acc2 ->
  a_flex_tvar Θ2 t2 ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  V ∪ cols_r ρ [<=] ftvar_in_aenv Θ2 ->
  exists ρn Ξh2 mid2,
    {{ Θ2 ⊢ₑ acc2 ∼ (pskl_var_f t2) ⤳ Ξh2 ⨾ mid2 }}a
    /\ Ξh = flex_pairs_l ρn /\ Ξh2 = flex_pairs_r ρn
    /\ uniq Ξh2 /\ dom Ξh2 ∩ L [=] empty
    /\ ( rel_pskl (ρn ++ ρ) V mid1 mid2
         \/ (mid1 = pskl_var_f t1 /\ mid2 = pskl_var_f t2) ).
Proof.
  intros Θ1 acc1 t1 Ξh mid1 HD.
  remember (pskl_var_f t1) as T eqn:HT.
  induction HD; inversion HT; subst;
    intros Θ2 L acc2 t2 ρ V Hrel Ht2 Hagr Hscp1 Hscp2.
  - (* SE-Var *)
    inversion Hrel; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ => rename Ha into Hat; rename b into γ2
    end.
    exists nil, nil, (pskl_var_f γ2).
    split; [ apply a_solve_eq__var | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ solve_uniq | ]. split; [ simpl; clear; fsetdec | ].
    left. simpl. apply rel_pskl__var_f. exact Hat.
  - (* SE-FlexR: mirror at the flexible t2 *)
    match goal with
    | HG : a_guess_mono _ _ _ ?AA |- _ => rename HG into Hguess
    end.
    destruct (a_guess_mono_rel Hguess Θ2 L Hrel Hscp1 Hscp2)
      as (ρn & Ξ2g & A2 & HG2 & E1 & E2 & Hu & HL & Hrel').
    exists ρn, Ξ2g, (ptyp_to_pskl A2).
    split.
    { apply a_solve_eq__flex_r.
      - exact Ht2.
      - eapply rel_pskl_non_flex; [ exact Hrel | exact Hagr | assumption ].
      - eapply rel_pskl_nonghost; [ exact Hrel | assumption ].
      - exact HG2. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    left. exact Hrel'.
  - (* SE-GhostL: the divergence — both yields are the raw targets *)
    inversion Hrel; subst.
    exists nil, nil, (pskl_var_f t2).
    split; [ apply a_solve_eq__hole_l | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ solve_uniq | ]. split; [ simpl; clear; fsetdec | ].
    right. split; reflexivity.
  - (* SE-GhostGuarded: unfold the ⫯ on both sides, recurse *)
    inversion Hrel; subst.
    match goal with
    | Hq : rel_pskl ρ V P ?x |- _ => rename Hq into Hrel0; rename x into acc0'
    end.
    destruct (IHHD eq_refl Θ2 L acc0' t2 ρ V
                Hrel0 Ht2 Hagr Hscp1 Hscp2)
      as (ρn & Ξh2 & mid2 & Hd2 & E1 & E2 & Hu & HL & Hyield).
    exists ρn, Ξh2, mid2.
    split.
    { apply a_solve_eq__tophole_l_guarded;
        [ apply guarded_pskl__var | exact Hd2 ]. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    exact Hyield.
Qed.

(* ===================================================================== *)
(*  §2g  the KEEP-variant of the ∀-peel (conclusion at the consed ctx)    *)
(* ===================================================================== *)

Lemma a_solve_sub_peel_forall_r_keep_n : forall n P B Θ Ξ P' β,
  size_pskl P + size_pskl B < n ->
  {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B ->
  exists Ξ' P'',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
       (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ' ⨾ P'' }}a.
Proof.
  induction n as [ | n IH ]; intros P B Θ Ξ P' β Hsz Hd Hβ;
    [ exfalso; clear - Hsz; lia | ].
  inversion Hd; subst.
  - (* SS-Var *)
    do 2 eexists. apply a_solve_sub__var.
  - (* SS-ForallL: rebind the subject opener off β and the new entry *)
    match goal with
    | Hfr : ?g `notin` union _ _ ,
      Hp : a_solve_sub ((?g ~ abind_tvar) ++ _) _ _ _ _ _ |- _ =>
        rename Hfr into Hγfr; rename Hp into Hprem
    end.
    match goal with
    | Hprem : a_solve_sub _ _ (open_pskl_wrt_pskl ?B0 _) _ _ _ |- _ =>
        rename B0 into P0
    end.
    destruct (atom_fresh (ftvar_in_aenv Θ ∪ ftvar_in_pskl P0
                ∪ ftvar_in_pskl B ∪ {{ β }})) as [γ' Hγ'].
    assert (Hγ'r : γ' `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P0
                     ∪ ftvar_in_pskl (pskl_all_syn B))
      by (simpl; clear - Hγ'; fsetdec).
    destruct (a_solve_sub_rebind_l Hprem Hγfr Hγ'r) as [Ξ2 [P2 Hp']].
    assert (Hsz' : size_pskl (open_pskl_wrt_pskl P0 (pskl_var_f γ'))
                     + size_pskl B < n)
      by (rewrite size_pskl_open_pskl_wrt_pskl_var;
          clear - Hsz; simpl in *; lia).
    assert (Hβ' : β `notin`
              ftvar_in_aenv ((γ' ~ abind_tvar) ++ Θ)
              ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0 (pskl_var_f γ'))
              ∪ ftvar_in_pskl B).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0
                    (pskl_var_f γ')) as Hup.
      clear - Hβ Hγ' Hup. simpl in *. fsetdec. }
    destruct (IH _ _ _ _ _ β Hsz' Hp' Hβ') as [Ξ3 [P3 Hpeel]].
    apply a_solve_sub_ctx_exchange in Hpeel.
    do 2 eexists.
    apply a_solve_sub__forall_l with (β := γ').
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                    (pskl_var_f β)) as Hup.
      clear - Hγ' Hup. simpl in *. fsetdec.
    + exact Hpeel.
  - (* SS-UnivGhostL *)
    match goal with
    | Hp : a_solve_sub _ _ ?P0 (pskl_all_syn _) _ _ |- _ =>
        assert (Hsz' : size_pskl P0 + size_pskl B < n)
          by (clear - Hsz; simpl in *; lia);
        assert (Hβ' : β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P0
                        ∪ ftvar_in_pskl B)
          by (clear - Hβ; simpl in *; fsetdec);
        destruct (IH _ _ _ _ _ β Hsz' Hp Hβ') as [Ξ3 [P3 Hpeel]]
    end.
    do 2 eexists. apply a_solve_sub__univ_ghost_l. exact Hpeel.
  - (* SS-Check: guarded ∀ has no constructor *)
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  - (* SS-ForallR: rebind its opener to β — the goal, no strip *)
    match goal with
    | Hfr : ?g `notin` union _ _ ,
      Hp : a_solve_sub ((?g ~ abind_tvar) ++ _) _ _ _ _ _ |- _ =>
        rename Hfr into Hγfr; rename Hp into Hprem
    end.
    assert (Hβr : β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P
                    ∪ ftvar_in_pskl B)
      by (clear - Hβ; fsetdec).
    destruct (a_solve_sub_rebind_r Hprem Hγfr Hβr) as [Ξ2 [P2 Hp']].
    exists Ξ2, P2. exact Hp'.
  - (* SS-GhostL: guarded ∀ has no constructor *)
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
Qed.

Lemma a_solve_sub_peel_forall_r_keep : forall P B Θ Ξ P' β,
  {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B ->
  exists Ξ' P'',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
       (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ' ⨾ P'' }}a.
Proof.
  intros.
  eapply a_solve_sub_peel_forall_r_keep_n
    with (n := S (size_pskl P + size_pskl B)); eauto.
Qed.

(* ===================================================================== *)
(*  §2h  e-solve context equivalence (rigid entries are invisible)        *)
(* ===================================================================== *)

Lemma a_flex_tvar_app_or : forall (Ξ Θ : aenv) α,
  a_flex_tvar (Ξ ++ Θ) α <-> (a_flex_tvar Ξ α \/ a_flex_tvar Θ α).
Proof.
  unfold a_flex_tvar, binds. intros. split.
  - intros [Hb | [τ Hb]]; apply in_app_or in Hb; destruct Hb as [Hb | Hb];
      eauto 6.
  - intros [[Hb | [τ Hb]] | [Hb | [τ Hb]]];
      [ left | right; eexists | left | right; eexists ];
      apply in_or_app; eauto.
Qed.

Lemma a_flex_tvar_app_iff : forall (Ξ Θ Θ' : aenv),
  (forall α, a_flex_tvar Θ α <-> a_flex_tvar Θ' α) ->
  forall α, a_flex_tvar (Ξ ++ Θ) α <-> a_flex_tvar (Ξ ++ Θ') α.
Proof.
  intros * Hiff α.
  pose proof (a_flex_tvar_app_or Ξ Θ α).
  pose proof (a_flex_tvar_app_or Ξ Θ' α).
  pose proof (Hiff α).
  tauto.
Qed.

Lemma a_flex_of_tvar_iff : forall Θ Θ' P,
  (forall α, a_flex_tvar Θ α <-> a_flex_tvar Θ' α) ->
  a_flex Θ P -> a_flex Θ' P.
Proof.
  intros * Hiff Hf.
  inversion Hf; subst.
  - assert (Hft : a_flex_tvar Θ' α) by (apply Hiff; left; assumption).
    destruct Hft as [Hb | [τ Hb]];
      [ apply a_flex__var | eapply a_flex__var_def ]; eassumption.
  - assert (Hft : a_flex_tvar Θ' α)
      by (apply Hiff; right; eexists; eassumption).
    destruct Hft as [Hb | [τ0 Hb]];
      [ apply a_flex__var | eapply a_flex__var_def ]; eassumption.
Qed.

(* the recursive positions: the IH's context obligation is the iff,
   possibly lifted over the block/binder prefix the premise runs under *)
Local Ltac ctx_equiv_ih :=
  match goal with
  | IH : forall _, _ -> e_solve_sub _ _ _ _ _ _ _ _
    |- e_solve_sub _ _ _ _ _ _ _ _ =>
      apply IH;
      first [ assumption | apply a_flex_tvar_app_iff; assumption ]
  | IH : forall _, _ -> e_solve_eq _ _ _ _ _ _ _
    |- e_solve_eq _ _ _ _ _ _ _ =>
      apply IH;
      first [ assumption | apply a_flex_tvar_app_iff; assumption ]
  end.

Lemma e_solve_sub_eq_ctx_equiv :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     forall Θ', (forall α, a_flex_tvar Θ α <-> a_flex_tvar Θ' α) ->
     {{ S0 ↝ S1 ⊨ Θ' ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     forall Θ', (forall α, a_flex_tvar Θ α <-> a_flex_tvar Θ' α) ->
     {{ S0 ↝ S1 ⊨ Θ' ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e).
Proof.
  apply (e_solve_sub_eq_mutind
           (fun S0 Θ m P Q S1 Ξ P' _ =>
              forall Θ', (forall α, a_flex_tvar Θ α <-> a_flex_tvar Θ' α) ->
              {{ S0 ↝ S1 ⊨ Θ' ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e)
           (fun S0 Θ P Q S1 Ξ P' _ =>
              forall Θ', (forall α, a_flex_tvar Θ α <-> a_flex_tvar Θ' α) ->
              {{ S0 ↝ S1 ⊨ Θ' ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e));
    intros;
    match goal with
    | |- _ => idtac
    end.
  - (* SS-Var *) apply e_solve_sub__var.
  - (* SS-ForallL *)
    apply e_solve_sub__forall_l; [ assumption | ctx_equiv_ih ].
  - (* SS-UnivGhostL *) apply e_solve_sub__univ_ghost_l; ctx_equiv_ih.
  - (* SS-Vacuous *) apply e_solve_sub__vacuous.
  - (* SS-Check *)
    apply e_solve_sub__check; try assumption; ctx_equiv_ih.
  - (* SS-ForallR *)
    eapply e_solve_sub__forall_r;
      [ assumption | eassumption | ctx_equiv_ih ].
  - (* SS-Arrow *) eapply e_solve_sub__arrow; ctx_equiv_ih.
  - (* SS-GhostLF *) eapply e_solve_sub__ghost_l_fn; ctx_equiv_ih.
  - (* SS-GhostL *) apply e_solve_sub__ghost_l; assumption.
  - (* SE-Unit *) apply e_solve_eq__unit.
  - (* SE-Var *) apply e_solve_eq__var.
  - (* SE-FlexR *)
    match goal with
    | Hft : a_flex_tvar _ ?a, Hnf : a_non_flex _ _,
      Hiff : forall _, a_flex_tvar _ _ <-> a_flex_tvar _ _ |- _ =>
        apply e_solve_eq__flex_r;
        [ apply Hiff; exact Hft
        | destruct Hnf as [Hlc Hnfl];
          split;
          [ exact Hlc
          | intros Hf0; apply Hnfl;
            eapply a_flex_of_tvar_iff;
            [ intros a0; exact (iff_sym (Hiff a0)) | exact Hf0 ] ]
        | assumption
        | assumption ]
    end.
  - (* SE-GhostL *) apply e_solve_eq__hole_l.
  - (* SE-VacuousR *) apply e_solve_eq__hole_r.
  - (* SE-Arrow *) eapply e_solve_eq__arrow; ctx_equiv_ih.
  - (* SE-Forall *)
    eapply e_solve_eq__forall; [ eassumption | ctx_equiv_ih ].
  - (* SE-UnivGhost *) apply e_solve_eq__tophole_both; ctx_equiv_ih.
  - (* SE-GhostForall *)
    eapply e_solve_eq__tophole_l_all; [ eassumption | ctx_equiv_ih ].
  - (* SE-GhostGuarded *)
    apply e_solve_eq__tophole_l_guarded; [ assumption | ctx_equiv_ih ].
  - (* SE-ForallGhost *)
    eapply e_solve_eq__all_l_tophole; [ eassumption | ctx_equiv_ih ].
  - (* SE-GuardedGhost *)
    apply e_solve_eq__tophole_r_guarded; [ assumption | ctx_equiv_ih ].
Qed.

Lemma e_solve_cstr_ctx_equiv : forall S0 Θ C P S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ P' }}e ->
  forall Θ', (forall α, a_flex_tvar Θ α <-> a_flex_tvar Θ' α) ->
  {{ S0 ↝ S1 ⊨ Θ' ⊩ C ⨾ P ⤳ Ξ ⨾ P' }}e.
Proof.
  intros * H; induction H; intros Θ' Hiff.
  - apply e_solve_cstr__empty.
  - apply e_solve_cstr__sub.
    eapply (proj1 e_solve_sub_eq_ctx_equiv); eassumption.
  - eapply e_solve_cstr__eq.
    + eapply (proj2 e_solve_sub_eq_ctx_equiv); eassumption.
    + apply IHe_solve_cstr. apply a_flex_tvar_app_iff. exact Hiff.
Qed.

Lemma a_flex_tvar_rigid_prefix_iff : forall (Δr Θ : aenv) α,
  (forall x bd, binds x bd Δr -> bd = abind_tvar) ->
  (a_flex_tvar (Δr ++ Θ) α <-> a_flex_tvar Θ α).
Proof.
  intros * Hr.
  pose proof (a_flex_tvar_app_or Δr Θ α) as Hor.
  assert (Hnf : ~ a_flex_tvar Δr α).
  { intros [Hb | [τ Hb]]; pose proof (Hr _ _ Hb); discriminate. }
  tauto.
Qed.

(** The assembly's enrichment move: an e-fold rigid-weakens freely
    (its freshness reads the SUPPLY, and rigid entries are invisible to
    the flex tests). *)
Lemma e_solve_cstr_weaken_rigid : forall S0 Θ C P S1 Ξ P' (Δr : aenv),
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ P' }}e ->
  (forall x bd, binds x bd Δr -> bd = abind_tvar) ->
  {{ S0 ↝ S1 ⊨ (Δr ++ Θ) ⊩ C ⨾ P ⤳ Ξ ⨾ P' }}e.
Proof.
  intros * H Hr.
  eapply e_solve_cstr_ctx_equiv; [ exact H | ].
  intros α. symmetry. apply a_flex_tvar_rigid_prefix_iff. exact Hr.
Qed.
