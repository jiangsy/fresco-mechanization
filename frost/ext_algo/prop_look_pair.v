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

    The b-core itself (§2, forthcoming) is stated over [e_looksub] on
    BOTH sides — see HANDOFF-extractable-algo-encoding.md §8c.9 (third
    pass) for why output-level hygiene premises are not maintainable and
    why a conflated raw derivation would make the statement false. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.prop_ln.
Require Import src.frost.def_shapes.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.sub.prop_looksub.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.prop_look.

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
