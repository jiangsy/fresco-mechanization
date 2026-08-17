(** ext_algo — THE b-CORE'S HOME (campaign §8c.9 §6b): the fused
    look-pair/fold-transport lemma over SUPPLY-THREADED looks, and its
    e-side prerequisites.

    §1 is the e-side look kit the pair induction leans on:

    §1a  the e-look's context is INERT (every freshness condition reads
         the SUPPLY), so derivations transport to ANY context — which is
         what replaces the a-side [a_looksub_ctx_exchange] surgery;
    §1c  the COLLECTION-PRESERVING re-rootings, e-side: R″
         ([e_looksub_strip_tophole_l] — outputs AND supplies exact) and
         R′ ([e_looksub_open_forall_l_first]) — ⭐ stated with an
         EXISTENTIAL opener, which kills the whole rebinding apparatus:
         in its ForallL case the premise IS the goal at the derivation's
         own opener (+ ctx_any), and in its ForallR case the IH's opener
         is reused below the rebuilt root (+ prop_look.v §5's supply
         respect for the [add]-exchange) — so unlike the a-side R′
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
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_ln.
Require Import src.frost.def_shapes.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.sub.prop_looksub.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import src.frost.algo.sub.look.prop_eq_cstr.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_dec.
Require Import src.frost.ext_algo.prop_dec.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.prop_look.
Require Import src.frost.ext_algo.prop_look_equiv.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.prop_solve.
Require Import src.frost.ext_algo.prop_solve_det.
Require Import src.frost.ext_algo.prop_solve_rel.
Require Import src.frost.ext_algo.def_order.
Require Import src.frost.ext_algo.prop_termination.
Require Import src.frost.ext_algo.def_look_impl.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_guess_impl.
Require Import src.frost.ext_algo.def_guess_impl_sk.
Require Import src.frost.ext_algo.def_solve_impl.
Require Import src.frost.ext_algo.def_uip.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.def_extract_impl.
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
(*  §1c  The COLLECTION-PRESERVING re-rootings, e-side (R″ and R′)        *)
(*                                                                        *)
(*  Mirrors of prop_look_equiv.v §6, leaning on the inert context.  R′    *)
(*  is stated with an EXISTENTIAL opener: in its ForallL case the        *)
(*  premise IS the goal at the derivation's own opener, so no rebinding  *)
(*  (hence no e-swap kit) is ever needed.                                *)
(* ===================================================================== *)

(** R″ — strip a ⫯ subject to the front; outputs AND supplies exact. *)
Lemma e_looksub_strip_tophole_l : forall S0 Θ α m P0 P' S1 Ξ C,
  (* ⚠️ [P' ≠ ◇] — see the a-side twin in prop_look_equiv.v: unconditionally
     this is FALSE under the ◇-dispatch guard. *)
  P' <> pskl_hole ->
  P0 <> pskl_var_f α ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole P0) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ P0 ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * Hnh Hnv H.
  remember (pskl_tophole P0) as S eqn:HS.
  revert P0 Hnv HS.
  induction H; intros P0' Hnv HS; inversion HS; subst.
  - (* LS-Absent *)
    apply e_looksub__absent. simpl in *. assumption.
  - (* LS-Vacuous — impossible: the counterpart is ◇ *)
    exfalso. apply Hnh. reflexivity.
  - (* LS-Check: a ⫯ subject is not guarded *)
    match goal with
    | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
    end.
  - (* LS-ForallR *)
    apply e_looksub__forall_r with (β := β);
      [ assumption | assumption
      | (* the guard on [⫯P0] IS the guard on [P0] *) simpl in *; assumption
      | exact Hnv | ].
    apply IHe_looksub;
      [ apply ghost_free_open_var_neq_hole; exact H
      | exact Hnv | reflexivity ].
  - (* LS-UnivGhostL *)
    assumption.
Qed.

(** R′ — open a ∀ subject at the front, at SOME supply-fresh opener;
    outputs exact, the output supply exact up to [=] after inserting the
    opener.  Size induction on the TARGET (only LS-ForallR recurses). *)
Lemma e_looksub_open_forall_l_first_n : forall n S0 Θ α m P0 P' S1 Ξ C,
  (* the two ◇-dispatch side conditions — see the a-side twin in
     prop_look_equiv.v; unconditionally this is FALSE *)
  P' <> pskl_hole ->
  P0 <> pskl_var_f α ->
  (* ⚙ coverage: it is what makes every DRAWN opener differ from [α], which
     the [≠ α] half of the guard needs after the binder peel *)
  α `in` S0 ->
  size_pskl P' < n ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P0) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  exists γ S1',
    γ `notin` S0 /\
    {{ (add γ S0) ↝ S1' ⊨ ((γ ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P0 (pskl_var_f γ)) ≼[ α , m ] P'
       ⤳ Ξ ⨾ C }}e.
Proof.
  induction n as [ | n IH ]; intros * Hnh Hnv HαS Hsz Hd;
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
  - (* LS-Vacuous — impossible: the counterpart is ◇ *)
    exfalso. apply Hnh. reflexivity.
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
    (* ⚠️ HOIST both side conditions OUT of the [destruct]: inside it the
       [_] placeholders are still EVARS, and an [fsetdec] on an evar set-goal
       is the classic hang (this one alone cost the file >15 min). *)
    assert (HαS1 : α `in` add β1 S0) by (clear - HαS; fsetdec).
    assert (Hnh1 : open_pskl_wrt_pskl B (pskl_var_f β1) <> pskl_hole)
      by (apply ghost_free_open_var_neq_hole; assumption).
    destruct (IH _ _ _ _ _ _ _ _ _ Hnh1 Hnv HαS1 Hszp Hprem)
      as (γ & S1' & Hγ & Hd').
    destruct ((proj1 e_looksub_lookeq_supply_respect) _ _ _ _ _ _ _ _ _ Hd'
                (add β1 (add γ S0)) ltac:(clear; fsetdec))
      as [S1'' [Heq Hd'']].
    pose proof ((proj1 e_looksub_lookeq_ctx_any) _ _ _ _ _ _ _ _ _ Hd''
                  ((β1 ~ abind_tvar) ++ (γ ~ abind_tvar) ++ Θ)) as Hd3.
    assert (Hγα : γ <> α) by (clear - Hγ HαS; fsetdec).
    exists γ, S1''.
    split; [ clear - Hγ; fsetdec | ].
    apply e_looksub__forall_r with (β := β1);
      [ assumption | clear - Hγ H0; fsetdec
      | (* ⭐ the absence-first guard SURVIVES THE OPENING *)
        match goal with
        | Hocc : α `in` ftvar_in_pskl (pskl_all_syn P0) |- _ =>
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P0
                          (pskl_var_f γ)) as Hlo;
            simpl in Hocc; clear - Hocc Hlo; fsetdec
        end
      | apply open_var_neq_var; [ exact Hnv | exact Hγα ]
      | exact Hd3 ].
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

(** R′, packaged.  ⚙ carries the [_n] form's three side conditions. *)
Lemma e_looksub_open_forall_l_first : forall S0 Θ α m P0 P' S1 Ξ C,
  P' <> pskl_hole ->
  P0 <> pskl_var_f α ->
  α `in` S0 ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P0) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  exists γ S1',
    γ `notin` S0 /\
    {{ (add γ S0) ↝ S1' ⊨ ((γ ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P0 (pskl_var_f γ)) ≼[ α , m ] P'
       ⤳ Ξ ⨾ C }}e.
Proof.
  intros * Hnh Hnv HαS Hd.
  exact (@e_looksub_open_forall_l_first_n (S (size_pskl P'))
           S0 Θ α m P0 P' S1 Ξ C Hnh Hnv HαS ltac:(lia) Hd).
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
  (* ⚙ the ◇-dispatch guard asks the PEELED target not to be a ghost — the
     runner's own ForallR test is exactly this check *)
  pskl_ghost_free (pskl_all_syn B) ->
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
  intros * H Hgft.
  remember (pskl_all_syn B) as T eqn:HT.
  remember mode_tc as m0 eqn:Hm.
  revert B Hgft HT.
  induction H; intros B0 Hgft HT Hα; inversion HT; subst; subst.
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
    destruct (IHe_looksub eq_refl _ Hgft eq_refl Hαo)
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
        [ clear - Hγfr Hβ1; fsetdec | exact Hα
        | apply ghost_free_open_var_neq_hole; exact Hgft
        | exact Hd'' ]. }
    destruct Hdisj as [ (HinS & -> & ->) | (HL & -> & -> & -> & ->) ].
    + left. split; [ assumption | ]. split; reflexivity.
    + right. split; [ assumption | ].
      repeat (split; [ reflexivity | ]); reflexivity.
  - (* LS-UnivGhostL: recurse and rebuild *)
    simpl in Hα.
    destruct (IHe_looksub eq_refl _ Hgft eq_refl Hα)
      as (β1 & S1' & Ξ' & C' & Hβ1 & HS1' & Hd & Hdisj).
    exists β1, S1', Ξ', C'.
    split; [ assumption | ].
    split; [ assumption | ].
    split;
      [ apply e_looksub__univ_ghost_l;
          [ apply ghost_free_open_var_neq_hole; exact Hgft | exact Hd ] | ].
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

(* --------------------------------------------------------------------- *)
(*  §2i  late kit additions the b-core's composition case needs           *)
(* --------------------------------------------------------------------- *)

Lemma flex_agree_rel_extend_pairs_iff : forall ρe ρ V Θ1 Θ2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  (forall a b, In (a, b) ρe ->
     (a_flex_tvar Θ1 a <-> a_flex_tvar Θ2 b)) ->
  flex_agree_rel (ρe ++ ρ) V Θ1 Θ2.
Proof.
  induction ρe as [ | [a b] ρe' IH ]; intros * Hagr Hiff; simpl.
  - exact Hagr.
  - apply flex_agree_rel_extend_pair_iff.
    + apply IH; [ exact Hagr | ].
      intros a' b' Hin. apply Hiff. right. exact Hin.
    + apply Hiff. left. reflexivity.
Qed.

Lemma cols_l_bound : forall (ρ : list (atom * atom)) (S : atoms),
  (forall a b, In (a, b) ρ -> a `in` S) ->
  cols_l ρ [<=] S.
Proof.
  induction ρ as [ | [a b] ρ' IH ]; intros * Hb; simpl.
  - clear. fsetdec.
  - pose proof (Hb a b (or_introl eq_refl)) as Ha.
    pose proof (IH _ ltac:(intros a' b' Hin; apply (Hb a' b');
                           right; exact Hin)) as Htl.
    clear - Ha Htl. fsetdec.
Qed.

Lemma cols_r_bound : forall (ρ : list (atom * atom)) (S : atoms),
  (forall a b, In (a, b) ρ -> b `in` S) ->
  cols_r ρ [<=] S.
Proof.
  induction ρ as [ | [a b] ρ' IH ]; intros * Hb; simpl.
  - clear. fsetdec.
  - pose proof (Hb a b (or_introl eq_refl)) as Ha.
    pose proof (IH _ ltac:(intros a' b' Hin; apply (Hb a' b');
                           right; exact Hin)) as Htl.
    clear - Ha Htl. fsetdec.
Qed.

Lemma binds_app_right : forall (x : atom) (bd : abind) (Ξ Θ : aenv),
  binds x bd Θ -> binds x bd (Ξ ++ Θ).
Proof.
  intros. unfold binds in *. apply in_or_app. right. assumption.
Qed.

Lemma a_flex_tvar_dom : forall (Θ : aenv) x,
  a_flex_tvar Θ x -> x `in` dom Θ.
Proof.
  intros * [Hb | [τ Hb]]; eapply binds_In; eassumption.
Qed.

(* ===================================================================== *)
(*  §3  THE b-CORE — the fused look-pair/fold-transport (§8c.9 §6b)       *)
(*                                                                        *)
(*  RUNNER-SIDED (fourth pass): side 1 an arbitrary supply-threaded       *)
(*  derivation + its fold, side 2 the runner's computation.  The EQ half  *)
(*  ([bcore_eq]) is a size induction of its own (the eq layer never       *)
(*  calls the sub layer); its conclusion carries the block PAIRING, the   *)
(*  interval/status-iff fact pack for its ρe extension, and the           *)
(*  rel-or-HATCH yield (both yields raw vars — harmless because a var     *)
(*  pattern is a fixed point of the fold, §2d).  The SUB half follows.    *)
(* ===================================================================== *)

Definition bcore_eq_stmt (n : nat) : Prop :=
  forall Sa0 Sa1 Θd α P1 P1' Ξ1 C1,
  size_pskl P1 + size_pskl P1' < n ->
  {{ Sa0 ↝ Sa1 ⊨ Θd ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
  forall Sb0 Θr P2 P2' hp2 hp2' Hord (s : sig (lookeq_spec Sb0 Θr α P2 P2')),
  e_lookeq_impl Sb0 Θr α P2 P2' hp2 hp2' Hord = Some s ->
  forall ρ V Θf1 Θf2 acc1 acc2 Ξs1 Q1 (L : atoms),
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V P1' P2' ->
  α `in` V ->
  α `notin` cols_l ρ ->
  α `notin` cols_r ρ ->
  {{ Θf1 ⊩ C1 ⨾ acc1 ⤳ Ξs1 ⨾ Q1 }}a ->
  rel_pskl ρ V acc1 acc2 ->
  flex_agree_rel ρ V Θf1 Θf2 ->
  (forall x bd, binds x bd Ξ1 -> binds x bd Θf1) ->
  (forall x bd, binds x bd (lk_block (proj1_sig s)) -> binds x bd Θf2) ->
  (forall x, x `in` Sa1 -> x `notin` Sa0 -> x `notin` dom Ξ1 ->
     ~ a_flex_tvar Θf1 x) ->
  (forall x, x `in` lk_supply (proj1_sig s) -> x `notin` Sb0 ->
     x `notin` dom (lk_block (proj1_sig s)) -> ~ a_flex_tvar Θf2 x) ->
  (Sa1 ∖ Sa0) [<=] ftvar_in_aenv Θf1 ->
  (lk_supply (proj1_sig s) ∖ Sb0) [<=] ftvar_in_aenv Θf2 ->
  V ∪ cols_l ρ ∪ ftvar_in_pskl acc1 ∪ ftvar_in_a_cstrs C1
    [<=] ftvar_in_aenv Θf1 ->
  V ∪ cols_r ρ ∪ ftvar_in_pskl acc2
    ∪ ftvar_in_a_cstrs (lk_cstrs (proj1_sig s)) [<=] ftvar_in_aenv Θf2 ->
  V ∪ ftvar_in_pskl P1 ∪ ftvar_in_pskl P1' [<=] Sa0 ->
  V ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] Sb0 ->
  exists ρe ρn Ξs2 Q2,
    {{ Θf2 ⊩ (lk_cstrs (proj1_sig s)) ⨾ acc2 ⤳ Ξs2 ⨾ Q2 }}a
    /\ Ξs1 = flex_pairs_l ρn /\ Ξs2 = flex_pairs_r ρn
    /\ uniq Ξs2 /\ dom Ξs2 ∩ L [=] empty
    /\ (forall a b, In (a, b) ρe ->
          a `in` Sa1 /\ a `notin` Sa0 /\
          b `in` lk_supply (proj1_sig s) /\ b `notin` Sb0 /\
          (a_flex_tvar Θf1 a <-> a_flex_tvar Θf2 b))
    /\ ( rel_pskl (ρe ++ ρn ++ ρ) V Q1 Q2
         \/ (exists γ1 γ2, Q1 = pskl_var_f γ1 /\ Q2 = pskl_var_f γ2) ).

Lemma bcore_eq : forall n, bcore_eq_stmt n.
Proof.
  induction n as [ | n IHn ]; unfold bcore_eq_stmt;
    [ intros; exfalso; lia | ].
  intros Sa0 Sa1 Θd α P1 P1' Ξ1 C1 Hsz E1 Sb0 Θr P2 P2' hp2 hp2' Hord s Hs
    ρ V Θf1 Θf2 acc1 acc2 Ξs1 Q1 L
    HrelP HrelP' HαV Hαl Hαr Hfold Hrelacc Hagr Hb1 Hb2 Hop1 Hop2
    Henr1 Henr2 Hscp1 Hscp2 Hcov1 Hcov2.
  destruct (sumbool_of_bool (mem α (ftvar_in_pskl P1))) as [Hmem | Hmem].
  2:{ (* ---- the α-FREE collapse: both sides emit nothing ---- *)
    apply mem_false_notin in Hmem.
    assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
    assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
    destruct (e_lookeq_subject_absent E1 HαSa Hmem) as [EΞ1 EC1]; subst.
    assert (HαP2 : α `notin` ftvar_in_pskl P2)
      by (eapply rel_pskl_notin_r; [ exact HrelP | exact Hmem | exact Hαr ]).
    destruct s as [r Hr]. simpl in *.
    destruct (e_lookeq_subject_absent Hr HαSb HαP2) as [EΞ2 EC2].
    rewrite EC2.
    inversion Hfold; subst.
    exists (@nil (atom * atom)), (@nil (atom * atom)), (@nil (atom * abind)).
    eexists.
    split; [ apply a_solve_cstr__empty | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ auto | ]. split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    left. simpl. exact Hrelacc. }
  apply mem_true_in in Hmem. rename Hmem into HαP1.
  assert (HαP2 : α `in` ftvar_in_pskl P2)
    by (eapply rel_pskl_in_id; [ exact HrelP | exact HαP1 | exact Hαl ]).
  inversion E1; subst.
  - (* LE-Var: P1 = var α — the runner retains the target *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ =>
        inversion Ha; subst;
        [ exfalso; apply Hαl;
          match goal with
          | Hin : In (α, _) ρ |- _ => exact (cols_l_in _ _ _ Hin)
          end | ]
    end.
    revert Hs. simp e_lookeq_impl.
    match goal with
    | |- context [ match ?scr with left _ => _ | right _ => _ end ] =>
        destruct scr as [Heq | Hne]; [ | contradiction ]
    end.
    intros Hs. inversion Hs; subst s; clear Hs.
    simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
    apply a_solve_cstr_eq_inv in Hfold
      as (Ξh & Ξt & mid & EΞ & Hh & Ht).
    inversion Ht; subst.
    assert (Hscp1' : V ∪ cols_l ρ [<=] ftvar_in_aenv Θf1)
      by (clear - Hscp1; fsetdec).
    assert (Hscp2' : V ∪ cols_r ρ [<=] ftvar_in_aenv Θf2)
      by (clear - Hscp2; fsetdec).
    destruct (a_solve_eq_rel Hh L Hrelacc HrelP' Hagr Hscp1' Hscp2')
      as (ρn & Ξh2 & mid2 & D2 & E1p & E2p & Hu & HL & Hrel').
    exists (@nil (atom * atom)), ρn, (nil ++ Ξh2).
    eexists.
    split.
    { eapply a_solve_cstr__eq; [ exact D2 | apply a_solve_cstr__empty ]. }
    split; [ simpl; exact E1p | ].
    split; [ simpl; exact E2p | ].
    split; [ simpl; exact Hu | ].
    split; [ simpl; exact HL | ].
    split; [ intros a b Hin; inversion Hin | ].
    left. simpl. exact Hrel'.
  - (* LE-Absent: α ∉ ftv P1 — contradiction *)
    exfalso. clear - HαP1 H. fsetdec.
  - (* LE-Vacuous: target ◇ on both sides *)
    inversion HrelP'; subst.
    inversion Hfold; subst.
    inversion HrelP; subst;
      try solve [ exfalso; simpl in HαP1; clear - HαP1; fsetdec ].
    + (* subject a VAR pair: the runner's var-clause retains [eq ◇] *)
      match goal with
      | Ha : rel_atom ρ V ?g1 ?g2 |- _ =>
          assert (Hg1 : g1 = α)
            by (simpl in HαP1; clear - HαP1; fsetdec);
          subst g1;
          inversion Ha; subst;
          [ exfalso; apply Hαl;
            match goal with
            | Hin : In (α, _) ρ |- _ => exact (cols_l_in _ _ _ Hin)
            end | ]
      end.
      revert Hs. simp e_lookeq_impl.
      match goal with
      | |- context [ match ?scr with left _ => _ | right _ => _ end ] =>
          destruct scr as [Heq | Hne]; [ | contradiction ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      exists (@nil (atom * atom)), (@nil (atom * atom)).
      do 2 eexists.
      split.
      { eapply a_solve_cstr__eq;
          [ apply a_solve_eq__hole_r | apply a_solve_cstr__empty ]. }
      split; [ reflexivity | ]. split; [ reflexivity | ].
      split; [ auto | ]. split; [ simpl; clear; fsetdec | ].
      split; [ intros a b Hin; inversion Hin | ].
      left. simpl. exact Hrelacc.
    + (* subject arrow *)
      revert Hs. simp e_lookeq_impl. intros Hs.
      inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      exists (@nil (atom * atom)), (@nil (atom * atom)), (@nil (atom * abind)).
      eexists.
      split; [ apply a_solve_cstr__empty | ].
      split; [ reflexivity | ]. split; [ reflexivity | ].
      split; [ auto | ]. split; [ simpl; clear; fsetdec | ].
      split; [ intros a b Hin; inversion Hin | ].
      left. simpl. exact Hrelacc.
    + (* subject ∀ *)
      revert Hs. simp e_lookeq_impl. intros Hs.
      inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      exists (@nil (atom * atom)), (@nil (atom * atom)), (@nil (atom * abind)).
      eexists.
      split; [ apply a_solve_cstr__empty | ].
      split; [ reflexivity | ]. split; [ reflexivity | ].
      split; [ auto | ]. split; [ simpl; clear; fsetdec | ].
      split; [ intros a b Hin; inversion Hin | ].
      left. simpl. exact Hrelacc.
    + (* subject ⫯ *)
      revert Hs. simp e_lookeq_impl. intros Hs.
      inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      exists (@nil (atom * atom)), (@nil (atom * atom)), (@nil (atom * abind)).
      eexists.
      split; [ apply a_solve_cstr__empty | ].
      split; [ reflexivity | ]. split; [ reflexivity | ].
      split; [ auto | ]. split; [ simpl; clear; fsetdec | ].
      split; [ intros a b Hin; inversion Hin | ].
      left. simpl. exact Hrelacc.
  - (* LE-FlexR: shaped subject, var target — the junk head *)
    inversion HrelP'; subst.
    match goal with
    | Ha : rel_atom ρ V ?t1r ?t2r |- _ => clear Ha
    end.
    apply a_solve_cstr_eq_inv in Hfold
      as (Ξh & Ξt & mid & EΞ & Hh & Ht).
    inversion Ht; subst.
    assert (Hscp1' : V ∪ cols_l ρ [<=] ftvar_in_aenv Θf1)
      by (clear - Hscp1; fsetdec).
    assert (Hscp2' : V ∪ cols_r ρ [<=] ftvar_in_aenv Θf2)
      by (clear - Hscp2; fsetdec).
    (* the subject's shape resolves the runner's FlexR clause *)
    inversion HrelP; subst;
      try solve [ exfalso; simpl in HαP1; clear - HαP1; fsetdec ];
      [ (* var subject: contradicts P ≠ α *)
        match goal with
        | Ha : rel_atom ρ V ?g1 ?g2, Hnee : ?PP <> pskl_var_f α |- _ =>
            exfalso;
            assert (Hg1 : g1 = α)
              by (simpl in HαP1; clear - HαP1; fsetdec);
            subst g1; apply Hnee; reflexivity
        end
      | | | ];
      (revert Hs; simp e_lookeq_impl;
       match goal with
       | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
           let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
           destruct (sumbool_of_bool scr) as [Hmt | Hmf];
           [ | exfalso; apply mem_false_notin in Hmf;
               simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
       end;
       intros Hs; inversion Hs; subst s; clear Hs;
       simpl in Hb2, Hop2, Henr2, Hscp2 |- * );
      (assert (Hflex2 : a_flex_tvar Θf2 (supply_fresh Sb0))
        by (left; apply Hb2; unfold binds; simpl; auto));
      (destruct (a_solve_eq_var_target_junk Hh L Hrelacc Hflex2
                   Hagr Hscp1' Hscp2')
        as (ρn & Ξh2 & mid2 & D2 & E1p & E2p & Hu & HL & Hyield));
      exists (@nil (atom * atom)), ρn, (nil ++ Ξh2);
      eexists;
      (split;
       [ eapply a_solve_cstr__eq; [ exact D2 | apply a_solve_cstr__empty ] | ]);
      (split; [ simpl; exact E1p | ]);
      (split; [ simpl; exact E2p | ]);
      (split; [ simpl; exact Hu | ]);
      (split; [ simpl; exact HL | ]);
      (split; [ intros a b Hin; inversion Hin | ]);
      (destruct Hyield as [ Hrel' | [Emid1 Emid2] ];
       [ left; simpl; exact Hrel'
       | right; subst; eauto ]).
  - (* LE-Arrow: the composition case *)
    match goal with
    | Ha : e_lookeq Sa0 _ _ ?pa ?pa' ?sm ?xa ?ca,
      Hb : e_lookeq ?sm _ _ ?pb ?pb' Sa1 ?xb ?cb |- _ =>
        rename Ha into E1a; rename Hb into E1b; rename sm into Sm;
        rename pa into P1a; rename pa' into P1a';
        rename pb into P1b; rename pb' into P1b';
        rename xa into Ξ1a; rename xb into Ξ1b;
        rename ca into C1a; rename cb into C1b
    end.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | H1x : rel_pskl ρ V P1a ?qa, H2x : rel_pskl ρ V P1b ?qb,
      H3x : rel_pskl ρ V P1a' ?qa', H4x : rel_pskl ρ V P1b' ?qb' |- _ =>
        rename H1x into Hra; rename H2x into Hrb;
        rename H3x into Hra'; rename H4x into Hrb';
        rename qa into Q2a; rename qb into Q2b;
        rename qa' into Q2a'; rename qb' into Q2b'
    end.
    revert Hs. simp e_lookeq_impl.
    match goal with
    | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
        let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
        destruct (sumbool_of_bool scr) as [Hmt | Hmf];
        [ | exfalso; apply mem_false_notin in Hmf;
            simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
    end.
    match goal with
    | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
        let r1a := fresh "r1a" in let Hr1a := fresh "Hr1a" in
        let Era := fresh "Era" in
        destruct call as [ [r1a Hr1a] | ] eqn:Era;
        [ | intros Hs; discriminate ]
    end.
    match goal with
    | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
        let r2b := fresh "r2b" in let Hr2b := fresh "Hr2b" in
        let Erb := fresh "Erb" in
        destruct call as [ [r2b Hr2b] | ] eqn:Erb;
        [ | intros Hs; discriminate ]
    end.
    intros Hs. inversion Hs; subst s; clear Hs.
    simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
    (* decompose the given fold at the pure-eq seam *)
    pose proof (e_lookeq_cstrs_pure_eq E1a) as Hpea.
    pose proof (e_lookeq_cstrs_pure_eq E1b) as Hpeb.
    pose proof (e_lookeq_cstrs_pure_eq Hr1a) as Hpe2a.
    pose proof (e_lookeq_cstrs_pure_eq Hr2b) as Hpe2b.
    destruct (a_solve_cstr_app_inv _ Hpea Hfold)
      as (Ξsa & Ξsb & mid1 & EΞs1 & Hf1a & Hf1b).
    (* supply/block bookkeeping *)
    pose proof (e_lookeq_supply_grows E1a) as Hgra.
    pose proof (e_lookeq_supply_grows E1b) as Hgrb.
    pose proof (e_lookeq_supply_grows Hr1a) as Hgr2a.
    pose proof (e_lookeq_supply_grows Hr2b) as Hgr2b.
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ E1a)
      as (Hbla1 & Hbla2 & _ & _).
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ E1b)
      as (Hblb1 & Hblb2 & _ & _).
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ Hr1a)
      as (Hbl2a1 & Hbl2a2 & _ & _).
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ Hr2b)
      as (Hbl2b1 & Hbl2b2 & _ & _).
    pose proof (a_solve_cstr_generated_fresh_set Hf1a) as Hfsa.
    (* ---- the FIRST IH: the eq halves at the base contexts ---- *)
    assert (Hsza : size_pskl P1a + size_pskl P1a' < n)
      by (clear - Hsz; simpl in *; lia).
    assert (Hb1a : forall x bd, binds x bd Ξ1a -> binds x bd Θf1)
      by (intros x bd Hxb; apply Hb1; unfold binds in *;
          apply in_or_app; left; exact Hxb).
    assert (Hb2a : forall x bd, binds x bd (lk_block r1a) -> binds x bd Θf2)
      by (intros x bd Hxb; apply Hb2; unfold binds in *;
          apply in_or_app; left; exact Hxb).
    assert (Hop1a : forall x, x `in` Sm -> x `notin` Sa0 ->
              x `notin` dom Ξ1a -> ~ a_flex_tvar Θf1 x)
      by (intros x h1 h2 h3; apply Hop1;
          [ clear - h1 Hgrb; fsetdec | exact h2
          | rewrite dom_app; clear - h1 h3 Hblb2; fsetdec ]).
    assert (Hop2a : forall x, x `in` lk_supply r1a -> x `notin` Sb0 ->
              x `notin` dom (lk_block r1a) -> ~ a_flex_tvar Θf2 x)
      by (intros x h1 h2 h3; apply Hop2;
          [ clear - h1 Hgr2b; fsetdec | exact h2
          | rewrite dom_app; clear - h1 h3 Hbl2b2; fsetdec ]).
    assert (Henr1a : Sm ∖ Sa0 [<=] ftvar_in_aenv Θf1)
      by (clear - Henr1 Hgrb; fsetdec).
    assert (Henr2a : lk_supply r1a ∖ Sb0 [<=] ftvar_in_aenv Θf2)
      by (clear - Henr2 Hgr2b; fsetdec).
    assert (Hscp1a : V ∪ cols_l ρ ∪ ftvar_in_pskl acc1
              ∪ ftvar_in_a_cstrs C1a [<=] ftvar_in_aenv Θf1).
    { rewrite ftvar_in_a_cstrs_app in Hscp1. clear - Hscp1. fsetdec. }
    assert (Hscp2a : V ∪ cols_r ρ ∪ ftvar_in_pskl acc2
              ∪ ftvar_in_a_cstrs (lk_cstrs r1a) [<=] ftvar_in_aenv Θf2).
    { rewrite ftvar_in_a_cstrs_app in Hscp2. clear - Hscp2. fsetdec. }
    assert (Hcov1a : V ∪ ftvar_in_pskl P1a ∪ ftvar_in_pskl P1a' [<=] Sa0)
      by (clear - Hcov1; simpl in *; fsetdec).
    assert (Hcov2a : V ∪ ftvar_in_pskl Q2a ∪ ftvar_in_pskl Q2a' [<=] Sb0)
      by (clear - Hcov2; simpl in *; fsetdec).
    pose proof (IHn Sa0 Sm _ _ _ _ _ _ Hsza E1a
                  _ _ _ _ _ _ _ (exist _ r1a Hr1a) Era
                  ρ _ _ _ _ _ _ _ L
                  Hra Hra'
                  HαV Hαl Hαr Hf1a Hrelacc Hagr
                  Hb1a Hb2a Hop1a Hop2a Henr1a Henr2a Hscp1a Hscp2a
                  Hcov1a Hcov2a) as HRECa.
    destruct HRECa as (ρea & ρna & Ξ2a & mid2 & Hf2a & E1pa & E2pa & Hua
                       & HLa & Hρea & Hyielda).
    simpl in Hρea.
    pose proof (a_solve_cstr_generated_fresh_set Hf2a) as Hfs2a.
    (* interval bounds for the first extension's columns *)
    assert (Hcolsea1 : cols_l ρea [<=] ftvar_in_aenv Θf1).
    { apply cols_l_bound. intros a b Hin.
      destruct (Hρea _ _ Hin) as (h1 & h2 & _).
      apply Henr1. clear - h1 h2 Hgrb. fsetdec. }
    assert (Hcolsea2 : cols_r ρea [<=] ftvar_in_aenv Θf2).
    { apply cols_r_bound. intros a b Hin.
      destruct (Hρea _ _ Hin) as (_ & _ & h1 & h2 & _).
      apply Henr2. clear - h1 h2 Hgr2b. fsetdec. }
    destruct Hyielda as [ Hrelmid | [γ1 [γ2 [Emid1 Emid2]]] ].
    + (* ---- rel branch: the SECOND IH at the extended contexts ---- *)
      assert (Hszb : size_pskl P1b + size_pskl P1b' < n)
        by (clear - Hsz; simpl in *; lia).
      assert (Hrbw : rel_pskl (ρea ++ ρna ++ ρ) V P1b Q2b).
      { eapply rel_pskl_mono; [ exact Hrb | | intros x Hx; exact Hx ].
        intros a0 b0 Hi. rewrite ? in_app_iff. tauto. }
      assert (Hrbw' : rel_pskl (ρea ++ ρna ++ ρ) V P1b' Q2b').
      { eapply rel_pskl_mono; [ exact Hrb' | | intros x Hx; exact Hx ].
        intros a0 b0 Hi. rewrite ? in_app_iff. tauto. }
      assert (Hαl'' : α `notin` cols_l (ρea ++ ρna ++ ρ)).
      { rewrite ! cols_l_app.
        assert (Hα1 : α `notin` cols_l ρea).
        { apply cols_l_fresh. intros a b Hin.
          destruct (Hρea _ _ Hin) as (_ & h2 & _).
          assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
          intros ->. clear - h2 HαSa. fsetdec. }
        assert (Hα2 : α `notin` cols_l ρna).
        { rewrite <- dom_flex_pairs_l. rewrite <- E1pa.
          assert (HαF : α `in` ftvar_in_aenv Θf1)
            by (clear - HαV Hscp1; fsetdec).
          clear - Hfsa HαF. fsetdec. }
        clear - Hα1 Hα2 Hαl. fsetdec. }
      assert (Hαr'' : α `notin` cols_r (ρea ++ ρna ++ ρ)).
      { rewrite ! cols_r_app.
        assert (Hα1 : α `notin` cols_r ρea).
        { apply cols_r_fresh. intros a b Hin.
          destruct (Hρea _ _ Hin) as (_ & _ & _ & h2 & _).
          assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
          intros ->. clear - h2 HαSb. fsetdec. }
        assert (Hα2 : α `notin` cols_r ρna).
        { rewrite <- dom_flex_pairs_r. rewrite <- E2pa.
          assert (HαF : α `in` ftvar_in_aenv Θf2)
            by (clear - HαV Hscp2; fsetdec).
          clear - Hfs2a HαF. fsetdec. }
        clear - Hα1 Hα2 Hαr. fsetdec. }
      assert (Hagre : flex_agree_rel (ρea ++ ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pairs_iff; [ exact Hagr | ].
        intros a b Hin. destruct (Hρea _ _ Hin) as (_ & _ & _ & _ & Hiff).
        exact Hiff. }
      assert (Hagr'' : flex_agree_rel (ρea ++ ρna ++ ρ) V
                (Ξsa ++ Θf1) (Ξ2a ++ Θf2)).
      { assert (Hd1 : cols_l ρna ∩ (V ∪ cols_l (ρea ++ ρ)) [=] empty).
        { rewrite <- dom_flex_pairs_l. rewrite <- E1pa.
          rewrite cols_l_app.
          assert (HU : V ∪ (cols_l ρea ∪ cols_l ρ)
                        [<=] ftvar_in_aenv Θf1)
            by (clear - Hscp1 Hcolsea1; fsetdec).
          clear - Hfsa HU. fsetdec. }
        assert (Hd2 : cols_r ρna ∩ (V ∪ cols_r (ρea ++ ρ)) [=] empty).
        { rewrite <- dom_flex_pairs_r. rewrite <- E2pa.
          rewrite cols_r_app.
          assert (HU : V ∪ (cols_r ρea ∪ cols_r ρ)
                        [<=] ftvar_in_aenv Θf2)
            by (clear - Hscp2 Hcolsea2; fsetdec).
          clear - Hfs2a HU. fsetdec. }
        pose proof (flex_agree_rel_push_pairs ρna Hagre Hd1 Hd2) as Hpp.
        rewrite <- E1pa in Hpp. rewrite <- E2pa in Hpp.
        eapply flex_agree_rel_weaken;
          [ exact Hpp
          | intros a b Hi; revert Hi; rewrite ? in_app_iff; tauto
          | intros x Hx; exact Hx ]. }
      assert (Hb1b : forall x bd, binds x bd Ξ1b ->
                binds x bd (Ξsa ++ Θf1))
        by (intros x bd Hxb; apply binds_app_right; apply Hb1;
            unfold binds in *; apply in_or_app; right; exact Hxb).
      assert (Hb2b : forall x bd, binds x bd (lk_block r2b) ->
                binds x bd (Ξ2a ++ Θf2))
        by (intros x bd Hxb; apply binds_app_right; apply Hb2;
            unfold binds in *; apply in_or_app; right; exact Hxb).
      assert (Hop1b : forall x, x `in` Sa1 -> x `notin` Sm ->
                x `notin` dom Ξ1b -> ~ a_flex_tvar (Ξsa ++ Θf1) x).
      { intros x h1 h2 h3 Hf.
        assert (hx0 : x `notin` Sa0) by (clear - h2 Hgra; fsetdec).
        assert (hxa : x `notin` dom Ξ1a)
          by (clear - h2 Hbla1; fsetdec).
        assert (Hnf : ~ a_flex_tvar Θf1 x)
          by (apply Hop1; [ exact h1 | exact hx0
                          | rewrite dom_app; clear - hxa h3; fsetdec ]).
        assert (hxsa : x `notin` dom Ξsa).
        { assert (hxf : x `in` ftvar_in_aenv Θf1)
            by (apply Henr1; clear - h1 hx0; fsetdec).
          clear - Hfsa hxf. fsetdec. }
        apply (proj1 (a_flex_tvar_app_or Ξsa Θf1 x)) in Hf.
        destruct Hf as [ Hf | Hf ];
          [ apply hxsa; eapply a_flex_tvar_dom; exact Hf
          | exact (Hnf Hf) ]. }
      assert (Hop2b : forall x, x `in` lk_supply r2b ->
                x `notin` lk_supply r1a ->
                x `notin` dom (lk_block r2b) ->
                ~ a_flex_tvar (Ξ2a ++ Θf2) x).
      { intros x h1 h2 h3 Hf.
        assert (hx0 : x `notin` Sb0) by (clear - h2 Hgr2a; fsetdec).
        assert (hxa : x `notin` dom (lk_block r1a))
          by (clear - h2 Hbl2a1; fsetdec).
        assert (Hnf : ~ a_flex_tvar Θf2 x)
          by (apply Hop2; [ exact h1 | exact hx0
                          | rewrite dom_app; clear - hxa h3; fsetdec ]).
        assert (hx2a : x `notin` dom Ξ2a).
        { assert (hxf : x `in` ftvar_in_aenv Θf2)
            by (apply Henr2; clear - h1 hx0; fsetdec).
          clear - Hfs2a hxf. fsetdec. }
        apply (proj1 (a_flex_tvar_app_or Ξ2a Θf2 x)) in Hf.
        destruct Hf as [ Hf | Hf ];
          [ apply hx2a; eapply a_flex_tvar_dom; exact Hf
          | exact (Hnf Hf) ]. }
      assert (Henr1b : Sa1 ∖ Sm [<=] ftvar_in_aenv (Ξsa ++ Θf1))
        by (rewrite ftvar_in_aenv_app; clear - Henr1 Hgra; fsetdec).
      assert (Henr2b : lk_supply r2b ∖ lk_supply r1a
                [<=] ftvar_in_aenv (Ξ2a ++ Θf2))
        by (rewrite ftvar_in_aenv_app; clear - Henr2 Hgr2a; fsetdec).
      pose proof (dom_subset_ftvar_in_aenv Ξsa) as Hdfa.
      pose proof (dom_subset_ftvar_in_aenv Ξ2a) as Hdf2a.
      assert (Hmid1f : ftvar_in_pskl mid1
                [<=] ftvar_in_aenv Ξsa ∪ ftvar_in_aenv Θf1).
      { pose proof (a_solve_cstr_pure_eq_ftv Hpea Hf1a) as Hbd.
        rewrite ftvar_in_a_cstrs_app in Hscp1.
        clear - Hbd Hscp1 Hdfa. fsetdec. }
      assert (Hmid2f : ftvar_in_pskl mid2
                [<=] ftvar_in_aenv Ξ2a ∪ ftvar_in_aenv Θf2).
      { pose proof (a_solve_cstr_pure_eq_ftv Hpe2a Hf2a) as Hbd.
        rewrite ftvar_in_a_cstrs_app in Hscp2.
        clear - Hbd Hscp2 Hdf2a. fsetdec. }
      assert (Hscp1b : V ∪ cols_l (ρea ++ ρna ++ ρ)
                ∪ ftvar_in_pskl mid1 ∪ ftvar_in_a_cstrs C1b
                [<=] ftvar_in_aenv (Ξsa ++ Θf1)).
      { rewrite ! cols_l_app.
        assert (Hna : cols_l ρna [<=] ftvar_in_aenv Ξsa)
          by (rewrite <- dom_flex_pairs_l; rewrite <- E1pa; exact Hdfa).
        rewrite ftvar_in_a_cstrs_app in Hscp1.
        rewrite ftvar_in_aenv_app.
        clear - Hscp1 Hcolsea1 Hna Hmid1f. fsetdec. }
      assert (Hscp2b : V ∪ cols_r (ρea ++ ρna ++ ρ)
                ∪ ftvar_in_pskl mid2 ∪ ftvar_in_a_cstrs (lk_cstrs r2b)
                [<=] ftvar_in_aenv (Ξ2a ++ Θf2)).
      { rewrite ! cols_r_app.
        assert (Hna : cols_r ρna [<=] ftvar_in_aenv Ξ2a)
          by (rewrite <- dom_flex_pairs_r; rewrite <- E2pa; exact Hdf2a).
        rewrite ftvar_in_a_cstrs_app in Hscp2.
        rewrite ftvar_in_aenv_app.
        clear - Hscp2 Hcolsea2 Hna Hmid2f. fsetdec. }
      assert (Hcov1b : V ∪ ftvar_in_pskl P1b ∪ ftvar_in_pskl P1b' [<=] Sm)
        by (clear - Hcov1 Hgra; simpl in *; fsetdec).
      assert (Hcov2b : V ∪ ftvar_in_pskl Q2b ∪ ftvar_in_pskl Q2b'
                [<=] lk_supply r1a)
        by (clear - Hcov2 Hgr2a; simpl in *; fsetdec).
      pose proof (IHn Sm Sa1 _ _ _ _ _ _ Hszb E1b
                    _ _ _ _ _ _ _ (exist _ r2b Hr2b) Erb
                    (ρea ++ ρna ++ ρ) _ _ _ _ _ _ _ (L ∪ dom Ξ2a)
                    Hrbw Hrbw'
                    HαV Hαl'' Hαr'' Hf1b Hrelmid Hagr''
                    Hb1b Hb2b Hop1b Hop2b Henr1b Henr2b Hscp1b Hscp2b
                    Hcov1b Hcov2b) as HRECb.
      destruct HRECb as (ρeb & ρnb & Ξs2b & Q2f & Hf2b & E1pb & E2pb & Hub
                         & HLb & Hρeb & Hyieldb).
      simpl in Hρeb.
      exists (ρeb ++ ρea), (ρnb ++ ρna), (Ξs2b ++ Ξ2a), Q2f.
      split.
      { eapply a_solve_cstr_app; [ exact Hpe2a | exact Hf2a | exact Hf2b ]. }
      split.
      { subst Ξs1. rewrite E1pa. rewrite E1pb.
        rewrite flex_pairs_l_app. reflexivity. }
      split.
      { rewrite E2pa. rewrite E2pb.
        rewrite flex_pairs_r_app. reflexivity. }
      split.
      { apply uniq_app_4; [ exact Hub | exact Hua | ].
        unfold disjoint. clear - HLb. fsetdec. }
      split.
      { rewrite dom_app. clear - HLa HLb. fsetdec. }
      split.
      { intros a b Hin. apply in_app_or in Hin.
        destruct Hin as [ Hin | Hin ].
        - destruct (Hρeb _ _ Hin) as (h1 & h2 & h3 & h4 & Hiff).
          assert (ha0 : a `notin` Sa0) by (clear - h2 Hgra; fsetdec).
          assert (hb0 : b `notin` Sb0) by (clear - h4 Hgr2a; fsetdec).
          assert (hasa : a `notin` dom Ξsa).
          { assert (haf : a `in` ftvar_in_aenv Θf1)
              by (apply Henr1; clear - h1 ha0; fsetdec).
            clear - Hfsa haf. fsetdec. }
          assert (hb2a : b `notin` dom Ξ2a).
          { assert (hbf : b `in` ftvar_in_aenv Θf2)
              by (apply Henr2; clear - h3 hb0; fsetdec).
            clear - Hfs2a hbf. fsetdec. }
          rewrite (a_flex_tvar_notin_app Ξsa Θf1 hasa) in Hiff.
          rewrite (a_flex_tvar_notin_app Ξ2a Θf2 hb2a) in Hiff.
          split; [ exact h1 | ]. split; [ exact ha0 | ].
          split; [ exact h3 | ]. split; [ exact hb0 | ]. exact Hiff.
        - destruct (Hρea _ _ Hin) as (h1 & h2 & h3 & h4 & Hiff).
          split; [ clear - h1 Hgrb; fsetdec | ].
          split; [ exact h2 | ].
          split; [ clear - h3 Hgr2b; fsetdec | ].
          split; [ exact h4 | ]. exact Hiff. }
      destruct Hyieldb as [ Hrel' | Hh ]; [ left | right; exact Hh ].
      eapply rel_pskl_mono; [ exact Hrel' | | intros x Hx; exact Hx ].
      intros a0 b0 Hi; revert Hi;
        rewrite ? in_app_iff; simpl; rewrite ? in_app_iff; tauto.
    + (* ---- hatch branch: a var pattern absorbs the rest of the fold ---- *)
      subst mid1.
      destruct (a_solve_cstr_var_subject_inv Hpeb Hf1b) as [EΞsb EQ1].
      subst Ξsb. subst Q1. subst mid2.
      pose proof (a_solve_cstr_var_subject (Ξ2a ++ Θf2) γ2 Hpe2b) as Hf2b.
      exists ρea, ρna, (nil ++ Ξ2a).
      eexists.
      split.
      { eapply a_solve_cstr_app; [ exact Hpe2a | exact Hf2a | exact Hf2b ]. }
      split.
      { rewrite EΞs1. simpl. exact E1pa. }
      split.
      { simpl. exact E2pa. }
      split; [ simpl; exact Hua | ].
      split; [ simpl; exact HLa | ].
      split.
      { intros a b Hin.
        destruct (Hρea _ _ Hin) as (h1 & h2 & h3 & h4 & Hiff).
        split; [ clear - h1 Hgrb; fsetdec | ].
        split; [ exact h2 | ].
        split; [ clear - h3 Hgr2b; fsetdec | ].
        split; [ exact h4 | ]. exact Hiff. }
      right. exists γ1, γ2. split; reflexivity.
  - (* LE-ForallInh: (∀,∀) — pair (β1n, sf) *)
    match goal with
    | Hfr : ?b `notin` Sa0, Hp : e_lookeq (add ?b Sa0) _ _ _ _ _ _ _ |- _ =>
        rename Hfr into Hβfr; rename Hp into Hprem; rename b into β1n
    end.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | Hx : rel_pskl ρ V P ?q, Hy : rel_pskl ρ V P' ?q' |- _ =>
        rename Hx into Hrs; rename Hy into Hrt;
        rename q into Q2s; rename q' into Q2t
    end.
    revert Hs. simp e_lookeq_impl.
    match goal with
    | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
        let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
        destruct (sumbool_of_bool scr) as [Hmt | Hmf];
        [ | exfalso; apply mem_false_notin in Hmf;
            simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
    end.
    match goal with
    | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
        let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
        let Er := fresh "Er" in
        destruct call as [ [r1 Hr1] | ] eqn:Er;
        [ | intros Hs; discriminate ]
    end.
    intros Hs. inversion Hs; subst s; clear Hs.
    simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
    set (sf := supply_fresh Sb0) in *.
    (* the pair's facts *)
    assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
    assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
    pose proof (e_lookeq_supply_grows Hprem) as Hgr1.
    assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ Hprem)
      as (_ & Hbl1 & _ & _).
    assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
    assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
      by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
    pose proof (supply_fresh_notin Sb0) as Hsf0.
    pose proof (e_lookeq_supply_grows Hr1) as Hgr2.
    assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ Hr1)
      as (_ & Hbl2 & _ & _).
    assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
    assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
      by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
    assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
      by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
    assert (Hsff : sf `in` ftvar_in_aenv Θf2)
      by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
    (* the recursion at the extended pair list *)
    assert (Hsz' : size_pskl (open_pskl_wrt_pskl P (pskl_var_f β1n))
                   + size_pskl (open_pskl_wrt_pskl P' (pskl_var_f β1n)) < n)
      by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
          clear - Hsz; simpl in *; lia).
    assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
    { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
      split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
    assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
      by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
    assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
      by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
    assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
              x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
      by (intros x Hx1 Hx2 Hx3; apply Hop1;
          [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
    assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
              x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
      by (intros x Hx1 Hx2 Hx3; apply Hop2;
          [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
    assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
      by (clear - Henr1; fsetdec).
    assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
      by (clear - Henr2; fsetdec).
    assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
              ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
      by (simpl; clear - Hscp1 Hβ1f; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
              ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
      by (simpl; clear - Hscp2 Hsff; fsetdec).
    assert (Hcov1' : V ∪ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f β1n))
              ∪ ftvar_in_pskl (open_pskl_wrt_pskl P' (pskl_var_f β1n))
              [<=] add β1n Sa0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β1n))
        as Hup1.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f β1n))
        as Hup2.
      clear - Hcov1 Hup1 Hup2. simpl in *. fsetdec. }
    assert (Hcov2' : V ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q2s (pskl_var_f sf))
              ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q2t (pskl_var_f sf))
              [<=] add sf Sb0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q2s (pskl_var_f sf))
        as Hup1.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q2t (pskl_var_f sf))
        as Hup2.
      clear - Hcov2 Hup1 Hup2. simpl in *. fsetdec. }
    assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V
              (open_pskl_wrt_pskl P (pskl_var_f β1n))
              (open_pskl_wrt_pskl Q2s (pskl_var_f sf)))
      by (apply rel_pskl_open_pair; exact Hrs).
    assert (Hrt' : rel_pskl ((β1n, sf) :: ρ) V
              (open_pskl_wrt_pskl P' (pskl_var_f β1n))
              (open_pskl_wrt_pskl Q2t (pskl_var_f sf)))
      by (apply rel_pskl_open_pair; exact Hrt).
    assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
      by (apply rel_pskl_extend_pair; exact Hrelacc).
    pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ Hsz' Hprem
                  _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                  ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                  Hrs' Hrt'
                  HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                  Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                  Hcov1' Hcov2') as HREC.
    destruct HREC as (ρe' & ρn & Ξs2 & Q2f & Hf2 & E1p & E2p & Hu & HL
                      & Hρe & Hyield).
    exists (ρe' ++ ((β1n, sf) :: nil)), ρn, Ξs2, Q2f.
    split; [ exact Hf2 | ].
    split; [ exact E1p | ]. split; [ exact E2p | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    split.
    { intros a b Hin. apply in_app_or in Hin.
      destruct Hin as [ Hin | Hin ].
      - destruct (Hρe _ _ Hin) as (Ha1 & Ha2 & Hb1' & Hb2' & Hiff).
        repeat split;
          solve [ assumption
                | clear - Ha2; fsetdec
                | clear - Hb2'; fsetdec
                | exact (proj1 Hiff) | exact (proj2 Hiff) ].
      - destruct Hin as [ E | [] ]. inversion E; subst.
        repeat split;
          solve [ assumption
                | intros Hf; exfalso; [ exact (Hnf1 Hf) ]
                | intros Hf; exfalso; [ exact (Hnf2 Hf) ] ]. }
    destruct Hyield as [ Hrel' | Hh ]; [ left | right; exact Hh ].
    eapply rel_pskl_mono; [ exact Hrel' | | intros x Hx; exact Hx ].
    intros a0 b0 Hi; revert Hi;
      rewrite ? in_app_iff; simpl; rewrite ? in_app_iff; tauto.
  - (* LE-ForallSyn: (∀,⫯) — pair (β1n, sf), target unchanged *)
    match goal with
    | Hfr : ?b `notin` Sa0, Hp : e_lookeq (add ?b Sa0) _ _ _ _ _ _ _ |- _ =>
        rename Hfr into Hβfr; rename Hp into Hprem; rename b into β1n
    end.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | Hx : rel_pskl ρ V P ?q |- _ =>
        rename Hx into Hrs; rename q into Q2s
    end.
    match goal with
    | Hy : rel_pskl ρ V P' ?q' |- _ =>
        rename Hy into Hrt0; rename q' into Q2t
    end.
    revert Hs. simp e_lookeq_impl.
    match goal with
    | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
        let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
        destruct (sumbool_of_bool scr) as [Hmt | Hmf];
        [ | exfalso; apply mem_false_notin in Hmf;
            simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
    end.
    match goal with
    | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
        let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
        let Er := fresh "Er" in
        destruct call as [ [r1 Hr1] | ] eqn:Er;
        [ | intros Hs; discriminate ]
    end.
    intros Hs. inversion Hs; subst s; clear Hs.
    simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
    set (sf := supply_fresh Sb0) in *.
    assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
    assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
    pose proof (e_lookeq_supply_grows Hprem) as Hgr1.
    assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ Hprem)
      as (_ & Hbl1 & _ & _).
    assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
    assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
      by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
    pose proof (supply_fresh_notin Sb0) as Hsf0.
    pose proof (e_lookeq_supply_grows Hr1) as Hgr2.
    assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ Hr1)
      as (_ & Hbl2 & _ & _).
    assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
    assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
      by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
    assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
      by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
    assert (Hsff : sf `in` ftvar_in_aenv Θf2)
      by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
    assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
    { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
      split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
    assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
      by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
    assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
      by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
    assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
              x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
      by (intros x Hx1 Hx2 Hx3; apply Hop1;
          [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
    assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
              x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
      by (intros x Hx1 Hx2 Hx3; apply Hop2;
          [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
    assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
      by (clear - Henr1; fsetdec).
    assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
      by (clear - Henr2; fsetdec).
    assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
              ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
      by (simpl; clear - Hscp1 Hβ1f; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
              ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
      by (simpl; clear - Hscp2 Hsff; fsetdec).
    assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
      by (apply rel_pskl_extend_pair; exact Hrelacc).

    assert (Hsz' : size_pskl (open_pskl_wrt_pskl P (pskl_var_f β1n))
                   + size_pskl (pskl_tophole P') < n)
      by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
          clear - Hsz; simpl in *; lia).
    assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V
              (open_pskl_wrt_pskl P (pskl_var_f β1n))
              (open_pskl_wrt_pskl Q2s (pskl_var_f sf)))
      by (apply rel_pskl_open_pair; exact Hrs).
    assert (Hrt' : rel_pskl ((β1n, sf) :: ρ) V
              (pskl_tophole P') (pskl_tophole Q2t))
      by (apply rel_pskl_extend_pair; exact HrelP').
    assert (Hcov1' : V ∪ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f β1n))
              ∪ ftvar_in_pskl (pskl_tophole P') [<=] add β1n Sa0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β1n))
          as Hup1.
      clear - Hcov1 Hup1. simpl in *. fsetdec. }
    assert (Hcov2' : V ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q2s (pskl_var_f sf))
              ∪ ftvar_in_pskl (pskl_tophole Q2t) [<=] add sf Sb0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q2s (pskl_var_f sf))
          as Hup1.
      clear - Hcov2 Hup1. simpl in *. fsetdec. }
    pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ Hsz' Hprem
                  _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                  ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                  Hrs' Hrt'
                  HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                  Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                  Hcov1' Hcov2') as HREC.
    destruct HREC as (ρe' & ρn & Ξs2 & Q2f & Hf2 & E1p & E2p & Hu & HL
                      & Hρe & Hyield).
    exists (ρe' ++ ((β1n, sf) :: nil)), ρn, Ξs2, Q2f.
    split; [ exact Hf2 | ].
    split; [ exact E1p | ]. split; [ exact E2p | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    split.
    { intros a b Hin. apply in_app_or in Hin.
      destruct Hin as [ Hin | Hin ].
      - destruct (Hρe _ _ Hin) as (Ha1 & Ha2 & Hb1' & Hb2' & Hiff).
        repeat split;
          solve [ assumption
                | clear - Ha2; fsetdec
                | clear - Hb2'; fsetdec
                | exact (proj1 Hiff) | exact (proj2 Hiff) ].
      - destruct Hin as [ E | [] ]. inversion E; subst.
        repeat split;
          solve [ assumption
                | intros Hf; exfalso; [ exact (Hnf1 Hf) ]
                | intros Hf; exfalso; [ exact (Hnf2 Hf) ] ]. }
    destruct Hyield as [ Hrel' | Hh ]; [ left | right; exact Hh ].
    eapply rel_pskl_mono; [ exact Hrel' | | intros x Hx; exact Hx ].
    intros a0 b0 Hi; revert Hi;
      rewrite ? in_app_iff; simpl; rewrite ? in_app_iff; tauto.
  - (* LE-UnivGhost: (⫯,⫯) unfold both *)
    inversion HrelP; subst. inversion HrelP'; subst.
    revert Hs. simp e_lookeq_impl.
    match goal with
    | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
        let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
        destruct (sumbool_of_bool scr) as [Hmt | Hmf];
        [ | exfalso; apply mem_false_notin in Hmf;
            simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
    end.
    match goal with
    | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
        let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
        let Er := fresh "Er" in
        destruct call as [ [r1 Hr1] | ] eqn:Er;
        [ | intros Hs; discriminate ]
    end.
    intros Hs. inversion Hs; subst s; clear Hs.
    simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
    clear E1.
    match goal with
    | Hr1x : lookeq_spec _ _ _ _ _ ?r |- _ =>
        eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
    end; try eassumption.
    all: try solve [ simpl in Hsz |- *; lia
                   | clear - Hcov1; simpl in *; fsetdec
                   | clear - Hcov2; simpl in *; fsetdec ].
  - (* LE-UnivGhost1: (⫯,∀) — pair (β1n, sf), subject unchanged *)
    match goal with
    | Hfr : ?b `notin` Sa0, Hp : e_lookeq (add ?b Sa0) _ _ _ _ _ _ _ |- _ =>
        rename Hfr into Hβfr; rename Hp into Hprem; rename b into β1n
    end.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | Hy : rel_pskl ρ V P' ?q' |- _ =>
        rename Hy into Hrt; rename q' into Q2t
    end.
    match goal with
    | Hx : rel_pskl ρ V P ?q |- _ =>
        rename Hx into Hrs0; rename q into Q2s
    end.
    revert Hs. simp e_lookeq_impl.
    match goal with
    | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
        let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
        destruct (sumbool_of_bool scr) as [Hmt | Hmf];
        [ | exfalso; apply mem_false_notin in Hmf;
            simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
    end.
    match goal with
    | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
        let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
        let Er := fresh "Er" in
        destruct call as [ [r1 Hr1] | ] eqn:Er;
        [ | intros Hs; discriminate ]
    end.
    intros Hs. inversion Hs; subst s; clear Hs.
    simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
    set (sf := supply_fresh Sb0) in *.
    assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
    assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
    pose proof (e_lookeq_supply_grows Hprem) as Hgr1.
    assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ Hprem)
      as (_ & Hbl1 & _ & _).
    assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
    assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
      by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
    pose proof (supply_fresh_notin Sb0) as Hsf0.
    pose proof (e_lookeq_supply_grows Hr1) as Hgr2.
    assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ Hr1)
      as (_ & Hbl2 & _ & _).
    assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
    assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
      by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
    assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
      by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
    assert (Hsff : sf `in` ftvar_in_aenv Θf2)
      by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
    assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
    { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
      split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
    assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
      by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
    assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
      by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
    assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
              x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
      by (intros x Hx1 Hx2 Hx3; apply Hop1;
          [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
    assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
              x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
      by (intros x Hx1 Hx2 Hx3; apply Hop2;
          [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
    assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
      by (clear - Henr1; fsetdec).
    assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
      by (clear - Henr2; fsetdec).
    assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
              ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
      by (simpl; clear - Hscp1 Hβ1f; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
              ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
      by (simpl; clear - Hscp2 Hsff; fsetdec).
    assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
      by (apply rel_pskl_extend_pair; exact Hrelacc).

    assert (Hsz' : size_pskl (pskl_tophole P)
                   + size_pskl (open_pskl_wrt_pskl P' (pskl_var_f β1n)) < n)
      by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
          clear - Hsz; simpl in *; lia).
    assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V
              (pskl_tophole P) (pskl_tophole Q2s))
      by (apply rel_pskl_extend_pair; exact HrelP).
    assert (Hrt' : rel_pskl ((β1n, sf) :: ρ) V
              (open_pskl_wrt_pskl P' (pskl_var_f β1n))
              (open_pskl_wrt_pskl Q2t (pskl_var_f sf)))
      by (apply rel_pskl_open_pair; exact Hrt).
    assert (Hcov1' : V ∪ ftvar_in_pskl (pskl_tophole P)
              ∪ ftvar_in_pskl (open_pskl_wrt_pskl P' (pskl_var_f β1n))
              [<=] add β1n Sa0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f β1n))
          as Hup1.
      clear - Hcov1 Hup1. simpl in *. fsetdec. }
    assert (Hcov2' : V ∪ ftvar_in_pskl (pskl_tophole Q2s)
              ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q2t (pskl_var_f sf))
              [<=] add sf Sb0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q2t (pskl_var_f sf))
          as Hup1.
      clear - Hcov2 Hup1. simpl in *. fsetdec. }
    pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ Hsz' Hprem
                  _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                  ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                  Hrs' Hrt'
                  HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                  Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                  Hcov1' Hcov2') as HREC.
    destruct HREC as (ρe' & ρn & Ξs2 & Q2f & Hf2 & E1p & E2p & Hu & HL
                      & Hρe & Hyield).
    exists (ρe' ++ ((β1n, sf) :: nil)), ρn, Ξs2, Q2f.
    split; [ exact Hf2 | ].
    split; [ exact E1p | ]. split; [ exact E2p | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    split.
    { intros a b Hin. apply in_app_or in Hin.
      destruct Hin as [ Hin | Hin ].
      - destruct (Hρe _ _ Hin) as (Ha1 & Ha2 & Hb1' & Hb2' & Hiff).
        repeat split;
          solve [ assumption
                | clear - Ha2; fsetdec
                | clear - Hb2'; fsetdec
                | exact (proj1 Hiff) | exact (proj2 Hiff) ].
      - destruct Hin as [ E | [] ]. inversion E; subst.
        repeat split;
          solve [ assumption
                | intros Hf; exfalso; [ exact (Hnf1 Hf) ]
                | intros Hf; exfalso; [ exact (Hnf2 Hf) ] ]. }
    destruct Hyield as [ Hrel' | Hh ]; [ left | right; exact Hh ].
    eapply rel_pskl_mono; [ exact Hrel' | | intros x Hx; exact Hx ].
    intros a0 b0 Hi; revert Hi;
      rewrite ? in_app_iff; simpl; rewrite ? in_app_iff; tauto.
  - (* LE-UnivGhost2: (⫯, guarded target) *)
    inversion HrelP; subst.
    match goal with
    | Hgd : guarded_pskl _ |- _ => inversion Hgd; subst
    end.
    + (* target unit: recurse through the runner's UG2 clause *)
      inversion HrelP'; subst.
      revert Hs. simp e_lookeq_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      clear E1.
      match goal with
      | Hr1x : lookeq_spec _ _ _ _ _ ?r |- _ =>
          eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
      end; try eassumption.
      all: try solve [ simpl in Hsz |- *; lia
                     | clear - Hcov1; simpl in *; fsetdec
                     | clear - Hcov2; simpl in *; fsetdec ].
    + (* target a VAR: the runner FlexRs — the junk head *)
      inversion HrelP'; subst.
      apply e_lookeq_var_target_inv in E1;
        [ | simpl in HαP1; exact HαP1 ].
      revert Hs. simp e_lookeq_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      assert (Hflex2 : a_flex_tvar Θf2 (supply_fresh Sb0))
        by (left; apply Hb2; unfold binds; simpl; auto).
      assert (Hscp1' : V ∪ cols_l ρ [<=] ftvar_in_aenv Θf1)
        by (clear - Hscp1; fsetdec).
      assert (Hscp2' : V ∪ cols_r ρ [<=] ftvar_in_aenv Θf2)
        by (clear - Hscp2; fsetdec).
      destruct E1 as [ [EΞ1 EC1] | (α1x & EΞ1 & EC1 & _) ]; subst;
        (apply a_solve_cstr_eq_inv in Hfold
          as (Ξh & Ξt & mid & EΞ & Hh & Ht));
        (inversion Ht; subst);
        (destruct (a_solve_eq_var_target_junk Hh L Hrelacc Hflex2
                     Hagr Hscp1' Hscp2')
          as (ρn & Ξh2 & mid2 & D2 & E1p & E2p & Hu & HL & Hyield));
        (exists (@nil (atom * atom)), ρn, (nil ++ Ξh2));
        eexists;
        (split;
         [ eapply a_solve_cstr__eq;
           [ exact D2 | apply a_solve_cstr__empty ] | ]);
        (split; [ simpl; exact E1p | ]);
        (split; [ simpl; exact E2p | ]);
        (split; [ simpl; exact Hu | ]);
        (split; [ simpl; exact HL | ]);
        (split; [ intros a b Hin; inversion Hin | ]);
        (destruct Hyield as [ Hrel' | [Emid1 Emid2] ];
         [ left; simpl; exact Hrel'
         | right; subst; eauto ]).
    + (* target an arrow: recurse through the runner's UG2 clause *)
      inversion HrelP'; subst.
      revert Hs. simp e_lookeq_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      clear E1.
      match goal with
      | Hr1x : lookeq_spec _ _ _ _ _ ?r |- _ =>
          eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
      end; try eassumption.
      all: try solve [ simpl in Hsz |- *; lia
                     | clear - Hcov1; simpl in *; fsetdec
                     | clear - Hcov2; simpl in *; fsetdec ].
  - (* LE-UnivGhostR: (guarded, ⫯) — unfold the target *)
    inversion HrelP'; subst.
    (* the subject is an arrow (unit/var are dead) *)
    inversion HrelP; subst;
      try solve [ exfalso; simpl in HαP1; clear - HαP1; fsetdec ];
      [ (* var subject: contradicts P ≠ α *)
        match goal with
        | Ha : rel_atom ρ V ?g1 ?g2, Hnee : ?PP <> pskl_var_f α |- _ =>
            exfalso;
            assert (Hg1 : g1 = α)
              by (simpl in HαP1; clear - HαP1; fsetdec);
            subst g1; apply Hnee; reflexivity
        end
      | | (* ∀ subject: not guarded *)
        match goal with
        | Hgd : guarded_pskl (pskl_all_syn _) |- _ => inversion Hgd
        end
      | (* ⫯ subject: not guarded *)
        match goal with
        | Hgd : guarded_pskl (pskl_tophole _) |- _ => inversion Hgd
        end ].
    revert Hs. simp e_lookeq_impl.
    match goal with
    | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
        let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
        destruct (sumbool_of_bool scr) as [Hmt | Hmf];
        [ | exfalso; apply mem_false_notin in Hmf;
            simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
    end.
    match goal with
    | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
        let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
        let Er := fresh "Er" in
        destruct call as [ [r1 Hr1] | ] eqn:Er;
        [ | intros Hs; discriminate ]
    end.
    intros Hs. inversion Hs; subst s; clear Hs.
    simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
    clear E1.
    match goal with
    | Hr1x : lookeq_spec _ _ _ _ _ ?r |- _ =>
        eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
    end; try eassumption.
    all: try solve [ simpl in Hsz |- *; lia
                   | clear - Hcov1; simpl in *; fsetdec
                   | clear - Hcov2; simpl in *; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §3 (cont.)  THE b-CORE, sub half                                      *)
(*                                                                        *)
(*  The conclusion pack is BARE — nothing downstream consumes a sub       *)
(*  yield or block pairing (the assembly wants only the fold, its         *)
(*  [uniq], and the avoid-set).                                           *)
(* ===================================================================== *)

Definition bcore_sub_stmt (n : nat) : Prop :=
  forall Sa0 Sa1 Θd α m P1 P1' Ξ1 C1,
  size_pskl P1 + size_pskl P1' < n ->
  {{ Sa0 ↝ Sa1 ⊨ Θd ⊢ P1 ≼[ α , m ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
  forall Sb0 Θr P2 P2' hp2 hp2' Hord
         (s : sig (looksub_spec Sb0 Θr α m P2 P2')),
  e_looksub_impl Sb0 Θr α m P2 P2' hp2 hp2' Hord = Some s ->
  forall ρ V Θf1 Θf2 acc1 acc2 Ξs1 Q1 (L : atoms),
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V P1' P2' ->
  α `in` V ->
  α `notin` cols_l ρ ->
  α `notin` cols_r ρ ->
  {{ Θf1 ⊩ C1 ⨾ acc1 ⤳ Ξs1 ⨾ Q1 }}a ->
  rel_pskl ρ V acc1 acc2 ->
  flex_agree_rel ρ V Θf1 Θf2 ->
  (forall x bd, binds x bd Ξ1 -> binds x bd Θf1) ->
  (forall x bd, binds x bd (lk_block (proj1_sig s)) -> binds x bd Θf2) ->
  (forall x, x `in` Sa1 -> x `notin` Sa0 -> x `notin` dom Ξ1 ->
     ~ a_flex_tvar Θf1 x) ->
  (forall x, x `in` lk_supply (proj1_sig s) -> x `notin` Sb0 ->
     x `notin` dom (lk_block (proj1_sig s)) -> ~ a_flex_tvar Θf2 x) ->
  (Sa1 ∖ Sa0) [<=] ftvar_in_aenv Θf1 ->
  (lk_supply (proj1_sig s) ∖ Sb0) [<=] ftvar_in_aenv Θf2 ->
  V ∪ cols_l ρ ∪ ftvar_in_pskl acc1 ∪ ftvar_in_a_cstrs C1
    [<=] ftvar_in_aenv Θf1 ->
  V ∪ cols_r ρ ∪ ftvar_in_pskl acc2
    ∪ ftvar_in_a_cstrs (lk_cstrs (proj1_sig s)) [<=] ftvar_in_aenv Θf2 ->
  V ∪ ftvar_in_pskl P1 ∪ ftvar_in_pskl P1' [<=] Sa0 ->
  V ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] Sb0 ->
  exists Ξs2 Q2,
    {{ Θf2 ⊩ (lk_cstrs (proj1_sig s)) ⨾ acc2 ⤳ Ξs2 ⨾ Q2 }}a
    /\ uniq Ξs2 /\ dom Ξs2 ∩ L [=] empty.

Lemma bcore_sub : forall n, bcore_sub_stmt n.
Proof.
  induction n as [ | n IHn ]; unfold bcore_sub_stmt;
    [ intros; exfalso; lia | ].
  intros Sa0 Sa1 Θd α m P1 P1' Ξ1 C1 Hsz E1 Sb0 Θr P2 P2' hp2 hp2' Hord s Hs
    ρ V Θf1 Θf2 acc1 acc2 Ξs1 Q1 L
    HrelP HrelP' HαV Hαl Hαr Hfold Hrelacc Hagr Hb1 Hb2 Hop1 Hop2
    Henr1 Henr2 Hscp1 Hscp2 Hcov1 Hcov2.
  destruct (sumbool_of_bool (mem α (ftvar_in_pskl P1))) as [Hmem | Hmem].
  2:{ (* ---- the α-FREE collapse ---- *)
    apply mem_false_notin in Hmem.
    assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
    assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
    destruct (e_looksub_subject_absent E1 HαSa Hmem) as [EΞ1 EC1]; subst.
    assert (HαP2 : α `notin` ftvar_in_pskl P2)
      by (eapply rel_pskl_notin_r; [ exact HrelP | exact Hmem | exact Hαr ]).
    destruct s as [r Hr]. simpl in *.
    destruct (e_looksub_subject_absent Hr HαSb HαP2) as [EΞ2 EC2].
    rewrite EC2.
    inversion Hfold; subst.
    exists (@nil (atom * abind)).
    eexists.
    split; [ apply a_solve_cstr__empty | ].
    split; [ auto | simpl; clear; fsetdec ]. }
  apply mem_true_in in Hmem. rename Hmem into HαP1.
  assert (HαP2 : α `in` ftvar_in_pskl P2)
    by (eapply rel_pskl_in_id; [ exact HrelP | exact HαP1 | exact Hαl ]).
  inversion E1; subst.
  - (* LS-Var: transport 3 on the fold's terminal solve *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ =>
        inversion Ha; subst;
        [ exfalso; apply Hαl;
          match goal with
          | Hin : In (α, _) ρ |- _ => exact (cols_l_in _ _ _ Hin)
          end | ]
    end.
    revert Hs. simp e_looksub_impl.
    match goal with
    | |- context [ match ?scr with left _ => _ | right _ => _ end ] =>
        destruct scr as [Heq | Hne]; [ | contradiction ]
    end.
    intros Hs. inversion Hs; subst s; clear Hs.
    simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
    destruct (a_solve_cstr_sub_inv Hfold) as [_ Hsolve1].
    assert (Hscp1' : V ∪ cols_l ρ [<=] ftvar_in_aenv Θf1)
      by (clear - Hscp1; fsetdec).
    assert (Hscp2' : V ∪ cols_r ρ [<=] ftvar_in_aenv Θf2)
      by (clear - Hscp2; fsetdec).
    destruct (a_solve_sub_rel Hsolve1 L Hrelacc HrelP' Hagr Hscp1' Hscp2')
      as (ρx & ρn & Ξ2s & Y2 & D2s & E1p & E2p & Hu & HL & Hρx & Hrel').
    exists Ξ2s, Y2.
    split; [ apply a_solve_cstr__sub; exact D2s | ].
    split; [ exact Hu | exact HL ].
  - (* LS-Absent: contradiction *)
    exfalso. clear - HαP1 H. fsetdec.
  - (* LS-Vacuous: target ◇ *)
    inversion HrelP'; subst.
    inversion Hfold; subst.
    inversion HrelP; subst;
      try solve [ exfalso; simpl in HαP1; clear - HαP1; fsetdec ].
    + (* var subject: the runner retains [sub m ◇] *)
      match goal with
      | Ha : rel_atom ρ V ?g1 ?g2 |- _ =>
          assert (Hg1 : g1 = α)
            by (simpl in HαP1; clear - HαP1; fsetdec);
          subst g1;
          inversion Ha; subst;
          [ exfalso; apply Hαl;
            match goal with
            | Hin : In (α, _) ρ |- _ => exact (cols_l_in _ _ _ Hin)
            end | ]
      end.
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match ?scr with left _ => _ | right _ => _ end ] =>
          destruct scr as [Heq | Hne]; [ | contradiction ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      exists (@nil (atom * abind)).
      eexists.
      split.
      { apply a_solve_cstr__sub. apply a_solve_sub__vacuous. }
      split; [ auto | simpl; clear; fsetdec ].
    + (* arrow subject *)
      revert Hs. simp e_looksub_impl. intros Hs.
      inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      exists (@nil (atom * abind)).
      eexists.
      split; [ apply a_solve_cstr__empty | ].
      split; [ auto | simpl; clear; fsetdec ].
    + (* ∀ subject *)
      revert Hs. simp e_looksub_impl. intros Hs.
      inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      exists (@nil (atom * abind)).
      eexists.
      split; [ apply a_solve_cstr__empty | ].
      split; [ auto | simpl; clear; fsetdec ].
    + (* ⫯ subject *)
      revert Hs. simp e_looksub_impl. intros Hs.
      inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      exists (@nil (atom * abind)).
      eexists.
      split; [ apply a_solve_cstr__empty | ].
      split; [ auto | simpl; clear; fsetdec ].
  - (* LS-Check: drop into the eq b-core *)
    match goal with
    | He : e_lookeq Sa0 _ _ _ _ Sa1 _ _ |- _ => rename He into E1e
    end.
    (* the subject is guarded, ≠ α, and holds α: an arrow *)
    inversion HrelP; subst;
      try solve [ exfalso; simpl in HαP1; clear - HαP1; fsetdec ];
      [ (* var subject: contradicts A ≠ var α *)
        match goal with
        | Ha : rel_atom ρ V ?g1 ?g2, Hnee : ?PP <> pskl_var_f α |- _ =>
            exfalso;
            assert (Hg1 : g1 = α)
              by (simpl in HαP1; clear - HαP1; fsetdec);
            subst g1; apply Hnee; reflexivity
        end
      | | (* ∀ subject: not guarded *)
        match goal with
        | Hgd : guarded_pskl (pskl_all_syn _) |- _ => inversion Hgd
        end
      | (* ⫯ subject: not guarded *)
        match goal with
        | Hgd : guarded_pskl (pskl_tophole _) |- _ => inversion Hgd
        end ].
    assert (Hgd2 : guarded_pskl P2')
      by (eapply rel_pskl_guarded; [ exact HrelP' | assumption ]).
    assert (Hgf2 : pskl_ghost_free P2')
      by (eapply rel_pskl_ghost_free; [ exact HrelP' | assumption ]).
    (* P2' is guarded — unit, var or arrow — and in each shape the TC
       catch-all (the Check clause) fires; the eq b-core finishes. *)
    inversion Hgd2; subst.
    +
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hck := fresh "Hck" in let Hcf := fresh "Hcf" in
          destruct (sumbool_of_bool scr) as [Hck | Hcf];
          [ | exfalso;
              rewrite (guarded_shape_ck_complete _ Hgd2) in Hcf;
              rewrite (ghost_free_ck_complete _ Hgf2) in Hcf;
              discriminate ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs. subst s. clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      pose proof (@bcore_eq
                    (S (size_pskl (pskl_arrow P0 P3) + size_pskl P1'))
                    Sa0 Sa1 _ _ (pskl_arrow P0 P3) P1' _ _ ltac:(lia) E1e
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ρ _ _ _ _ _ _ _ L
                    HrelP HrelP'
                    HαV Hαl Hαr Hfold Hrelacc Hagr
                    Hb1 Hb2 Hop1 Hop2 Henr1 Henr2 Hscp1 Hscp2
                    Hcov1 Hcov2) as HREC.
      destruct HREC as (ρe & ρn & Ξs2 & Q2c & Hf2 & _ & _ & Hu & HL & _ & _).
      exists Ξs2, Q2c.
      split; [ exact Hf2 | ]. split; [ exact Hu | exact HL ].
    +
      revert Hs; simp e_looksub_impl;
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end;
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hck := fresh "Hck" in let Hcf := fresh "Hcf" in
          destruct (sumbool_of_bool scr) as [Hck | Hcf];
          [ | exfalso;
              rewrite (guarded_shape_ck_complete _ Hgd2) in Hcf;
              rewrite (ghost_free_ck_complete _ Hgf2) in Hcf;
              discriminate ]
      end;
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end;
      intros Hs; inversion Hs; subst s; clear Hs;
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *;
      match goal with
      | Hr1x : lookeq_spec _ _ _ _ _ ?r, Erx : _ = Some _ |- _ =>
          pose proof (@bcore_eq
                    (S (size_pskl (pskl_arrow P0 P3) + size_pskl P1'))
                    Sa0 Sa1 _ _ (pskl_arrow P0 P3) P1' _ _ ltac:(lia) E1e
                    _ _ _ _ _ _ _ (exist _ r Hr1x) Erx
                    ρ _ _ _ _ _ _ _ L
                    HrelP HrelP'
                    HαV Hαl Hαr Hfold Hrelacc Hagr
                    Hb1 Hb2 Hop1 Hop2 Henr1 Henr2 Hscp1 Hscp2
                    Hcov1 Hcov2) as HREC
      end;
      destruct HREC as (ρe & ρn & Ξs2 & Q2c & Hf2 & _ & _ & Hu & HL & _ & _);
      exists Ξs2, Q2c;
      (split; [ exact Hf2 | ]); (split; [ exact Hu | exact HL ]).
    +
      revert Hs; simp e_looksub_impl;
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end;
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hck := fresh "Hck" in let Hcf := fresh "Hcf" in
          destruct (sumbool_of_bool scr) as [Hck | Hcf];
          [ | exfalso;
              rewrite (guarded_shape_ck_complete _ Hgd2) in Hcf;
              rewrite (ghost_free_ck_complete _ Hgf2) in Hcf;
              discriminate ]
      end;
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end;
      intros Hs; inversion Hs; subst s; clear Hs;
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *;
      match goal with
      | Hr1x : lookeq_spec _ _ _ _ _ ?r, Erx : _ = Some _ |- _ =>
          pose proof (@bcore_eq
                    (S (size_pskl (pskl_arrow P0 P3) + size_pskl P1'))
                    Sa0 Sa1 _ _ (pskl_arrow P0 P3) P1' _ _ ltac:(lia) E1e
                    _ _ _ _ _ _ _ (exist _ r Hr1x) Erx
                    ρ _ _ _ _ _ _ _ L
                    HrelP HrelP'
                    HαV Hαl Hαr Hfold Hrelacc Hagr
                    Hb1 Hb2 Hop1 Hop2 Henr1 Henr2 Hscp1 Hscp2
                    Hcov1 Hcov2) as HREC
      end;
      destruct HREC as (ρe & ρn & Ξs2 & Q2c & Hf2 & _ & _ & Hu & HL & _ & _);
      exists Ξs2, Q2c;
      (split; [ exact Hf2 | ]); (split; [ exact Hu | exact HL ]).
  - (* LS-ForallR: target peels — same-root at shaped subjects,
       the o2 crossing at a var subject *)
    match goal with
    | Hfr : ?b `notin` Sa0,
      Hp : e_looksub (add ?b Sa0) _ _ _ _ _ _ _ _ |- _ =>
        rename Hfr into Hβfr; rename Hp into Hprem; rename b into β1n
    end.
    match goal with
    | Hg : pskl_ghost_free (pskl_all_syn ?bb) |- _ =>
        rename Hg into Hgf1; rename bb into B1
    end.
    inversion HrelP'; subst.
    match goal with
    | Hy : rel_pskl ρ V B1 ?q' |- _ =>
        rename Hy into Hrt; rename q' into B2
    end.
    assert (Hgf2' : pskl_ghost_free (pskl_all_syn B2))
      by (eapply rel_pskl_ghost_free; [ exact HrelP' | exact Hgf1 ]).
    inversion HrelP; subst;
      try solve [ exfalso; simpl in HαP1; clear - HαP1; fsetdec ].
    + (* var subject — the o2 crossing *)
      match goal with
      | Ha : rel_atom ρ V ?g1 ?g2 |- _ =>
          assert (Hg1 : g1 = α)
            by (simpl in HαP1; clear - HαP1; fsetdec);
          subst g1;
          inversion Ha; subst;
          [ exfalso; apply Hαl;
            match goal with
            | Hin : In (α, _) ρ |- _ => exact (cols_l_in _ _ _ Hin)
            end | ]
      end.
      match goal with
      | Hp : e_looksub _ _ ?a mode_tc (pskl_var_f ?a) _ _ _ _ |- _ =>
          try rename a into α
      end.
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match ?scr with left _ => _ | right _ => _ end ] =>
          destruct scr as [Heq | Hne]; [ | contradiction ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      destruct (atom_fresh (ftvar_in_aenv Θf2 ∪ ftvar_in_pskl acc2
                  ∪ ftvar_in_pskl B2 ∪ V ∪ cols_l ρ ∪ cols_r ρ ∪ L
                  ∪ Sb0 ∪ {{ α }} ∪ ftvar_in_aenv Θf1)) as [β2' Hβ2'].
      assert (Hlc1 : lc_pskl (pskl_var_f α)) by auto.
      assert (Hlc2 : lc_pskl (open_pskl_wrt_pskl B2 (pskl_var_f β2'))).
      { inversion hp2'; subst. auto. }
      pose proof (e_looksub_order_total (add β2' Sb0) Θr α mode_tc
                    (pskl_var_f α)
                    (open_pskl_wrt_pskl B2 (pskl_var_f β2'))) as ordL.
      assert (Hleaf : exists
        (HrL : looksub_spec (add β2' Sb0) Θr α mode_tc (pskl_var_f α)
                 (open_pskl_wrt_pskl B2 (pskl_var_f β2'))
                 (mk_look_result (add β2' Sb0) nil
                    (a_cstr_sub mode_tc
                       (open_pskl_wrt_pskl B2 (pskl_var_f β2')) :: nil))),
        e_looksub_impl (add β2' Sb0) Θr α mode_tc (pskl_var_f α)
          (open_pskl_wrt_pskl B2 (pskl_var_f β2')) Hlc1 Hlc2 ordL
        = Some (exist _ _ HrL)).
      { simp e_looksub_impl.
        match goal with
        | |- context [ match ?scr with left _ => _ | right _ => _ end ] =>
            destruct scr as [Heq' | Hne']; [ | contradiction ]
        end.
        eexists. reflexivity. }
      destruct Hleaf as [HrL EleafT].
      assert (Hsz' : size_pskl (pskl_var_f α)
                     + size_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1n)) < n)
        by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
            clear - Hsz; simpl in *; lia).
      assert (Hrs' : rel_pskl ((β1n, β2') :: ρ) V
                (pskl_var_f α) (pskl_var_f α)).
      { apply rel_pskl_extend_pair. apply rel_pskl__var_f.
        apply rel_atom__id. exact HαV. }
      assert (Hrt' : rel_pskl ((β1n, β2') :: ρ) V
                (open_pskl_wrt_pskl B1 (pskl_var_f β1n))
                (open_pskl_wrt_pskl B2 (pskl_var_f β2')))
        by (apply rel_pskl_open_pair; exact Hrt).
      assert (Hnf2' : ~ a_flex_tvar ((β2' ~ abind_tvar) ++ Θf2) β2').
      { apply a_flex_tvar_cons_tvar_self.
        pose proof (dom_subset_ftvar_in_aenv Θf2) as Hd.
        clear - Hβ2' Hd. fsetdec. }
      assert (Hagr' : flex_agree_rel ((β1n, β2') :: ρ) V Θf1
                ((β2' ~ abind_tvar) ++ Θf2)).
      { apply flex_agree_rel_extend_pair_iff.
        - apply flex_agree_rel_push_tvar_r; [ exact Hagr | ].
          clear - Hβ2'. fsetdec.
        - split; intros Hf; exfalso.
          + exact (Hnf1 Hf).
          + exact (Hnf2' Hf). }
      assert (Hαl' : α `notin` cols_l ((β1n, β2') :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, β2') :: ρ))
        by (simpl; clear - Hαr Hβ2'; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, β2') :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      assert (Hb2L : forall x bd,
                binds x bd (@nil (atom * abind)) ->
                binds x bd ((β2' ~ abind_tvar) ++ Θf2))
        by (intros x bd Hxb; inversion Hxb).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2L : forall x, x `in` add β2' Sb0 ->
                x `notin` add β2' Sb0 ->
                x `notin` dom (@nil (atom * abind)) ->
                ~ a_flex_tvar ((β2' ~ abind_tvar) ++ Θf2) x)
        by (intros x Hx1 Hx2; exfalso; exact (Hx2 Hx1)).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2L : (add β2' Sb0) ∖ (add β2' Sb0)
                [<=] ftvar_in_aenv ((β2' ~ abind_tvar) ++ Θf2))
        by (clear; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, β2') :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2L : V ∪ cols_r ((β1n, β2') :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs
                    (a_cstr_sub mode_tc
                       (open_pskl_wrt_pskl B2 (pskl_var_f β2')) :: nil)
                [<=] ftvar_in_aenv ((β2' ~ abind_tvar) ++ Θf2)).
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B2
                      (pskl_var_f β2')) as Hup.
        simpl in Hscp2, Hup |- *. clear - Hscp2 Hup. fsetdec. }
      assert (Hcov1' : V ∪ ftvar_in_pskl (pskl_var_f α)
                ∪ ftvar_in_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1n))
                [<=] add β1n Sa0).
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B1
                      (pskl_var_f β1n)) as Hup.
        clear - Hcov1 Hup HαSa. simpl in *. fsetdec. }
      assert (Hcov2' : V ∪ ftvar_in_pskl (pskl_var_f α)
                ∪ ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f β2'))
                [<=] add β2' Sb0).
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B2
                      (pskl_var_f β2')) as Hup.
        clear - Hcov2 Hup HαSb. simpl in *. fsetdec. }
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ _ EleafT
                    ((β1n, β2') :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2L Hop1' Hop2L Henr1' Henr2L Hscp1' Hscp2L
                    Hcov1' Hcov2') as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      simpl in Hf2'.
      destruct (a_solve_cstr_sub_inv Hf2') as [_ Hsolve2].
      exists Ξs2, Q2c.
      split.
      { apply a_solve_cstr__sub.
        apply a_solve_sub__forall_r with (β := β2');
          [ exact Hgf2' | clear - Hβ2'; fsetdec | exact Hsolve2 ]. }
      split; [ exact Hu | exact HL ].
    + (* arrow subject — same root *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hgt := fresh "Hgt" in let Hgfx := fresh "Hgfx" in
          destruct (sumbool_of_bool scr) as [Hgt | Hgfx];
          [ | exfalso;
              rewrite (ghost_free_ck_complete _ Hgf2') in Hgfx;
              discriminate ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      set (sf := supply_fresh Sb0) in *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
        split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
      assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
        by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      match type of HrelP with
      | rel_pskl _ _ ?p1x ?p2x =>
          assert (Hsz' : size_pskl p1x
                   + size_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1n)) < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V p1x p2x)
            by (apply rel_pskl_extend_pair; exact HrelP);
          assert (Hcov1x : V ∪ ftvar_in_pskl p1x
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1n))
                   [<=] add β1n Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B1
                           (pskl_var_f β1n)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V ∪ ftvar_in_pskl p2x
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f sf))
                   [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B2
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      assert (Hrt' : rel_pskl ((β1n, sf) :: ρ) V
                (open_pskl_wrt_pskl B1 (pskl_var_f β1n))
                (open_pskl_wrt_pskl B2 (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrt).
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                    Hcov1x Hcov2x) as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      exists Ξs2, Q2c.
      split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
    + (* ∀ subject — same root *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hgt := fresh "Hgt" in let Hgfx := fresh "Hgfx" in
          destruct (sumbool_of_bool scr) as [Hgt | Hgfx];
          [ | exfalso;
              rewrite (ghost_free_ck_complete _ Hgf2') in Hgfx;
              discriminate ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      set (sf := supply_fresh Sb0) in *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
        split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
      assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
        by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      match type of HrelP with
      | rel_pskl _ _ ?p1x ?p2x =>
          assert (Hsz' : size_pskl p1x
                   + size_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1n)) < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V p1x p2x)
            by (apply rel_pskl_extend_pair; exact HrelP);
          assert (Hcov1x : V ∪ ftvar_in_pskl p1x
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1n))
                   [<=] add β1n Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B1
                           (pskl_var_f β1n)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V ∪ ftvar_in_pskl p2x
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f sf))
                   [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B2
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      assert (Hrt' : rel_pskl ((β1n, sf) :: ρ) V
                (open_pskl_wrt_pskl B1 (pskl_var_f β1n))
                (open_pskl_wrt_pskl B2 (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrt).
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                    Hcov1x Hcov2x) as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      exists Ξs2, Q2c.
      split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
    + (* ⫯ subject — same root *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hgt := fresh "Hgt" in let Hgfx := fresh "Hgfx" in
          destruct (sumbool_of_bool scr) as [Hgt | Hgfx];
          [ | exfalso;
              rewrite (ghost_free_ck_complete _ Hgf2') in Hgfx;
              discriminate ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      set (sf := supply_fresh Sb0) in *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
        split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
      assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
        by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      match type of HrelP with
      | rel_pskl _ _ ?p1x ?p2x =>
          assert (Hsz' : size_pskl p1x
                   + size_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1n)) < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V p1x p2x)
            by (apply rel_pskl_extend_pair; exact HrelP);
          assert (Hcov1x : V ∪ ftvar_in_pskl p1x
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1n))
                   [<=] add β1n Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B1
                           (pskl_var_f β1n)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V ∪ ftvar_in_pskl p2x
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f sf))
                   [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B2
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      assert (Hrt' : rel_pskl ((β1n, sf) :: ρ) V
                (open_pskl_wrt_pskl B1 (pskl_var_f β1n))
                (open_pskl_wrt_pskl B2 (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrt).
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                    Hcov1x Hcov2x) as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      exists Ξs2, Q2c.
      split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
  - (* LS-Arrow: the composition case (eq half via bcore_eq, sub via IHn) *)
    match goal with
    | Ha : e_lookeq Sa0 _ _ ?pa ?pa' ?sm ?xa ?ca,
      Hb : e_looksub ?sm _ _ _ ?pb ?pb' Sa1 ?xb ?cb |- _ =>
        rename Ha into E1a; rename Hb into E1b; rename sm into Sm;
        rename pa into P1a; rename pa' into P1a';
        rename pb into P1b; rename pb' into P1b';
        rename xa into Ξ1a; rename xb into Ξ1b;
        rename ca into C1a; rename cb into C1b
    end.
    inversion HrelP; subst. inversion HrelP'; subst.
    match goal with
    | H1x : rel_pskl ρ V P1a ?qa, H2x : rel_pskl ρ V P1b ?qb,
      H3x : rel_pskl ρ V P1a' ?qa', H4x : rel_pskl ρ V P1b' ?qb' |- _ =>
        rename H1x into Hra; rename H2x into Hrb;
        rename H3x into Hra'; rename H4x into Hrb';
        rename qa into Q2a; rename qb into Q2b;
        rename qa' into Q2a'; rename qb' into Q2b'
    end.
    revert Hs. simp e_looksub_impl.
    match goal with
    | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
        let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
        destruct (sumbool_of_bool scr) as [Hmt | Hmf];
        [ | exfalso; apply mem_false_notin in Hmf;
            simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
    end.
    match goal with
    | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
        let r1a := fresh "r1a" in let Hr1a := fresh "Hr1a" in
        let Era := fresh "Era" in
        destruct call as [ [r1a Hr1a] | ] eqn:Era;
        [ | intros Hs; discriminate ]
    end.
    match goal with
    | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
        let r2b := fresh "r2b" in let Hr2b := fresh "Hr2b" in
        let Erb := fresh "Erb" in
        destruct call as [ [r2b Hr2b] | ] eqn:Erb;
        [ | intros Hs; discriminate ]
    end.
    intros Hs. inversion Hs; subst s; clear Hs.
    simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
    pose proof (e_lookeq_cstrs_pure_eq E1a) as Hpea.
    pose proof (e_lookeq_cstrs_pure_eq Hr1a) as Hpe2a.
    destruct (a_solve_cstr_app_inv _ Hpea Hfold)
      as (Ξsa & Ξsb & mid1 & EΞs1 & Hf1a & Hf1b).
    pose proof (e_lookeq_supply_grows E1a) as Hgra.
    pose proof (e_looksub_supply_grows E1b) as Hgrb.
    pose proof (e_lookeq_supply_grows Hr1a) as Hgr2a.
    pose proof (e_looksub_supply_grows Hr2b) as Hgr2b.
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ E1a)
      as (Hbla1 & Hbla2 & _ & _).
    pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ E1b)
      as (Hblb1 & Hblb2 & _ & _).
    pose proof ((proj2 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ Hr1a)
      as (Hbl2a1 & Hbl2a2 & _ & _).
    pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr2b)
      as (Hbl2b1 & Hbl2b2 & _ & _).
    pose proof (a_solve_cstr_generated_fresh_set Hf1a) as Hfsa.
    assert (Hb1a : forall x bd, binds x bd Ξ1a -> binds x bd Θf1)
      by (intros x bd Hxb; apply Hb1; unfold binds in *;
          apply in_or_app; left; exact Hxb).
    assert (Hb2a : forall x bd, binds x bd (lk_block r1a) -> binds x bd Θf2)
      by (intros x bd Hxb; apply Hb2; unfold binds in *;
          apply in_or_app; left; exact Hxb).
    assert (Hop1a : forall x, x `in` Sm -> x `notin` Sa0 ->
              x `notin` dom Ξ1a -> ~ a_flex_tvar Θf1 x)
      by (intros x h1 h2 h3; apply Hop1;
          [ clear - h1 Hgrb; fsetdec | exact h2
          | rewrite dom_app; clear - h1 h3 Hblb2; fsetdec ]).
    assert (Hop2a : forall x, x `in` lk_supply r1a -> x `notin` Sb0 ->
              x `notin` dom (lk_block r1a) -> ~ a_flex_tvar Θf2 x)
      by (intros x h1 h2 h3; apply Hop2;
          [ clear - h1 Hgr2b; fsetdec | exact h2
          | rewrite dom_app; clear - h1 h3 Hbl2b2; fsetdec ]).
    assert (Henr1a : Sm ∖ Sa0 [<=] ftvar_in_aenv Θf1)
      by (clear - Henr1 Hgrb; fsetdec).
    assert (Henr2a : lk_supply r1a ∖ Sb0 [<=] ftvar_in_aenv Θf2)
      by (clear - Henr2 Hgr2b; fsetdec).
    assert (Hscp1a : V ∪ cols_l ρ ∪ ftvar_in_pskl acc1
              ∪ ftvar_in_a_cstrs C1a [<=] ftvar_in_aenv Θf1).
    { rewrite ftvar_in_a_cstrs_app in Hscp1. clear - Hscp1. fsetdec. }
    assert (Hscp2a : V ∪ cols_r ρ ∪ ftvar_in_pskl acc2
              ∪ ftvar_in_a_cstrs (lk_cstrs r1a) [<=] ftvar_in_aenv Θf2).
    { rewrite ftvar_in_a_cstrs_app in Hscp2. clear - Hscp2. fsetdec. }
    assert (Hcov1a : V ∪ ftvar_in_pskl P1a ∪ ftvar_in_pskl P1a' [<=] Sa0)
      by (clear - Hcov1; simpl in *; fsetdec).
    assert (Hcov2a : V ∪ ftvar_in_pskl Q2a ∪ ftvar_in_pskl Q2a' [<=] Sb0)
      by (clear - Hcov2; simpl in *; fsetdec).
    pose proof (@bcore_eq
                  (S (size_pskl P1a + size_pskl P1a'))
                  Sa0 Sm _ _ P1a P1a' _ _ ltac:(lia) E1a
                  _ _ _ _ _ _ _ (exist _ r1a Hr1a) Era
                  ρ _ _ _ _ _ _ _ L
                  Hra Hra'
                  HαV Hαl Hαr Hf1a Hrelacc Hagr
                  Hb1a Hb2a Hop1a Hop2a Henr1a Henr2a Hscp1a Hscp2a
                  Hcov1a Hcov2a) as HRECa.
    destruct HRECa as (ρea & ρna & Ξ2a & mid2 & Hf2a & E1pa & E2pa & Hua
                       & HLa & Hρea & Hyielda).
    simpl in Hρea, Hf2a.
    pose proof (a_solve_cstr_generated_fresh_set Hf2a) as Hfs2a.
    assert (Hcolsea1 : cols_l ρea [<=] ftvar_in_aenv Θf1).
    { apply cols_l_bound. intros a b Hin.
      destruct (Hρea _ _ Hin) as (h1 & h2 & _).
      apply Henr1. clear - h1 h2 Hgrb. fsetdec. }
    assert (Hcolsea2 : cols_r ρea [<=] ftvar_in_aenv Θf2).
    { apply cols_r_bound. intros a b Hin.
      destruct (Hρea _ _ Hin) as (_ & _ & h1 & h2 & _).
      apply Henr2. clear - h1 h2 Hgr2b. fsetdec. }
    destruct Hyielda as [ Hrelmid | [γ1 [γ2 [Emid1 Emid2]]] ].
    + (* rel branch: the sub-IH at the extended contexts *)
      assert (Hszb : size_pskl P1b + size_pskl P1b' < n)
        by (clear - Hsz; simpl in *; lia).
      assert (Hrbw : rel_pskl (ρea ++ ρna ++ ρ) V P1b Q2b).
      { eapply rel_pskl_mono; [ exact Hrb | | intros x Hx; exact Hx ].
        intros a0 b0 Hi. rewrite ? in_app_iff. tauto. }
      assert (Hrbw' : rel_pskl (ρea ++ ρna ++ ρ) V P1b' Q2b').
      { eapply rel_pskl_mono; [ exact Hrb' | | intros x Hx; exact Hx ].
        intros a0 b0 Hi. rewrite ? in_app_iff. tauto. }
      assert (Hαl'' : α `notin` cols_l (ρea ++ ρna ++ ρ)).
      { rewrite ! cols_l_app.
        assert (Hα1 : α `notin` cols_l ρea).
        { apply cols_l_fresh. intros a b Hin.
          destruct (Hρea _ _ Hin) as (_ & h2 & _).
          assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
          intros ->. clear - h2 HαSa. fsetdec. }
        assert (Hα2 : α `notin` cols_l ρna).
        { rewrite <- dom_flex_pairs_l. rewrite <- E1pa.
          assert (HαF : α `in` ftvar_in_aenv Θf1)
            by (clear - HαV Hscp1; fsetdec).
          clear - Hfsa HαF. fsetdec. }
        clear - Hα1 Hα2 Hαl. fsetdec. }
      assert (Hαr'' : α `notin` cols_r (ρea ++ ρna ++ ρ)).
      { rewrite ! cols_r_app.
        assert (Hα1 : α `notin` cols_r ρea).
        { apply cols_r_fresh. intros a b Hin.
          destruct (Hρea _ _ Hin) as (_ & _ & _ & h2 & _).
          assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
          intros ->. clear - h2 HαSb. fsetdec. }
        assert (Hα2 : α `notin` cols_r ρna).
        { rewrite <- dom_flex_pairs_r. rewrite <- E2pa.
          assert (HαF : α `in` ftvar_in_aenv Θf2)
            by (clear - HαV Hscp2; fsetdec).
          clear - Hfs2a HαF. fsetdec. }
        clear - Hα1 Hα2 Hαr. fsetdec. }
      assert (Hagre : flex_agree_rel (ρea ++ ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pairs_iff; [ exact Hagr | ].
        intros a b Hin. destruct (Hρea _ _ Hin) as (_ & _ & _ & _ & Hiff).
        exact Hiff. }
      assert (Hagr'' : flex_agree_rel (ρea ++ ρna ++ ρ) V
                (Ξsa ++ Θf1) (Ξ2a ++ Θf2)).
      { assert (Hd1 : cols_l ρna ∩ (V ∪ cols_l (ρea ++ ρ)) [=] empty).
        { rewrite <- dom_flex_pairs_l. rewrite <- E1pa.
          rewrite cols_l_app.
          assert (HU : V ∪ (cols_l ρea ∪ cols_l ρ)
                        [<=] ftvar_in_aenv Θf1)
            by (clear - Hscp1 Hcolsea1; fsetdec).
          clear - Hfsa HU. fsetdec. }
        assert (Hd2 : cols_r ρna ∩ (V ∪ cols_r (ρea ++ ρ)) [=] empty).
        { rewrite <- dom_flex_pairs_r. rewrite <- E2pa.
          rewrite cols_r_app.
          assert (HU : V ∪ (cols_r ρea ∪ cols_r ρ)
                        [<=] ftvar_in_aenv Θf2)
            by (clear - Hscp2 Hcolsea2; fsetdec).
          clear - Hfs2a HU. fsetdec. }
        pose proof (flex_agree_rel_push_pairs ρna Hagre Hd1 Hd2) as Hpp.
        rewrite <- E1pa in Hpp. rewrite <- E2pa in Hpp.
        eapply flex_agree_rel_weaken;
          [ exact Hpp
          | intros a b Hi; revert Hi; rewrite ? in_app_iff; tauto
          | intros x Hx; exact Hx ]. }
      assert (Hb1b : forall x bd, binds x bd Ξ1b ->
                binds x bd (Ξsa ++ Θf1))
        by (intros x bd Hxb; apply binds_app_right; apply Hb1;
            unfold binds in *; apply in_or_app; right; exact Hxb).
      assert (Hb2b : forall x bd, binds x bd (lk_block r2b) ->
                binds x bd (Ξ2a ++ Θf2))
        by (intros x bd Hxb; apply binds_app_right; apply Hb2;
            unfold binds in *; apply in_or_app; right; exact Hxb).
      assert (Hop1b : forall x, x `in` Sa1 -> x `notin` Sm ->
                x `notin` dom Ξ1b -> ~ a_flex_tvar (Ξsa ++ Θf1) x).
      { intros x h1 h2 h3 Hf.
        assert (hx0 : x `notin` Sa0) by (clear - h2 Hgra; fsetdec).
        assert (hxa : x `notin` dom Ξ1a)
          by (clear - h2 Hbla1; fsetdec).
        assert (Hnf : ~ a_flex_tvar Θf1 x)
          by (apply Hop1; [ exact h1 | exact hx0
                          | rewrite dom_app; clear - hxa h3; fsetdec ]).
        assert (hxsa : x `notin` dom Ξsa).
        { assert (hxf : x `in` ftvar_in_aenv Θf1)
            by (apply Henr1; clear - h1 hx0; fsetdec).
          clear - Hfsa hxf. fsetdec. }
        apply (proj1 (a_flex_tvar_app_or Ξsa Θf1 x)) in Hf.
        destruct Hf as [ Hf | Hf ];
          [ apply hxsa; eapply a_flex_tvar_dom; exact Hf
          | exact (Hnf Hf) ]. }
      assert (Hop2b : forall x, x `in` lk_supply r2b ->
                x `notin` lk_supply r1a ->
                x `notin` dom (lk_block r2b) ->
                ~ a_flex_tvar (Ξ2a ++ Θf2) x).
      { intros x h1 h2 h3 Hf.
        assert (hx0 : x `notin` Sb0) by (clear - h2 Hgr2a; fsetdec).
        assert (hxa : x `notin` dom (lk_block r1a))
          by (clear - h2 Hbl2a1; fsetdec).
        assert (Hnf : ~ a_flex_tvar Θf2 x)
          by (apply Hop2; [ exact h1 | exact hx0
                          | rewrite dom_app; clear - hxa h3; fsetdec ]).
        assert (hx2a : x `notin` dom Ξ2a).
        { assert (hxf : x `in` ftvar_in_aenv Θf2)
            by (apply Henr2; clear - h1 hx0; fsetdec).
          clear - Hfs2a hxf. fsetdec. }
        apply (proj1 (a_flex_tvar_app_or Ξ2a Θf2 x)) in Hf.
        destruct Hf as [ Hf | Hf ];
          [ apply hx2a; eapply a_flex_tvar_dom; exact Hf
          | exact (Hnf Hf) ]. }
      assert (Henr1b : Sa1 ∖ Sm [<=] ftvar_in_aenv (Ξsa ++ Θf1))
        by (rewrite ftvar_in_aenv_app; clear - Henr1 Hgra; fsetdec).
      assert (Henr2b : lk_supply r2b ∖ lk_supply r1a
                [<=] ftvar_in_aenv (Ξ2a ++ Θf2))
        by (rewrite ftvar_in_aenv_app; clear - Henr2 Hgr2a; fsetdec).
      pose proof (dom_subset_ftvar_in_aenv Ξsa) as Hdfa.
      pose proof (dom_subset_ftvar_in_aenv Ξ2a) as Hdf2a.
      assert (Hmid1f : ftvar_in_pskl mid1
                [<=] union (ftvar_in_aenv Ξsa) (ftvar_in_aenv Θf1)).
      { pose proof (a_solve_cstr_pure_eq_ftv Hpea Hf1a) as Hbd.
        rewrite ftvar_in_a_cstrs_app in Hscp1.
        clear - Hbd Hscp1 Hdfa. fsetdec. }
      assert (Hmid2f : ftvar_in_pskl mid2
                [<=] union (ftvar_in_aenv Ξ2a) (ftvar_in_aenv Θf2)).
      { pose proof (a_solve_cstr_pure_eq_ftv Hpe2a Hf2a) as Hbd.
        rewrite ftvar_in_a_cstrs_app in Hscp2.
        clear - Hbd Hscp2 Hdf2a. fsetdec. }
      assert (Hscp1b : V ∪ cols_l (ρea ++ ρna ++ ρ)
                ∪ ftvar_in_pskl mid1 ∪ ftvar_in_a_cstrs C1b
                [<=] ftvar_in_aenv (Ξsa ++ Θf1)).
      { rewrite ! cols_l_app.
        assert (Hna : cols_l ρna [<=] ftvar_in_aenv Ξsa)
          by (rewrite <- dom_flex_pairs_l; rewrite <- E1pa; exact Hdfa).
        rewrite ftvar_in_a_cstrs_app in Hscp1.
        rewrite ftvar_in_aenv_app.
        clear - Hscp1 Hcolsea1 Hna Hmid1f. fsetdec. }
      assert (Hscp2b : V ∪ cols_r (ρea ++ ρna ++ ρ)
                ∪ ftvar_in_pskl mid2 ∪ ftvar_in_a_cstrs (lk_cstrs r2b)
                [<=] ftvar_in_aenv (Ξ2a ++ Θf2)).
      { rewrite ! cols_r_app.
        assert (Hna : cols_r ρna [<=] ftvar_in_aenv Ξ2a)
          by (rewrite <- dom_flex_pairs_r; rewrite <- E2pa; exact Hdf2a).
        rewrite ftvar_in_a_cstrs_app in Hscp2.
        rewrite ftvar_in_aenv_app.
        clear - Hscp2 Hcolsea2 Hna Hmid2f. fsetdec. }
      assert (Hcov1b : V ∪ ftvar_in_pskl P1b ∪ ftvar_in_pskl P1b' [<=] Sm)
        by (clear - Hcov1 Hgra; simpl in *; fsetdec).
      assert (Hcov2b : V ∪ ftvar_in_pskl Q2b ∪ ftvar_in_pskl Q2b'
                [<=] lk_supply r1a)
        by (clear - Hcov2 Hgr2a; simpl in *; fsetdec).
      pose proof (IHn Sm Sa1 _ _ _ _ _ _ _ Hszb E1b
                    _ _ _ _ _ _ _ (exist _ r2b Hr2b) Erb
                    (ρea ++ ρna ++ ρ) _ _ _ _ _ _ _ (L ∪ dom Ξ2a)
                    Hrbw Hrbw'
                    HαV Hαl'' Hαr'' Hf1b Hrelmid Hagr''
                    Hb1b Hb2b Hop1b Hop2b Henr1b Henr2b Hscp1b Hscp2b
                    Hcov1b Hcov2b) as HRECb.
      destruct HRECb as (Ξs2b & Q2f & Hf2b & Hub & HLb).
      simpl in Hf2b.
      exists (Ξs2b ++ Ξ2a), Q2f.
      split.
      { eapply a_solve_cstr_app; [ exact Hpe2a | exact Hf2a | exact Hf2b ]. }
      split.
      { apply uniq_app_4; [ exact Hub | exact Hua | ].
        unfold disjoint. clear - HLb. fsetdec. }
      { rewrite dom_app. clear - HLa HLb. fsetdec. }
    + (* hatch branch: a var pattern absorbs the sub half *)
      subst mid1. subst mid2.
      destruct (e_looksub_cstrs_shape Hr2b) as (Ce & Cs & ECs & Hpe & Hcs).
      assert (Hf2b : {{ (Ξ2a ++ Θf2) ⊩ (lk_cstrs r2b) ⨾ (pskl_var_f γ2)
                        ⤳ nil ⨾ (pskl_var_f γ2) }}a).
      { rewrite ECs.
        destruct Hcs as [ -> | (m'' & Q'' & ->) ].
        - rewrite app_nil_r. apply a_solve_cstr_var_subject. exact Hpe.
        - apply a_solve_cstr_var_subject_sub. exact Hpe. }
      exists (nil ++ Ξ2a).
      eexists.
      split.
      { eapply a_solve_cstr_app; [ exact Hpe2a | exact Hf2a | exact Hf2b ]. }
      split; [ simpl; exact Hua | ].
      simpl. exact HLa.
  - (* LS-ForallL: subject peels — same-root everywhere except the
       (∀-gf target @ TC) diagonal, paid by e_looksub_forall_r_first
       (+ the keep-peel at its Var bottom) *)
    match goal with
    | Hfr : ?b `notin` Sa0,
      Hp : e_looksub (add ?b Sa0) _ _ _ _ _ _ _ _ |- _ =>
        rename Hfr into Hβfr; rename Hp into Hprem; rename b into β1n
    end.
    inversion HrelP; subst.
    match goal with
    | Hx : rel_pskl ρ V ?p0 ?q0,
      Hp2 : e_looksub _ _ _ _ (open_pskl_wrt_pskl ?p0 _) _ _ _ _ |- _ =>
        rename Hx into Hrs0; rename p0 into P0s; rename q0 into Q0s
    end.
    inversion HrelP'; subst;
      try solve [ inversion hp2' ].
    + (* unit target — same root through the catch-all *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      set (sf := supply_fresh Sb0) in *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
        split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
      assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
        by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      match type of HrelP' with
      | rel_pskl _ _ ?t1x ?t2x =>
          assert (Hsz' : size_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   + size_pskl t1x < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrt2' : rel_pskl ((β1n, sf) :: ρ) V t1x t2x)
            by (apply rel_pskl_extend_pair; exact HrelP');
          assert (Hcov1x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   ∪ ftvar_in_pskl t1x [<=] add β1n Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0s
                           (pskl_var_f β1n)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q0s (pskl_var_f sf))
                   ∪ ftvar_in_pskl t2x [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0s
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V
                (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                (open_pskl_wrt_pskl Q0s (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrs0).
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt2'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                    Hcov1x Hcov2x) as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      exists Ξs2, Q2c.
      split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
    + (* var target — same root *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      set (sf := supply_fresh Sb0) in *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
        split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
      assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
        by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      match type of HrelP' with
      | rel_pskl _ _ ?t1x ?t2x =>
          assert (Hsz' : size_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   + size_pskl t1x < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrt2' : rel_pskl ((β1n, sf) :: ρ) V t1x t2x)
            by (apply rel_pskl_extend_pair; exact HrelP');
          assert (Hcov1x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   ∪ ftvar_in_pskl t1x [<=] add β1n Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0s
                           (pskl_var_f β1n)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q0s (pskl_var_f sf))
                   ∪ ftvar_in_pskl t2x [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0s
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V
                (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                (open_pskl_wrt_pskl Q0s (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrs0).
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt2'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                    Hcov1x Hcov2x) as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      exists Ξs2, Q2c.
      split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
    + (* arrow target — same root *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      set (sf := supply_fresh Sb0) in *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
        split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
      assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
        by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      match type of HrelP' with
      | rel_pskl _ _ ?t1x ?t2x =>
          assert (Hsz' : size_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   + size_pskl t1x < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrt2' : rel_pskl ((β1n, sf) :: ρ) V t1x t2x)
            by (apply rel_pskl_extend_pair; exact HrelP');
          assert (Hcov1x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   ∪ ftvar_in_pskl t1x [<=] add β1n Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0s
                           (pskl_var_f β1n)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q0s (pskl_var_f sf))
                   ∪ ftvar_in_pskl t2x [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0s
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V
                (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                (open_pskl_wrt_pskl Q0s (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrs0).
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt2'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                    Hcov1x Hcov2x) as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      exists Ξs2, Q2c.
      split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
    + (* ∀ target: TC splits on the runner's gf test *)
      match goal with
      | Hy : rel_pskl ρ V ?b1 ?b2,
        Hpx : e_looksub _ _ _ _ _ (pskl_all_syn ?b1) _ _ _ |- _ =>
          rename Hy into Hrt; rename b1 into B1; rename b2 into B2
      end.
      destruct m.
      * (* TI — the catch-all *)
        revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      set (sf := supply_fresh Sb0) in *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
        split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
      assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
        by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      match type of HrelP' with
      | rel_pskl _ _ ?t1x ?t2x =>
          assert (Hsz' : size_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   + size_pskl t1x < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrt2' : rel_pskl ((β1n, sf) :: ρ) V t1x t2x)
            by (apply rel_pskl_extend_pair; exact HrelP');
          assert (Hcov1x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   ∪ ftvar_in_pskl t1x [<=] add β1n Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0s
                           (pskl_var_f β1n)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q0s (pskl_var_f sf))
                   ∪ ftvar_in_pskl t2x [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0s
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V
                (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                (open_pskl_wrt_pskl Q0s (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrs0).
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt2'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                    Hcov1x Hcov2x) as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      exists Ξs2, Q2c.
      split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
      * (* TC — gf split *)
        revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
        match goal with
        | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
            let Hgt := fresh "Hgt" in let Hgfx := fresh "Hgfx" in
            destruct (sumbool_of_bool scr) as [Hgt | Hgfx]
        end.
        { (* gf TRUE — the runner ForallR-peels: the DIAGONAL *)
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
          intros Hs. inversion Hs; subst s; clear Hs.
          simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
          set (sf := supply_fresh Sb0) in *.
      set (Lβd := ftvar_in_aenv Θf1 ∪ ftvar_in_pskl acc1
                  ∪ ftvar_in_pskl B1 ∪ V ∪ cols_l ρ ∪ {{ α }}) in *.
      (* the runner's own ForallR test supplies the ghost-freeness *)
      assert (Hgft1 : pskl_ghost_free (pskl_all_syn B1))
        by (eapply rel_pskl_ghost_free_rev;
              [ apply rel_pskl__all_syn; exact Hrt
              | apply ghost_free_ck_sound; exact Hgt ]).
      destruct (e_looksub_forall_r_first Lβd E1 Hgft1 HαP1)
        as (β1d & S1' & Ξ' & C' & Hβ1d & HS1' & E1r & Hdisj).
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ E1r)
        as (_ & Hbl1r & _ & _).
      assert (Hαl' : α `notin` cols_l ((β1d, sf) :: ρ))
        by (simpl; clear - Hαl Hβ1d HαSa; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1d, sf) :: ρ))
        by (simpl; clear - Hαr Hsf0 HαSb; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1d, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1d, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrt' : rel_pskl ((β1d, sf) :: ρ) V
                (open_pskl_wrt_pskl B1 (pskl_var_f β1d))
                (open_pskl_wrt_pskl B2 (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrt).
      match type of HrelP with
      | rel_pskl _ _ ?p1x ?p2x =>
          assert (Hsz' : size_pskl p1x
                   + size_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1d)) < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrs' : rel_pskl ((β1d, sf) :: ρ) V p1x p2x)
            by (apply rel_pskl_extend_pair; exact HrelP);
          assert (Hcov1x : V ∪ ftvar_in_pskl p1x
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1d))
                   [<=] add β1d Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B1
                           (pskl_var_f β1d)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V ∪ ftvar_in_pskl p2x
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f sf))
                   [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B2
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      destruct Hdisj as [ (Hβ1S & EΞ' & EC') | (HβL & EΞ1 & EC1 & EΞ' & EC') ].
      * (* disjunct 1: the outputs ride, no enrichment *)
        subst Ξ' C'.
        assert (Hβ1Ξ1 : β1d `notin` dom Ξ1) by (clear - Hbl1r; fsetdec).
        assert (Hnf1 : ~ a_flex_tvar Θf1 β1d)
          by (apply Hop1; [ exact Hβ1S | exact Hβ1d | exact Hβ1Ξ1 ]).
        assert (Hβ1f : β1d `in` ftvar_in_aenv Θf1)
          by (apply Henr1; clear - Hβ1S Hβ1d; fsetdec).
        assert (Hagr' : flex_agree_rel ((β1d, sf) :: ρ) V Θf1 Θf2).
        { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
          split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
        assert (Hop1' : forall x, x `in` S1' -> x `notin` add β1d Sa0 ->
                  x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
          by (intros x Hx1 Hx2 Hx3; apply Hop1;
              [ clear - Hx1 Hx2 HS1'; fsetdec
              | clear - Hx2; fsetdec | exact Hx3 ]).
        assert (Henr1' : S1' ∖ (add β1d Sa0) [<=] ftvar_in_aenv Θf1)
          by (clear - Henr1 HS1'; fsetdec).
        assert (Hscp1' : V ∪ cols_l ((β1d, sf) :: ρ) ∪ ftvar_in_pskl acc1
                  ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
          by (simpl; clear - Hscp1 Hβ1f; fsetdec).
        pose proof (IHn (add β1d Sa0) S1' _ _ _ _ _ _ _ Hsz' E1r
                      _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                      ((β1d, sf) :: ρ) _ _ _ _ _ _ _ L
                      Hrs' Hrt'
                      HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                      Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                      Hcov1x Hcov2x) as HREC.
        destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
        exists Ξs2, Q2c.
        split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
      * (* disjunct 2: the Var bottom — keep-peel, side-1 enrichment *)
        subst Ξ1 C1 Ξ' C'.
        destruct (a_solve_cstr_sub_inv Hfold) as [_ Hsolve1].
        assert (Hβfr1 : β1d `notin` ftvar_in_aenv Θf1 ∪ ftvar_in_pskl acc1
                  ∪ ftvar_in_pskl B1)
          by (clear - HβL; subst Lβd; fsetdec).
        destruct (a_solve_sub_peel_forall_r_keep Hsolve1 Hβfr1)
          as (Ξp & Pp & Hsolvep).
        assert (Hfold' : {{ ((β1d ~ abind_tvar) ++ Θf1)
                  ⊩ (a_cstr_sub mode_tc
                       (open_pskl_wrt_pskl B1 (pskl_var_f β1d)) :: nil)
                  ⨾ acc1 ⤳ Ξp ⨾ Pp }}a)
          by (apply a_solve_cstr__sub; exact Hsolvep).
        assert (Hnf1' : ~ a_flex_tvar ((β1d ~ abind_tvar) ++ Θf1) β1d).
        { apply a_flex_tvar_cons_tvar_self.
          pose proof (dom_subset_ftvar_in_aenv Θf1) as Hd.
          clear - HβL Hd. subst Lβd. fsetdec. }
        assert (Hagr' : flex_agree_rel ((β1d, sf) :: ρ) V
                  ((β1d ~ abind_tvar) ++ Θf1) Θf2).
        { apply flex_agree_rel_extend_pair_iff.
          - apply flex_agree_rel_push_tvar_l; [ exact Hagr | ].
            clear - HβL. subst Lβd. fsetdec.
          - split; intros Hf; exfalso.
            + exact (Hnf1' Hf).
            + exact (Hnf2 Hf). }
        assert (Hb1' : forall x bd, binds x bd (@nil (atom * abind)) ->
                  binds x bd ((β1d ~ abind_tvar) ++ Θf1))
          by (intros x bd Hxb; inversion Hxb).
        assert (Hop1' : forall x, x `in` S1' -> x `notin` add β1d Sa0 ->
                  x `notin` dom (@nil (atom * abind)) ->
                  ~ a_flex_tvar ((β1d ~ abind_tvar) ++ Θf1) x).
        { intros x Hx1 Hx2 Hx3.
          assert (Hne : x <> β1d) by (clear - Hx2; fsetdec).
          rewrite (a_flex_tvar_cons_tvar_other Θf1 Hne).
          apply Hop1;
            [ clear - Hx1 Hx2 HS1'; fsetdec
            | clear - Hx2; fsetdec | simpl; auto ]. }
        assert (Henr1' : S1' ∖ (add β1d Sa0)
                  [<=] ftvar_in_aenv ((β1d ~ abind_tvar) ++ Θf1))
          by (simpl; clear - Henr1 HS1'; fsetdec).
        assert (Hscp1' : V ∪ cols_l ((β1d, sf) :: ρ) ∪ ftvar_in_pskl acc1
                  ∪ ftvar_in_a_cstrs
                      (a_cstr_sub mode_tc
                         (open_pskl_wrt_pskl B1 (pskl_var_f β1d)) :: nil)
                  [<=] ftvar_in_aenv ((β1d ~ abind_tvar) ++ Θf1)).
        { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B1
                        (pskl_var_f β1d)) as Hup.
          simpl in Hscp1, Hup |- *. clear - Hscp1 Hup. fsetdec. }
        pose proof (IHn (add β1d Sa0) S1' _ _ _ _ _ _ _ Hsz' E1r
                      _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                      ((β1d, sf) :: ρ) _ _ _ _ _ _ _ L
                      Hrs' Hrt'
                      HαV Hαl' Hαr' Hfold' Hrelacc' Hagr'
                      Hb1' Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                      Hcov1x Hcov2x) as HREC.
        destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
        exists Ξs2, Q2c.
        split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ]. }
        { (* gf FALSE — ForallL on both sides *)
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      set (sf := supply_fresh Sb0) in *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
        split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
      assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
        by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      match type of HrelP' with
      | rel_pskl _ _ ?t1x ?t2x =>
          assert (Hsz' : size_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   + size_pskl t1x < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrt2' : rel_pskl ((β1n, sf) :: ρ) V t1x t2x)
            by (apply rel_pskl_extend_pair; exact HrelP');
          assert (Hcov1x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   ∪ ftvar_in_pskl t1x [<=] add β1n Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0s
                           (pskl_var_f β1n)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q0s (pskl_var_f sf))
                   ∪ ftvar_in_pskl t2x [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0s
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V
                (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                (open_pskl_wrt_pskl Q0s (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrs0).
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt2'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                    Hcov1x Hcov2x) as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      exists Ξs2, Q2c.
      split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ]. }
      * (* FN — the catch-all *)
        revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      set (sf := supply_fresh Sb0) in *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
        split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
      assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
        by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      match type of HrelP' with
      | rel_pskl _ _ ?t1x ?t2x =>
          assert (Hsz' : size_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   + size_pskl t1x < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrt2' : rel_pskl ((β1n, sf) :: ρ) V t1x t2x)
            by (apply rel_pskl_extend_pair; exact HrelP');
          assert (Hcov1x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   ∪ ftvar_in_pskl t1x [<=] add β1n Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0s
                           (pskl_var_f β1n)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q0s (pskl_var_f sf))
                   ∪ ftvar_in_pskl t2x [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0s
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V
                (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                (open_pskl_wrt_pskl Q0s (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrs0).
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt2'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                    Hcov1x Hcov2x) as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      exists Ξs2, Q2c.
      split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
    + (* ◇ target — the spec collapse; only the runner's outputs matter *)
      destruct s as [r Hr]. simpl in *.
      destruct (e_looksub_hole_target Hr) as [EΞ2 EC2].
      destruct EC2 as [ -> | -> ].
      * exists (@nil (atom * abind)). eexists.
        split; [ apply a_solve_cstr__empty | ].
        split; [ auto | simpl; clear; fsetdec ].
      * exists (@nil (atom * abind)). eexists.
        split; [ apply a_solve_cstr__sub; apply a_solve_sub__vacuous | ].
        split; [ auto | simpl; clear; fsetdec ].
    + (* ⫯ target — same root *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      set (sf := supply_fresh Sb0) in *.
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (e_looksub_supply_grows Hprem) as Hgr1.
      assert (Hβ1Sa1 : β1n `in` Sa1) by (clear - Hgr1; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hprem)
        as (_ & Hbl1 & _ & _).
      assert (Hβ1Ξ1 : β1n `notin` dom Ξ1) by (clear - Hbl1; fsetdec).
      assert (Hnf1 : ~ a_flex_tvar Θf1 β1n)
        by (apply Hop1; [ exact Hβ1Sa1 | exact Hβfr | exact Hβ1Ξ1 ]).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hβ1f : β1n `in` ftvar_in_aenv Θf1)
        by (apply Henr1; clear - Hβ1Sa1 Hβfr; fsetdec).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      assert (Hagr' : flex_agree_rel ((β1n, sf) :: ρ) V Θf1 Θf2).
      { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
        split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
      assert (Hαl' : α `notin` cols_l ((β1n, sf) :: ρ))
        by (simpl; clear - Hαl HαSa Hβfr; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1n, sf) :: ρ))
        by (simpl; clear - Hαr HαSb Hsf0; fsetdec).
      assert (Hop1' : forall x, x `in` Sa1 -> x `notin` add β1n Sa0 ->
                x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop1;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr1' : Sa1 ∖ (add β1n Sa0) [<=] ftvar_in_aenv Θf1)
        by (clear - Henr1; fsetdec).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp1' : V ∪ cols_l ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc1
                ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
        by (simpl; clear - Hscp1 Hβ1f; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1n, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1n, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      match type of HrelP' with
      | rel_pskl _ _ ?t1x ?t2x =>
          assert (Hsz' : size_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   + size_pskl t1x < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrt2' : rel_pskl ((β1n, sf) :: ρ) V t1x t2x)
            by (apply rel_pskl_extend_pair; exact HrelP');
          assert (Hcov1x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                   ∪ ftvar_in_pskl t1x [<=] add β1n Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0s
                           (pskl_var_f β1n)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q0s (pskl_var_f sf))
                   ∪ ftvar_in_pskl t2x [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0s
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      assert (Hrs' : rel_pskl ((β1n, sf) :: ρ) V
                (open_pskl_wrt_pskl P0s (pskl_var_f β1n))
                (open_pskl_wrt_pskl Q0s (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrs0).
      pose proof (IHn (add β1n Sa0) Sa1 _ _ _ _ _ _ _ Hsz' Hprem
                    _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                    ((β1n, sf) :: ρ) _ _ _ _ _ _ _ L
                    Hrs' Hrt2'
                    HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                    Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                    Hcov1x Hcov2x) as HREC.
      destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
      exists Ξs2, Q2c.
      split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
  - (* LS-UnivGhostL: the ⫯ unfolds — same-root everywhere except the
       (∀-gf target @ TC) diagonal *)
    inversion HrelP; subst.
    inversion HrelP'; subst;
      try solve [ inversion hp2' ].
    + (* unit target *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      clear E1.
      match goal with
      | Hr1x : looksub_spec _ _ _ _ _ _ ?r |- _ =>
          eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
      end; try eassumption.
      all: try solve [ simpl in Hsz |- *; lia
                     | clear - Hcov1; simpl in *; fsetdec
                     | clear - Hcov2; simpl in *; fsetdec ].
    + (* var target *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      clear E1.
      match goal with
      | Hr1x : looksub_spec _ _ _ _ _ _ ?r |- _ =>
          eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
      end; try eassumption.
      all: try solve [ simpl in Hsz |- *; lia
                     | clear - Hcov1; simpl in *; fsetdec
                     | clear - Hcov2; simpl in *; fsetdec ].
    + (* arrow target *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      clear E1.
      match goal with
      | Hr1x : looksub_spec _ _ _ _ _ _ ?r |- _ =>
          eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
      end; try eassumption.
      all: try solve [ simpl in Hsz |- *; lia
                     | clear - Hcov1; simpl in *; fsetdec
                     | clear - Hcov2; simpl in *; fsetdec ].
    + (* ∀ target: TC splits on the runner's gf test *)
      match goal with
      | Hy : rel_pskl ρ V ?b1 ?b2,
        Hpx : e_looksub _ _ _ _ _ (pskl_all_syn ?b1) _ _ _ |- _ =>
          rename Hy into Hrt; rename b1 into B1; rename b2 into B2
      end.
      destruct m.
      * (* TI — the catch-all *)
        revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      clear E1.
      match goal with
      | Hr1x : looksub_spec _ _ _ _ _ _ ?r |- _ =>
          eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
      end; try eassumption.
      all: try solve [ simpl in Hsz |- *; lia
                     | clear - Hcov1; simpl in *; fsetdec
                     | clear - Hcov2; simpl in *; fsetdec ].
      * (* TC — gf split *)
        revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
        match goal with
        | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
            let Hgt := fresh "Hgt" in let Hgfx := fresh "Hgfx" in
            destruct (sumbool_of_bool scr) as [Hgt | Hgfx]
        end.
        { (* gf TRUE — the runner ForallR-peels: the DIAGONAL *)
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
          intros Hs. inversion Hs; subst s; clear Hs.
          simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
          set (sf := supply_fresh Sb0) in *.
      set (Lβd := ftvar_in_aenv Θf1 ∪ ftvar_in_pskl acc1
                  ∪ ftvar_in_pskl B1 ∪ V ∪ cols_l ρ ∪ {{ α }}) in *.
      (* the runner's own ForallR test supplies the ghost-freeness *)
      assert (Hgft1 : pskl_ghost_free (pskl_all_syn B1))
        by (eapply rel_pskl_ghost_free_rev;
              [ apply rel_pskl__all_syn; exact Hrt
              | apply ghost_free_ck_sound; exact Hgt ]).
      destruct (e_looksub_forall_r_first Lβd E1 Hgft1 HαP1)
        as (β1d & S1' & Ξ' & C' & Hβ1d & HS1' & E1r & Hdisj).
      assert (HαSa : α `in` Sa0) by (clear - HαV Hcov1; fsetdec).
      assert (HαSb : α `in` Sb0) by (clear - HαV Hcov2; fsetdec).
      pose proof (supply_fresh_notin Sb0) as Hsf0.
      pose proof (e_looksub_supply_grows Hr1) as Hgr2.
      assert (HsfS1 : sf `in` lk_supply r1) by (clear - Hgr2; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
        as (_ & Hbl2 & _ & _).
      assert (HsfΞ2 : sf `notin` dom (lk_block r1)) by (clear - Hbl2; fsetdec).
      assert (Hnf2 : ~ a_flex_tvar Θf2 sf)
        by (apply Hop2; [ exact HsfS1 | exact Hsf0 | exact HsfΞ2 ]).
      assert (Hsff : sf `in` ftvar_in_aenv Θf2)
        by (apply Henr2; clear - HsfS1 Hsf0; fsetdec).
      pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ E1r)
        as (_ & Hbl1r & _ & _).
      assert (Hαl' : α `notin` cols_l ((β1d, sf) :: ρ))
        by (simpl; clear - Hαl Hβ1d HαSa; fsetdec).
      assert (Hαr' : α `notin` cols_r ((β1d, sf) :: ρ))
        by (simpl; clear - Hαr Hsf0 HαSb; fsetdec).
      assert (Hrelacc' : rel_pskl ((β1d, sf) :: ρ) V acc1 acc2)
        by (apply rel_pskl_extend_pair; exact Hrelacc).
      assert (Hop2' : forall x, x `in` lk_supply r1 -> x `notin` add sf Sb0 ->
                x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x)
        by (intros x Hx1 Hx2 Hx3; apply Hop2;
            [ exact Hx1 | clear - Hx2; fsetdec | exact Hx3 ]).
      assert (Henr2' : lk_supply r1 ∖ (add sf Sb0) [<=] ftvar_in_aenv Θf2)
        by (clear - Henr2; fsetdec).
      assert (Hscp2' : V ∪ cols_r ((β1d, sf) :: ρ) ∪ ftvar_in_pskl acc2
                ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2)
        by (simpl; clear - Hscp2 Hsff; fsetdec).
      assert (Hrt' : rel_pskl ((β1d, sf) :: ρ) V
                (open_pskl_wrt_pskl B1 (pskl_var_f β1d))
                (open_pskl_wrt_pskl B2 (pskl_var_f sf)))
        by (apply rel_pskl_open_pair; exact Hrt).
      match type of HrelP with
      | rel_pskl _ _ ?p1x ?p2x =>
          assert (Hsz' : size_pskl p1x
                   + size_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1d)) < n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                clear - Hsz; simpl in *; lia);
          assert (Hrs' : rel_pskl ((β1d, sf) :: ρ) V p1x p2x)
            by (apply rel_pskl_extend_pair; exact HrelP);
          assert (Hcov1x : V ∪ ftvar_in_pskl p1x
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl B1 (pskl_var_f β1d))
                   [<=] add β1d Sa0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B1
                           (pskl_var_f β1d)) as Hup;
                clear - Hcov1 Hup; simpl in *; fsetdec);
          assert (Hcov2x : V ∪ ftvar_in_pskl p2x
                   ∪ ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f sf))
                   [<=] add sf Sb0)
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B2
                           (pskl_var_f sf)) as Hup;
                clear - Hcov2 Hup; simpl in *; fsetdec)
      end.
      destruct Hdisj as [ (Hβ1S & EΞ' & EC') | (HβL & EΞ1 & EC1 & EΞ' & EC') ].
      * (* disjunct 1: the outputs ride, no enrichment *)
        subst Ξ' C'.
        assert (Hβ1Ξ1 : β1d `notin` dom Ξ1) by (clear - Hbl1r; fsetdec).
        assert (Hnf1 : ~ a_flex_tvar Θf1 β1d)
          by (apply Hop1; [ exact Hβ1S | exact Hβ1d | exact Hβ1Ξ1 ]).
        assert (Hβ1f : β1d `in` ftvar_in_aenv Θf1)
          by (apply Henr1; clear - Hβ1S Hβ1d; fsetdec).
        assert (Hagr' : flex_agree_rel ((β1d, sf) :: ρ) V Θf1 Θf2).
        { apply flex_agree_rel_extend_pair_iff; [ exact Hagr | ].
          split; intros Hf; exfalso; [ exact (Hnf1 Hf) | exact (Hnf2 Hf) ]. }
        assert (Hop1' : forall x, x `in` S1' -> x `notin` add β1d Sa0 ->
                  x `notin` dom Ξ1 -> ~ a_flex_tvar Θf1 x)
          by (intros x Hx1 Hx2 Hx3; apply Hop1;
              [ clear - Hx1 Hx2 HS1'; fsetdec
              | clear - Hx2; fsetdec | exact Hx3 ]).
        assert (Henr1' : S1' ∖ (add β1d Sa0) [<=] ftvar_in_aenv Θf1)
          by (clear - Henr1 HS1'; fsetdec).
        assert (Hscp1' : V ∪ cols_l ((β1d, sf) :: ρ) ∪ ftvar_in_pskl acc1
                  ∪ ftvar_in_a_cstrs C1 [<=] ftvar_in_aenv Θf1)
          by (simpl; clear - Hscp1 Hβ1f; fsetdec).
        pose proof (IHn (add β1d Sa0) S1' _ _ _ _ _ _ _ Hsz' E1r
                      _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                      ((β1d, sf) :: ρ) _ _ _ _ _ _ _ L
                      Hrs' Hrt'
                      HαV Hαl' Hαr' Hfold Hrelacc' Hagr'
                      Hb1 Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                      Hcov1x Hcov2x) as HREC.
        destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
        exists Ξs2, Q2c.
        split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ].
      * (* disjunct 2: the Var bottom — keep-peel, side-1 enrichment *)
        subst Ξ1 C1 Ξ' C'.
        destruct (a_solve_cstr_sub_inv Hfold) as [_ Hsolve1].
        assert (Hβfr1 : β1d `notin` ftvar_in_aenv Θf1 ∪ ftvar_in_pskl acc1
                  ∪ ftvar_in_pskl B1)
          by (clear - HβL; subst Lβd; fsetdec).
        destruct (a_solve_sub_peel_forall_r_keep Hsolve1 Hβfr1)
          as (Ξp & Pp & Hsolvep).
        assert (Hfold' : {{ ((β1d ~ abind_tvar) ++ Θf1)
                  ⊩ (a_cstr_sub mode_tc
                       (open_pskl_wrt_pskl B1 (pskl_var_f β1d)) :: nil)
                  ⨾ acc1 ⤳ Ξp ⨾ Pp }}a)
          by (apply a_solve_cstr__sub; exact Hsolvep).
        assert (Hnf1' : ~ a_flex_tvar ((β1d ~ abind_tvar) ++ Θf1) β1d).
        { apply a_flex_tvar_cons_tvar_self.
          pose proof (dom_subset_ftvar_in_aenv Θf1) as Hd.
          clear - HβL Hd. subst Lβd. fsetdec. }
        assert (Hagr' : flex_agree_rel ((β1d, sf) :: ρ) V
                  ((β1d ~ abind_tvar) ++ Θf1) Θf2).
        { apply flex_agree_rel_extend_pair_iff.
          - apply flex_agree_rel_push_tvar_l; [ exact Hagr | ].
            clear - HβL. subst Lβd. fsetdec.
          - split; intros Hf; exfalso.
            + exact (Hnf1' Hf).
            + exact (Hnf2 Hf). }
        assert (Hb1' : forall x bd, binds x bd (@nil (atom * abind)) ->
                  binds x bd ((β1d ~ abind_tvar) ++ Θf1))
          by (intros x bd Hxb; inversion Hxb).
        assert (Hop1' : forall x, x `in` S1' -> x `notin` add β1d Sa0 ->
                  x `notin` dom (@nil (atom * abind)) ->
                  ~ a_flex_tvar ((β1d ~ abind_tvar) ++ Θf1) x).
        { intros x Hx1 Hx2 Hx3.
          assert (Hne : x <> β1d) by (clear - Hx2; fsetdec).
          rewrite (a_flex_tvar_cons_tvar_other Θf1 Hne).
          apply Hop1;
            [ clear - Hx1 Hx2 HS1'; fsetdec
            | clear - Hx2; fsetdec | simpl; auto ]. }
        assert (Henr1' : S1' ∖ (add β1d Sa0)
                  [<=] ftvar_in_aenv ((β1d ~ abind_tvar) ++ Θf1))
          by (simpl; clear - Henr1 HS1'; fsetdec).
        assert (Hscp1' : V ∪ cols_l ((β1d, sf) :: ρ) ∪ ftvar_in_pskl acc1
                  ∪ ftvar_in_a_cstrs
                      (a_cstr_sub mode_tc
                         (open_pskl_wrt_pskl B1 (pskl_var_f β1d)) :: nil)
                  [<=] ftvar_in_aenv ((β1d ~ abind_tvar) ++ Θf1)).
        { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B1
                        (pskl_var_f β1d)) as Hup.
          simpl in Hscp1, Hup |- *. clear - Hscp1 Hup. fsetdec. }
        pose proof (IHn (add β1d Sa0) S1' _ _ _ _ _ _ _ Hsz' E1r
                      _ _ _ _ _ _ _ (exist _ r1 Hr1) Er
                      ((β1d, sf) :: ρ) _ _ _ _ _ _ _ L
                      Hrs' Hrt'
                      HαV Hαl' Hαr' Hfold' Hrelacc' Hagr'
                      Hb1' Hb2 Hop1' Hop2' Henr1' Henr2' Hscp1' Hscp2'
                      Hcov1x Hcov2x) as HREC.
        destruct HREC as (Ξs2 & Q2c & Hf2' & Hu & HL).
        exists Ξs2, Q2c.
        split; [ exact Hf2' | ]. split; [ exact Hu | exact HL ]. }
        { (* gf FALSE — UnivGhostL on both sides *)
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
          intros Hs. inversion Hs; subst s; clear Hs.
          simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
          clear E1.
          match goal with
          | Hr1x : looksub_spec _ _ _ _ _ _ ?r |- _ =>
              eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
          end; try eassumption.
          all: try solve [ simpl in Hsz |- *; lia
                         | clear - Hcov1; simpl in *; fsetdec
                         | clear - Hcov2; simpl in *; fsetdec ]. }
      * (* FN — the catch-all *)
        revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      clear E1.
      match goal with
      | Hr1x : looksub_spec _ _ _ _ _ _ ?r |- _ =>
          eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
      end; try eassumption.
      all: try solve [ simpl in Hsz |- *; lia
                     | clear - Hcov1; simpl in *; fsetdec
                     | clear - Hcov2; simpl in *; fsetdec ].
    + (* ◇ target — the spec collapse *)
      destruct s as [r Hr]. simpl in *.
      destruct (e_looksub_hole_target Hr) as [EΞ2 EC2].
      destruct EC2 as [ -> | -> ].
      * exists (@nil (atom * abind)). eexists.
        split; [ apply a_solve_cstr__empty | ].
        split; [ auto | simpl; clear; fsetdec ].
      * exists (@nil (atom * abind)). eexists.
        split; [ apply a_solve_cstr__sub; apply a_solve_sub__vacuous | ].
        split; [ auto | simpl; clear; fsetdec ].
    + (* ⫯ target *)
      revert Hs. simp e_looksub_impl.
      match goal with
      | |- context [ match sumbool_of_bool ?scr with _ => _ end ] =>
          let Hmt := fresh "Hmt" in let Hmf := fresh "Hmf" in
          destruct (sumbool_of_bool scr) as [Hmt | Hmf];
          [ | exfalso; apply mem_false_notin in Hmf;
              simpl in HαP2, Hmf; clear - HαP2 Hmf; fsetdec ]
      end.
      match goal with
      | |- context [ match ?call with Some _ => _ | None => _ end = Some _ -> _ ] =>
          let r1 := fresh "r1" in let Hr1 := fresh "Hr1" in
          let Er := fresh "Er" in
          destruct call as [ [r1 Hr1] | ] eqn:Er;
          [ | intros Hs; discriminate ]
      end.
      intros Hs. inversion Hs; subst s; clear Hs.
      simpl in Hb2, Hop2, Henr2, Hscp2 |- *.
      clear E1.
      match goal with
      | Hr1x : looksub_spec _ _ _ _ _ _ ?r |- _ =>
          eapply (IHn Sa0 Sa1) with (s := exist _ r Hr1x)
      end; try eassumption.
      all: try solve [ simpl in Hsz |- *; lia
                     | clear - Hcov1; simpl in *; fsetdec
                     | clear - Hcov2; simpl in *; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §4  The §6c ASSEMBLY — the extract level's run-completeness           *)
(*                                                                        *)
(*  The hygiene premises (both stages of an e-extract on the SAME         *)
(*  outputs as the raw derivation) are the level-above's debt — the       *)
(*  fourth-pass finding is that NEITHER can be manufactured from a raw    *)
(*  [a_extract] inversion down here (the raw fold's collection mentions   *)
(*  leaked look-openers outside every context, so no transport of it      *)
(*  exists to build).  Transport 5 supplies the look half; its fold       *)
(*  analog is the flagship's burden (handoff §8c.9, fourth pass).         *)
(* ===================================================================== *)

(** Rigid enrichment: one [~ tvar] entry per atom of a finite set. *)
Definition rigids (S : atoms) : aenv :=
  List.map (fun x => (x, abind_tvar)) (AtomSetImpl.elements S).

Lemma rigids_binds_tvar : forall S x bd,
  binds x bd (rigids S) -> bd = abind_tvar.
Proof.
  intros S. unfold rigids.
  induction (AtomSetImpl.elements S) as [ | a l IH ]; intros x bd Hb.
  - inversion Hb.
  - unfold binds in Hb. simpl in Hb.
    destruct Hb as [ E | Hb ]; [ inversion E; reflexivity | ].
    apply (IH x). exact Hb.
Qed.

Lemma rigids_dom : forall S, dom (rigids S) [=] S.
Proof.
  intros S. unfold rigids.
  intros x. split.
  - intros Hx.
    assert (Hin : In x (AtomSetImpl.elements S)).
    { induction (AtomSetImpl.elements S) as [ | a l IH ]; simpl in *.
      - exfalso. clear - Hx. fsetdec.
      - destruct (x == a) as [ -> | Hne ]; [ auto | ].
        right. apply IH. clear - Hx Hne. fsetdec. }
    apply AtomSetImpl.elements_2.
    apply CoqListFacts.InA_iff_In. exact Hin.
  - intros Hx.
    apply AtomSetImpl.elements_1 in Hx.
    apply CoqListFacts.InA_iff_In in Hx.
    induction (AtomSetImpl.elements S) as [ | a l IH ]; simpl in *.
    + inversion Hx.
    + destruct Hx as [ -> | Hx ]; [ fsetdec | ].
      pose proof (IH Hx). fsetdec.
Qed.

Lemma map_tvar_ftvar_dom : forall (l : list atom),
  ftvar_in_aenv (List.map (fun x => (x, abind_tvar)) l)
  [=] dom (List.map (fun x => (x, abind_tvar)) l).
Proof.
  induction l as [ | a l IH ]; simpl.
  - clear. fsetdec.
  - rewrite IH. clear. fsetdec.
Qed.

Lemma rigids_ftvar : forall S, ftvar_in_aenv (rigids S) [=] S.
Proof.
  intros S. unfold rigids.
  rewrite map_tvar_ftvar_dom.
  exact (rigids_dom S).
Qed.

(** ⚠️ THE STAGE-KILL IDIOM IS LOAD-BEARING FOR SPEED (measured
    2026-08-16): matching the goal's nested [match ?call with Some …]
    and destructing the captured scrutinee HANGS (>200 s, killed) —
    [context] can select an inner stage whose type depends on an
    outer, not-yet-introduced result.  Matching the APPLICATION with
    its argument metavariables, asserting [<> None] first and then
    destructing that exact application — prop_run_complete.v §5c's
    [kill_*] recipe — runs in 0.05 s. *)
Lemma e_extract_impl_complete : forall S0 Θ0 NM α m P P'
    (HP : lc_pskl P) (HP' : lc_pskl P')
    (H : e_extract_order S0 Θ0 NM α m P P')
    Ξl 𝒞l Ξs1 Q1 Sh0 Sh1 Sf1,
  {{ Sh0 ↝ Sh1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξl ⨾ 𝒞l }}e ->
  {{ Sh1 ↝ Sf1 ⊨ (Ξl ++ Θ0) ⊩ 𝒞l ⨾ pskl_hole ⤳ Ξs1 ⨾ Q1 }}e ->
  add α (ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] ftvar_in_aenv Θ0 ->
  add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] Sh0 ->
  add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  e_extract_impl S0 Θ0 NM α m P P' HP HP' H <> None.
Proof.
  intros * Hhl Hhf Hscp0 HcovH Hcov0.
  simp e_extract_impl.
  (* ---- stage 1: the runner's look answers (level 1) ---- *)
  pose proof ((proj1 e_looksub_lookeq_sound) _ _ _ _ _ _ _ _ _ Hhl
                ltac:(clear - HcovH; fsetdec)) as Hlookraw.
  match goal with
  | |- context [ e_looksub_impl ?S ?T ?a ?mm ?p ?q ?hp ?hq ?h ] =>
      let Hne := fresh "Hne" in let Hcl := fresh "Hcl" in
      assert (Hne : e_looksub_impl S T a mm p q hp hq h <> None)
        by (exact (e_looksub_impl_complete hp hq h Hlookraw
                     ltac:(clear - Hcov0; fsetdec)));
      destruct (e_looksub_impl S T a mm p q hp hq h) as [ [r1 Hr1] | ] eqn:Hcl;
      [ cbv beta iota | exact (False_ind _ (Hne eq_refl)) ]
  end.
  unfold looksub_spec in Hr1.
  (* ---- the two sides' supply/block facts ---- *)
  pose proof (e_looksub_supply_grows Hhl) as HgrH.
  pose proof (e_looksub_supply_grows Hr1) as Hgr1.
  pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hhl)
    as (Hbl1a & Hbl1b & Hbu1 & Hbf1).
  pose proof ((proj1 e_looksub_lookeq_block) _ _ _ _ _ _ _ _ _ Hr1)
    as (Hbl2a & Hbl2b & Hbu2 & Hbf2).
  pose proof ((proj1 e_looksub_lookeq_cstr_ftvar_tight)
                _ _ _ _ _ _ _ _ _ Hhl) as Htight1.
  pose proof ((proj1 e_looksub_lookeq_cstr_ftvar_tight)
                _ _ _ _ _ _ _ _ _ Hr1) as Htight2.
  pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
  (* ---- the RIGID ENRICHMENT (§8c.9 decision (a), fourth-pass form):
     each side's whole generated interval, so the b-core's scoping
     premises hold of the leaked openers the collections mention ---- *)
  set (Δr1 := rigids (Sh1 ∖ Sh0)) in *.
  set (Δr2 := rigids (lk_supply r1 ∖ S0)) in *.
  set (Θf1 := Δr1 ++ Ξl ++ Θ0) in *.
  set (Θf2 := Δr2 ++ lk_block r1 ++ Θ0) in *.
  assert (Hr1d : dom Δr1 [=] Sh1 ∖ Sh0) by apply rigids_dom.
  assert (Hr2d : dom Δr2 [=] lk_supply r1 ∖ S0) by apply rigids_dom.
  assert (Hr1f : ftvar_in_aenv Δr1 [=] Sh1 ∖ Sh0) by apply rigids_ftvar.
  assert (Hr2f : ftvar_in_aenv Δr2 [=] lk_supply r1 ∖ S0)
    by apply rigids_ftvar.
  assert (Hrig1 : forall x bd, binds x bd Δr1 -> bd = abind_tvar)
    by (intros x bd Hb; eapply rigids_binds_tvar; exact Hb).
  assert (Hrig2 : forall x bd, binds x bd Δr2 -> bd = abind_tvar)
    by (intros x bd Hb; eapply rigids_binds_tvar; exact Hb).
  (* the HYGIENIC fold rigid-weakens to the enriched context (its
     freshness reads the supply), then projects to the a-side fold *)
  assert (Hcovf : ftvar_in_aenv Θf1 ∪ ftvar_in_a_cstrs 𝒞l
            ∪ ftvar_in_pskl pskl_hole [<=] Sh1).
  { unfold Θf1. rewrite ! ftvar_in_aenv_app. rewrite Hr1f. simpl.
    assert (Hx : ftvar_in_aenv Ξl [<=] Sh1) by (clear - Hbl1a Hbf1; fsetdec).
    assert (Hy : ftvar_in_a_cstrs 𝒞l [<=] Sh1)
      by (clear - Htight1 HcovH HgrH; fsetdec).
    assert (Hz : ftvar_in_aenv Θ0 [<=] Sh1) by (clear - HcovH HgrH; fsetdec).
    clear - Hx Hy Hz. fsetdec. }
  assert (Hfold1 : {{ Θf1 ⊩ 𝒞l ⨾ pskl_hole ⤳ Ξs1 ⨾ Q1 }}a).
  { eapply e_solve_cstr_sound; [ | exact Hcovf ].
    unfold Θf1. apply e_solve_cstr_weaken_rigid; [ exact Hhf | exact Hrig1 ]. }
  (* ---- the b-core: the runner-side fold ---- *)
  set (V := add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P')) in *.
  assert (HVΘ : V [<=] ftvar_in_aenv Θ0) by (unfold V; clear - Hscp0; fsetdec).
  assert (HrelP : rel_pskl nil V P P)
    by (apply rel_pskl_refl; unfold V; clear; fsetdec).
  assert (HrelP' : rel_pskl nil V P' P')
    by (apply rel_pskl_refl; unfold V; clear; fsetdec).
  assert (Hagr : flex_agree_rel nil V Θf1 Θf2).
  { split; [ | intros a b Hin; inversion Hin ].
    intros x Hx.
    assert (Hx1 : x `notin` dom Δr1)
      by (rewrite Hr1d; clear - Hx HVΘ HcovH; fsetdec).
    assert (Hx2 : x `notin` dom Δr2)
      by (rewrite Hr2d; clear - Hx HVΘ Hcov0; fsetdec).
    assert (Hx3 : x `notin` dom Ξl)
      by (clear - Hx HVΘ Hbl1b HcovH; fsetdec).
    assert (Hx4 : x `notin` dom (lk_block r1))
      by (clear - Hx HVΘ Hbl2b Hcov0; fsetdec).
    unfold Θf1, Θf2.
    rewrite (a_flex_tvar_notin_app Δr1 (Ξl ++ Θ0) Hx1).
    rewrite (a_flex_tvar_notin_app Δr2 (lk_block r1 ++ Θ0) Hx2).
    rewrite (a_flex_tvar_notin_app Ξl Θ0 Hx3).
    rewrite (a_flex_tvar_notin_app (lk_block r1) Θ0 Hx4).
    reflexivity. }
  assert (Hb1 : forall x bd, binds x bd Ξl -> binds x bd Θf1)
    by (intros x bd Hxb; unfold Θf1; unfold binds in *;
        apply in_or_app; right; apply in_or_app; left; exact Hxb).
  assert (Hb2 : forall x bd, binds x bd (lk_block r1) -> binds x bd Θf2)
    by (intros x bd Hxb; unfold Θf2; unfold binds in *;
        apply in_or_app; right; apply in_or_app; left; exact Hxb).
  assert (Hop1 : forall x, x `in` Sh1 -> x `notin` Sh0 ->
            x `notin` dom Ξl -> ~ a_flex_tvar Θf1 x).
  { intros x h1 h2 h3 Hf. unfold Θf1 in Hf.
    apply (proj1 (a_flex_tvar_app_or Δr1 (Ξl ++ Θ0) x)) in Hf.
    destruct Hf as [ Hf | Hf ].
    - destruct Hf as [ Hb | [τ Hb] ];
        pose proof (Hrig1 _ _ Hb); discriminate.
    - apply (proj1 (a_flex_tvar_app_or Ξl Θ0 x)) in Hf.
      destruct Hf as [ Hf | Hf ].
      + apply h3. eapply a_flex_tvar_dom. exact Hf.
      + assert (Hxd : x `in` dom Θ0) by (eapply a_flex_tvar_dom; exact Hf).
        clear - h2 HcovH Hd0 Hxd. fsetdec. }
  assert (Hop2 : forall x, x `in` lk_supply r1 -> x `notin` S0 ->
            x `notin` dom (lk_block r1) -> ~ a_flex_tvar Θf2 x).
  { intros x h1 h2 h3 Hf. unfold Θf2 in Hf.
    apply (proj1 (a_flex_tvar_app_or Δr2 (lk_block r1 ++ Θ0) x)) in Hf.
    destruct Hf as [ Hf | Hf ].
    - destruct Hf as [ Hb | [τ Hb] ];
        pose proof (Hrig2 _ _ Hb); discriminate.
    - apply (proj1 (a_flex_tvar_app_or (lk_block r1) Θ0 x)) in Hf.
      destruct Hf as [ Hf | Hf ].
      + apply h3. eapply a_flex_tvar_dom. exact Hf.
      + assert (Hxd : x `in` dom Θ0) by (eapply a_flex_tvar_dom; exact Hf).
        clear - h2 Hcov0 Hd0 Hxd. fsetdec. }
  assert (Henr1 : Sh1 ∖ Sh0 [<=] ftvar_in_aenv Θf1)
    by (unfold Θf1; rewrite ! ftvar_in_aenv_app; rewrite Hr1f;
        clear; fsetdec).
  assert (Henr2 : lk_supply r1 ∖ S0 [<=] ftvar_in_aenv Θf2)
    by (unfold Θf2; rewrite ! ftvar_in_aenv_app; rewrite Hr2f;
        clear; fsetdec).
  assert (Hscp1 : V ∪ cols_l nil ∪ ftvar_in_pskl pskl_hole
            ∪ ftvar_in_a_cstrs 𝒞l [<=] ftvar_in_aenv Θf1).
  { unfold Θf1. rewrite ! ftvar_in_aenv_app. rewrite Hr1f. simpl.
    clear - Htight1 HVΘ. fsetdec. }
  assert (Hscp2 : V ∪ cols_r nil ∪ ftvar_in_pskl pskl_hole
            ∪ ftvar_in_a_cstrs (lk_cstrs r1) [<=] ftvar_in_aenv Θf2).
  { unfold Θf2. rewrite ! ftvar_in_aenv_app. rewrite Hr2f. simpl.
    clear - Htight2 HVΘ. fsetdec. }
  pose proof (@bcore_sub (S (size_pskl P + size_pskl P'))
                Sh0 Sh1 _ _ _ P P' _ _ ltac:(lia) Hhl
                _ _ _ _ _ _ _ (exist _ r1 Hr1) Hcl
                nil _ _ _ _ _ _ _ empty
                HrelP HrelP'
                ltac:(unfold V; clear; fsetdec)
                ltac:(simpl; clear; fsetdec)
                ltac:(simpl; clear; fsetdec)
                Hfold1 (rel_pskl__hole nil V) Hagr
                Hb1 Hb2 Hop1 Hop2 Henr1 Henr2 Hscp1 Hscp2
                ltac:(clear - HcovH HVΘ; unfold V; fsetdec)
                ltac:(clear - Hcov0 HVΘ; unfold V; fsetdec)) as HB.
  destruct HB as (Ξs2 & Q2 & Hfold2 & Hu2 & _).
  simpl in Hfold2.
  (* ---- stage 2: the runner's fold answers (level 3) ---- *)
  assert (Hagr2 : flex_agree
            (ftvar_in_pskl pskl_hole ∪ ftvar_in_a_cstrs (lk_cstrs r1))
            Θf2 (lk_block r1 ++ Θ0)).
  { intros x _. unfold Θf2.
    apply a_flex_tvar_rigid_prefix_iff. exact Hrig2. }
  assert (Hscpf : ftvar_in_pskl pskl_hole ∪ ftvar_in_a_cstrs (lk_cstrs r1)
            [<=] ftvar_in_aenv Θf2)
    by (clear - Hscp2; simpl in *; fsetdec).
  assert (Hcovf2 : ftvar_in_aenv (lk_block r1 ++ Θ0)
            ∪ ftvar_in_pskl pskl_hole ∪ ftvar_in_a_cstrs (lk_cstrs r1)
            [<=] lk_supply r1).
  { rewrite ftvar_in_aenv_app. simpl.
    assert (Hx : ftvar_in_aenv (lk_block r1) [<=] lk_supply r1)
      by (clear - Hbl2a Hbf2; fsetdec).
    assert (Hy : ftvar_in_a_cstrs (lk_cstrs r1) [<=] lk_supply r1)
      by (clear - Htight2 Hcov0 Hgr1; fsetdec).
    assert (Hz : ftvar_in_aenv Θ0 [<=] lk_supply r1)
      by (clear - Hcov0 Hgr1; fsetdec).
    clear - Hx Hy Hz. fsetdec. }
  match goal with
  | |- context [ e_solve_cstr_impl ?S ?T ?c ?pp ?hp ?hc ?h ] =>
      let Hne := fresh "Hne" in let Hcl2 := fresh "Hcl2" in
      assert (Hne : e_solve_cstr_impl S T c pp hp hc h <> None)
        by (exact (e_solve_cstr_impl_complete hp hc h Hfold2 Hu2
                     Hagr2 Hscpf Hcovf2));
      destruct (e_solve_cstr_impl S T c pp hp hc h) as [ [r2 Hr2] | ] eqn:Hcl2;
      [ cbv beta iota | exact (False_ind _ (Hne eq_refl)) ]
  end.
  (* ---- stage 3 (the guess) is TOTAL ---- *)
  discriminate.
Qed.

(** ⭐ THE EXTRACT LEVEL'S HEADLINE (campaign §8c.3 level 4): a raw
    [a_extract]'s two stages, given e-DERIVABLY (the hygiene premises
    the level above owes — see the file header and §8c.9's fourth
    pass), make the EXTRACTED runner succeed. *)
Lemma e_extract_run_complete : forall S0 Θ0 NM α m P P' HP HP'
    Ξl 𝒞l Ξs1 Q1 Sh0 Sh1 Sf1,
  {{ Sh0 ↝ Sh1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξl ⨾ 𝒞l }}e ->
  {{ Sh1 ↝ Sf1 ⊨ (Ξl ++ Θ0) ⊩ 𝒞l ⨾ pskl_hole ⤳ Ξs1 ⨾ Q1 }}e ->
  add α (ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] ftvar_in_aenv Θ0 ->
  add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] Sh0 ->
  add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  e_extract_run S0 Θ0 NM α m P P' HP HP' <> None.
Proof.
  intros * Hhl Hhf Hscp0 HcovH Hcov0. unfold e_extract_run.
  pose proof (e_extract_impl_complete HP HP'
                (@e_extract_order_total S0 Θ0 NM α m P P' HP HP')
                Hhl Hhf Hscp0 HcovH Hcov0) as Hne.
  revert Hne.
  destruct (e_extract_impl S0 Θ0 NM α m P P' HP HP'
              (@e_extract_order_total S0 Θ0 NM α m P P' HP HP'))
    as [ [r Hr] | ]; intros Hne.
  - discriminate.
  - exact (False_ind _ (Hne eq_refl)).
Qed.
