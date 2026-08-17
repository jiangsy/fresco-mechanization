(** THE EXTRACT LEVEL'S FOUNDATIONS — structure facts about the look
    judgements' collections and the fold, feeding §8c.9's b-core (the
    fused look-pair/fold-transport lemma; docs/
    HANDOFF-extractable-algo-encoding.md §8c.9).

    The collection is NOT deterministic up to renaming
    (cex/cex_looksub_not_det.v), but two derivations of the same look
    node differ ONLY by fresh names, by the ∀-peel slack at the final
    sub-constraint, and by ◇-EMISSION slack ([≼m ◇] / [eq ◇] vs
    nothing) — and a ◇-target solve step is the IDENTITY, which is what
    makes the slack free to transport.  This file proves that
    inventory's foundation facts:

    §1  a lookeq collection is PURE-EQ (so LS-Arrow's left half never
        contributes a sub-constraint, and the fold of [𝒞1 ++ 𝒞2]
        decomposes at the seam);
    §2  an α-FREE subject collects NOTHING, through EVERY derivation
        (crossing 4 of §8c.9's inventory: LS/LE-Absent vs a structural
        derivation is no slack at all);
    §3  a ◇-TARGET solve step is the identity — nil block, pattern
        through — on both layers (crossing 3: the ◇-emission slack);
    §4  the fold's head inversions and the PURE-EQ APPEND DECOMPOSITION
        [a_solve_cstr_app_inv], the mirror of [a_solve_cstr_app]
        (algo/sub/look/prop_eq_cstr.v) that the b-core's Arrow case
        splits the given fold with.  ⚙ [a_solve_cstr_sub_inv] /
        [a_solve_cstr_eq_inv] MOVED here from prop_run_complete.v §5
        (2026-08-16, one fact one name one file — this file sits below
        the runner-completeness stack, which now imports it);
    §5  a ◇-TARGET look collapses to at most one trivial constraint,
        through EVERY derivation (crossing 3's look half);
    §6  the COLLECTION-PRESERVING re-rootings R′/R″ — a subject peel
        moves to the root with [(Ξ, 𝒞)] EXACTLY preserved, so they
        apply to EITHER side of the b-core pair (even the pinned one)
        and any fold rides for free. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_tag.
Require Import src.frost.def_shapes.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.sub.prop_looksub.

(* the ∀-quantified inputs are inferable from the derivation arguments, so
   applications read [lemma Hd Habs] — the §8c.6 note on implicit result
   args applies to this file's consumers *)
Set Implicit Arguments.

Open Scope frost_a_scope.

(* ===================================================================== *)
(*  §1  A lookeq collection is pure-eq                                    *)
(* ===================================================================== *)

Definition a_cstr_is_eq (c : a_cstr) : Prop := exists Q, c = a_cstr_eq Q.

Lemma a_lookeq_cstrs_pure_eq : forall Θ α P P' Ξ C,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
  Forall a_cstr_is_eq C.
Proof.
  intros * H.
  induction H; try solve [ constructor ]; auto.
  - (* LE-Var *)
    constructor; [ exists P; reflexivity | constructor ].
  - (* LE-FlexR *)
    constructor; [ eexists; reflexivity | constructor ].
  - (* LE-Arrow *)
    apply Forall_app; split; assumption.
Qed.

(* ===================================================================== *)
(*  §2  An α-free subject collects nothing                                *)
(* ===================================================================== *)

(** The only EMITTING rules — LS/LE-Var, LE-FlexR — need an α-occurrence
    in the subject, and every ∀-opener is fresh from α, so absence is an
    invariant of the whole subtree: EVERY derivation at an α-free
    subject returns [nil ⨾ nil], not just the LS/LE-Absent one. *)
Lemma a_lookeq_subject_absent : forall Θ α P P' Ξ C,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
  α `notin` ftvar_in_pskl P ->
  Ξ = nil /\ C = nil.
Proof.
  intros * H.
  induction H; intros Habs; simpl in *;
    (* ⭐ WITH THE ABSENCE-FIRST GUARD the LEAKING rows are not merely
       collection-free here, they are IMPOSSIBLE: their own premise
       [α ∈ ftv <subject>] contradicts [Habs] outright.  Before the guard
       each had to be walked through its opener. *)
    try (exfalso;
         match goal with
         | Hin : α `in` ftvar_in_pskl _ |- _ => clear - Habs Hin; fsetdec
         end);
    auto.
  - (* LE-Var: subject IS α *)
    exfalso. clear - Habs. fsetdec.
  - (* LE-Arrow *)
    destruct IHa_lookeq1 as [-> ->]; [ clear - Habs; fsetdec | ].
    destruct IHa_lookeq2 as [-> ->]; [ clear - Habs; fsetdec | ].
    auto.
Qed.

Lemma a_looksub_subject_absent : forall Θ α m P P' Ξ C,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  α `notin` ftvar_in_pskl P ->
  Ξ = nil /\ C = nil.
Proof.
  intros * H.
  induction H; intros Habs; simpl in *;
    try (exfalso;
         match goal with
         | Hin : α `in` ftvar_in_pskl _ |- _ => clear - Habs Hin; fsetdec
         end);
    auto.
  - (* LS-Var: subject IS α *)
    exfalso. clear - Habs. fsetdec.
  - (* LS-Check: drops into the eq layer *)
    match goal with
    | He : a_lookeq _ _ _ _ _ _ |- _ =>
        eapply a_lookeq_subject_absent; [ exact He | exact Habs ]
    end.
  - (* LS-Arrow *)
    match goal with
    | He : a_lookeq _ _ ?A _ _ _ |- _ =>
        assert (Habs1 : α `notin` ftvar_in_pskl A)
          by (clear - Habs; fsetdec);
        destruct (a_lookeq_subject_absent He Habs1) as [-> ->]
    end.
    destruct IHa_looksub as [-> ->]; [ clear - Habs; fsetdec | ].
    auto.
Qed.

(* ===================================================================== *)
(*  §3  A ◇-target solve step is the identity                             *)
(* ===================================================================== *)

(** Crossing 3's engine: the slack constraints ([eq ◇] and [≼m ◇]) cost
    the fold NOTHING — the pattern passes through and no names are
    generated — so the side that emitted them and the side that did not
    fold to the SAME state.  (The BUILD direction is one constructor,
    SE-VacuousR / SS-Vacuous; these are the INVERSIONS.) *)
Lemma a_solve_eq_hole_target_inv : forall Θ P Ξ P',
  {{ Θ ⊢ₑ P ∼ pskl_hole ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = P.
Proof.
  intros * H.
  inversion H; subst; auto.
  (* SE-GhostGuarded: guarded ◇ has no constructor *)
  match goal with
  | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
  end.
Qed.

Lemma a_solve_sub_hole_target_inv : forall Θ m P Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] pskl_hole ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = P.
Proof.
  intros Θ m P Ξ P' H.
  remember pskl_hole as T eqn:HT.
  induction H; inversion HT; subst.
  - (* SS-Var *) auto.
  - (* SS-ForallL: the yield re-closes to the subject *)
    destruct IHa_solve_sub as [-> ->]; [ reflexivity | ].
    split; [ reflexivity | ].
    rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
      [ reflexivity | clear - H; fsetdec ].
  - (* SS-UnivGhostL *)
    destruct IHa_solve_sub as [-> ->]; [ reflexivity | ]. auto.
  - (* SS-Vacuous *) auto.
  - (* SS-Check: guarded ◇ has no constructor *)
    match goal with
    | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
    end.
  - (* SS-GhostL at B = ◇: ghost-free ◇ has no constructor *)
    match goal with
    | Hg : pskl_ghost_free pskl_hole |- _ => inversion Hg
    end.
Qed.

(* ===================================================================== *)
(*  §4  The fold's head inversions and the pure-eq append decomposition   *)
(* ===================================================================== *)

(** ⚙ Moved from prop_run_complete.v §5 (2026-08-16) — see the header. *)
Lemma a_solve_cstr_sub_inv : forall Θ m Q C P Ξ P',
  {{ Θ ⊩ (a_cstr_sub m Q :: C) ⨾ P ⤳ Ξ ⨾ P' }}a ->
  C = nil /\ {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a.
Proof.
  intros * Hd. inversion Hd; subst. split; [ reflexivity | assumption ].
Qed.

Lemma a_solve_cstr_eq_inv : forall Θ Q C P Ξ P',
  {{ Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ Ξ ⨾ P' }}a ->
  exists Ξ1 Ξ2 P'',
    Ξ = Ξ2 ++ Ξ1
    /\ {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}a
    /\ {{ (Ξ1 ++ Θ) ⊩ C ⨾ P'' ⤳ Ξ2 ⨾ P' }}a.
Proof.
  intros * Hd. inversion Hd; subst.
  match goal with
  | Hh : a_solve_eq _ _ _ ?X1 ?Pm, Ht : a_solve_cstr _ _ _ ?X2 _ |- _ =>
      exists X1, X2, Pm
  end.
  repeat split; assumption.
Qed.

(** The mirror of [a_solve_cstr_app] (algo/sub/look/prop_eq_cstr.v:155):
    a fold across a pure-eq prefix SPLITS at the seam.  The b-core's
    Arrow case decomposes the derivation-side fold with this, hands the
    halves to the two IHs, and recomposes the runner side with the
    original. *)
Lemma a_solve_cstr_app_inv : forall C1 Θ 𝒞2 P Ξ P',
  Forall a_cstr_is_eq C1 ->
  {{ Θ ⊩ (C1 ++ 𝒞2) ⨾ P ⤳ Ξ ⨾ P' }}a ->
  exists Ξ1 Ξ2 Pmid,
    Ξ = Ξ2 ++ Ξ1
    /\ {{ Θ ⊩ C1 ⨾ P ⤳ Ξ1 ⨾ Pmid }}a
    /\ {{ (Ξ1 ++ Θ) ⊩ 𝒞2 ⨾ Pmid ⤳ Ξ2 ⨾ P' }}a.
Proof.
  induction C1 as [ | c C1' IH ]; intros Θ 𝒞2 P Ξ P' Hall Hd.
  - exists nil, Ξ, P.
    split; [ rewrite app_nil_r; reflexivity | ].
    split; [ apply a_solve_cstr__empty | ].
    simpl. exact Hd.
  - inversion Hall as [ | ? ? [Q ->] Hall' ]; subst.
    simpl in Hd.
    apply a_solve_cstr_eq_inv in Hd
      as (Ξa & Ξb & Pmid0 & -> & Hhead & Htail).
    apply IH in Htail as (Ξ1' & Ξ2 & Pmid & -> & Hpre & Hpost);
      [ | exact Hall' ].
    exists (Ξ1' ++ Ξa), Ξ2, Pmid.
    split;
      [ solve [ apply app_assoc | symmetry; apply app_assoc ] | ].
    split.
    + eapply a_solve_cstr__eq; [ exact Hhead | exact Hpre ].
    + replace ((Ξ1' ++ Ξa) ++ Θ) with (Ξ1' ++ (Ξa ++ Θ))
        by (solve [ apply app_assoc | symmetry; apply app_assoc ]).
      exact Hpost.
Qed.

(* ===================================================================== *)
(*  §5  A ◇-target look collapses to at most one trivial constraint       *)
(* ===================================================================== *)

(** Crossing 3's other half: at a ◇ target the only reachable rules are
    Var/Absent/Vacuous (plus subject-peels on the sub layer), so EVERY
    derivation returns [nil] or the single trivial constraint — whose
    solve step is the §3 identity.  With §2 this prunes the pair
    induction to subjects containing α and non-◇ targets. *)
Lemma a_lookeq_hole_target : forall Θ α P Ξ C,
  {{ Θ ⊢ P ∼[ α ] pskl_hole ⤳ Ξ ⨾ C }}a ->
  Ξ = nil /\ (C = nil \/ C = a_cstr_eq pskl_hole :: nil).
Proof.
  intros * H.
  inversion H; subst; auto.
  match goal with
  | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
  end.
Qed.

Lemma a_looksub_hole_target : forall Θ α m P Ξ C,
  {{ Θ ⊢ P ≼[ α , m ] pskl_hole ⤳ Ξ ⨾ C }}a ->
  Ξ = nil /\ (C = nil \/ C = a_cstr_sub m pskl_hole :: nil).
Proof.
  intros Θ α m P Ξ C H.
  remember pskl_hole as T eqn:HT.
  induction H; inversion HT; subst.
  - (* LS-Var *) split; [ reflexivity | right; reflexivity ].
  - (* LS-Absent *) auto.
  - (* LS-Vacuous *) auto.
  - (* LS-Check: guarded ◇ has no constructor *)
    match goal with
    | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
    end.
  - (* LS-ForallL *) apply IHa_looksub. reflexivity.
  - (* LS-UnivGhostL *) apply IHa_looksub. reflexivity.
Qed.

(* ===================================================================== *)
(*  §6  The COLLECTION-PRESERVING re-rootings (§8c.9's R′/R″)             *)
(*                                                                        *)
(*  A constraint list is built from TARGET material and generated names   *)
(*  alone — the subject never enters it — so re-rooting a SUBJECT-peel    *)
(*  to the front preserves (Ξ, 𝒞) EXACTLY, and any fold on 𝒞 rides for   *)
(*  free.  These are what let the b-core pair induction descend the       *)
(*  subject on whichever side is ForallR-rooted: apply R′/R″ to THAT      *)
(*  side (either one — the outputs are pinned), then recurse aligned.     *)
(*  The only output-CHANGING re-rooting is the target peel at a Var       *)
(*  root, and there the fold pays by [a_solve_sub_peel_forall_r]          *)
(*  (prop_run_complete.v §6a).                                            *)
(* ===================================================================== *)

(** R″ — strip a ⫯ subject to the front.  No freshness owed at all. *)
Lemma a_looksub_strip_tophole_l : forall Θ α m P0 P' Ξ C,
  (* ⚠️ [P' ≠ ◇] IS LOAD-BEARING under the ◇-dispatch guard, and the
     unconditional form is FALSE: at [⫯α ≼[α,m] ◇] the ⫯ subject answers by
     LS-Vacuous with [𝒞 = ·], while the STRIPPED subject [α] is an LS-Var
     node and answers [𝒞 = [≼m ◇]].  The runner agrees — it dispatches on
     the subject, so it takes Vacuous at [⫯] and Var at [α]. *)
  P' <> pskl_hole ->
  P0 <> pskl_var_f α ->
  {{ Θ ⊢ (pskl_tophole P0) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ P0 ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α m P0 P' Ξ C Hnh Hnv H.
  remember (pskl_tophole P0) as S eqn:HS.
  revert P0 Hnv HS.
  induction H; intros P0' Hnv HS; inversion HS; subst.
  - (* LS-Absent *)
    apply a_looksub__absent. simpl in *. assumption.
  - (* LS-Vacuous — impossible: the counterpart is ◇ *)
    exfalso. apply Hnh. reflexivity.
  - (* LS-Check: a ⫯ subject is not guarded *)
    match goal with
    | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
    end.
  - (* LS-ForallR *)
    apply a_looksub__forall_r with (β := β);
      [ assumption | simpl in *; assumption
      | (* the guard on [⫯P0] IS the guard on [P0] *) simpl in *; assumption
      | (* ⚠️ NOT derivable from the row's own [⫯P0 ≠ α], which is vacuous —
           this is the lemma's second side condition *) exact Hnv
      | ].
    apply IHa_looksub;
      [ apply ghost_free_open_var_neq_hole; exact H
      | exact Hnv | reflexivity ].
  - (* LS-UnivGhostL *)
    assumption.
Qed.

(** R′ — open a ∀ subject at the front, at ANY name fresh for the node's
    data AND its outputs.  The size induction is on the TARGET alone:
    only LS-ForallR recurses, and it peels the target; LS-ForallL's own
    premise IS the goal at the derivation's opener, rebound by one swap
    (its opener avoids the outputs — [a_looksub_lookeq_generated_fresh]
    for the block, the disjunctive [a_looksub_lookeq_ftv] for the
    collection). *)
Lemma a_looksub_open_forall_l_first_n : forall n Θ α m P0 P' Ξ C γ,
  (* ⚠️ [P' ≠ ◇] under the ◇-dispatch guard, and the unconditional form is
     FALSE: at [∀_. α ≼[α,m] ◇] the ∀ subject answers by LS-Vacuous, while
     its OPENED body [α] is an LS-Var node. *)
  P' <> pskl_hole ->
  P0 <> pskl_var_f α ->
  size_pskl P' < n ->
  {{ Θ ⊢ (pskl_all_syn P0) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  γ `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P'
      ∪ ftvar_in_aenv Ξ ∪ ftvar_in_cstrs C) ->
  {{ ((γ ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P0 (pskl_var_f γ))
      ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a.
Proof.
  induction n as [ | n IH ]; intros Θ α m P0 P' Ξ C γ Hnh Hnv Hsz Hd Hγ;
    [ exfalso; clear - Hsz; lia | ].
  inversion Hd; subst.
  - (* LS-Absent *)
    apply a_looksub__absent.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f γ))
      as Hup.
    match goal with
    | Ha : α `notin` ftvar_in_pskl (pskl_all_syn _) |- _ =>
        clear - Ha Hγ Hup; simpl in *; fsetdec
    end.
  - (* LS-Vacuous — impossible: the counterpart is ◇ *)
    exfalso. apply Hnh. reflexivity.
  - (* LS-Check *)
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  - (* LS-ForallR: recurse below, exchange, rebuild, rebind *)
    match goal with
    | Hfr : ?b `notin` add α _ ,
      Hp : a_looksub ((?b ~ abind_tvar) ++ _) _ _ (pskl_all_syn _) _ _ _ |- _ =>
        rename Hfr into Hβ1; rename Hp into Hprem; rename b into β1
    end.
    destruct (atom_fresh (add α (add β1 (add γ
                (ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl B
                 ∪ ftvar_in_aenv Ξ ∪ ftvar_in_cstrs C))))) as [γ'' Hγ''].
    assert (Hszp : size_pskl (open_pskl_wrt_pskl B (pskl_var_f β1)) < n)
      by (rewrite size_pskl_open_pskl_wrt_pskl_var;
          clear - Hsz; simpl in *; lia).
    assert (Hγ''p : γ'' `notin` add α (ftvar_in_aenv ((β1 ~ abind_tvar) ++ Θ)
              ∪ ftvar_in_pskl P0
              ∪ ftvar_in_pskl (open_pskl_wrt_pskl B (pskl_var_f β1))
              ∪ ftvar_in_aenv Ξ ∪ ftvar_in_cstrs C)).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β1))
        as Hup.
      clear - Hγ'' Hup. simpl in *. fsetdec. }
    pose proof (IH _ _ _ _ _ _ _ _
                  (ghost_free_open_var_neq_hole B β1 ltac:(assumption))
                  Hnv Hszp Hprem Hγ''p) as Hih.
    apply a_looksub_ctx_exchange in Hih.
    assert (Hre : {{ ((γ'' ~ abind_tvar) ++ Θ)
        ⊢ (open_pskl_wrt_pskl P0 (pskl_var_f γ'')) ≼[ α , mode_tc ]
        (pskl_all_syn B) ⤳ Ξ ⨾ C }}a).
    { apply a_looksub__forall_r with (β := β1);
        [ assumption
        | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0
                        (pskl_var_f γ'')) as Hup;
          clear - Hβ1 Hγ'' Hup; simpl in *; fsetdec
        | (* ⭐ the absence-first guard SURVIVES THE RE-OPENING *)
          apply ftvar_in_pskl_open_keep;
          match goal with
          | Ho : α `in` ftvar_in_pskl (pskl_all_syn _) |- _ =>
              simpl in Ho; exact Ho
          end
        | (* the subject re-opens at [γ''] — [open_var_neq_var] *)
          apply open_var_neq_var; [ exact Hnv | clear - Hγ''; fsetdec ]
        | exact Hih ]. }
    destruct (γ'' == γ) as [-> | Hne]; [ exact Hre | ].
    pose proof (proj1 (a_looksub_lookeq_swap γ'' γ) _ _ _ _ _ _ _ Hre) as Hs.
    revert Hs.
    assert (Hctx : swap_aenv γ'' γ ((γ'' ~ abind_tvar) ++ Θ)
                   = (γ ~ abind_tvar) ++ Θ).
    { simpl. rewrite swap_atom_l.
      rewrite (swap_aenv_fresh_id γ'' γ Θ) by (clear - Hγ Hγ''; fsetdec).
      reflexivity. }
    rewrite Hctx.
    rewrite (swap_atom_other γ'' γ α) by (clear - Hγ Hγ''; fsetdec).
    rewrite swap_pskl_open_var.
    rewrite swap_atom_l.
    rewrite (swap_pskl_fresh_id γ'' γ P0) by (clear - Hγ Hγ''; fsetdec).
    assert (Hall : swap_pskl γ'' γ (pskl_all_syn B) = pskl_all_syn B)
      by (apply swap_pskl_fresh_id; clear - Hγ Hγ''; simpl in *; fsetdec).
    rewrite Hall.
    rewrite (swap_aenv_fresh_id γ'' γ Ξ) by (clear - Hγ Hγ''; fsetdec).
    rewrite swap_cstrs_fresh_id by (clear - Hγ Hγ''; fsetdec).
    intros Hs; exact Hs.
  - (* LS-ForallL: the premise IS the goal at its own opener; rebind *)
    match goal with
    | Hfr : ?b `notin` add α _ ,
      Hp : a_looksub ((?b ~ abind_tvar) ++ _) _ _ _ _ _ _ |- _ =>
        rename Hfr into Hγ1; rename Hp into Hprem; rename b into γ1
    end.
    (* the opener avoids the outputs: generated names dodge the context,
       and the collection's variables are target material or generated *)
    assert (Hd1 : γ1 `notin` dom Ξ).
    { eapply (proj1 a_looksub_lookeq_generated_fresh); [ exact Hprem | ].
      simpl. clear - Hγ. fsetdec. }
    assert (HΞ1 : γ1 `notin` ftvar_in_aenv Ξ).
    { pose proof (a_looksub_decls Hprem) as Hdc.
      pose proof (a_decls_no_ftvar Hdc) as Hsub.
      clear - Hd1 Hsub. fsetdec. }
    assert (HC1 : γ1 `notin` ftvar_in_cstrs C).
    { intros Hin.
      destruct ((proj1 a_looksub_lookeq_ftv) _ _ _ _ _ _ _ Hprem _ Hin)
        as [Hio | Hno].
      - clear - Hio Hγ1 Hd1. fsetdec.
      - apply Hno. simpl. clear - Hγ. fsetdec.
    }
    destruct (γ1 == γ) as [-> | Hne]; [ exact Hprem | ].
    pose proof (proj1 (a_looksub_lookeq_swap γ1 γ) _ _ _ _ _ _ _ Hprem) as Hs.
    revert Hs.
    assert (Hctx : swap_aenv γ1 γ ((γ1 ~ abind_tvar) ++ Θ)
                   = (γ ~ abind_tvar) ++ Θ).
    { simpl. rewrite swap_atom_l.
      rewrite (swap_aenv_fresh_id γ1 γ Θ) by (clear - Hγ Hγ1; fsetdec).
      reflexivity. }
    rewrite Hctx.
    rewrite (swap_atom_other γ1 γ α) by (clear - Hγ Hγ1; fsetdec).
    rewrite swap_pskl_open_var.
    rewrite swap_atom_l.
    rewrite (swap_pskl_fresh_id γ1 γ P0) by (clear - Hγ Hγ1; fsetdec).
    rewrite (swap_pskl_fresh_id γ1 γ P') by (clear - Hγ Hγ1; fsetdec).
    rewrite (swap_aenv_fresh_id γ1 γ Ξ) by (clear - Hγ HΞ1; fsetdec).
    rewrite swap_cstrs_fresh_id by (clear - Hγ HC1; fsetdec).
    intros Hs; exact Hs.
Qed.

(** R′, packaged. *)
Lemma a_looksub_open_forall_l_first : forall Θ α m P0 P' Ξ C γ,
  (* the two ◇-dispatch side conditions — see the [_n] form above *)
  P' <> pskl_hole ->
  P0 <> pskl_var_f α ->
  {{ Θ ⊢ (pskl_all_syn P0) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  γ `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P'
      ∪ ftvar_in_aenv Ξ ∪ ftvar_in_cstrs C) ->
  {{ ((γ ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P0 (pskl_var_f γ))
      ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a.
Proof.
  intros.
  eapply a_looksub_open_forall_l_first_n with (n := S (size_pskl P'));
    eauto.
Qed.
