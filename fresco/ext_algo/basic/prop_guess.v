(** ext_algo — the supply invariants of [e_guess_mono], its bridge to
    [a_guess_mono], and the [uniq] payoff.

    §1  the three supply invariants, and [uniq] off them
    §2  the payoff: [uniq (Ξ ++ Θ)] — [AT-Abs]'s premise, DERIVED
    §3  SOUNDNESS of the new encoding: [e_guess_mono -> a_guess_mono], over
        the SAME [Ξ] and [A], at any [Θ] the supply covers
    §4  why the converse cannot be stated over the same [Ξ] (with the
        counterexample)

    ⭐ THE TWO DIRECTIONS ARE NOT SYMMETRIC.  §3 is on-the-nose — inputs
    fixed pointwise, [Ξ] and [A] carried across unchanged — because it is
    the direction that has to COMPOSE with the theorems, which fix
    [Θ0]/[Θ1] (hand-off §3).  The converse could only be existential,
    because the threaded encoding is STRICTLY STRONGER: it cannot produce a
    block with a repeated name, and the old one can (§4's exhibit). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  The supply invariants                                             *)
(*                                                                        *)
(*  Three facts, in dependency order.  Together they say the supply is a   *)
(*  correct account of what the run has spent: it only grows (1.1), it     *)
(*  contains everything the run generated (1.2), and it contained none of  *)
(*  it beforehand (1.3).  [uniq] (1.4) is then immediate, and it is the    *)
(*  fact the whole milestone is for.                                       *)
(* ===================================================================== *)

(** 1.1  THE SUPPLY ONLY GROWS.  Consumed by the arrow row of every proof
    below: the second half runs at [S1], so anything known against [S0] has
    to travel forward. *)
Lemma e_guess_mono_supply_grows : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> S0 [<=] S1.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    fsetdec.
Qed.

(** 1.2  EVERYTHING GENERATED IS IN THE OUTPUT SUPPLY. *)
Lemma e_guess_mono_generated_in_supply : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> dom Ξ [<=] S1.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    simpl; try fsetdec.
  (* arrow: the left block is in [S1], and [S1] has travelled to [S2] *)
  pose proof (e_guess_mono_supply_grows H2) as Hgrow.
  rewrite dom_app. clear - IH1 IH2 Hgrow. fsetdec.
Qed.

(** 1.3  NOTHING GENERATED WAS IN THE INPUT SUPPLY.  The [e]-side counterpart
    of [a_guess_mono_generated_fresh] (algo/basic/prop_context.v), and strictly
    stronger in the arrow row: there, freshness of the RIGHT block is against
    [S1], which already holds the LEFT block. *)
Lemma e_guess_mono_generated_fresh : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A ->
  forall α, α `in` dom Ξ -> α `notin` S0.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    intros α0 Hα0; simpl in *.
  - (* ghost *) assert (α0 = α) by (clear - Hα0; fsetdec). subst. assumption.
  - (* univ_ghost *) auto.
  - (* var *) clear - Hα0; fsetdec.
  - (* unit *) clear - Hα0; fsetdec.
  - (* arrow *)
    rewrite dom_app in Hα0. destruct (union_1 Hα0) as [Hin | Hin]; auto.
    pose proof (e_guess_mono_supply_grows H1) as Hgrow.
    pose proof (IH2 _ Hin) as Hout. clear - Hgrow Hout. fsetdec.
  - (* ∀ : the premise ran at [add β S0], so its block dodges β too *)
    specialize (IH _ Hα0). clear - IH. fsetdec.
Qed.

(** 1.3b  The same fact as SET ARITHMETIC.  ⭐ This is the shape later
    clusters want (ext_algo/subtyping/prop_look.v §2, prop_solve.v): stated with an
    explicit [∀ γ], every consumer needs a [specialize] whose [match goal] is
    fragile under [Combined Scheme]'s auto-generated hypothesis names; stated
    as an intersection, one [fsetdec] absorbs it. *)
Corollary e_guess_mono_block_fresh : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> dom Ξ ∩ S0 [=] empty.
Proof.
  intros * H. intros γ. split; intros Hγ; [ | clear - Hγ; fsetdec ].
  assert (Hin : γ `in` dom Ξ) by (clear - Hγ; fsetdec).
  pose proof (e_guess_mono_generated_fresh H Hin) as Hout.
  clear - Hγ Hout. fsetdec.
Qed.

(** The generated block holds only BARE flexibles, so it mentions exactly its
    own domain.  ⚙ The [e]-side twin of [a_guess_mono_generated_ftvar]
    (algo/basic/prop_context.v), proved directly rather than through §3's bridge so
    that it carries no coverage hypothesis — the solve layer needs it to move
    a context [Ξ1 ++ Θ] into the supply, which is itself a coverage step. *)
Lemma e_guess_mono_generated_ftvar : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    simpl; try fsetdec.
  rewrite ftvar_in_aenv_app, dom_app. fsetdec.
Qed.

(** 1.4  ⭐ THE BLOCK IS DUPLICATE-FREE — the fact [a_guess_mono] cannot
    supply, and the reason M1 is this judgement.  It is exactly the arrow
    row's threading that buys it: the right block is fresh for a supply that
    already contains the left one. *)
Lemma e_guess_mono_uniq : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> uniq Ξ.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    try solve [ solve_uniq ].
  (* arrow *)
  apply uniq_app_4; auto.
  unfold disjoint. intros y Hy.
  assert (Hy1 : y `in` dom Ξ1) by (clear - Hy; fsetdec).
  assert (Hy2 : y `in` dom Ξ2) by (clear - Hy; fsetdec).
  pose proof (e_guess_mono_generated_in_supply H1 Hy1) as Hin.
  pose proof (e_guess_mono_generated_fresh H2 Hy2) as Hout.
  contradiction.
Qed.

(** 1.5  WHAT THE GUESSED TYPE CAN MENTION — the source, plus the block it
    invented.  ⚙ The [e]-side twin of [a_guess_mono_ftv] (algo/basic/prop_context.v),
    proved directly so it carries no coverage hypothesis: the solve layer
    needs it to bound its OWN output, which is a hypothesis-free statement
    there too (ext_algo/subtyping/prop_solve.v). *)
Lemma e_guess_mono_ftv : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A ->
  ftvar_in_ptyp A [<=] ftvar_in_pskl P ∪ dom Ξ.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    simpl; repeat rewrite dom_app; try solve [ fsetdec ].
  (* ∀ : the payload is CLOSED at β, so β drops out of the bound *)
  { assert (Hcl : ftvar_in_ptyp (close_ptyp_wrt_ptyp β A)
                    [=] AtomSetImpl.remove β (ftvar_in_ptyp A))
      by (apply ftvar_in_ptyp_close_ptyp_wrt_ptyp).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
    simpl in Hup. clear - IH Hcl Hup. fsetdec. }
Qed.

(* ===================================================================== *)
(*  §1b  The sort wrapper [e_guess]                                       *)
(*                                                                        *)
(*  Two rows, so every invariant is [e_guess_mono]'s plus a trivial case.  *)
(* ===================================================================== *)

(** ⚙ Six one-line lemmas rather than one conjunction: the wrapper has two
    rows, so each is [destruct] plus a citation, and separate statements are
    what the consumers ([a_extract]) actually apply. *)
Lemma e_guess_supply_grows : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> S0 [<=] S1.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ];
    [ fsetdec | exact (e_guess_mono_supply_grows Hg) ].
Qed.

Lemma e_guess_block_in_supply : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> dom Ξ [<=] S1.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ];
    [ simpl; fsetdec | exact (e_guess_mono_generated_in_supply Hg) ].
Qed.

Lemma e_guess_block_fresh : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> dom Ξ ∩ S0 [=] empty.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ];
    [ simpl; fsetdec | exact (e_guess_mono_block_fresh Hg) ].
Qed.

Lemma e_guess_uniq : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> uniq Ξ.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ];
    [ apply uniq_nil | exact (e_guess_mono_uniq Hg) ].
Qed.

Lemma e_guess_block_ftvar : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ];
    [ simpl; fsetdec | exact (e_guess_mono_generated_ftvar Hg) ].
Qed.

Lemma e_guess_ftv : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> ftvar_in_pskl Q' [<=] ftvar_in_pskl Q ∪ dom Ξ.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ]; [ simpl; fsetdec | ].
  (* the wrapper reads the guessed TYPE back into [pskl] *)
  rewrite ftvar_ptyp_to_pskl. exact (e_guess_mono_ftv Hg).
Qed.

(* ===================================================================== *)
(*  §2  THE PAYOFF — [AT-Abs]'s [uniq (αs ++ Θ1)] becomes DERIVABLE        *)
(*                                                                        *)
(*  fresco/algo/def_rules.v:1491 carries [uniq (αs ++ Θ1)] as a             *)
(*  consumer-side filter, because [a_guess_mono__arrow] runs both halves   *)
(*  at the same [Θ] and so cannot rule out a collision.                    *)
(*  docs/REPORT-postclosure-audit.md §1.3 priced the fix at 316            *)
(*  occurrences across 19 files and declined it.  Threaded, the premise is *)
(*  a two-line corollary of §1 — and no existing site pays anything.       *)
(* ===================================================================== *)

Corollary e_guess_mono_uniq_app : forall S0 P S1 Ξ A Θ,
  e_guess_mono S0 P S1 Ξ A ->
  ftvar_in_aenv Θ [<=] S0 ->
  uniq Θ ->
  uniq (Ξ ++ Θ).
Proof.
  intros * Hg HΘ Hu.
  apply uniq_app_4; [ eapply e_guess_mono_uniq; eassumption | assumption | ].
  unfold disjoint. intros y Hy.
  assert (Hy1 : y `in` dom Ξ) by (clear - Hy; fsetdec).
  assert (Hy2 : y `in` dom Θ) by (clear - Hy; fsetdec).
  pose proof (e_guess_mono_generated_fresh Hg Hy1) as Hout.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hdom.
  assert (Hin : y `in` S0) by (clear - Hy2 Hdom HΘ; fsetdec).
  contradiction.
Qed.

(* ===================================================================== *)
(*  §3  SOUNDNESS — [e_guess_mono] implies [a_guess_mono]                  *)
(*                                                                        *)
(*  ⭐ ON THE NOSE: same [Ξ], same [A], and [Θ] fixed pointwise.  This is   *)
(*  the direction that has to compose with the soundness/completeness      *)
(*  theorems, which fix the contexts, so it is stated the way the          *)
(*  [*_swap_junk] lemmas are (hand-off §3) and not up to renaming.         *)
(*                                                                        *)
(*  The single hypothesis is the SUPPLY INVARIANT: [S0] covers everything  *)
(*  the ambient context and the subject mention.  It replaces both of      *)
(*  [a_guess_mono]'s side conditions at once — [α ∉ ftvar_in_aenv Θ] on    *)
(*  the ghost row, and [β ∉ ftvar_in_aenv Θ ∪ ftvar_in_pskl P] on the ∀     *)
(*  row — because a supply, unlike a context, holds the subject's          *)
(*  variables too.                                                         *)
(* ===================================================================== *)

Lemma e_guess_mono_sound : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A ->
  forall Θ,
  ftvar_in_aenv Θ [<=] S0 ->
  ftvar_in_pskl P [<=] S0 ->
  a_guess_mono Θ P Ξ A.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    intros Θ HΘ HP; simpl in HP.
  - (* ghost *)
    apply a_guess_mono__ghost. clear - Hα HΘ. fsetdec.
  - (* univ_ghost *) apply a_guess_mono__univ_ghost. auto.
  - (* var *) apply a_guess_mono__var.
  - (* unit *) apply a_guess_mono__unit.
  - (* arrow: the right half runs at [S1], so [Θ] travels by 1.1 *)
    pose proof (e_guess_mono_supply_grows H1) as Hgrow.
    apply a_guess_mono__arrow.
    + apply IH1; [ assumption | clear - HP; fsetdec ].
    + apply IH2; [ clear - HΘ Hgrow; fsetdec | clear - HP Hgrow; fsetdec ].
  - (* ∀ : the witness enters BOTH the supply and the context, in step *)
    apply a_guess_mono__forall with (β := β).
    + clear - Hβ HΘ HP. fsetdec.
    + apply IH.
      * rewrite ftvar_in_aenv_cons_tvar. clear - HΘ. fsetdec.
      * pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β))
          as Hup.
        simpl in Hup. clear - Hup HP. fsetdec.
Qed.

(* ===================================================================== *)
(*  §4  WHY A CONVERSE OF §3 CANNOT CARRY [Ξ] AND [A] ACROSS              *)
(*                                                                        *)
(*  ⚠️ COUNTEREXAMPLE.  [a_guess_mono] admits a block with a REPEATED      *)
(*  name, and [e_guess_mono] never can (§1.4).  So the converse of §3 is   *)
(*  FALSE as an on-the-nose statement, at every supply, and no hypothesis  *)
(*  about [Θ] repairs it: the defect is in the OLD encoding's arrow row,   *)
(*  which runs both halves at the same [Θ].                                *)
(*                                                                        *)
(*  ⭐ This is the [uniq] payoff of §2 read backwards, so it is a feature   *)
(*  and not an obstruction — but it does fix the shape of the statement.   *)
(*  A stronger completeness (the two blocks agree up to a BIJECTIVE        *)
(*  renaming of generated names) is true and is not needed by anything     *)
(*  yet; it would want an [e_guess_mono] swap kit mirroring                *)
(*  algo/basic/prop_swap.v, which is only worth building when a consumer asks.   *)
(* ===================================================================== *)

Example a_guess_mono_admits_repeated_block : forall α,
  a_guess_mono nil (pskl_arrow pskl_ghost pskl_ghost)
    ((α ~ abind_flex_mono) ++ (α ~ abind_flex_mono))
    (ptyp_arrow (ptyp_var_f α) (ptyp_var_f α)).
Proof.
  intros α.
  apply a_guess_mono__arrow with
    (Ξ1 := (α ~ abind_flex_mono) ++ nil) (Ξ2 := (α ~ abind_flex_mono) ++ nil);
    apply a_guess_mono__ghost; simpl; solve_notin_auto.
Qed.

Example e_guess_mono_refuses_repeated_block : forall α S0 S1,
  ~ e_guess_mono S0 (pskl_arrow pskl_ghost pskl_ghost) S1
      ((α ~ abind_flex_mono) ++ (α ~ abind_flex_mono))
      (ptyp_arrow (ptyp_var_f α) (ptyp_var_f α)).
Proof.
  intros α S0 S1 H.
  pose proof (e_guess_mono_uniq H) as Hu.
  inversion Hu as [ | β bd Ξ Hu' Hβ Heq ]; subst.
  simpl in Hβ. clear - Hβ. fsetdec.
Qed.

(** The bridge for the wrapper.  Same shape as §3's. *)
Lemma e_guess_sound : forall S0 NM Q S1 Ξ Q' Θ,
  e_guess S0 NM Q S1 Ξ Q' ->
  ftvar_in_aenv Θ [<=] S0 ->
  ftvar_in_pskl Q [<=] S0 ->
  a_guess Θ NM Q Ξ Q'.
Proof.
  intros * H HΘ HQ; destruct H as [ S Q0 | S0 S1 Q0 Ξ A Hg ].
  - apply a_guess__sk.
  - apply a_guess__ty. eapply e_guess_mono_sound; eassumption.
Qed.

(* ===================================================================== *)
(*  §7  THE SUPPLY IS READ UP TO [=]                                      *)
(*                                                                        *)
(*  A supply is a SET, so a caller that has assembled one by a different  *)
(*  route holds an [=]-variant, not the same term — and the judgement     *)
(*  takes it as an INDEX, which no [rewrite] can move under.  Every       *)
(*  consumer above therefore needs this transport; §8c.10's completeness  *)
(*  level is the first, and prop_look_pair.v §1's look-side twin          *)
(*  ([e_looksub_lookeq_supply_respect]) is the template, including the    *)
(*  ∃-form: the OUTPUT supply moves too, and only up to [=].              *)
(* ===================================================================== *)

Lemma e_guess_mono_supply_respect : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\ e_guess_mono S0' P S1' Ξ A.
Proof.
  induction 1; intros S0' Heq.
  - (* ghost — the one row that INVENTS *)
    exists (add α S0'). split; [ clear - Heq; fsetdec | ].
    apply e_guess_mono__ghost. clear - H Heq. fsetdec.
  - (* univ_ghost *)
    destruct (IHe_guess_mono _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_guess_mono__univ_ghost; exact Hd ].
  - (* var *)
    exists S0'. split; [ exact Heq | apply e_guess_mono__var ].
  - (* unit *)
    exists S0'. split; [ exact Heq | apply e_guess_mono__unit ].
  - (* arrow — threaded, so the two [=]-witnesses chain *)
    destruct (IHe_guess_mono1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IHe_guess_mono2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | eapply e_guess_mono__arrow; eassumption ].
  - (* forall — the witness is drawn FROM the supply *)
    destruct (IHe_guess_mono (add β S0')) as [S1' [HS1 Hd]];
      [ clear - Heq; fsetdec | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_guess_mono__forall with (β := β);
      [ clear - H Heq; fsetdec | exact Hd ].
Qed.

(** The sort wrapper reads its supply up to [=] as well. *)
Lemma e_guess_supply_respect : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\ e_guess S0' NM Q S1' Ξ Q'.
Proof.
  intros * H. destruct H as [ S Q0 | S0' S1' Q0 Ξ0 A Hg ]; intros S0'' Heq.
  - exists S0''. split; [ exact Heq | apply e_guess__sk ].
  - destruct (e_guess_mono_supply_respect Hg Heq) as [S1'' [HS1 Hg']].
    exists S1''. split; [ exact HS1 | apply e_guess__ty; exact Hg' ].
Qed.

(* ===================================================================== *)
(*  §8  EQUIVARIANCE                                                      *)
(*                                                                        *)
(*  §8c.10's completeness level needs it because the RUNNER opens its     *)
(*  binders at [supply_fresh S0] while a derivation opens them at any     *)
(*  fresh atom: the two answers agree only up to a transposition.         *)
(*  algo/basic/prop_swap.v §5's [a_guess_mono_swap] is the template; what the   *)
(*  supply-threaded copy adds is the ∃-form of prop_guess.v §7 — the      *)
(*  swapped run's OUTPUT supply is fixed only up to [=], because          *)
(*  [swap_atoms] is not a Leibniz homomorphism on the opaque [atoms].     *)
(* ===================================================================== *)

Lemma e_guess_mono_swap : forall a b S0 P S1 Ξ τ,
  e_guess_mono S0 P S1 Ξ τ ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    e_guess_mono S0' (swap_pskl a b P) S1' (swap_aenv a b Ξ)
      (swap_ptyp a b τ).
Proof.
  intros a b S0 P S1 Ξ τ H. induction H; intros S0' Heq; simpl.
  - (* ghost — the row that INVENTS; its witness rides the swap *)
    exists (add (swap_atom a b α) S0'). split;
      [ apply eq_swap_atoms_add; exact Heq | ].
    apply e_guess_mono__ghost. eapply swap_notin_eq; eassumption.
  - (* univ_ghost *)
    destruct (IHe_guess_mono _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_guess_mono__univ_ghost; exact Hd ].
  - (* var *) exists S0'. split; [ exact Heq | apply e_guess_mono__var ].
  - (* unit *) exists S0'. split; [ exact Heq | apply e_guess_mono__unit ].
  - (* arrow — threaded, so the two ∃-witnesses chain *)
    destruct (IHe_guess_mono1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IHe_guess_mono2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | ].
    rewrite swap_aenv_app. eapply e_guess_mono__arrow; eassumption.
  - (* forall — the witness is drawn FROM the supply *)
    destruct (IHe_guess_mono (add (swap_atom a b β) S0'))
      as [S1' [HS1 Hd]]; [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    rewrite swap_ptyp_close.
    apply e_guess_mono__forall with (β := swap_atom a b β).
    + eapply swap_notin_eq; eassumption.
    + rewrite swap_pskl_open_var in Hd. exact Hd.
Qed.

(** §1b's wrapper along the same transposition: [guess^SK] moves nothing,
    [guess^TY] is the mono row read back through the coercion.  ⚙ Added for
    §8c.11's level, which reaches it through [e_extract_swap]. *)
Lemma e_guess_swap : forall a b S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    e_guess S0' NM (swap_pskl a b Q) S1' (swap_aenv a b Ξ)
      (swap_pskl a b Q').
Proof.
  intros a b S0 NM Q S1 Ξ Q' H.
  destruct H as [ S Q0 | S0' S1' Q0 Ξ0 A Hg ]; intros S0'' Heq.
  - exists S0''. split; [ exact Heq | simpl; apply e_guess__sk ].
  - destruct (e_guess_mono_swap Hg Heq) as [S1'' [HS1 Hg']].
    exists S1''. split; [ exact HS1 | ].
    rewrite swap_pskl_ptyp_to_pskl. apply e_guess__ty. exact Hg'.
Qed.

(* ===================================================================== *)
(*  §9  SHAPE INVERSIONS                                                  *)
(*                                                                        *)
(*  One per subject constructor.  Written out rather than left to         *)
(*  [inversion … as], whose binder COUNT shifts with what the unifier     *)
(*  already determined — the same discipline prop_consis_complete.v §4    *)
(*  applies to the consistency rules.  ⚙ [guess^TY] is syntax-directed,   *)
(*  so every one of them is unconditional.                                *)
(* ===================================================================== *)

Lemma e_guess_mono_inv_ghost : forall S0 S1 Ξ A,
  e_guess_mono S0 pskl_ghost S1 Ξ A ->
  exists α, α `notin` S0 /\ S1 = add α S0 /\
    Ξ = (α ~ abind_flex_mono) ++ nil /\ A = ptyp_var_f α.
Proof. intros * Hd. inversion Hd; subst; eauto 10. Qed.

Lemma e_guess_mono_inv_unit : forall S0 S1 Ξ A,
  e_guess_mono S0 pskl_unit S1 Ξ A -> S1 = S0 /\ Ξ = nil /\ A = ptyp_unit.
Proof. intros * Hd. inversion Hd; subst; auto. Qed.

Lemma e_guess_mono_inv_var : forall S0 α S1 Ξ A,
  e_guess_mono S0 (pskl_var_f α) S1 Ξ A ->
  S1 = S0 /\ Ξ = nil /\ A = ptyp_var_f α.
Proof. intros * Hd. inversion Hd; subst; auto. Qed.

Lemma e_guess_mono_inv_arrow : forall S0 P Q S2 Ξ A,
  e_guess_mono S0 (pskl_arrow P Q) S2 Ξ A ->
  exists S1 Ξ1 Ξ2 A1 A2,
    Ξ = Ξ1 ++ Ξ2 /\ A = ptyp_arrow A1 A2 /\
    e_guess_mono S0 P S1 Ξ1 A1 /\ e_guess_mono S1 Q S2 Ξ2 A2.
Proof. intros * Hd. inversion Hd; subst; eauto 10. Qed.

Lemma e_guess_mono_inv_all_syn : forall S0 P S1 Ξ A,
  e_guess_mono S0 (pskl_all_syn P) S1 Ξ A ->
  exists β A0, β `notin` S0 /\ A = ptyp_all (close_ptyp_wrt_ptyp β A0) /\
    e_guess_mono (add β S0) (open_pskl_wrt_pskl P (pskl_var_f β)) S1 Ξ A0.
Proof. intros * Hd. inversion Hd; subst; eauto 10. Qed.

Lemma e_guess_mono_inv_univ_ghost : forall S0 P S1 Ξ A,
  e_guess_mono S0 (pskl_univ_ghost P) S1 Ξ A -> e_guess_mono S0 P S1 Ξ A.
Proof. intros * Hd. inversion Hd; subst; auto. Qed.

(** A dangling index is not a skeleton any run can be given — the same
    fact [e_guess_mono_order_var_b_absurd] states for the ORDER. *)
Lemma e_guess_mono_inv_var_b : forall S0 n S1 Ξ A,
  e_guess_mono S0 (pskl_var_b n) S1 Ξ A -> False.
Proof. intros * Hd. inversion Hd. Qed.
