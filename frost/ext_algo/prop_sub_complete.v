(** ext_algo — §8c.11, campaign level 6: the SUBTYPING runner's
    completeness SCAFFOLDING — the parts that are settled, and the
    machine-checked reason the level cannot be closed on level 5's design.

    §1  a strong-induction principle for [e_sub_call_order]
    §3  equivariance along a CHAIN, for [e_sub] / [e_sub_flex]
    §4  the ROOT INVERSIONS — §8c.11's overlap table, as lemmas

    ⭐ §4 IS THE LEVEL'S GOOD NEWS AND IT IS ALL HERE.  [guarded_pskl] is
    [unit | var | arrow] and NOTHING else, so [∀], [◇] and [⫯] are all
    UNGUARDED and every cell of the runner's dispatch admits EXACTLY ONE
    rule — including [◇ ⩽ ◇], where [SI-Ghost] and [SI-UnivGhostR] would
    otherwise have returned different answers.  Contrast level 5, whose §4
    has three genuinely disjunctive cells.  The [e_sub_flex] side is
    overlap-free by construction, and at [TI] the only rule is [SI-Infer],
    hereditarily (the audit's one finding, fixed in `35a13b3`).

    ⛔⛔ WHY §6/§7 ARE NOT HERE.  Level 5's motive relates the derivation's
    outputs to the runner's UP TO A SWAP CHAIN, and its supply conjunct is
    [swaps_atoms ps Sd [=] cs_supply r].  Mirrored to this level that
    conjunct is FALSE, and [cex/probe_extract_supply_drift.v] is the
    witness: at an α-FREE subject against a ∀ counterpart, [LS-Absent] and
    [LS-ForallR] both fire, the first spends no supply and the second draws
    an opener, and both emit the empty collection — so two [e_extract]
    derivations at the SAME inputs agree on their block and their
    instantiation and differ ONLY in how much supply they spent, by one
    atom.  No renaming can relate them; a chain that fixes the input supply
    fixes it exactly.  [SI-ForallL] runs precisely that extraction (see
    that file's closing note for the configuration, argued by inspection).

    ⭐⭐ THE DIAGNOSIS IS LEVEL 5's, ONE LAYER DOWN — A MISSING DISPATCH
    GUARD.  The reference implementation tests ABSENCE FIRST, and so does
    this tree's runner: every non-Absent clause of [e_looksub_impl] /
    [e_lookeq_impl] sits behind [mem α (ftvar_in_pskl P)]
    (def_look_impl.v:360, 377, 393, 406, …).  A relational encoding has no
    match order, so that exclusion has to be a PREMISE — and
    [e_looksub__forall_r] and its neighbours carry none.  Identical species
    to [U-FlexL]/[U-FlexR]'s missing [≠ ◇] (`0829607`) and [SI-Ghost]'s
    missing [M ≠ TI] (`35a13b3`).  ⚙ [LS-Vacuous] (counterpart [◇])
    overlaps the same way, so the repair is a pair of guards, not one, and
    it is owed on BOTH encodings ([algo/def_rules.v] and
    [ext_algo/def_look.v]) with a [paper-gap] entry.

    So: everything below is Qed and motive-independent, and it is what the
    level resumes from once the collection's guards land. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_coercions.
Require Import src.frost.prop_tag.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_dec.
Require Import src.frost.ext_algo.prop_dec.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.prop_guess.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.prop_consis.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.prop_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.prop_solve.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.prop_extract.
Require Import src.frost.ext_algo.def_sub.
Require Import src.frost.ext_algo.prop_sub.
Require Import src.frost.ext_algo.def_order.
Require Import src.frost.ext_algo.prop_termination.
Require Import src.frost.ext_algo.prop_solve_det.
Require Import src.frost.ext_algo.def_consis_impl.
Require Import src.frost.ext_algo.prop_consis_complete.
Require Import src.frost.ext_algo.def_extract_impl.
Require Import src.frost.ext_algo.def_sub_impl.

Set Implicit Arguments.

Open Scope frost_a_scope.
Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  Strong induction for [e_sub_call_order]                           *)
(*                                                                        *)
(*  prop_consis_complete.v §1's idiom, verbatim: the runner recurses on    *)
(*  the ORDER, so completeness must too, and the order's own [Induction]   *)
(*  scheme gives an IH only at the immediate sub-orders.  Hand-write the   *)
(*  principle with every RECURSIVE premise DOUBLED — the order premise     *)
(*  itself and its motive companion — so a case script may use either.     *)
(*                                                                        *)
(*  ⚙ Three premises have no companion because they are not recursive      *)
(*  calls of this block: [Check]'s [e_consis_order], [Arrow]'s first       *)
(*  conjunct (also an [e_consis_order]) and [ForallL]'s first conjunct     *)
(*  (an [e_extract_order]).                                               *)
(* ===================================================================== *)

Section e_sub_call_order_sind.

Variable Qc : supply -> a_sub_mode -> mode -> pskl -> aenv -> sub_call -> Prop.

Hypothesis Hsub : forall S0 NM M P0 Θ0 P,
    (* Check — one consistency run *)
    (M = mode_tc -> e_consis_order empty empty S0 Θ0 P0 P) ->
    (* ForallR — peel the pattern's quantifier *)
    (forall B,
       M = mode_tc -> P0 = pskl_all_syn B ->
       e_sub_call_order (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
         ((supply_fresh S0 ~ abind_tvar) ++ Θ0) (sub_call_sub P)) ->
    (forall B,
       M = mode_tc -> P0 = pskl_all_syn B ->
       Qc (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
         ((supply_fresh S0 ~ abind_tvar) ++ Θ0) (sub_call_sub P)) ->
    (* FlexMono — enter the walk *)
    (forall α M',
       P = pskl_var_f α -> M = mode_fn M' ->
       e_sub_call_order S0 NM M' P0 Θ0 (sub_call_flex nil α)) ->
    (forall α M',
       P = pskl_var_f α -> M = mode_fn M' ->
       Qc S0 NM M' P0 Θ0 (sub_call_flex nil α)) ->
    (* Arrow — the domain goes to consistency, the codomain stays *)
    (forall M' P0a P0b P1 P2,
       M = mode_fn M' -> P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_order empty empty S0 Θ0 P0a P1
       /\ (forall S1 Θ1 Q1,
             {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
             e_sub_call_order S1 NM M' P0b Θ1 (sub_call_sub P2))) ->
    (forall M' P0a P0b P1 P2,
       M = mode_fn M' -> P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       forall S1 Θ1 Q1,
         {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
         Qc S1 NM M' P0b Θ1 (sub_call_sub P2)) ->
    (* ForallL — extract an instantiation, then recurse on the opened body *)
    (forall Q,
       P = pskl_all_syn Q -> M <> mode_ti ->
       (guarded_pskl P0 \/ P0 = pskl_hole) ->
       e_extract_order (add (supply_fresh S0) S0) Θ0 NM (supply_fresh S0) M
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0))) P0
       /\ (forall S1 Ξ P1,
             {{ (add (supply_fresh S0) S0) ↝ S1 ⊨ Θ0
                ⊢ (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                ⊳[ NM , (supply_fresh S0) , M ] P0 ⤳ Ξ ↪ P1 }}e ->
             {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
             e_sub_call_order S1 NM M P0 (Ξ ++ Θ0)
               (sub_call_sub (open_pskl_wrt_pskl Q P1)))) ->
    (forall Q,
       P = pskl_all_syn Q -> M <> mode_ti ->
       (guarded_pskl P0 \/ P0 = pskl_hole) ->
       forall S1 Ξ P1,
         {{ (add (supply_fresh S0) S0) ↝ S1 ⊨ Θ0
            ⊢ (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
            ⊳[ NM , (supply_fresh S0) , M ] P0 ⤳ Ξ ↪ P1 }}e ->
         {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
         Qc S1 NM M P0 (Ξ ++ Θ0)
           (sub_call_sub (open_pskl_wrt_pskl Q P1))) ->
    (* UnivGhostL — strip the subject's ⫯ *)
    (forall Q,
       P = pskl_tophole Q -> M <> mode_ti ->
       e_sub_call_order S0 NM M P0 Θ0 (sub_call_sub Q)) ->
    (forall Q,
       P = pskl_tophole Q -> M <> mode_ti ->
       Qc S0 NM M P0 Θ0 (sub_call_sub Q)) ->
    Qc S0 NM M P0 Θ0 (sub_call_sub P).

Hypothesis Hflex : forall S0 NM M P0 Θ0 Ξ α,
    (* Flex-Solve — the head IS the target, undefined *)
    (forall Θ0',
       Θ0 = (α ~ abind_flex_mono) ++ Θ0' ->
       e_sub_call_order
         (add (supply_fresh (add (supply_fresh S0) S0))
            (add (supply_fresh S0) S0))
         NM (mode_fn M) P0
         (Ξ ++ (α ~ abind_flex_mono_def
                      (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                         (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
             ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
             ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
         (sub_call_sub
            (pskl_arrow (pskl_var_f (supply_fresh S0))
               (pskl_var_f (supply_fresh (add (supply_fresh S0) S0)))))) ->
    (forall Θ0',
       Θ0 = (α ~ abind_flex_mono) ++ Θ0' ->
       Qc (add (supply_fresh (add (supply_fresh S0) S0))
             (add (supply_fresh S0) S0))
         NM (mode_fn M) P0
         (Ξ ++ (α ~ abind_flex_mono_def
                      (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                         (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
             ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
             ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
         (sub_call_sub
            (pskl_arrow (pskl_var_f (supply_fresh S0))
               (pskl_var_f (supply_fresh (add (supply_fresh S0) S0)))))) ->
    (* Flex-Assign — a defined head is substituted away and dropped *)
    (forall β τ Θ0',
       Θ0 = (β ~ abind_flex_mono_def τ) ++ Θ0' ->
       e_sub_call_order S0 NM (mode_fn M)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
         (Ξ ++ Θ0')
         (sub_call_sub
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->
    (forall β τ Θ0',
       Θ0 = (β ~ abind_flex_mono_def τ) ++ Θ0' ->
       Qc S0 NM (mode_fn M)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
         (Ξ ++ Θ0')
         (sub_call_sub
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->
    (* Flex-Depend / Flex-Skip — an undefined non-target head *)
    (forall β Θ0',
       Θ0 = (β ~ abind_flex_mono) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0'
         (sub_call_flex (Ξ ++ (β ~ abind_flex_mono)) α)
       /\ e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall β Θ0',
       Θ0 = (β ~ abind_flex_mono) ++ Θ0' ->
       Qc S0 NM M P0 Θ0' (sub_call_flex (Ξ ++ (β ~ abind_flex_mono)) α)
       /\ Qc S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (* Flex-SkipRigid *)
    (forall β Θ0',
       Θ0 = (β ~ abind_tvar) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall β Θ0',
       Θ0 = (β ~ abind_tvar) ++ Θ0' ->
       Qc S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (* Flex-SkipTmVar, both payload sorts *)
    (forall x A Θ0',
       Θ0 = (x ~ abind_var_typ A) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall x A Θ0',
       Θ0 = (x ~ abind_var_typ A) ++ Θ0' ->
       Qc S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall x Q Θ0',
       Θ0 = (x ~ abind_var_skl Q) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall x Q Θ0',
       Θ0 = (x ~ abind_var_skl Q) ++ Θ0' ->
       Qc S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    Qc S0 NM M P0 Θ0 (sub_call_flex Ξ α).

Fixpoint e_sub_call_order_sind S0 NM M P0 Θ0 c
    (H : e_sub_call_order S0 NM M P0 Θ0 c) {struct H} : Qc S0 NM M P0 Θ0 c :=
  match H in e_sub_call_order S0' NM' M' P0' Θ0' c'
        return Qc S0' NM' M' P0' Θ0' c' with
  | e_sub_call_order__sub _ _ _ _ _ _ p1 p2 p3 p4 p5 p6 =>
      @Hsub _ _ _ _ _ _
        p1
        p2
        (fun B E1 E2 => e_sub_call_order_sind (p2 B E1 E2))
        p3
        (fun α M' E1 E2 => e_sub_call_order_sind (p3 α M' E1 E2))
        p4
        (fun M' P0a P0b P1 P2 E1 E2 E3 S1 Θ1 Q1 Hrun =>
           match p4 M' P0a P0b P1 P2 E1 E2 E3 with
           | conj _ Hrec => e_sub_call_order_sind (Hrec S1 Θ1 Q1 Hrun)
           end)
        p5
        (fun Q E1 E2 Hg S1 Ξ P1 Hrun Hwf =>
           match p5 Q E1 E2 Hg with
           | conj _ Hrec => e_sub_call_order_sind (Hrec S1 Ξ P1 Hrun Hwf)
           end)
        p6
        (fun Q E1 E2 => e_sub_call_order_sind (p6 Q E1 E2))
  | e_sub_call_order__flex _ _ _ _ _ _ _ q1 q2 q3 q4 q5 q6 =>
      @Hflex _ _ _ _ _ _ _
        q1
        (fun Θ0' E => e_sub_call_order_sind (q1 Θ0' E))
        q2
        (fun β τ Θ0' E => e_sub_call_order_sind (q2 β τ Θ0' E))
        q3
        (fun β Θ0' E =>
           match q3 β Θ0' E with
           | conj Ha Hb =>
               conj (e_sub_call_order_sind Ha) (e_sub_call_order_sind Hb)
           end)
        q4
        (fun β Θ0' E => e_sub_call_order_sind (q4 β Θ0' E))
        q5
        (fun x A Θ0' E => e_sub_call_order_sind (q5 x A Θ0' E))
        q6
        (fun x Q Θ0' E => e_sub_call_order_sind (q6 x Q Θ0' E))
  end.

End e_sub_call_order_sind.

(* ===================================================================== *)
(*  §3  EQUIVARIANCE ALONG A CHAIN                                        *)
(*                                                                        *)
(*  prop_consis_complete.v §3's iteration, for this level's judgements.    *)
(*  What consumes it: [SI-Arrow] and [SI-ForallL] run their second premise *)
(*  at the FIRST premise's output, and by then the derivation's names and  *)
(*  the runner's differ by a whole CHAIN of transpositions, not one.       *)
(* ===================================================================== *)

Lemma e_sub_swaps : forall ps S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0) ⊢[ NM | M | (swaps_pskl ps P0) ]
       (swaps_pskl ps P) ⩽ (swaps_pskl ps Q) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - (* the empty chain moves nothing but the supply *)
    exact (e_sub_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_sub_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_sub_flex_swaps : forall ps S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    e_sub_flex S0' NM M (swaps_pskl ps P0) (swaps_aenv ps Θ0)
      (swaps_aenv ps Ξ) (swaps_atom ps α) (swaps_pskl ps Q)
      S1' (swaps_aenv ps Θ1).
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_sub_flex_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_sub_flex_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

(** ⚙ [a_suffix] survives a chain, which is what [SI-ForallR]'s
    [split_at_tvar] step below needs of the transported junk block. *)
Lemma a_suffix_swaps : forall ps (Ξ : aenv),
  a_suffix Ξ -> a_suffix (swaps_aenv ps Ξ).
Proof.
  induction ps as [ | [a b] ps IH ]; intros Ξ Hs; simpl; [ exact Hs | ].
  apply IH. apply a_suffix_swap. exact Hs.
Qed.

(* ===================================================================== *)
(*  §4  ROOT INVERSIONS — the case backbone, machine-checked              *)
(*                                                                        *)
(*  §8c.11's overlap table as lemmas: one per clause of the runner's       *)
(*  dispatch, each turning a derivation at the clause's shape into that    *)
(*  rule's premises — or into [False] where the runner rejects.  ⭐ Every  *)
(*  one is a SINGLE rule, no disjunctions: [guarded_pskl] is               *)
(*  [unit | var | arrow] and nothing else, so the ∀ / ◇ / ⫯ overlaps the   *)
(*  rule list suggests are all vacuous, and the [e_sub_flex] side is       *)
(*  keyed to distinct binding shapes.  (Contrast level 5, whose §4 has     *)
(*  three genuinely disjunctive cells.)                                    *)
(* ===================================================================== *)

(** After [inversion], the rows that COULD have matched the shape but demand
    [guarded_pskl] of a ∀ / ⫯ / ◇ leave that demand behind; it is never
    derivable, so one [inversion] each closes them. *)
Local Ltac kill_unguarded :=
  repeat match goal with
         | Hg : guarded_pskl (pskl_all_syn _) |- _ => solve [ inversion Hg ]
         | Hg : guarded_pskl (pskl_tophole _) |- _ => solve [ inversion Hg ]
         | Hg : guarded_pskl pskl_hole |- _ => solve [ inversion Hg ]
         end.

(** [SI-ForallL]'s own guard, at a counterpart that is neither guarded nor
    a hole — the shape that kills it beside [SI-ForallR]. *)
Local Ltac kill_forall_l_guard :=
  repeat match goal with
         | Hg : guarded_pskl ?X \/ ?X = pskl_hole |- _ =>
             solve [ destruct Hg as [Hg | Hg];
                     [ inversion Hg | discriminate ] ]
         end.

(* --- the mode dispatch: at TI only SI-Infer, hereditarily (`35a13b3`) --- *)

Lemma e_sub_inv_ti : forall S0 NM P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | mode_ti | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  P0 = pskl_hole /\ Q = P /\ S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros * Hd. inversion Hd; subst; try congruence.
  repeat split; reflexivity.
Qed.

(* --- (ty, tc) --- *)

Lemma e_sub_inv_forall_r : forall S0 Θ0 B P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | mode_tc | (pskl_all_syn B) ]
     P ⩽ Q ⊣ Θ1 }}e ->
  Q = pskl_all_syn B /\ pskl_ghost_free (pskl_all_syn B) /\
  exists α Ξ,
    a_suffix Ξ /\ uniq (Ξ ++ Θ0) /\ α `notin` S0 /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ a_sub_mode_ty | mode_tc | (open_pskl_wrt_pskl B (pskl_var_f α)) ]
       P ⩽ (open_pskl_wrt_pskl B (pskl_var_f α))
       ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}e.
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded; kill_forall_l_guard.
  split; [ reflexivity | split; [ assumption | eauto 10 ] ].
Qed.

Lemma e_sub_inv_check : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | mode_tc | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  (forall B, P0 <> pskl_all_syn B) ->
  (forall B, P <> pskl_all_syn B) ->
  Q = P0 /\ pskl_ghost_free P /\ pskl_ghost_free P0 /\
  guarded_pskl P /\ guarded_pskl P0 /\ e_consis_chk S0 Θ0 P P0 S1 Θ1.
Proof.
  intros * Hd Hn0 Hn. inversion Hd; subst;
    try solve [ exfalso; eapply Hn0; reflexivity
              | exfalso; eapply Hn; reflexivity ].
  repeat split; assumption.
Qed.

(* --- the subject is a ∀: [SI-ForallL], at every mode that admits it --- *)

Lemma e_sub_inv_forall_l : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] (pskl_all_syn P) ⩽ Q ⊣ Θ1 }}e ->
  M <> mode_ti ->
  (forall B, P0 <> pskl_all_syn B) ->
  (guarded_pskl P0 \/ P0 = pskl_hole) /\
  exists α Sm Ξ P1,
    α `notin` S0 /\
    {{ (add α S0) ↝ Sm ⊨ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α))
       ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}e /\
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a /\
    {{ Sm ↝ S1 ⊨ (Ξ ++ Θ0) ⊢[ NM | M | P0 ]
       (open_pskl_wrt_pskl P P1) ⩽ Q ⊣ Θ1 }}e.
Proof.
  intros * Hd Hti Hn0. inversion Hd; subst; kill_unguarded;
    try solve [ congruence | exfalso; eapply Hn0; reflexivity ].
  split; [ assumption | eauto 10 ].
Qed.

(* --- (sk, M ≠ TI) --- *)

Lemma e_sub_inv_ghost : forall S0 M P0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] pskl_hole ⩽ Q ⊣ Θ1 }}e ->
  M <> mode_ti ->
  Q = P0 /\ S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros * Hd Hti. inversion Hd; subst; kill_unguarded; try congruence.
  repeat split; reflexivity.
Qed.

Lemma e_sub_inv_univ_ghost_l : forall S0 M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] (pskl_tophole P) ⩽ Q ⊣ Θ1 }}e ->
  M <> mode_ti ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] P ⩽ Q ⊣ Θ1 }}e.
Proof.
  intros * Hd Hti. inversion Hd; subst; kill_unguarded;
    solve [ congruence | assumption ].
Qed.

(** ⭐ The audit's dangerous-looking cell, and it is not: [UnivGhostR] wants
    a GUARDED subject, so at [◇ ⩽ ◇] only [SI-Ghost] fires and the two
    would-be outputs never meet. *)
Lemma e_sub_inv_univ_ghost_r : forall S0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | mode_tc | pskl_hole ] P ⩽ Q ⊣ Θ1 }}e ->
  P <> pskl_hole -> (forall Pb, P <> pskl_tophole Pb) ->
  (forall Pb, P <> pskl_all_syn Pb) ->
  guarded_pskl P /\ Q = pskl_tophole P /\ S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros * Hd Hnh Hnt Hna. inversion Hd; subst;
    try solve [ congruence
              | exfalso; eapply Hnt; reflexivity
              | exfalso; eapply Hna; reflexivity ].
  repeat split; solve [ assumption | reflexivity ].
Qed.

(** The runner's [None] at [(sk, tc)] with a guarded subject and a
    non-ghost counterpart: no rule fires there either. *)
Lemma e_sub_inv_sk_tc_none : forall S0 P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | mode_tc | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  P <> pskl_hole -> (forall Pb, P <> pskl_tophole Pb) ->
  (forall Pb, P <> pskl_all_syn Pb) -> P0 <> pskl_hole -> False.
Proof.
  intros * Hd Hnh Hnt Hna Hn0. inversion Hd; subst;
    solve [ congruence
          | exfalso; eapply Hnt; reflexivity
          | exfalso; eapply Hna; reflexivity ].
Qed.

(* --- (fn) --- *)

Lemma e_sub_inv_arrow : forall S0 NM M P0a P0b Θ0 P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | (pskl_arrow P0a P0b) ]
     (pskl_arrow P1 P2) ⩽ Q ⊣ Θ1 }}e ->
  exists Sm Θm Q1 Q2,
    Q = pskl_arrow Q1 Q2 /\
    {{ S0 ↝ Sm ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θm }}e /\
    {{ Sm ↝ S1 ⊨ Θm ⊢[ NM | M | P0b ] P2 ⩽ Q2 ⊣ Θ1 }}e.
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded. eauto 10.
Qed.

Lemma e_sub_inv_arrow_none : forall S0 NM M P0 Θ0 P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | P0 ] (pskl_arrow P1 P2) ⩽ Q ⊣ Θ1 }}e ->
  (forall A B, P0 <> pskl_arrow A B) -> False.
Proof.
  intros * Hd Hn0. inversion Hd; subst;
    solve [ congruence | exfalso; eapply Hn0; reflexivity ].
Qed.

Lemma e_sub_inv_flex_mono : forall S0 NM M P0 Θ0 α Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | P0 ] (pskl_var_f α) ⩽ Q ⊣ Θ1 }}e ->
  e_sub_flex S0 NM M P0 Θ0 nil α Q S1 Θ1.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded. assumption. Qed.

Lemma e_sub_inv_fn_unit_none : forall S0 NM M P0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | P0 ] pskl_unit ⩽ Q ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

Lemma e_sub_inv_fn_ty_hole_none : forall S0 M P0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | (mode_fn M) | P0 ]
     pskl_hole ⩽ Q ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

Lemma e_sub_inv_fn_ty_tophole_none : forall S0 M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | (mode_fn M) | P0 ]
     (pskl_tophole P) ⩽ Q ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

(* --- the WALK: one inversion per head binding shape --------------------- *)

Lemma e_sub_flex_inv_nil : forall S0 NM M P0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 nil Ξ α Q S1 Θ1 -> False.
Proof. intros * Hd. inversion Hd. Qed.

(** The head IS the target: only [SI-Flex-Solve] — every other row of the
    walk demands [α <> β] or a different binding shape. *)
Lemma e_sub_flex_inv_self : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((α ~ abind_flex_mono) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists a1 b1, a1 `notin` S0 /\ b1 `notin` add a1 S0 /\
    {{ (add b1 (add a1 S0)) ↝ S1 ⊨
       (Ξ ++ (α ~ abind_flex_mono_def
                    (ptyp_arrow (ptyp_var_f a1) (ptyp_var_f b1)))
           ++ (b1 ~ abind_flex_mono) ++ (a1 ~ abind_flex_mono) ++ Θ0)
       ⊢[ NM | (mode_fn M) | P0 ]
       (pskl_arrow (pskl_var_f a1) (pskl_var_f b1)) ⩽ Q ⊣ Θ1 }}e.
Proof.
  intros * Hd. inversion Hd; subst; try congruence. eauto 10.
Qed.

Lemma e_sub_flex_inv_other_flex : forall S0 NM M P0 Θ0 Ξ α β Q S1 Θ1,
  α <> β ->
  e_sub_flex S0 NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α Q S1 Θ1 ->
  (β `in` ftvar_in_pskl P0 /\
     e_sub_flex S0 NM M P0 Θ0 (Ξ ++ (β ~ abind_flex_mono)) α Q S1 Θ1)
  \/ (β `notin` ftvar_in_pskl P0 /\ exists Θ1',
        Θ1 = (β ~ abind_flex_mono) ++ Θ1' /\
        e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1').
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence.
  - left; split; assumption.
  - right; split; [ assumption | eauto ].
Qed.

Lemma e_sub_flex_inv_def : forall S0 NM M P0 Θ0 Ξ α β τ Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists Θ1', Θ1 = (β ~ abind_flex_mono_def τ) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ (Ξ ++ Θ0)
       ⊢[ NM | (mode_fn M) | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) ]
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ⩽ Q
       ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma e_sub_flex_inv_tvar : forall S0 NM M P0 Θ0 Ξ α β Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((β ~ abind_tvar) ++ Θ0) Ξ α Q S1 Θ1 ->
  α <> β /\ β `notin` ftvar_in_pskl P0 /\ exists Θ1',
    Θ1 = (β ~ abind_tvar) ++ Θ1' /\ e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1'.
Proof.
  intros * Hd. inversion Hd; subst.
  split; [ assumption | split; [ assumption | eauto ] ].
Qed.

Lemma e_sub_flex_inv_var_typ : forall S0 NM M P0 Θ0 Ξ α x A Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((x ~ abind_var_typ A) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists Θ1', Θ1 = (x ~ abind_var_typ A) ++ Θ1' /\
    e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1'.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma e_sub_flex_inv_var_skl : forall S0 NM M P0 Θ0 Ξ α x Qp Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((x ~ abind_var_skl Qp) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists Θ1', Θ1 = (x ~ abind_var_skl Qp) ++ Θ1' /\
    e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1'.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

