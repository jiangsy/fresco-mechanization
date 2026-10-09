(** ext_algo — campaign level 7: the SPLITTING and SKELETON-INFERENCE
    runners' COMPLETENESS.

    §1  the chain kit these two levels add — [swaps_exp], the dodge
        lemma, and the three chain iterations
    §2  the ROOT INVERSIONS — one per clause of the two runners' dispatch
    §3  the [e_split] flexible row's REALIGNMENT (prop_sub_complete.v §5's
        shape, for the pair [e_split__flex] invents)
    §4  ⭐ [e_split_impl_complete] — [e_split] takes no order argument, so
        the level's first half is a three-row case analysis
    §5  THE MOTIVE for [e_pat]
    §6  THE MAIN INDUCTION — one bullet per clause of the runner
    §7  the headlines, over [e_pat_impl] and the argument-free [e_pat_run]

    ⭐ THE RUNNERS ABOVE SUBTYPING ARE INDEPENDENT.  [e_pat_impl] calls
    [e_sub_impl], [e_split_impl] and itself; [e_typing_impl] calls those
    three and itself.  Neither calls the other, so §8c.4's tagged
    single-block workaround is not needed at this level: each is one
    [Equations] with its own order, and completeness is one order-induction
    per runner.  ⚙ And [e_pat_order] / [e_typing_order] are conjunction-free
    one-constructor orders, so Coq's own [_ind] already DOUBLES every
    recursive premise — prop_sub_complete.v §1's hand-written principle has
    no counterpart here.

    ⭐⭐ WHAT IS NEW ABOVE LEVEL 6, AND IT IS ONE THING: the four abs rows
    bind a TERM variable.  So the chain that realigns a derivation onto the
    runner's rails has to act on the SUBJECT too, which is why prop_pat.v
    §4 states equivariance with [swap_exp] and why §1 below iterates it.

    ⚠️ THE SHAPE FACTS COME FROM THE RULE, NOT FROM AN INVARIANT (§8c.22's
    closing note).  The abs rows' output context really is
    [Ξ ++ (x ~ b) ++ Θ] because the RULE says so, and that is what
    [split_at_key_*_complete] is applied to — transported along the chain,
    exactly as level 6 transported [SI-ForallR]'s [Ξ ++ (α~tvar) ++ Θ1]. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_dec.
Require Import src.fresco.ext_algo.prop_dec.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.prop_guess.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.prop_consis.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.prop_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.prop_solve.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.prop_extract.
Require Import src.fresco.ext_algo.def_sub.
Require Import src.fresco.ext_algo.prop_sub.
Require Import src.fresco.ext_algo.def_pat.
Require Import src.fresco.ext_algo.prop_pat.
Require Import src.fresco.ext_algo.def_order.
Require Import src.fresco.ext_algo.prop_termination.
Require Import src.fresco.ext_algo.prop_solve_det.
Require Import src.fresco.ext_algo.prop_run_invariants.
Require Import src.fresco.ext_algo.def_consis_impl.
Require Import src.fresco.ext_algo.prop_consis_complete.
Require Import src.fresco.ext_algo.def_extract_impl.
Require Import src.fresco.ext_algo.prop_extract_det.
Require Import src.fresco.ext_algo.prop_look_pair.
Require Import src.fresco.ext_algo.def_sub_impl.
Require Import src.fresco.ext_algo.prop_sub_complete.
Require Import src.fresco.ext_algo.def_pat_impl.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §1  THE CHAIN KIT THIS LEVEL ADDS                                     *)
(*                                                                        *)
(*  ⚙ [swaps_exp] belongs beside the rest of the [swaps_*] family          *)
(*  (prop_solve_det.v §2), and sits here for the reason that file's own    *)
(*  §3 header gives for [ptyp_to_pskl_close]: it is the first consumer     *)
(*  that needs it, and adding it upstream rebuilds the whole tower for a   *)
(*  six-line fixpoint.                                                    *)
(* ===================================================================== *)

Fixpoint swaps_exp (ps : list (atom * atom)) (e : exp) : exp :=
  match ps with
  | nil => e
  | (a, b) :: ps' => swaps_exp ps' (swap_exp a b e)
  end.

Lemma swaps_exp_app : forall ps1 ps2 e,
  swaps_exp (ps1 ++ ps2) e = swaps_exp ps2 (swaps_exp ps1 e).
Proof.
  induction ps1 as [ | [a b] ps1 IH ]; intros; simpl; [ reflexivity | ].
  apply IH.
Qed.

(** A subject neither column of the chain touches is fixed — which is what
    every use needs, since the motive's coverage puts the subject's free
    variables (TERM ones included) inside [S0] and every pair dodges [S0]. *)
Lemma swaps_exp_fresh_id : forall ps e,
  (forall a b, In (a, b) ps ->
     a `notin` fvar_in_exp e ∪ ftvar_in_exp e
     /\ b `notin` fvar_in_exp e ∪ ftvar_in_exp e) ->
  swaps_exp ps e = e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros e Hav; simpl; [ reflexivity | ].
  destruct (Hav a b (or_introl eq_refl)) as [Ha Hb].
  rewrite (swap_exp_fresh_id e Ha Hb).
  apply IH. intros a' b' Hin. apply Hav. right. exact Hin.
Qed.

Lemma swaps_exp_open_var : forall ps e x,
  swaps_exp ps (open_exp_wrt_exp e (exp_var_f x))
  = open_exp_wrt_exp (swaps_exp ps e) (exp_var_f (swaps_atom ps x)).
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; [ reflexivity | ].
  rewrite swap_exp_open_var. apply IH.
Qed.

(** ⭐ A chain whose columns all dodge [S] maps the complement of [S] to
    itself — which is how a binder drawn fresh for a LATER supply stays
    fresh for [S0] after the realignment. *)
Lemma swaps_atom_dodge : forall ps (S : atoms) x,
  (forall a b, In (a, b) ps -> a `notin` S /\ b `notin` S) ->
  x `notin` S -> swaps_atom ps x `notin` S.
Proof.
  induction ps as [ | [a b] ps IH ]; intros S x Hav Hx; simpl;
    [ exact Hx | ].
  destruct (Hav a b (or_introl eq_refl)) as [Ha Hb].
  apply IH; [ intros a' b' Hin; apply Hav; right; exact Hin | ].
  unfold swap_atom. destruct (x == a); [ subst; assumption | ].
  destruct (x == b); [ subst; assumption | exact Hx ].
Qed.

(** The two Δ slots of a consistency run are [empty] at every call site
    above the solve layer, and a chain fixes [empty]. *)
Lemma swaps_atoms_empty : forall ps, swaps_atoms ps empty [=] empty.
Proof.
  intros ps. apply swaps_atoms_notin. intros a b _. split; fsetdec.
Qed.

(** The two term-variable markers the abs rows push, transported.  ⚙ The
    [swaps_abind] family (prop_solve_det.v §2b) stops at the three binder
    shapes the SOLVE layer meets; these two are the ones this level pushes. *)
Lemma swaps_abind_var_skl : forall ps P,
  swaps_abind ps (abind_var_skl P) = abind_var_skl (swaps_pskl ps P).
Proof. induction ps as [ | [a b] ps IH ]; intros; simpl; auto. Qed.

Lemma swaps_abind_var_typ : forall ps A,
  swaps_abind ps (abind_var_typ A) = abind_var_typ (swaps_ptyp ps A).
Proof. induction ps as [ | [a b] ps IH ]; intros; simpl; auto. Qed.

Lemma swaps_aenv_one_var_skl : forall ps x P,
  swaps_aenv ps (x ~ abind_var_skl P)
  = (swaps_atom ps x ~ abind_var_skl (swaps_pskl ps P)).
Proof.
  intros. unfold one.
  rewrite swaps_aenv_cons, swaps_abind_var_skl, swaps_aenv_nil. reflexivity.
Qed.

Lemma swaps_aenv_one_var_typ : forall ps x A,
  swaps_aenv ps (x ~ abind_var_typ A)
  = (swaps_atom ps x ~ abind_var_typ (swaps_ptyp ps A)).
Proof.
  intros. unfold one.
  rewrite swaps_aenv_cons, swaps_abind_var_typ, swaps_aenv_nil. reflexivity.
Qed.

Lemma swaps_aenv_cons_var_skl : forall ps x P (Θ : aenv),
  swaps_aenv ps ((x ~ abind_var_skl P) ++ Θ)
  = (swaps_atom ps x ~ abind_var_skl (swaps_pskl ps P)) ++ swaps_aenv ps Θ.
Proof.
  intros. rewrite swaps_aenv_app_dist, swaps_aenv_one_var_skl. reflexivity.
Qed.

(** [swap_notin_eq] along a chain — a binder the derivation drew fresh for
    its own supply is fresh for the transported one. *)
Lemma swaps_notin_eq : forall ps x (S S' : atoms),
  S' [=] swaps_atoms ps S -> x `notin` S -> swaps_atom ps x `notin` S'.
Proof.
  induction ps as [ | [a b] ps IH ]; intros x S S' Heq Hx; simpl in *;
    [ rewrite Heq; exact Hx | ].
  eapply IH; [ exact Heq | ].
  eapply swap_notin_eq; [ reflexivity | exact Hx ].
Qed.

Lemma e_pat_swaps : forall ps S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0) ⊢ˢ[ m ; (swaps_pskl ps P0) ]
       (swaps_exp ps e) ⦂ (swaps_pskl ps Q) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_pat_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_pat_swap (a := a) (b := b) Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

(* ===================================================================== *)
(*  §2  ROOT INVERSIONS — the case backbone                               *)
(*                                                                        *)
(*  One per clause of the two runners' dispatch, each turning a derivation *)
(*  at that shape into the rule's premises — or into [False] where the     *)
(*  runner rejects.  ⭐ THE DISPATCH IS OVERLAP-FREE BY THE SUBJECT: nine  *)
(*  of the ten [e_pat] rows are keyed by the subject's head constructor,   *)
(*  and the two [exp_abs] pairs are separated by [m <> mode_tc] on the     *)
(*  non-check rows.  The only cell with two rules is [exp_var_f], where    *)
(*  the two [AP-Var] rows are separated by the BINDING's payload sort —    *)
(*  and [uniq Θ0] makes that binding unique.                              *)
(* ===================================================================== *)

Lemma e_split_inv_arrow : forall S0 Θ0 P1 P2 Pd Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊲ (pskl_arrow P1 P2) ▹ Pd ⇢ Qd ⊣ Θd }}e ->
  Pd = P1 /\ Qd = P2 /\ Sd = S0 /\ Θd = Θ0.
Proof. intros * H. inversion H; subst. repeat split. Qed.

Lemma e_split_inv_ghost : forall S0 Θ0 Pd Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊲ pskl_ghost ▹ Pd ⇢ Qd ⊣ Θd }}e ->
  Pd = pskl_ghost /\ Qd = pskl_ghost /\ Sd = S0 /\ Θd = Θ0.
Proof. intros * H. inversion H; subst. repeat split. Qed.

Lemma e_split_inv_var : forall S0 Θ0 α Pd Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊲ (pskl_var_f α) ▹ Pd ⇢ Qd ⊣ Θd }}e ->
  exists ad bd Q,
    ad `notin` S0 /\ bd `notin` add ad S0
    /\ Pd = pskl_var_f ad /\ Qd = pskl_var_f bd
    /\ {{ (add bd (add ad S0)) ↝ Sd
          ⊨ ((bd ~ abind_flex_mono) ++ (ad ~ abind_flex_mono) ++ Θ0)
          ⊢[ empty | empty | (pskl_arrow (pskl_var_f ad) (pskl_var_f bd)) ]
            (pskl_var_f α) ∼ Q ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. eauto 10. Qed.

Lemma e_split_inv_unit : forall S0 Θ0 Pd Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊲ pskl_unit ▹ Pd ⇢ Qd ⊣ Θd }}e -> False.
Proof. intros * H. inversion H. Qed.

Lemma e_split_inv_var_b : forall S0 Θ0 n Pd Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊲ (pskl_var_b n) ▹ Pd ⇢ Qd ⊣ Θd }}e -> False.
Proof. intros * H. inversion H. Qed.

Lemma e_split_inv_all_syn : forall S0 Θ0 P Pd Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊲ (pskl_all_syn P) ▹ Pd ⇢ Qd ⊣ Θd }}e -> False.
Proof. intros * H. inversion H. Qed.

Lemma e_split_inv_univ_ghost : forall S0 Θ0 P Pd Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊲ (pskl_univ_ghost P) ▹ Pd ⇢ Qd ⊣ Θd }}e -> False.
Proof. intros * H. inversion H. Qed.

Lemma e_pat_inv_unit : forall S0 m Θ0 P0 Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] exp_unit ⦂ Qd ⊣ Θd }}e ->
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] pskl_unit ⩽ Qd ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. assumption. Qed.

Lemma e_pat_inv_var_b : forall S0 m Θ0 P0 n Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_var_b n) ⦂ Qd ⊣ Θd }}e -> False.
Proof. intros * H. inversion H. Qed.

Lemma e_pat_inv_var : forall S0 m Θ0 P0 x Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_var_f x) ⦂ Qd ⊣ Θd }}e ->
  (exists A, binds x (abind_var_typ A) Θ0
     /\ {{ S0 ↝ Sd ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ]
           (ptyp_to_pskl A) ⩽ Qd ⊣ Θd }}e)
  \/ (exists P, binds x (abind_var_skl P) Θ0
     /\ {{ S0 ↝ Sd ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] P ⩽ Qd ⊣ Θd }}e).
Proof. intros * H. inversion H; subst; eauto. Qed.

Lemma e_pat_inv_anno : forall S0 m Θ0 P0 e1 A Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_anno e1 A) ⦂ Qd ⊣ Θd }}e ->
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ]
     (ptyp_to_pskl A) ⩽ Qd ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. assumption. Qed.

Lemma e_pat_inv_freeze : forall S0 m Θ0 P0 e1 Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_freeze e1) ⦂ Qd ⊣ Θd }}e ->
  m = mode_tc /\ P0 = pskl_ghost
  /\ {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ mode_ti ; pskl_ghost ] e1 ⦂ Qd ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. repeat split. assumption. Qed.

(** ⭐ THE TWO abs CELLS, AS ONE DISJUNCTION.  The runner splits [exp_abs]
    by MODE and the rules by [m <> mode_tc]; stating the inversion as a
    disjunction lets each mode branch kill the wrong disjunct by
    [congruence] WITHOUT first having to produce the mode inequality — and
    the check disjunct hands back [P0 = pskl_ghost], which is what makes the
    [mode_tc] branch's clause reachable at all. *)
Lemma e_pat_inv_abs_all : forall S0 m Θ0 P0 e1 Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_abs e1) ⦂ Qd ⊣ Θd }}e ->
  (m <> mode_tc /\
   exists x S1 Θ1 Θ2 P Q0 Q Ξ,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}e
     /\ a_suffix Ξ /\ x `notin` S1
     /\ {{ (add x S1) ↝ Sd ⊨ ((x ~ abind_var_skl P) ++ Θ1)
           ⊢ˢ[ (decr_mode m) ; Q0 ]
           (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ Q
           ⊣ (Ξ ++ (x ~ abind_var_skl P) ++ Θ2) }}e
     /\ Qd = pskl_arrow P Q /\ Θd = Ξ ++ Θ2)
  \/ (m = mode_tc /\ P0 = pskl_ghost /\
      exists x Θ1 Q Ξ,
        a_suffix Ξ /\ x `notin` S0
        /\ {{ (add x S0) ↝ Sd ⊨ ((x ~ abind_var_skl pskl_ghost) ++ Θ0)
              ⊢ˢ[ mode_tc ; pskl_ghost ]
              (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ Q
              ⊣ (Ξ ++ (x ~ abind_var_skl pskl_ghost) ++ Θ1) }}e
        /\ Qd = pskl_univ_ghost (pskl_arrow pskl_ghost Q) /\ Θd = Ξ ++ Θ1).
Proof.
  intros * H. inversion H; subst;
    [ left; split; [ assumption | eauto 15 ]
    | right; split; [ reflexivity | split; [ reflexivity | eauto 15 ] ] ].
Qed.

Lemma e_pat_inv_abs_anno_all : forall S0 m Θ0 P0 A e1 Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_abs_anno A e1) ⦂ Qd ⊣ Θd }}e ->
  (m <> mode_tc /\
   exists x S1 S2 Θ1 Θ2 Θ3 P Q0 Q Ξ,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}e
     /\ e_consis_chk S1 Θ1 (ptyp_to_pskl A) P S2 Θ2
     /\ a_suffix Ξ /\ x `notin` S2
     /\ {{ (add x S2) ↝ Sd ⊨ ((x ~ abind_var_typ A) ++ Θ2)
           ⊢ˢ[ (decr_mode m) ; Q0 ]
           (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ Q
           ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}e
     /\ Qd = pskl_arrow (ptyp_to_pskl A) Q /\ Θd = Ξ ++ Θ3)
  \/ (m = mode_tc /\ P0 = pskl_ghost /\
      exists x Θ1 Q Ξ,
        a_suffix Ξ /\ x `notin` S0
        /\ {{ (add x S0) ↝ Sd ⊨ ((x ~ abind_var_typ A) ++ Θ0)
              ⊢ˢ[ mode_tc ; pskl_ghost ]
              (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ Q
              ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ1) }}e
        /\ Qd = pskl_univ_ghost (pskl_arrow (ptyp_to_pskl A) Q)
        /\ Θd = Ξ ++ Θ1).
Proof.
  intros * H. inversion H; subst;
    [ left; split; [ assumption | eauto 20 ]
    | right; split; [ reflexivity | split; [ reflexivity | eauto 15 ] ] ].
Qed.

Lemma e_pat_inv_app : forall S0 m Θ0 P0 e1 e2 Qd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_app e1 e2) ⦂ Qd ⊣ Θd }}e ->
  exists S1 Θ1 P1 P,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] e2 ⦂ P1 ⊣ Θ1 }}e
    /\ {{ S1 ↝ Sd ⊨ Θ1 ⊢ˢ[ (mode_fn m) ; (pskl_arrow P1 P0) ] e1
          ⦂ (pskl_arrow P Qd) ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. eauto 10. Qed.

(* ===================================================================== *)
(*  §3  THE [e_split] FLEXIBLE ROW'S REALIGNMENT                          *)
(*                                                                        *)
(*  prop_sub_complete.v §5's shape, for the pair [e_split__flex] invents.  *)
(*  The row draws TWO names in sequence and the runner draws              *)
(*  [supply_fresh S0] and [supply_fresh (add … S0)]; ONE chain realigns    *)
(*  them, and — the lesson §5 records — it is NOT [(ad,a1)::(bd,b1)]: the  *)
(*  first transposition may already have moved [bd] (namely when           *)
(*  [bd = a1], where it lands on [ad]), so the second pair's LEFT column   *)
(*  is [swap_atom ad a1 bd].                                              *)
(* ===================================================================== *)

Lemma e_split_flex_realign : forall S0 Θ0 α Qd Sd Θd ad bd,
  ad `notin` S0 -> bd `notin` add ad S0 ->
  ftvar_in_aenv Θ0 ∪ singleton α [<=] S0 ->
  {{ (add bd (add ad S0)) ↝ Sd
     ⊨ ((bd ~ abind_flex_mono) ++ (ad ~ abind_flex_mono) ++ Θ0)
     ⊢[ empty | empty | (pskl_arrow (pskl_var_f ad) (pskl_var_f bd)) ]
       (pskl_var_f α) ∼ Qd ⊣ Θd }}e ->
  exists ps0 Sd',
    (forall a b, In (a, b) ps0 -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atom ps0 ad = supply_fresh S0
    /\ swaps_atom ps0 bd = supply_fresh (add (supply_fresh S0) S0)
    /\ Sd' [=] swaps_atoms ps0 Sd
    /\ {{ (add (supply_fresh (add (supply_fresh S0) S0))
             (add (supply_fresh S0) S0)) ↝ Sd'
       ⊨ ((supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
          ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0)
       ⊢[ empty | empty
        | (pskl_arrow (pskl_var_f (supply_fresh S0))
             (pskl_var_f (supply_fresh (add (supply_fresh S0) S0)))) ]
         (pskl_var_f α) ∼ (swaps_pskl ps0 Qd) ⊣ (swaps_aenv ps0 Θd) }}e.
Proof.
  intros * Had Hbd Hcov Ds.
  assert (Hswl : forall x y, swap_atom x y x = y).
  { intros x y. unfold swap_atom.
    destruct (x == x) as [_ | Hc]; [ reflexivity | contradiction ]. }
  remember (supply_fresh S0) as a1 eqn:Ea1.
  remember (supply_fresh (add a1 S0)) as b1 eqn:Eb1.
  assert (Ha1 : a1 `notin` S0) by (subst a1; apply supply_fresh_notin).
  assert (Hb1 : b1 `notin` add a1 S0) by (subst b1; apply supply_fresh_notin).
  remember (swap_atom ad a1 bd) as c eqn:Ec.
  assert (Hbdad : bd <> ad) by (clear - Hbd; fsetdec).
  assert (Hc : c `notin` add a1 S0).
  { subst c. unfold swap_atom.
    destruct (bd == ad) as [Hc1 | Hne1]; [ contradiction | ].
    destruct (bd == a1) as [Hc2 | Hne2].
    - assert (Hada1 : ad <> a1) by congruence. clear - Had Hada1. fsetdec.
    - clear - Hbd Hne2. fsetdec. }
  assert (Hav : forall a b, In (a, b) ((ad, a1) :: (c, b1) :: nil) ->
                a `notin` S0 /\ b `notin` S0).
  { intros a b [Heq | [Heq | []]]; inversion Heq; subst;
      solve [ split; assumption
            | split; [ clear - Hc; fsetdec | clear - Hb1; fsetdec ] ]. }
  assert (Hsad : swaps_atom ((ad, a1) :: (c, b1) :: nil) ad = a1).
  { simpl. rewrite Hswl.
    apply swap_atom_other; [ clear - Hc | clear - Hb1 ]; fsetdec. }
  assert (Hsbd : swaps_atom ((ad, a1) :: (c, b1) :: nil) bd = b1).
  { simpl. rewrite <- Ec. rewrite Hswl. reflexivity. }
  assert (Hfixa : forall (x : atom), x `in` S0 ->
            swaps_atom ((ad, a1) :: (c, b1) :: nil) x = x).
  { intros x Hx. apply swaps_atom_notin. intros a b Hin.
    destruct (Hav a b Hin) as [Ha Hb]. split; intros ->; contradiction. }
  assert (HfixΘ : forall (Θ : aenv), ftvar_in_aenv Θ [<=] S0 ->
            swaps_aenv ((ad, a1) :: (c, b1) :: nil) Θ = Θ).
  { intros Θ HΘ. apply swaps_aenv_fresh_id. intros a b Hin.
    destruct (Hav a b Hin) as [Ha Hb]. split; fsetdec. }
  destruct (e_consis_swaps ((ad, a1) :: (c, b1) :: nil) Ds
              (Δ1' := empty) (Δ2' := empty)
              (S0' := add b1 (add a1 S0)))
    as [Sd' [HSd' Ds']].
  { symmetry. apply swaps_atoms_empty. }
  { symmetry. apply swaps_atoms_empty. }
  { rewrite swaps_atoms_add, swaps_atoms_add, Hsad, Hsbd.
    rewrite (swaps_atoms_notin _ _ Hav). reflexivity. }
  exists ((ad, a1) :: (c, b1) :: nil), Sd'.
  split; [ exact Hav | ].
  split; [ subst a1; exact Hsad | ].
  split; [ subst a1 b1; exact Hsbd | ].
  split; [ exact HSd' | ].
  repeat rewrite swaps_aenv_app_dist in Ds'.
  rewrite swaps_aenv_one_flex, swaps_aenv_one_flex in Ds'.
  rewrite swaps_pskl_arrow, swaps_pskl_var_f, swaps_pskl_var_f in Ds'.
  rewrite swaps_pskl_var_f in Ds'.
  rewrite Hsad, Hsbd in Ds'.
  rewrite (Hfixa α) in Ds' by (clear - Hcov; fsetdec).
  rewrite (HfixΘ Θ0) in Ds' by (clear - Hcov; fsetdec).
  subst a1 b1. exact Ds'.
Qed.

(* ⚠️ [Set Implicit Arguments] leaves [Θ0] EXPLICIT — it occurs only under
   [++], which is not a strict position — so pin the whole prefix. *)
Arguments e_split_flex_realign {S0 Θ0 α Qd Sd Θd ad bd} _ _ _ _.

(* ===================================================================== *)
(*  §4  ⭐ [e_split_impl] IS COMPLETE                                      *)
(*                                                                        *)
(*  [e_split_impl] takes NO order argument (its one recursive obligation   *)
(*  is a consistency run, delivered by [e_consis_order_total]), so the     *)
(*  level's first half is a three-row case analysis rather than an         *)
(*  induction.  ⚙ And no [lc_pskl P0] hypothesis is owed: the only test    *)
(*  the runner performs is [defs_mono_ck], the two skeletons it hands the  *)
(*  consistency call being variables.                                     *)
(* ===================================================================== *)

Local Ltac split4 := split; [ | split; [ | split ] ].
Local Ltac split5 := split; [ | split4 ].

Lemma e_split_impl_complete : forall S0 Θ0 P0 Sd Θd Pd Qd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊲ P0 ▹ Pd ⇢ Qd ⊣ Θd }}e ->
  aenv_defs_mono Θ0 -> uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0 ->
  exists r ps,
    e_split_impl S0 Θ0 P0 = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] sp_supply (proj1_sig r)
    /\ swaps_aenv ps Θd = sp_ctx (proj1_sig r)
    /\ swaps_pskl ps Pd = sp_dom (proj1_sig r)
    /\ swaps_pskl ps Qd = sp_cod (proj1_sig r).
Proof.
  intros S0 Θ0 P0 Sd Θd Pd Qd Hd HD Hu Hcov.
  destruct P0 as [ | n0 | α | P1 P2 | B | | P1 ].
  - exfalso. exact (e_split_inv_unit Hd).
  - exfalso. exact (e_split_inv_var_b Hd).
  - (* ⭐ the FLEXIBLE row — the runner's two [supply_fresh] draws *)
    destruct (e_split_inv_var Hd) as [ad [bd [Qc [Had [Hbd [-> [-> Ds]]]]]]].
    assert (Hcov1 : ftvar_in_aenv Θ0 ∪ singleton α [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    destruct (e_split_flex_realign Had Hbd Hcov1 Ds)
      as [ps0 [Sd0 [Hav0 [Hs_ad [Hs_bd [HS0 Ds0]]]]]].
    rewrite e_split_impl_equation_3.
    assert (Hbt : defs_mono_ck Θ0 = true)
      by (apply defs_mono_ck_complete; exact HD).
    destruct (sumbool_of_bool (defs_mono_ck Θ0)) as [Hb | Hb];
      [ cbv beta iota | congruence ].
    (* the two invented names, and the context they extend *)
    pose proof (supply_fresh_notin S0) as Ha1.
    pose proof (supply_fresh_notin (add (supply_fresh S0) S0)) as Hb1.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as HdΘ.
    assert (Ha1d : supply_fresh S0 `notin` dom Θ0)
      by (clear - Ha1 HdΘ Hcov1; fsetdec).
    assert (Hb1d : supply_fresh (add (supply_fresh S0) S0) `notin` dom Θ0)
      by (clear - Hb1 HdΘ Hcov1; fsetdec).
    assert (Hu1 : uniq ((supply_fresh (add (supply_fresh S0) S0)
                           ~ abind_flex_mono)
                        ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0)).
    { simpl_env. apply uniq_cons_3;
        [ apply uniq_cons_3; [ exact Hu | exact Ha1d ]
        | clear - Hb1 Hb1d; simpl; fsetdec ]. }
    assert (HD1 : aenv_defs_mono ((supply_fresh (add (supply_fresh S0) S0)
                                     ~ abind_flex_mono)
                                  ++ (supply_fresh S0 ~ abind_flex_mono)
                                  ++ Θ0)).
    { simpl. constructor; [ apply entry_def_mono_flex | ].
      constructor; [ apply entry_def_mono_flex | exact HD ]. }
    assert (Hcov2 : ftvar_in_aenv
                      ((supply_fresh (add (supply_fresh S0) S0)
                          ~ abind_flex_mono)
                       ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0)
                    ∪ ftvar_in_pskl
                        (pskl_arrow (pskl_var_f (supply_fresh S0))
                           (pskl_var_f
                              (supply_fresh (add (supply_fresh S0) S0))))
                    ∪ ftvar_in_pskl (pskl_var_f α) ∪ empty ∪ empty
                    [<=] add (supply_fresh (add (supply_fresh S0) S0))
                           (add (supply_fresh S0) S0))
      by (clear - Hcov1; simpl; fsetdec).
    match goal with
    | |- context [ e_consis_impl ?d1 ?d2 ?S ?T ?p0 ?p ?h0 ?h1 ?hd ?h ] =>
        destruct (e_consis_impl_complete h0 h1 hd h Ds0 Hu1 Hcov2)
          as [rc [ps1 [Hx [Hav1 [HS1 [HT1 _]]]]]];
        destruct (e_consis_impl d1 d2 S T p0 p h0 h1 hd h)
          as [ [rr Hrr] | ] eqn:Hcl;
        try rewrite Hcl in Hx;
        [ inversion Hx; subst; clear Hx Hcl; cbv beta iota | discriminate ]
    end.
    eexists; exists (ps0 ++ ps1).
    split; [ reflexivity | ].
    (* the chain dodges [S0]: [ps0] by §3, [ps1] by growth *)
    assert (Havc : forall a b, In (a, b) (ps0 ++ ps1) ->
                   a `notin` S0 /\ b `notin` S0).
    { intros a0 b0 Hin. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin]; [ exact (Hav0 _ _ Hin) | ].
      destruct (Hav1 _ _ Hin) as [Hka Hkb]. split; fsetdec. }
    split5.
    + exact Havc.
    + cbn [sp_supply proj1_sig]. rewrite swaps_atoms_app.
      rewrite <- HS1. apply swaps_atoms_cong. symmetry. exact HS0.
    + cbn [sp_ctx proj1_sig]. rewrite swaps_aenv_app. exact HT1.
    + cbn [sp_dom proj1_sig].
      rewrite swaps_pskl_app, ! swaps_pskl_var_f, Hs_ad, swaps_atom_notin;
        [ reflexivity | ].
      intros a0 b0 Hin. destruct (Hav1 _ _ Hin) as [Hka Hkb].
      split; intro Heq0;
        [ apply Hka | apply Hkb ]; rewrite Heq0; clear; fsetdec.
    + cbn [sp_cod proj1_sig].
      rewrite swaps_pskl_app, ! swaps_pskl_var_f, Hs_bd, swaps_atom_notin;
        [ reflexivity | ].
      intros a0 b0 Hin. destruct (Hav1 _ _ Hin) as [Hka Hkb].
      split; intro Heq0;
        [ apply Hka | apply Hkb ]; rewrite Heq0; clear; fsetdec.
  - (* the ARROW row — the runner answers from its input *)
    destruct (e_split_inv_arrow Hd) as [-> [-> [-> ->]]].
    rewrite e_split_impl_equation_4.
    eexists; exists (@nil (atom * atom)).
    split; [ reflexivity | ].
    split5; [ intros ? ? [] | reflexivity | reflexivity
            | reflexivity | reflexivity ].
  - exfalso. exact (e_split_inv_all_syn Hd).
  - (* the HOLE row *)
    destruct (e_split_inv_ghost Hd) as [-> [-> [-> ->]]].
    rewrite e_split_impl_equation_6.
    eexists; exists (@nil (atom * atom)).
    split; [ reflexivity | ].
    split5; [ intros ? ? [] | reflexivity | reflexivity
            | reflexivity | reflexivity ].
  - exfalso. exact (e_split_inv_univ_ghost Hd).
Qed.

(* --------------------------------------------------------------------- *)
(*  §4b  THE DECOMPOSERS, WITH THE EQUATION AS A PREMISE                   *)
(*                                                                         *)
(*  ⚠️ prop_dec.v §6 states each decomposer's converse AT the shape, i.e.    *)
(*  applied to a context/skeleton written out as [Ξ ++ (x ~ b) ++ Θ] or     *)
(*  [pskl_arrow P Q].  What the runner hands them is a RECURSIVE ANSWER'S   *)
(*  projection, which is not syntactically of that shape, and it must NOT   *)
(*  be rewritten into one: the [Equations] obligation sitting in the        *)
(*  branch has a TYPE that mentions it, so the rewrite retypes the          *)
(*  obligation and the [Some] branch stops typechecking (prop_sub_complete  *)
(*  §8c.21's fourth trap).  Restate with the equation as a PREMISE.         *)
(* --------------------------------------------------------------------- *)

Lemma arrow_split_complete_eq : forall P P1 P2,
  P = pskl_arrow P1 P2 ->
  exists r, arrow_split P = Some r /\ proj1_sig r = (P1, P2).
Proof. intros P P1 P2 ->. apply arrow_split_complete. Qed.

Lemma split_at_key_skl_complete_eq : forall x Θ Ξ P Θ',
  Θ = Ξ ++ (x ~ abind_var_skl P) ++ Θ' -> uniq Θ ->
  exists r, split_at_key_skl x Θ = Some r /\ proj1_sig r = (Ξ, P, Θ').
Proof. intros x Θ Ξ P Θ' -> Hu. apply split_at_key_skl_complete. exact Hu. Qed.

(* ⚠️ [Set Implicit Arguments] leaves everything under [++] EXPLICIT (a
   non-rigid position), so the caller would have to count underscores. *)
Arguments split_at_key_skl_complete_eq {x Θ Ξ P Θ'} _ _.

Lemma split_at_key_typ_complete_eq : forall x Θ Ξ A Θ',
  Θ = Ξ ++ (x ~ abind_var_typ A) ++ Θ' -> uniq Θ ->
  exists r, split_at_key_typ x Θ = Some r /\ proj1_sig r = (Ξ, A, Θ').
Proof. intros x Θ Ξ A Θ' -> Hu. apply split_at_key_typ_complete. exact Hu. Qed.

Arguments split_at_key_typ_complete_eq {x Θ Ξ A Θ'} _ _.

(* ===================================================================== *)
(*  §5  THE MOTIVE                                                        *)
(*                                                                        *)
(*  prop_sub_complete.v §6's shape, with the two hypotheses this level     *)
(*  adds and the one it drops.                                            *)
(*                                                                        *)
(*  ⭐ [lc_exp e] AND [lc_aenv Θ0] ARE THE NEW ONES, and each pays for a   *)
(*  runner TEST rather than for a rule: [AP-Anno] tests                    *)
(*  [degree_ptyp_ck 0 A] on an annotation carried by the SUBJECT, and the  *)
(*  two [AP-Var] rows test it on the payload the CONTEXT supplies.  Both   *)
(*  are preserved along the run — §8c.22's (2b) is exactly that fact.      *)
(*  ⚙ There is no [lc]-of-the-counterpart hypothesis: [e_pat]'s output     *)
(*  skeleton is not an input.                                             *)
(* ===================================================================== *)

Definition pat_answer {S0 : supply} {m : mode} {Θ0 : aenv} {P0 : pskl}
    {e : exp} (o : option (sig (pat_spec S0 m Θ0 P0 e)))
    : option pat_result :=
  match o with None => None | Some r => Some (proj1_sig r) end.

Definition pat_complete (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) : Prop :=
  forall (H : e_pat_order S0 m Θ0 P0 e),
    lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
    ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
      [<=] S0 ->
    forall Sd Θd Qd,
      {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Qd ⊣ Θd }}e ->
    exists r ps,
      pat_answer (e_pat_impl S0 m Θ0 P0 e H) = Some r
      /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
      /\ swaps_atoms ps Sd [=] pt_supply r
      /\ swaps_aenv ps Θd = pt_ctx r
      /\ swaps_pskl ps Qd = pt_skel r.

(* ===================================================================== *)
(*  §6  THE MAIN INDUCTION                                                *)
(* ===================================================================== *)

(** Every boolean the runner tests, discharged from the motive's own
    hypotheses.  ⚠️⚠️ [apply andb_true_intro] unifies up to DELTA, so the
    LEAF alternative has to be tried FIRST (prop_sub_complete.v §7's trap). *)
Local Ltac ck_leaf_pat :=
  solve [ apply defs_mono_ck_complete; assumption
        | apply lc_pskl_ck_complete; assumption
        | apply lc_ptyp_ck_complete; assumption
        | apply suffix_ck_complete; assumption
        | apply pskl_eqb_complete; reflexivity
        | apply ptyp_eqb_complete; reflexivity ].

Local Ltac ck_true_pat :=
  repeat (ck_leaf_pat || (apply andb_true_intro; split)).

Local Ltac bool_true_pat :=
  match goal with
  | |- context [ sumbool_of_bool ?b ] =>
      let Hbt := fresh "Hbt" in let Hb := fresh "Hb" in
      assert (Hbt : b = true) by ck_true_pat;
      destruct (sumbool_of_bool b) as [Hb | Hb];
      [ cbv beta iota | congruence ]
  end.

(** Run level 6's headline at the subtyping call the goal contains, then
    read the runner's answer off the same call. *)
Local Ltac kill_sub Hder Hu0 Hcov0 r Hr ps Hav HS HT HQ :=
  match goal with
  | |- context [ e_sub_impl ?S ?nm ?mm ?p0 ?T ?p ?hp ?hp0 ?hd ?h ] =>
      let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
      let rr := fresh "rr" in
      destruct (e_sub_impl_complete hp hp0 hd h Hder Hu0 Hcov0)
        as [r [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_sub_impl S nm mm p0 T p hp hp0 hd h)
        as [ [rr Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx;
      [ inversion Hx; subst; clear Hx Hcl; cbv beta iota | discriminate ]
  end.

(** The same for a RECURSIVE call: run the motive premise at the call's own
    inputs, then read the answer off the call. *)
(** ⚠️ The equation the motive returns is between the RESULT RECORDS, not
    between the [sig]s, and the [subst] that identifies them must go in the
    direction that keeps the name the caller passed — hence the explicit
    [subst r0] rather than a bare [subst]. *)
Local Ltac kill_pat Hmot Hp0 He0 HΘ0 HD0 Hu0 Hcov0 Hder r Hr ps
    Hav HS HT HQ :=
  match goal with
  | |- context [ e_pat_impl ?S ?mm ?T ?p0 ?ee ?h ] =>
      let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
      let r0 := fresh "r0" in let Heqr := fresh "Heqr" in
      destruct (Hmot h Hp0 He0 HΘ0 HD0 Hu0 Hcov0 _ _ _ Hder)
        as [r0 [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_pat_impl S mm T p0 ee h) as [ [r Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx; cbn [pat_answer proj1_sig] in Hx;
      [ assert (Heqr : r0 = r) by congruence;
        subst r0; clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

(** Read a DECOMPOSER's answer off the goal's own call.  ⚠️ The [match] is
    DEPENDENT, so the scrutinee is DESTRUCTED, never rewritten. *)
Local Ltac kill_dec Hcomp t Ht :=
  let t0 := fresh "t0" in let Hs := fresh "Hs" in
  let Hpr := fresh "Hpr" in let Hcl := fresh "Hcl" in
  let Heq0 := fresh "Heq0" in
  destruct Hcomp as [t0 [Hs Hpr]];
  match type of Hs with
  | ?f = Some _ =>
      destruct f as [ [t Ht] | ] eqn:Hcl;
      try rewrite Hcl in Hs;
      [ injection Hs; intro Heq0; subst t0;
        cbn [proj1_sig] in Hpr; subst t; clear Hs Hcl; cbv beta iota
      | discriminate ]
  end.

(** ⚠️ [lc_exp]'s two binder rows are COFINITE, so their inversion yields a
    FAMILY; the abs rows need it at the runner's own binder.  Select by
    TYPE (prop_run_invariants.v §4c's tactic, verbatim). *)
Local Ltac open_exp_lc x :=
  match goal with
  | Hx : forall _ : _, lc_exp (open_exp_wrt_exp _ (exp_var_f _)) |- _ =>
      exact (Hx x)
  end.

(** A row that answers from its inputs alone: the EMPTY chain. *)
Lemma e_pat_impl_complete_ind : forall S0 m Θ0 P0 e,
  e_pat_order S0 m Θ0 P0 e -> pat_complete S0 m Θ0 P0 e.
Proof.
  intros S0 m Θ0 P0 e H0.
  apply (e_pat_order_ind pat_complete); [ | exact H0 ].
  clear S0 m Θ0 P0 e H0.
  intros S0 m Θ0 P0 e hfz Hfz habs Habs habsa Habsa habsc Habsc
    habsac Habsac happ1 Happ1 happ2 Happ2.
  unfold pat_complete.
  intros H HP0 He HΘ HD Hu Hcov Sd Θd Qd Hd.
  destruct e as [ | n0 | x | e1 | A e1 | e1 e2 | e1 A | e1 ].

  - (* ================= AP-Unit ================= *)
    rewrite e_pat_impl_equation_1.
    pose proof (e_pat_inv_unit Hd) as Ds.
    bool_true_pat.
    assert (Hcovs : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl pskl_unit [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    kill_sub Ds Hu Hcovs r Hr ps Hav HS HT HQ.
    eexists; exists ps.
    split; [ cbn [pat_answer proj1_sig]; reflexivity | ].
    split4; [ exact Hav
            | cbn [pt_supply]; exact HS
            | cbn [pt_ctx]; exact HT
            | cbn [pt_skel]; exact HQ ].

  - (* ============ a bound index is unreachable ============ *)
    exfalso. exact (e_pat_inv_var_b Hd).

  - (* ================= AP-Var, both payload sorts ================= *)
    rewrite e_pat_impl_equation_3.
    destruct (e_pat_inv_var Hd) as [ [A [Hbd Ds]] | [P [Hbd Ds]] ].
    + (* TYPE payload *)
      assert (HA : lc_ptyp A) by (exact (lc_aenv_binds HΘ Hbd)).
      destruct (lookup_binding_complete _ _ _ Hu Hbd) as [[b Hb] [Hlk Hpr]].
      simpl in Hpr; subst b.
      rewrite Hlk. cbv beta iota.
      destruct (abind_var_typ_get_complete A) as [[A' HA'] [Hgt Hgpr]].
      simpl in Hgpr; subst A'.
      rewrite Hgt. cbv beta iota.
      bool_true_pat.
      pose proof (@ftvar_in_aenv_binds_ftv _ _ _ Hbd) as Hbf. simpl in Hbf.
      pose proof (ftvar_ptyp_to_pskl A) as HAe.
      assert (Hcovs : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0
                      ∪ ftvar_in_pskl (ptyp_to_pskl A) [<=] S0)
        by (clear - Hcov Hbf HAe; simpl in *; fsetdec).
      kill_sub Ds Hu Hcovs r Hr ps Hav HS HT HQ.
      eexists; exists ps.
      split; [ cbn [pat_answer proj1_sig]; reflexivity | ].
      split4; [ exact Hav
              | cbn [pt_supply]; exact HS
              | cbn [pt_ctx]; exact HT
              | cbn [pt_skel]; exact HQ ].
    + (* SKELETON payload *)
      assert (HA : lc_pskl P) by (exact (lc_aenv_binds HΘ Hbd)).
      destruct (lookup_binding_complete _ _ _ Hu Hbd) as [[b Hb] [Hlk Hpr]].
      simpl in Hpr; subst b.
      rewrite Hlk. cbv beta iota.
      destruct (abind_var_skl_get_complete P) as [[P' HP'] [Hgt Hgpr]].
      simpl in Hgpr; subst P'.
      rewrite Hgt. cbv beta iota.
      bool_true_pat.
      pose proof (@ftvar_in_aenv_binds_ftv _ _ _ Hbd) as Hbf. simpl in Hbf.
      assert (Hcovs : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0
                      ∪ ftvar_in_pskl P [<=] S0)
        by (clear - Hcov Hbf; simpl in *; fsetdec).
      kill_sub Ds Hu Hcovs r Hr ps Hav HS HT HQ.
      eexists; exists ps.
      split; [ cbn [pat_answer proj1_sig]; reflexivity | ].
      split4; [ exact Hav
              | cbn [pt_supply]; exact HS
              | cbn [pt_ctx]; exact HT
              | cbn [pt_skel]; exact HQ ].

  - (* ============ AP-Abs (infer / function) and AP-AbsCheck ============ *)
    assert (Hbody : forall y, lc_exp (open_exp_wrt_exp e1 (exp_var_f y)))
      by (inversion He; subst; assumption).
    destruct m as [ | | m' ];
      [ rewrite e_pat_impl_equation_4 | | rewrite e_pat_impl_equation_12 ].

    2: { (* ---------------- AP-AbsCheck ---------------- *)
      destruct (e_pat_inv_abs_all Hd) as [ [Hm _] | [_ [Hph Hchk]] ];
        [ exfalso; exact (Hm eq_refl) | ].
      subst P0.
      destruct Hchk as [xd [Θ1 [Q [Ξ [Hsuf [Hxd [Db [HQd HΘd]]]]]]]].
      subst Qd Θd.
      rewrite e_pat_impl_equation_10.
      pose proof (supply_fresh_notin S0) as Hsf.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdom0.
      (* the derivation's binder, transposed onto the runner's draw *)
      assert (Hav0 : forall a b, In (a, b) ((xd, supply_fresh S0) :: nil) ->
                     a `notin` S0 /\ b `notin` S0)
        by (intros a0 b0 [Heq0 | []]; inversion Heq0; subst; split; assumption).
      assert (Hsxd : swaps_atom ((xd, supply_fresh S0) :: nil) xd
                     = supply_fresh S0)
        by (simpl; unfold swap_atom;
            destruct (xd == xd); [ reflexivity | congruence ]).
      assert (HfixΘ : forall (X : aenv), ftvar_in_aenv X [<=] S0 ->
                swaps_aenv ((xd, supply_fresh S0) :: nil) X = X)
        by (intros X HX; apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct (Hav0 a0 b0 Hin) as [Hka Hkb]; split; fsetdec).
      assert (Hfixe : forall E, fvar_in_exp E ∪ ftvar_in_exp E [<=] S0 ->
                swaps_exp ((xd, supply_fresh S0) :: nil) E = E)
        by (intros E HE; apply swaps_exp_fresh_id; intros a0 b0 Hin;
            destruct (Hav0 a0 b0 Hin) as [Hka Hkb]; split; fsetdec).
      destruct (e_pat_swaps ((xd, supply_fresh S0) :: nil) Db
                  (S0' := add (supply_fresh S0) S0)) as [Sd1 [HSd1 Db1]].
      { simpl. rewrite swap_atoms_add.
        rewrite (swap_atoms_notin xd (supply_fresh S0) S0)
          by (clear - Hxd Hsf; fsetdec).
        unfold swap_atom. destruct (xd == xd); [ reflexivity | congruence ]. }
      rewrite swaps_aenv_cons_var_skl, Hsxd, swaps_pskl_ghost in Db1.
      rewrite (HfixΘ Θ0) in Db1 by (clear - Hcov; simpl in *; fsetdec).
      rewrite swaps_exp_open_var, Hsxd in Db1.
      rewrite (Hfixe e1) in Db1 by (clear - Hcov; simpl in *; fsetdec).
      rewrite swaps_aenv_app_dist, swaps_aenv_cons_var_skl, Hsxd,
        swaps_pskl_ghost in Db1.
      (* the recursive call's own side conditions *)
      assert (Hsfd : supply_fresh S0 `notin` dom Θ0)
        by (clear - Hsf Hdom0 Hcov; simpl in *; fsetdec).
      assert (Hu1 : uniq ((supply_fresh S0 ~ abind_var_skl pskl_ghost) ++ Θ0))
        by (clear - Hu Hsfd; solve_uniq).
      assert (HΘ1 : lc_aenv ((supply_fresh S0 ~ abind_var_skl pskl_ghost)
                             ++ Θ0))
        by (apply lc_aenv_app_intro;
            [ constructor; [ apply lc_abind_var_skl; apply lc_pskl_ghost
                           | apply lc_aenv_nil ]
            | exact HΘ ]).
      assert (HD1 : aenv_defs_mono ((supply_fresh S0 ~ abind_var_skl pskl_ghost)
                                    ++ Θ0))
        by (simpl; constructor; [ apply entry_def_mono_var_skl | exact HD ]).
      assert (Hcov1 : ftvar_in_aenv ((supply_fresh S0
                                        ~ abind_var_skl pskl_ghost) ++ Θ0)
                      ∪ ftvar_in_pskl pskl_ghost
                      ∪ fvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh S0)))
                      ∪ ftvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh S0)))
                      [<=] add (supply_fresh S0) S0).
      { pose proof (fvar_in_exp_open_exp_wrt_exp_upper e1
                      (exp_var_f (supply_fresh S0))) as Hfo.
        pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e1
                      (exp_var_f (supply_fresh S0))) as Hto.
        clear - Hcov Hfo Hto. simpl in *. fsetdec. }
      kill_pat (Habsc e1 eq_refl) lc_pskl_ghost (Hbody (supply_fresh S0))
        HΘ1 HD1 Hu1 Hcov1 Db1 r Hr ps2 Hav2 HS2 HT2 HQ2.
      (* the recursive answer's context, split at the runner's own marker *)
      destruct (e_pat_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]].
      assert (Hfix2a : swaps_atom ps2 (supply_fresh S0) = supply_fresh S0).
      { apply swaps_atom_notin. intros a0 b0 Hin.
        destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
        split; intro Heq0; [ apply Hka | apply Hkb ];
          rewrite <- Heq0; clear; fsetdec. }
      assert (Hctx : pt_ctx r
                = swaps_aenv (((xd, supply_fresh S0) :: nil) ++ ps2) Ξ
                  ++ (supply_fresh S0 ~ abind_var_skl pskl_ghost)
                  ++ swaps_aenv (((xd, supply_fresh S0) :: nil) ++ ps2) Θ1).
      { rewrite <- HT2. rewrite ! swaps_aenv_app.
        rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_skl.
        rewrite Hfix2a, swaps_pskl_ghost. reflexivity. }
      kill_dec (split_at_key_skl_complete_eq Hctx Hur) t Ht.
      cbn [fst snd].
      assert (Hsufr : a_suffix
                (swaps_aenv (((xd, supply_fresh S0) :: nil) ++ ps2) Ξ))
        by (rewrite swaps_aenv_app; apply a_suffix_swaps;
            apply a_suffix_swaps; exact Hsuf).
      bool_true_pat.
      eexists; exists (((xd, supply_fresh S0) :: nil) ++ ps2).
      split; [ cbn [pat_answer proj1_sig]; reflexivity | ].
      split4.
      - intros a0 b0 Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin]; [ exact (Hav0 _ _ Hin) | ].
        destruct (Hav2 _ _ Hin) as [Hka Hkb]. split; fsetdec.
      - cbn [pt_supply]. rewrite swaps_atoms_app. rewrite <- HS2.
        apply swaps_atoms_cong. symmetry. exact HSd1.
      - cbn [pt_ctx]. rewrite swaps_aenv_app_dist. reflexivity.
      - cbn [pt_skel].
        rewrite swaps_pskl_univ_ghost, swaps_pskl_arrow, swaps_pskl_ghost.
        rewrite swaps_pskl_app. rewrite HQ2. reflexivity. }

    all: (
      (* ---------------- AP-Abs, at both non-check modes ---------------- *)
      destruct (e_pat_inv_abs_all Hd) as [ [Hm Hdat] | [Hmc _] ];
        [ | discriminate ];
      destruct Hdat as [xd [S1 [Θ1 [Θ2 [P [Q0 [Q [Ξ
        [Dsp [Hsuf [Hxd [Db [HQd HΘd]]]]]]]]]]]]];
      subst Qd Θd;
      (* the SPLIT, at the runner's own call *)
      assert (Hcovsp : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec);
      destruct (e_split_impl_complete Dsp HD Hu Hcovsp)
        as [rs0 [ps1 [Hxs [Hav1 [HS1 [HT1 [HP1 HQ1]]]]]]];
      destruct (e_split_impl S0 Θ0 P0) as [ [rs Hrs] | ] eqn:Hcls;
      try rewrite Hcls in Hxs;
      [ | discriminate ];
      assert (Heqrs : rs0 = exist (split_spec S0 Θ0 P0) rs Hrs)
        by congruence;
      subst rs0; cbn [proj1_sig] in HS1, HT1, HP1, HQ1;
      clear Hxs Hcls; cbv beta iota;
      unfold split_spec in Hrs;
      (* the split's own output invariants *)
      destruct (e_split_sound Hrs Hu Hcovsp) as [Hsa [Hus [Hcvs Hpqs]]];
      pose proof (e_split_defs_mono Hrs HD) as HDs;
      pose proof (e_split_env_lc Hrs HΘ) as HΘs;
      destruct (e_split_lc Hrs HP0) as [Hlcd Hlcc];
      pose proof (e_split_supply_grows Hrs) as Hgrs;
      pose proof (e_split_supply_grows Dsp) as Hgrd;
      pose proof (supply_fresh_notin (sp_supply rs)) as Hsf;
      pose proof (dom_subset_ftvar_in_aenv (sp_ctx rs)) as Hdoms;
      (* the derivation's binder, first along the split's chain … *)
      assert (Hx1S : swaps_atom ps1 xd `notin` sp_supply rs)
        by (eapply swaps_notin_eq; [ symmetry; exact HS1 | exact Hxd ]);
      assert (Hx10 : swaps_atom ps1 xd `notin` S0)
        by (apply swaps_atom_dodge with (S := S0);
            [ exact Hav1 | clear - Hxd Hgrd; fsetdec ]);
      assert (Hfixe1 : swaps_exp ps1 e1 = e1)
        by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
            destruct (Hav1 a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hcov; simpl in *; fsetdec);
      destruct (e_pat_swaps ps1 Db
                  (S0' := add (swaps_atom ps1 xd) (sp_supply rs)))
        as [Sd1 [HSd1 Db1]];
      [ rewrite swaps_atoms_add, HS1; reflexivity | ];
      rewrite swaps_aenv_cons_var_skl, HT1, HP1, HQ1 in Db1;
      rewrite swaps_exp_open_var, Hfixe1 in Db1;
      rewrite swaps_aenv_app_dist, swaps_aenv_cons_var_skl, HP1 in Db1;
      (* … then onto the runner's own [supply_fresh] draw *)
      assert (Hsx1 : swaps_atom ((swaps_atom ps1 xd,
                        supply_fresh (sp_supply rs)) :: nil)
                       (swaps_atom ps1 xd) = supply_fresh (sp_supply rs))
        by (cbn [swaps_atom]; unfold swap_atom;
            destruct (swaps_atom ps1 xd == swaps_atom ps1 xd);
            [ reflexivity | congruence ]);
      assert (HfixCtx : swaps_aenv ((swaps_atom ps1 xd,
                          supply_fresh (sp_supply rs)) :: nil) (sp_ctx rs)
                        = sp_ctx rs)
        by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx1S Hsf Hcvs; fsetdec);
      assert (HfixDom : swaps_pskl ((swaps_atom ps1 xd,
                          supply_fresh (sp_supply rs)) :: nil) (sp_dom rs)
                        = sp_dom rs)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx1S Hsf Hpqs; fsetdec);
      assert (HfixCod : swaps_pskl ((swaps_atom ps1 xd,
                          supply_fresh (sp_supply rs)) :: nil) (sp_cod rs)
                        = sp_cod rs)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx1S Hsf Hpqs; fsetdec);
      assert (Hfixe2 : swaps_exp ((swaps_atom ps1 xd,
                         supply_fresh (sp_supply rs)) :: nil) e1 = e1)
        by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx10 Hsf Hgrs Hcov; simpl in *; fsetdec);
      destruct (e_pat_swaps ((swaps_atom ps1 xd,
                    supply_fresh (sp_supply rs)) :: nil) Db1
                  (S0' := add (supply_fresh (sp_supply rs)) (sp_supply rs)))
        as [Sd2 [HSd2 Db2]];
      [ cbn [swaps_atoms];
        rewrite swap_atoms_add,
          (swap_atoms_notin (swaps_atom ps1 xd)
             (supply_fresh (sp_supply rs)) (sp_supply rs))
            by (clear - Hx1S Hsf; fsetdec);
        unfold swap_atom;
        destruct (swaps_atom ps1 xd == swaps_atom ps1 xd);
        [ reflexivity | congruence ]
      | ];
      rewrite ! swaps_aenv_app_dist in Db2;
      rewrite ! swaps_aenv_one_var_skl in Db2;
      rewrite ! swaps_exp_open_var in Db2;
      rewrite ! Hsx1, ! HfixCtx, ! HfixDom, ! HfixCod, ! Hfixe2 in Db2;
      (* the recursive call's own side conditions *)
      assert (Hsfd : supply_fresh (sp_supply rs) `notin` dom (sp_ctx rs))
        by (clear - Hsf Hdoms Hcvs; fsetdec);
      assert (Hu1 : uniq ((supply_fresh (sp_supply rs)
                             ~ abind_var_skl (sp_dom rs)) ++ sp_ctx rs))
        by (clear - Hus Hsfd; solve_uniq);
      assert (HΘ1 : lc_aenv ((supply_fresh (sp_supply rs)
                                ~ abind_var_skl (sp_dom rs)) ++ sp_ctx rs))
        by (apply lc_aenv_app_intro;
            [ constructor; [ apply lc_abind_var_skl; exact Hlcd
                           | apply lc_aenv_nil ]
            | exact HΘs ]);
      assert (HD1 : aenv_defs_mono ((supply_fresh (sp_supply rs)
                       ~ abind_var_skl (sp_dom rs)) ++ sp_ctx rs))
        by (simpl; constructor; [ apply entry_def_mono_var_skl | exact HDs ]);
      assert (Hcov1 : ftvar_in_aenv ((supply_fresh (sp_supply rs)
                          ~ abind_var_skl (sp_dom rs)) ++ sp_ctx rs)
                      ∪ ftvar_in_pskl (sp_cod rs)
                      ∪ fvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh (sp_supply rs))))
                      ∪ ftvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh (sp_supply rs))))
                      [<=] add (supply_fresh (sp_supply rs)) (sp_supply rs))
        by (pose proof (fvar_in_exp_open_exp_wrt_exp_upper e1
                          (exp_var_f (supply_fresh (sp_supply rs)))) as Hfo;
            pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e1
                          (exp_var_f (supply_fresh (sp_supply rs)))) as Hto;
            clear - Hcov Hfo Hto Hcvs Hpqs Hgrs; simpl in *; fsetdec);
      kill_pat (Habs e1 eq_refl _ _ _ _ Hrs) Hlcc
        (Hbody (supply_fresh (sp_supply rs))) HΘ1 HD1 Hu1 Hcov1 Db2
        r Hr ps2 Hav2 HS2 HT2 HQ2;
      destruct (e_pat_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]];
      assert (Hfix2a : swaps_atom ps2 (supply_fresh (sp_supply rs))
                       = supply_fresh (sp_supply rs))
        by (apply swaps_atom_notin; intros a0 b0 Hin;
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
            split; intro Heq0; [ apply Hka | apply Hkb ];
            rewrite <- Heq0; clear; fsetdec);
      assert (Hfix2P : swaps_pskl ps2 (sp_dom rs) = sp_dom rs)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hpqs; fsetdec);
      (* the answer's context, split at the runner's own marker *)
      assert (Hctx : pt_ctx r
                = swaps_aenv ps2 (swaps_aenv ((swaps_atom ps1 xd,
                      supply_fresh (sp_supply rs)) :: nil)
                      (swaps_aenv ps1 Ξ))
                  ++ (supply_fresh (sp_supply rs)
                        ~ abind_var_skl (sp_dom rs))
                  ++ swaps_aenv ps2 (swaps_aenv ((swaps_atom ps1 xd,
                       supply_fresh (sp_supply rs)) :: nil)
                       (swaps_aenv ps1 Θ2)))
        by (rewrite <- HT2;
            rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_skl;
            rewrite Hfix2a, Hfix2P; reflexivity);
      kill_dec (split_at_key_skl_complete_eq Hctx Hur) t Ht;
      cbn [fst snd];
      assert (Hsufr : a_suffix (swaps_aenv ps2
                (swaps_aenv ((swaps_atom ps1 xd,
                   supply_fresh (sp_supply rs)) :: nil)
                   (swaps_aenv ps1 Ξ))))
        by (repeat apply a_suffix_swaps; exact Hsuf);
      bool_true_pat;
      eexists;
      exists ((ps1 ++ ((swaps_atom ps1 xd,
                supply_fresh (sp_supply rs)) :: nil)) ++ ps2);
      split; [ cbn [pat_answer proj1_sig]; reflexivity | ];
      split4;
      [ intros a0 b0 Hin; repeat (apply in_app_or in Hin;
          destruct Hin as [Hin | Hin]);
        [ exact (Hav1 _ _ Hin)
        | destruct Hin as [Heq0 | []]; inversion Heq0; subst;
          split; [ exact Hx10 | clear - Hsf Hgrs; fsetdec ]
        | destruct (Hav2 _ _ Hin) as [Hka Hkb]; split;
          clear - Hka Hkb Hgrs; fsetdec ]
      | cbn [pt_supply]; rewrite ! swaps_atoms_app; rewrite <- HS2;
        apply swaps_atoms_cong; rewrite HSd2;
        apply swaps_atoms_cong; symmetry; exact HSd1
      | cbn [pt_ctx]; rewrite swaps_aenv_app_dist, ! swaps_aenv_app;
        reflexivity
      | cbn [pt_skel]; rewrite swaps_pskl_arrow; f_equal;
        [ rewrite ! swaps_pskl_app, HP1, HfixDom; exact Hfix2P
        | rewrite ! swaps_pskl_app; exact HQ2 ] ]
    ).

  - (* ====== AP-AbsAnno (infer / function) and AP-AbsAnnoCheck ====== *)
    assert (Hbody : forall y, lc_exp (open_exp_wrt_exp e1 (exp_var_f y)))
      by (inversion He; subst; assumption).
    assert (HA : lc_ptyp A) by (inversion He; subst; assumption).
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    destruct m as [ | | m' ];
      [ rewrite e_pat_impl_equation_13 | | rewrite e_pat_impl_equation_21 ].

    2: { (* ---------------- AP-AbsAnnoCheck ---------------- *)
      destruct (e_pat_inv_abs_anno_all Hd) as [ [Hm _] | [_ [Hph Hchk]] ];
        [ exfalso; exact (Hm eq_refl) | ].
      subst P0.
      destruct Hchk as [xd [Θ1 [Q [Ξ [Hsuf [Hxd [Db [HQd HΘd]]]]]]]].
      subst Qd Θd.
      rewrite e_pat_impl_equation_19.
      pose proof (supply_fresh_notin S0) as Hsf.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdom0.
      assert (Hav0 : forall a b, In (a, b) ((xd, supply_fresh S0) :: nil) ->
                     a `notin` S0 /\ b `notin` S0)
        by (intros a0 b0 [Heq0 | []]; inversion Heq0; subst; split; assumption).
      assert (Hsxd : swaps_atom ((xd, supply_fresh S0) :: nil) xd
                     = supply_fresh S0)
        by (cbn [swaps_atom]; unfold swap_atom;
            destruct (xd == xd); [ reflexivity | congruence ]).
      assert (HfixΘ : swaps_aenv ((xd, supply_fresh S0) :: nil) Θ0 = Θ0)
        by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct (Hav0 a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
      assert (HfixA : swaps_ptyp ((xd, supply_fresh S0) :: nil) A = A)
        by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
            destruct (Hav0 a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
      assert (Hfixe : swaps_exp ((xd, supply_fresh S0) :: nil) e1 = e1)
        by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
            destruct (Hav0 a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hcov; simpl in *; fsetdec).
      destruct (e_pat_swaps ((xd, supply_fresh S0) :: nil) Db
                  (S0' := add (supply_fresh S0) S0)) as [Sd1 [HSd1 Db1]].
      { cbn [swaps_atoms]. rewrite swap_atoms_add.
        rewrite (swap_atoms_notin xd (supply_fresh S0) S0)
          by (clear - Hxd Hsf; fsetdec).
        unfold swap_atom. destruct (xd == xd); [ reflexivity | congruence ]. }
      rewrite ! swaps_aenv_app_dist in Db1.
      rewrite ! swaps_aenv_one_var_typ in Db1.
      rewrite ! swaps_exp_open_var in Db1.
      rewrite ! Hsxd, ! HfixΘ, ! HfixA, ! Hfixe, ! swaps_pskl_ghost in Db1.
      (* the recursive call's own side conditions *)
      assert (Hsfd : supply_fresh S0 `notin` dom Θ0)
        by (clear - Hsf Hdom0 Hcov; simpl in *; fsetdec).
      assert (Hu1 : uniq ((supply_fresh S0 ~ abind_var_typ A) ++ Θ0))
        by (clear - Hu Hsfd; solve_uniq).
      assert (HΘ1 : lc_aenv ((supply_fresh S0 ~ abind_var_typ A) ++ Θ0))
        by (apply lc_aenv_app_intro;
            [ constructor; [ apply lc_abind_var_typ; exact HA
                           | apply lc_aenv_nil ]
            | exact HΘ ]).
      assert (HD1 : aenv_defs_mono ((supply_fresh S0 ~ abind_var_typ A)
                                    ++ Θ0))
        by (simpl; constructor; [ apply entry_def_mono_var_typ | exact HD ]).
      assert (Hcov1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_var_typ A)
                                     ++ Θ0)
                      ∪ ftvar_in_pskl pskl_ghost
                      ∪ fvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh S0)))
                      ∪ ftvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh S0)))
                      [<=] add (supply_fresh S0) S0).
      { pose proof (fvar_in_exp_open_exp_wrt_exp_upper e1
                      (exp_var_f (supply_fresh S0))) as Hfo.
        pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e1
                      (exp_var_f (supply_fresh S0))) as Hto.
        clear - Hcov Hfo Hto. simpl in *. fsetdec. }
      kill_pat (Habsac A e1 eq_refl) lc_pskl_ghost (Hbody (supply_fresh S0))
        HΘ1 HD1 Hu1 Hcov1 Db1 r Hr ps2 Hav2 HS2 HT2 HQ2.
      destruct (e_pat_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]].
      assert (Hfix2a : swaps_atom ps2 (supply_fresh S0) = supply_fresh S0).
      { apply swaps_atom_notin. intros a0 b0 Hin.
        destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
        split; intro Heq0; [ apply Hka | apply Hkb ];
          rewrite <- Heq0; clear; fsetdec. }
      assert (Hfix2A : swaps_ptyp ps2 A = A).
      { apply swaps_ptyp_fresh_id. intros a0 b0 Hin.
        destruct (Hav2 a0 b0 Hin) as [Hka Hkb].
        split; clear - Hka Hkb Hcov; simpl in *; fsetdec. }
      assert (Hctx : pt_ctx r
                = swaps_aenv (((xd, supply_fresh S0) :: nil) ++ ps2) Ξ
                  ++ (supply_fresh S0 ~ abind_var_typ A)
                  ++ swaps_aenv (((xd, supply_fresh S0) :: nil) ++ ps2) Θ1).
      { rewrite <- HT2. rewrite ! swaps_aenv_app.
        rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_typ.
        rewrite Hfix2a, Hfix2A. reflexivity. }
      kill_dec (split_at_key_typ_complete_eq Hctx Hur) t Ht.
      cbn [fst snd].
      assert (Hsufr : a_suffix
                (swaps_aenv (((xd, supply_fresh S0) :: nil) ++ ps2) Ξ))
        by (rewrite swaps_aenv_app; repeat apply a_suffix_swaps; exact Hsuf).
      bool_true_pat.
      eexists; exists (((xd, supply_fresh S0) :: nil) ++ ps2).
      split; [ cbn [pat_answer proj1_sig]; reflexivity | ].
      split4.
      - intros a0 b0 Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin]; [ exact (Hav0 _ _ Hin) | ].
        destruct (Hav2 _ _ Hin) as [Hka Hkb]. split; fsetdec.
      - cbn [pt_supply]. rewrite swaps_atoms_app. rewrite <- HS2.
        apply swaps_atoms_cong. symmetry. exact HSd1.
      - cbn [pt_ctx]. rewrite swaps_aenv_app_dist. reflexivity.
      - cbn [pt_skel].
        rewrite swaps_pskl_univ_ghost, swaps_pskl_arrow.
        rewrite (swaps_pskl_fresh_id _ (ptyp_to_pskl A));
          [ | intros a0 b0 Hin; apply in_app_or in Hin;
              destruct Hin as [Hin | Hin];
              [ destruct (Hav0 _ _ Hin) as [Hka Hkb]
              | destruct (Hav2 _ _ Hin) as [Hka Hkb] ];
              split; clear - Hka Hkb Hcov HAe; simpl in *; fsetdec ].
        rewrite swaps_pskl_app. rewrite HQ2. reflexivity. }

    all: (
      (* ------------- AP-AbsAnno, at both non-check modes ------------- *)
      destruct (e_pat_inv_abs_anno_all Hd) as [ [Hm Hdat] | [Hmc _] ];
        [ | discriminate ];
      destruct Hdat as [xd [S1 [S2 [Θ1 [Θ2 [Θ3 [P [Q0 [Q [Ξ
        [Dsp [Dch [Hsuf [Hxd [Db [HQd HΘd]]]]]]]]]]]]]]]];
      subst Qd Θd;
      destruct Dch as [Qc Dc];
      (* the SPLIT *)
      assert (Hcovsp : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec);
      destruct (e_split_impl_complete Dsp HD Hu Hcovsp)
        as [rs0 [ps1 [Hxs [Hav1 [HS1 [HT1 [HP1 HQ1]]]]]]];
      destruct (e_split_impl S0 Θ0 P0) as [ [rs Hrs] | ] eqn:Hcls;
      try rewrite Hcls in Hxs;
      [ | discriminate ];
      assert (Heqrs : rs0 = exist (split_spec S0 Θ0 P0) rs Hrs)
        by congruence;
      subst rs0; cbn [proj1_sig] in HS1, HT1, HP1, HQ1;
      clear Hxs Hcls; cbv beta iota;
      unfold split_spec in Hrs;
      destruct (e_split_sound Hrs Hu Hcovsp) as [Hsa [Hus [Hcvs Hpqs]]];
      pose proof (e_split_defs_mono Hrs HD) as HDs;
      pose proof (e_split_env_lc Hrs HΘ) as HΘs;
      destruct (e_split_lc Hrs HP0) as [Hlcd Hlcc];
      pose proof (e_split_supply_grows Hrs) as Hgrs;
      pose proof (e_split_supply_grows Dsp) as Hgrd;
      bool_true_pat;
      (* the ANNOTATION's consistency run, transported onto the split's
         answer and then run through level 5's headline *)
      assert (HfixA1 : swaps_pskl ps1 (ptyp_to_pskl A) = ptyp_to_pskl A)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct (Hav1 a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hcov HAe; simpl in *; fsetdec);
      destruct (e_consis_swaps ps1 Dc (Δ1' := empty) (Δ2' := empty)
                  (S0' := sp_supply rs)) as [Sc1 [HSc1 Dc1]];
      [ symmetry; apply swaps_atoms_empty
      | symmetry; apply swaps_atoms_empty
      | symmetry; exact HS1
      | ];
      rewrite HT1, HP1, HfixA1 in Dc1;
      assert (Hcovc : ftvar_in_aenv (sp_ctx rs) ∪ ftvar_in_pskl (sp_dom rs)
                      ∪ ftvar_in_pskl (ptyp_to_pskl A) ∪ empty ∪ empty
                      [<=] sp_supply rs)
        by (clear - Hcvs Hpqs Hcov HAe Hgrs; simpl in *; fsetdec);
      match goal with
      | |- context [ e_consis_impl ?d1 ?d2 ?S ?T ?p0 ?p ?h0 ?h1 ?hd ?h ] =>
          destruct (e_consis_impl_complete h0 h1 hd h Dc1 Hus Hcovc)
            as [rc0 [psc [Hxc [Havc [HSc [HTc HQc]]]]]];
          destruct (e_consis_impl d1 d2 S T p0 p h0 h1 hd h)
            as [ [rc Hrc] | ] eqn:Hclc;
          try rewrite Hclc in Hxc;
          [ | discriminate ];
          assert (Heqrc : rc0 = exist (consis_spec d1 d2 S T p0 p) rc Hrc)
            by congruence;
          subst rc0; cbn [proj1_sig] in HSc, HTc, HQc;
          clear Hxc Hclc; cbv beta iota
      end;
      unfold consis_spec in Hrc;
      destruct ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hrc Hus Hcovc) as [Hca [Huc Hcvc]];
      pose proof (e_consis_defs_mono Hrc HDs) as HDc;
      pose proof (e_consis_env_lc Hrc HΘs) as HΘc;
      pose proof (e_consis_supply_grows Hrc) as Hgrc;
      pose proof (supply_fresh_notin (cs_supply rc)) as Hsf;
      pose proof (dom_subset_ftvar_in_aenv (cs_ctx rc)) as Hdoms;
      (* the derivation's binder, along BOTH chains and onto the draw *)
      assert (HScc : swaps_atoms psc (swaps_atoms ps1 S2) [=] cs_supply rc)
        by (rewrite <- HSc; apply swaps_atoms_cong; symmetry; exact HSc1);
      assert (Hx1S : swaps_atom psc (swaps_atom ps1 xd)
                     `notin` cs_supply rc)
        by (eapply swaps_notin_eq;
            [ symmetry; exact HScc
            | eapply swaps_notin_eq; [ reflexivity | exact Hxd ] ]);
      assert (Hx10 : swaps_atom psc (swaps_atom ps1 xd) `notin` S0)
        by (apply swaps_atom_dodge with (S := S0);
            [ intros a0 b0 Hin; destruct (Havc a0 b0 Hin) as [Hka Hkb];
              split; clear - Hka Hkb Hgrs; fsetdec
            | apply swaps_atom_dodge with (S := S0);
              [ exact Hav1
              | pose proof (e_consis_supply_grows Dc) as Hgc0;
                clear - Hxd Hgrd Hgc0; fsetdec ] ]);
      assert (Hfixe1 : swaps_exp (ps1 ++ psc) e1 = e1)
        by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
            apply in_app_or in Hin; destruct Hin as [Hin | Hin];
            [ destruct (Hav1 a0 b0 Hin) as [Hka Hkb]
            | destruct (Havc a0 b0 Hin) as [Hka Hkb] ];
            split; clear - Hka Hkb Hcov Hgrs; simpl in *; fsetdec);
      assert (HfixA2 : swaps_ptyp (ps1 ++ psc) A = A)
        by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
            apply in_app_or in Hin; destruct Hin as [Hin | Hin];
            [ destruct (Hav1 a0 b0 Hin) as [Hka Hkb]
            | destruct (Havc a0 b0 Hin) as [Hka Hkb] ];
            split; clear - Hka Hkb Hcov Hgrs; simpl in *; fsetdec);
      assert (HfixQ0 : swaps_pskl psc (sp_cod rs) = sp_cod rs)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct (Havc a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hpqs; fsetdec);
      destruct (e_pat_swaps (ps1 ++ psc) Db
                  (S0' := add (swaps_atom psc (swaps_atom ps1 xd))
                            (cs_supply rc))) as [Sd1 [HSd1 Db1]];
      [ rewrite swaps_atoms_app;
        assert (Heq2 : swaps_atoms psc (swaps_atoms ps1 (add xd S2))
                       [=] swaps_atoms psc
                             (add (swaps_atom ps1 xd) (swaps_atoms ps1 S2)))
          by (apply swaps_atoms_cong; apply swaps_atoms_add);
        rewrite Heq2, swaps_atoms_add, HScc; reflexivity
      | ];
      rewrite ! swaps_aenv_app_dist in Db1;
      rewrite ! swaps_aenv_one_var_typ in Db1;
      rewrite ! swaps_exp_open_var in Db1;
      rewrite ! swaps_aenv_app, ! swaps_pskl_app, ! swaps_atom_app,
        ! swaps_ptyp_app in Db1;
      rewrite HQ1, HTc, HfixQ0, Hfixe1 in Db1;
      rewrite ! swaps_ptyp_app in HfixA2;
      rewrite HfixA2 in Db1;
      (* onto the runner's own draw *)
      assert (Hsx1 : swaps_atom ((swaps_atom psc (swaps_atom ps1 xd),
                        supply_fresh (cs_supply rc)) :: nil)
                       (swaps_atom psc (swaps_atom ps1 xd))
                     = supply_fresh (cs_supply rc))
        by (cbn [swaps_atom]; unfold swap_atom;
            destruct (swaps_atom psc (swaps_atom ps1 xd)
                      == swaps_atom psc (swaps_atom ps1 xd));
            [ reflexivity | congruence ]);
      assert (HfixCtx : swaps_aenv ((swaps_atom psc (swaps_atom ps1 xd),
                          supply_fresh (cs_supply rc)) :: nil) (cs_ctx rc)
                        = cs_ctx rc)
        by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx1S Hsf Hcvc; fsetdec);
      assert (HfixCod : swaps_pskl ((swaps_atom psc (swaps_atom ps1 xd),
                          supply_fresh (cs_supply rc)) :: nil) (sp_cod rs)
                        = sp_cod rs)
        by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx1S Hsf Hpqs Hgrc; fsetdec);
      assert (HfixA3 : swaps_ptyp ((swaps_atom psc (swaps_atom ps1 xd),
                         supply_fresh (cs_supply rc)) :: nil) A = A)
        by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx10 Hsf Hgrs Hgrc Hcov; simpl in *; fsetdec);
      assert (Hfixe2 : swaps_exp ((swaps_atom psc (swaps_atom ps1 xd),
                         supply_fresh (cs_supply rc)) :: nil) e1 = e1)
        by (apply swaps_exp_fresh_id; intros a0 b0 Hin;
            destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            split; clear - Hx10 Hsf Hgrs Hgrc Hcov; simpl in *; fsetdec);
      destruct (e_pat_swaps ((swaps_atom psc (swaps_atom ps1 xd),
                    supply_fresh (cs_supply rc)) :: nil) Db1
                  (S0' := add (supply_fresh (cs_supply rc)) (cs_supply rc)))
        as [Sd2 [HSd2 Db2]];
      [ cbn [swaps_atoms];
        rewrite swap_atoms_add,
          (swap_atoms_notin (swaps_atom psc (swaps_atom ps1 xd))
             (supply_fresh (cs_supply rc)) (cs_supply rc))
            by (clear - Hx1S Hsf; fsetdec);
        unfold swap_atom;
        destruct (swaps_atom psc (swaps_atom ps1 xd)
                  == swaps_atom psc (swaps_atom ps1 xd));
        [ reflexivity | congruence ]
      | ];
      rewrite ! swaps_aenv_app_dist in Db2;
      rewrite ! swaps_aenv_one_var_typ in Db2;
      rewrite ! swaps_exp_open_var in Db2;
      rewrite ! Hsx1, ! HfixCtx, ! HfixCod, ! HfixA3, ! Hfixe2 in Db2;
      (* the recursive call's own side conditions *)
      assert (Hsfd : supply_fresh (cs_supply rc) `notin` dom (cs_ctx rc))
        by (clear - Hsf Hdoms Hcvc; fsetdec);
      assert (Hu1 : uniq ((supply_fresh (cs_supply rc)
                             ~ abind_var_typ A) ++ cs_ctx rc))
        by (clear - Huc Hsfd; solve_uniq);
      assert (HΘ1 : lc_aenv ((supply_fresh (cs_supply rc)
                                ~ abind_var_typ A) ++ cs_ctx rc))
        by (apply lc_aenv_app_intro;
            [ constructor; [ apply lc_abind_var_typ; exact HA
                           | apply lc_aenv_nil ]
            | exact HΘc ]);
      assert (HD1 : aenv_defs_mono ((supply_fresh (cs_supply rc)
                       ~ abind_var_typ A) ++ cs_ctx rc))
        by (simpl; constructor; [ apply entry_def_mono_var_typ | exact HDc ]);
      assert (Hcov1 : ftvar_in_aenv ((supply_fresh (cs_supply rc)
                          ~ abind_var_typ A) ++ cs_ctx rc)
                      ∪ ftvar_in_pskl (sp_cod rs)
                      ∪ fvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh (cs_supply rc))))
                      ∪ ftvar_in_exp (open_exp_wrt_exp e1
                           (exp_var_f (supply_fresh (cs_supply rc))))
                      [<=] add (supply_fresh (cs_supply rc)) (cs_supply rc))
        by (pose proof (fvar_in_exp_open_exp_wrt_exp_upper e1
                          (exp_var_f (supply_fresh (cs_supply rc)))) as Hfo;
            pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e1
                          (exp_var_f (supply_fresh (cs_supply rc)))) as Hto;
            clear - Hcov Hfo Hto Hcvc Hpqs Hgrs Hgrc; simpl in *; fsetdec);
      kill_pat (Habsa A e1 eq_refl _ _ _ _ Hrs _ _ _ Hrc) Hlcc
        (Hbody (supply_fresh (cs_supply rc))) HΘ1 HD1 Hu1 Hcov1 Db2
        r Hr ps2 Hav2 HS2 HT2 HQ2;
      destruct (e_pat_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]];
      assert (Hfix2a : swaps_atom ps2 (supply_fresh (cs_supply rc))
                       = supply_fresh (cs_supply rc))
        by (apply swaps_atom_notin; intros a0 b0 Hin;
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
            split; intro Heq0; [ apply Hka | apply Hkb ];
            rewrite <- Heq0; clear; fsetdec);
      assert (Hfix2A : swaps_ptyp ps2 A = A)
        by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
            destruct (Hav2 a0 b0 Hin) as [Hka Hkb];
            split; clear - Hka Hkb Hcov Hgrs Hgrc; simpl in *; fsetdec);
      assert (Hctx : pt_ctx r
                = swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom psc (swaps_atom ps1 xd),
                      supply_fresh (cs_supply rc)) :: nil)
                    (swaps_aenv psc (swaps_aenv ps1 Ξ)))
                  ++ (supply_fresh (cs_supply rc) ~ abind_var_typ A)
                  ++ swaps_aenv ps2 (swaps_aenv
                       ((swaps_atom psc (swaps_atom ps1 xd),
                         supply_fresh (cs_supply rc)) :: nil)
                       (swaps_aenv psc (swaps_aenv ps1 Θ3))))
        by (rewrite <- HT2;
            rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_typ;
            rewrite Hfix2a, Hfix2A; reflexivity);
      kill_dec (split_at_key_typ_complete_eq Hctx Hur) t Ht;
      cbn [fst snd];
      assert (Hsufr : a_suffix (swaps_aenv ps2 (swaps_aenv
                ((swaps_atom psc (swaps_atom ps1 xd),
                  supply_fresh (cs_supply rc)) :: nil)
                (swaps_aenv psc (swaps_aenv ps1 Ξ)))))
        by (repeat apply a_suffix_swaps; exact Hsuf);
      bool_true_pat;
      eexists;
      exists (((ps1 ++ psc) ++ ((swaps_atom psc (swaps_atom ps1 xd),
                supply_fresh (cs_supply rc)) :: nil)) ++ ps2);
      split; [ cbn [pat_answer proj1_sig]; reflexivity | ];
      split4;
      [ intros a0 b0 Hin; repeat (apply in_app_or in Hin;
          destruct Hin as [Hin | Hin]);
        [ exact (Hav1 _ _ Hin)
        | destruct (Havc _ _ Hin) as [Hka Hkb]; split;
          clear - Hka Hkb Hgrs; fsetdec
        | destruct Hin as [Heq0 | []]; inversion Heq0; subst;
          split; [ exact Hx10 | clear - Hsf Hgrs Hgrc; fsetdec ]
        | destruct (Hav2 _ _ Hin) as [Hka Hkb]; split;
          clear - Hka Hkb Hgrs Hgrc; fsetdec ]
      | cbn [pt_supply]; rewrite ! swaps_atoms_app; rewrite <- HS2;
        apply swaps_atoms_cong; rewrite HSd2;
        apply swaps_atoms_cong; symmetry;
        rewrite <- swaps_atoms_app; exact HSd1
      | cbn [pt_ctx]; rewrite swaps_aenv_app_dist, ! swaps_aenv_app;
        reflexivity
      | cbn [pt_skel]; rewrite swaps_pskl_arrow; f_equal;
        [ apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          repeat (apply in_app_or in Hin; destruct Hin as [Hin | Hin]);
          [ destruct (Hav1 _ _ Hin) as [Hka Hkb]
          | destruct (Havc _ _ Hin) as [Hka Hkb]
          | destruct Hin as [Heq0 | []]; inversion Heq0; subst;
            pose proof Hx10 as Hka; pose proof Hsf as Hkb
          | destruct (Hav2 _ _ Hin) as [Hka Hkb] ];
          split; clear - Hka Hkb Hcov HAe Hgrs Hgrc; simpl in *; fsetdec
        | rewrite ! swaps_pskl_app; exact HQ2 ] ]
    ).

  - (* ================= AP-App ================= *)
    rewrite e_pat_impl_equation_22.
    destruct (e_pat_inv_app Hd) as [S1 [Θ1 [P1 [P [D1 D2]]]]].
    assert (Hcov1 : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl pskl_ghost
                    ∪ fvar_in_exp e2 ∪ ftvar_in_exp e2 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    assert (He2 : lc_exp e2) by (inversion He; subst; assumption).
    assert (He1 : lc_exp e1) by (inversion He; subst; assumption).
    kill_pat (Happ1 e1 e2 eq_refl) (lc_pskl_ghost) He2 HΘ HD Hu Hcov1 D1
      r2 Hr2 ps1 Hav1 HS1 HT1 HQ1.
    (* the FIRST answer's own invariants — level 5/6's, re-established *)
    destruct (e_pat_sound Hr2 Hu Hcov1) as [Ha2 [Hu2 [Hcv2 Hq2]]].
    pose proof (e_pat_defs_mono Hr2 HD) as HD2.
    destruct (e_pat_lc_env Hr2 lc_pskl_ghost He2 HΘ HD) as [Hlc2 HΘ2].
    pose proof (e_pat_supply_grows Hr2) as Hgr2.
    (* transport the FUNCTION's derivation onto the first answer's rails *)
    assert (HfixP : forall X, ftvar_in_pskl X [<=] S0 ->
              swaps_pskl ps1 X = X)
      by (intros X HX; apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Hka Hkb]; split; fsetdec).
    assert (Hfixe : forall E, fvar_in_exp E ∪ ftvar_in_exp E [<=] S0 ->
              swaps_exp ps1 E = E)
      by (intros E HE; apply swaps_exp_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Hka Hkb]; split; fsetdec).
    destruct (e_pat_swaps ps1 D2 (S0' := pt_supply r2))
      as [Sd2 [HSd2 D2t]]; [ symmetry; exact HS1 | ].
    rewrite HT1 in D2t.
    rewrite swaps_pskl_arrow, HQ1 in D2t.
    rewrite (HfixP P0) in D2t by (clear - Hcov; simpl in *; fsetdec).
    rewrite (Hfixe e1) in D2t by (clear - Hcov; simpl in *; fsetdec).
    rewrite swaps_pskl_arrow in D2t.
    (* the SECOND call's own side conditions *)
    assert (Hcov2 : ftvar_in_aenv (pt_ctx r2)
                    ∪ ftvar_in_pskl (pskl_arrow (pt_skel r2) P0)
                    ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] pt_supply r2)
      by (clear - Hcov Hcv2 Hq2 Hgr2; simpl in *; fsetdec).
    kill_pat (Happ2 e1 e2 eq_refl _ _ _ Hr2)
      (lc_pskl_arrow _ _ Hlc2 HP0) He1 HΘ2 HD2 Hu2 Hcov2 D2t
      r1 Hr1 ps2 Hav2 HS2 HT2 HQ2.
    (* the arrow the function returned, decomposed AT the runner's answer *)
    assert (Hout : pt_skel r1
              = pskl_arrow (swaps_pskl ps2 (swaps_pskl ps1 P))
                  (swaps_pskl ps2 (swaps_pskl ps1 Qd)))
      by (rewrite <- HQ2; rewrite ! swaps_pskl_arrow; reflexivity).
    kill_dec (arrow_split_complete_eq Hout) p Hp.
    cbn [fst snd].
    eexists; exists (ps1 ++ ps2).
    split; [ cbn [pat_answer proj1_sig]; reflexivity | ].
    split4.
    + intros a0 b0 Hin. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin]; [ exact (Hav1 _ _ Hin) | ].
      destruct (Hav2 _ _ Hin) as [Hka Hkb]. split; fsetdec.
    + cbn [pt_supply]. rewrite swaps_atoms_app.
      rewrite <- HS2. apply swaps_atoms_cong. symmetry. exact HSd2.
    + cbn [pt_ctx]. rewrite swaps_aenv_app. exact HT2.
    + cbn [pt_skel]. rewrite swaps_pskl_app. reflexivity.

  - (* ================= AP-Anno ================= *)
    rewrite e_pat_impl_equation_23.
    pose proof (e_pat_inv_anno Hd) as Ds.
    assert (HA : lc_ptyp A) by (inversion He; subst; assumption).
    bool_true_pat.
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    assert (Hcovs : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl (ptyp_to_pskl A) [<=] S0)
      by (clear - Hcov HAe; simpl in *; fsetdec).
    kill_sub Ds Hu Hcovs r Hr ps Hav HS HT HQ.
    eexists; exists ps.
    split; [ cbn [pat_answer proj1_sig]; reflexivity | ].
    split4; [ exact Hav
            | cbn [pt_supply]; exact HS
            | cbn [pt_ctx]; exact HT
            | cbn [pt_skel]; exact HQ ].

  - (* ================= AP-Freeze ================= *)
    destruct (e_pat_inv_freeze Hd) as [-> [-> Db]].
    rewrite e_pat_impl_equation_30.
    assert (He1 : lc_exp e1) by (inversion He; subst; assumption).
    assert (Hcov1 : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl pskl_ghost
                    ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    kill_pat (Hfz e1 eq_refl) lc_pskl_ghost He1 HΘ HD Hu Hcov1 Db
      r Hr ps Hav HS HT HQ.
    eexists; exists ps.
    split; [ cbn [pat_answer proj1_sig]; reflexivity | ].
    split4; [ exact Hav
            | cbn [pt_supply]; exact HS
            | cbn [pt_ctx]; exact HT
            | cbn [pt_skel]; exact HQ ].
Qed.

(* ===================================================================== *)
(*  §7  THE HEADLINES                                                     *)
(*                                                                        *)
(*  prop_sub_complete.v §8's shape.  ⚙ [e_split] has no argument-free      *)
(*  runner to state a second headline over — [e_split_impl] already takes  *)
(*  no domain argument — so §4's lemma IS the splitting headline.          *)
(*                                                                        *)
(*  The side conditions are prop_pat.v §3's, plus the two local-closure    *)
(*  ones §8c.22 supplies: [uniq Θ0], the supply covering the context, the  *)
(*  pattern and the SUBJECT (term variables included), [lc_pskl P0],       *)
(*  [lc_exp e], [lc_aenv Θ0] and [aenv_defs_mono Θ0].                      *)
(* ===================================================================== *)

Corollary e_pat_impl_complete : forall S0 m Θ0 P0 e
    (H : e_pat_order S0 m Θ0 P0 e) Sd Θd Qd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Qd ⊣ Θd }}e ->
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
    [<=] S0 ->
  exists r ps,
    e_pat_impl S0 m Θ0 P0 e H = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] pt_supply (proj1_sig r)
    /\ swaps_aenv ps Θd = pt_ctx (proj1_sig r)
    /\ swaps_pskl ps Qd = pt_skel (proj1_sig r).
Proof.
  intros * Hd HP0 He HΘ HD Hu Hcov.
  pose proof (e_pat_impl_complete_ind (e_pat_order_total S0 m Θ0 P0 e))
    as Hmot.
  destruct (Hmot H HP0 He HΘ HD Hu Hcov Sd Θd Qd Hd)
    as [r0 [ps [Hx [Hav [HS [HT HQ]]]]]].
  destruct (e_pat_impl S0 m Θ0 P0 e H) as [ [rr Hrr] | ] eqn:Hcl;
    try rewrite Hcl in Hx; cbn [pat_answer proj1_sig] in Hx;
    [ | discriminate ].
  assert (Heqr : r0 = rr) by congruence. subst r0.
  eexists; exists ps.
  split; [ reflexivity | ].
  split; [ exact Hav | ]. split; [ exact HS | ].
  split; [ exact HT | exact HQ ].
Qed.

(** ⭐ The skeleton-inference headline, over the argument-free runner of
    def_pat_impl.v §7 — the twin of [e_pat_run_sound]. *)
Theorem e_pat_run_complete : forall S0 m Θ0 P0 e Sd Θd Qd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Qd ⊣ Θd }}e ->
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
    [<=] S0 ->
  exists r ps,
    e_pat_run S0 m Θ0 P0 e = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] pt_supply r
    /\ swaps_aenv ps Θd = pt_ctx r
    /\ swaps_pskl ps Qd = pt_skel r.
Proof.
  intros * Hd HP0 He HΘ HD Hu Hcov. unfold e_pat_run.
  destruct (e_pat_impl_complete (e_pat_order_total S0 m Θ0 P0 e)
              Hd HP0 He HΘ HD Hu Hcov) as [r [ps [Heq [Hav [HS [HT HQ]]]]]].
  rewrite Heq.
  exists (proj1_sig r), ps.
  split; [ reflexivity | ].
  split; [ exact Hav | ]. split; [ exact HS | ].
  split; [ exact HT | exact HQ ].
Qed.
