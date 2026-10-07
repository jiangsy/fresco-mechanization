(** COUNTEREXAMPLE (historical, machine-checked): with the ORIGINAL
    SYNTACTIC-MIDDLE information increase, the OPTIMALITY half of
    [thm:complete-consistency] (part 3, assignment; part 2 through
    Flex-Flex-Skip') is FALSE.

    ------------------------------------------------------------------------
    STATUS.  Found 2026-07-15; the mechanization has since ADOPTED the fix —
    GMM-style SEMANTIC ENTRIES (GundryMM10 §3.1: an increase preserves each
    entry up to the equational theory, never syntactically) — in [a_inc]'s
    var/var_skl rules (algo/def_meta.v).  This file keeps the refutation
    against a LOCAL COPY of the original rules ([a_inc_syn] below), plus the
    positive twin: under the adopted semantic rules the very same instance
    DOES factor ([cex_zeta_semantic]).  The paper still states the syntactic
    rules (algorithmic.tex:91-121) — see the flagged note after
    thm:complete-consistency (sections/appendices/optimality-cex.tex) and
    docs/PAPER-GAPS.md.

    ------------------------------------------------------------------------
    THE PROBLEM.  Two ingredients of the original definitions conspire:

    1. FLEX MIGRATION.  [Assign-Depend] places a payload flexible [α̂] into
       the pending suffix [Ξ]; [Assign-SkipTmVar] threads [Ξ] BELOW walked
       term binders; [Assign-SolveM] deposits it at the subject's position.
       The migration is FORCED by wf: the deposited definition mentions [α̂].

    2. SYNTACTIC MIDDLES + POSITIONAL WF: the original var rule

           Θ ⊑[κ] Θ'
           --------------------------------
           Θ,x:P ⊑[κ] Θ',x:κP,Ξ

       pins the target's binder payload to the syntactic [κP], and flex
       images must be well-formed in the POSITIONAL REMAINDER.

    A competing solution may solve [α̂] with a name [β1̂] it allocates ABOVE
    the walked binder [y] (legal at [α̂]'s ORIGINAL position); the factoring
    must then reproduce a binder payload mentioning [β1̂] — [ζα̂ = β1̂]
    SYNTACTICALLY — while [α̂] sits BELOW [y] in [Θ₁], out of [β1̂]'s scope.

    PROVENANCE.  The syntactic rules are faithful to Gundry's THESIS
    (Gundry13, Fig. 2.4 — term middles [x : κσ], positional remainder,
    term-variable localities), not to the MSFP paper's per-entry SEMANTIC
    ≼ (GundryMM10 §3.1).  The thesis's own unification moves metavariables
    past term entries (inst-depend/inst-skip-tm, Fig. 2.5), so the same
    configuration arises in plain HM, and its generality proof (Lemma 2.6,
    App. D.1) does not treat those cases — the gap predates this paper.
    See the paper note (sections/appendices/optimality-cex.tex).

    THE INSTANCE (five distinct atoms c, α, y, α, β1):

      Θ₀ = c : α̂→(),  α̂,  y : (),  α̂          P = α̂→()     (assign α̂ ≔ P)
      Θ₁ = c : α̂→(),  y : (),  α̂ ≔ α̂→(),  α̂             (α̂ moved below y)
      κ  = [β1̂/α̂, ()→()/α̂]   into   Θ = c : β1̂→(),  β1̂ ≔ (),  y : ()

    Under [a_inc_syn] no ζ exists ([cex_no_zeta_syn]); under the adopted
    semantic [a_inc], ζ = [()→()/α̂, ()/α̂] factors, using the depth-legal
    representative [()] of [β1̂]'s ≡ᵗ-class ([cex_zeta_semantic]).

    Everything below is Qed and axiom-free. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo.prop_basic.

Set Implicit Arguments.

(* ===================================================================== *)
(*  The ORIGINAL, syntactic-middle information increase (local copy).     *)
(*  Identical to [a_inc] except the var/var_skl middles.                  *)
(* ===================================================================== *)

Inductive a_inc_syn : aenv -> metasubst -> aenv -> Prop :=
| a_inc_syn__empty : forall Ξ,
    a_suffix Ξ ->
    a_inc_syn nil nil Ξ
| a_inc_syn__flex : forall Θ κ Θ' α τ,
    a_inc_syn Θ κ Θ' ->
    a_wf_ptyp Θ' τ ->
    mono_ptyp τ ->
    a_inc_syn ((α ~ abind_flex_mono) ++ Θ) ((α, τ) :: κ) Θ'
| a_inc_syn__flex_def : forall Θ κ Θ' α τ τ',
    a_inc_syn Θ κ Θ' ->
    a_wf_ptyp Θ' τ' ->
    mono_ptyp τ' ->
    {{ Θ' ⊢ τ' ≡ᵗ (msubst_ptyp κ τ) }}a ->
    a_inc_syn ((α ~ abind_flex_mono_def τ) ++ Θ) ((α, τ') :: κ) Θ'
| a_inc_syn__var : forall Θ κ Θ' Ξ x A,
    a_inc_syn Θ κ Θ' ->
    a_suffix Ξ ->
    a_inc_syn ((x ~ abind_var_typ A) ++ Θ) κ
      (Ξ ++ (x ~ abind_var_typ (msubst_ptyp κ A)) ++ Θ')
| a_inc_syn__var_skl : forall Θ κ Θ' Ξ x P,
    a_inc_syn Θ κ Θ' ->
    a_suffix Ξ ->
    a_inc_syn ((x ~ abind_var_skl P) ++ Θ) κ
      (Ξ ++ (x ~ abind_var_skl (msubst_pskl κ P)) ++ Θ')
| a_inc_syn__tvar : forall Θ κ Θ' Ξ α,
    a_inc_syn Θ κ Θ' ->
    a_suffix Ξ ->
    a_inc_syn ((α ~ abind_tvar) ++ Θ) κ (Ξ ++ (α ~ abind_tvar) ++ Θ').

Section Cex.

(* Five distinct names. *)
Variables c α y alpha delta : atom.
Hypothesis Hd1 : c <> α.    Hypothesis Hd2 : c <> y.
Hypothesis Hd3 : c <> alpha.  Hypothesis Hd4 : c <> delta.
Hypothesis Hd5 : α <> y.    Hypothesis Hd6 : α <> alpha.
Hypothesis Hd7 : α <> delta.  Hypothesis Hd8 : y <> alpha.
Hypothesis Hd9 : y <> delta.  Hypothesis Hd10 : alpha <> delta.

(* The assignment payload P = α̂ → () and its guess. *)
Definition Pc : pskl := pskl_arrow (pskl_var_f α) pskl_unit.
Definition tauP : ptyp := ptyp_arrow (ptyp_var_f α) ptyp_unit.

(* The input context  Θ₀ = c : α̂→(), α̂, y : (), α̂. *)
Definition Th0 : aenv :=
  (c ~ abind_var_typ tauP) ++
  (α ~ abind_flex_mono) ++
  (y ~ abind_var_typ ptyp_unit) ++
  (alpha ~ abind_flex_mono) ++ nil.

(* The algorithm's output  Θ₁ = c : α̂→(), y : (), α̂ ≔ α̂→(), α̂. *)
Definition Th1 : aenv :=
  (c ~ abind_var_typ tauP) ++
  (y ~ abind_var_typ ptyp_unit) ++
  (alpha ~ abind_flex_mono_def tauP) ++
  (α ~ abind_flex_mono) ++ nil.

(* The competing solution:  κ = [β1̂/α̂, ()→()/α̂]  into
   Θ = c : β1̂→(), β1̂ ≔ (), y : (). *)
Definition th : metasubst :=
  (α, ptyp_var_f delta) :: (alpha, ptyp_arrow ptyp_unit ptyp_unit) :: nil.
Definition Th : aenv :=
  (c ~ abind_var_typ (ptyp_arrow (ptyp_var_f delta) ptyp_unit)) ++
  (delta ~ abind_flex_mono_def ptyp_unit) ++
  (y ~ abind_var_typ ptyp_unit) ++ nil.

(* ------------------------------------------------------------------ *)
(*  1. The algorithm's run:  {{ Θ₀ ⊲[·] α̂ ≔ P ⊣ Θ₁  (unchanged rules) }}a. *)
(* ------------------------------------------------------------------ *)

Lemma cex_run : {{ Th0 ⊲[ nil ] alpha ≔ Pc ⊣ Th1 }}a.
Proof.
  unfold Th0, Th1.
  (* each re-attaching row now carries the Barendregt output premise *)
  apply a_assign__skip_tm_var;
    [ simpl; clear - Hd1 Hd2 Hd3; fsetdec | ].
  apply a_assign__depend;
    [ auto | unfold Pc; simpl; clear; fsetdec | ].
  simpl. apply a_assign__skip_tm_var;
    [ simpl; clear - Hd5 Hd8; fsetdec | ].
  change ({{ ((alpha ~ abind_flex_mono) ++ nil)
            ⊲[ (α ~ abind_flex_mono) ] alpha ≔ Pc
            ⊣ ((alpha ~ abind_flex_mono_def tauP) ++ nil ++ (α ~ abind_flex_mono) ++ nil) }}a).
  apply a_assign__solve_m.
  - unfold Pc; simpl. clear - Hd6. fsetdec.
  - unfold Pc, tauP.
    change (@nil (atom * abind)) with (@nil (atom * abind) ++ @nil (atom * abind)).
    apply a_guess_mono__arrow;
      [ apply a_guess_mono__var | apply a_guess_mono__unit ].
  - unfold tauP. apply mono_ptyp__arrow;
      [ apply mono_ptyp__var | apply mono_ptyp__unit ].
  - constructor.
  - intros α1 Hα1. simpl in Hα1. exfalso. clear - Hα1. fsetdec.
Qed.

(* ------------------------------------------------------------------ *)
(*  2. The competing solution is genuine: wf target + join.             *)
(* ------------------------------------------------------------------ *)

Lemma cex_wfTh : {{ ⊢ Th }}a.
Proof.
  unfold Th.
  apply a_wf_aenv__var_typ; simpl.
  { clear - Hd2 Hd4. fsetdec. }
  { apply a_wf_ptyp__arrow;
      [ apply a_wf_ptyp__var; right; right; exists ptyp_unit;
        unfold binds; left; reflexivity
      | apply a_wf_ptyp__unit ]. }
  apply a_wf_aenv__flex_def; simpl.
  { clear - Hd9. fsetdec. }
  { apply a_wf_ptyp__unit. }
  { apply mono_ptyp__unit. }
  apply a_wf_aenv__var_typ; simpl.
  { clear. fsetdec. }
  { apply a_wf_ptyp__unit. }
  apply a_wf_aenv__nil.
Qed.

Lemma cex_join :
  {{ empty ⨟ Th ⊢ˢ (pskl_to_uskl (msubst_pskl th Pc))
              ∼ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup th alpha))) }}ad.
Proof.
  unfold Pc, th. simpl.
  destruct (α == α) as [_|]; [ | contradiction ].
  destruct (alpha == α) as [Heq|_]; [ exfalso; auto | ].
  destruct (alpha == alpha) as [_|]; [ | contradiction ].
  simpl.
  apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty).
  - apply ad_pat_consis__flex_l with (τ := ptyp_unit).
    + unfold Th, binds; simpl. right. left. reflexivity.
    + apply ad_pat_consis__unit. clear; fsetdec.
  - apply ad_pat_consis__unit. clear; fsetdec.
  - clear; fsetdec.
Qed.

(* ------------------------------------------------------------------ *)
(*  3. The competing increment, in the ORIGINAL syntactic relation.     *)
(* ------------------------------------------------------------------ *)

Lemma cex_msubst_th_tauP :
  msubst_ptyp th tauP = ptyp_arrow (ptyp_var_f delta) ptyp_unit.
Proof.
  unfold th, tauP. simpl.
  destruct (α == α); [ reflexivity | contradiction ].
Qed.

Lemma cex_inc_syn : a_inc_syn (nil ++ Th0) th Th.
Proof.
  simpl. unfold Th0, Th.
  assert (D : a_inc_syn
              ((c ~ abind_var_typ tauP) ++
               (α ~ abind_flex_mono) ++
               (y ~ abind_var_typ ptyp_unit) ++
               (alpha ~ abind_flex_mono) ++ nil)
              th
              (nil ++
               (c ~ abind_var_typ (msubst_ptyp th tauP)) ++
               (delta ~ abind_flex_mono_def ptyp_unit) ++
               (y ~ abind_var_typ ptyp_unit) ++ nil)).
  2:{ rewrite cex_msubst_th_tauP in D. exact D. }
  apply a_inc_syn__var; [ | constructor ].
  (* α̂ ↦ β1̂ : in scope HERE (above y) *)
  unfold th. apply a_inc_syn__flex.
  2:{ apply a_wf_ptyp__var. right. right. exists ptyp_unit.
      unfold binds; simpl. left. reflexivity. }
  2:{ apply mono_ptyp__var. }
  replace ((delta, abind_flex_mono_def ptyp_unit)
             :: (y ~ abind_var_typ ptyp_unit) ++ nil)
    with ((delta ~ abind_flex_mono_def ptyp_unit) ++
          (y ~ abind_var_typ
                 (msubst_ptyp ((alpha, ptyp_arrow ptyp_unit ptyp_unit) :: nil)
                              ptyp_unit)) ++ nil)
    by reflexivity.
  apply a_inc_syn__var.
  2:{ apply a_suffix__cons; constructor. }
  apply a_inc_syn__flex.
  2:{ apply a_wf_ptyp__arrow; apply a_wf_ptyp__unit. }
  2:{ apply mono_ptyp__arrow; apply mono_ptyp__unit. }
  apply a_inc_syn__empty. constructor.
Qed.

(* ------------------------------------------------------------------ *)
(*  4. NO SYNTACTIC FACTORING EXISTS:  ¬ ∃ζ, a_inc_syn Θ₁ ζ Θ.          *)
(* ------------------------------------------------------------------ *)

Lemma cex_no_zeta_syn : forall ζ, ~ a_inc_syn Th1 ζ Th.
Proof.
  intros ζ Hζ. unfold Th1, Th in Hζ.
  inversion Hζ; subst.
  (* c's middle : Ξ must be nil, and it forces ζα̂ = β1̂ *)
  destruct Ξ as [ | [ac bc] Ξ' ].
  2:{ simpl in H4. inversion H4; subst.
      inversion H5 as [ | ? ? ? Hs' Hb ]; subst. inversion Hb. }
  simpl in H4. inversion H4. subst Θ'.
  (* y-split of the tail increment *)
  inversion H3; subst.
  destruct Ξ as [ | e1 Xi1 ].
  { simpl in H8. inversion H8. }
  destruct Xi1 as [ | e2 Xi2 ].
  2:{ simpl in H8. inversion H8; subst.
      match goal with
      | Hx : Xi2 ++ (y, abind_var_typ ptyp_unit) :: _ = nil |- _ =>
          destruct Xi2; simpl in Hx; inversion Hx
      | Hx : _ :: _ = nil |- _ => inversion Hx
      | Hx : nil = _ :: _ |- _ => inversion Hx
      | Hx : Xi2 ++ _ :: _ = _ |- _ =>
          destruct Xi2; simpl in Hx; inversion Hx
      end. }
  simpl in H8. inversion H8; subst.
  (* α̂-def entry against the EMPTY remainder *)
  inversion H7; subst.
  simpl in H0.
  destruct (α == alpha) as [Heq | _]; [ exfalso; apply Hd6; exact Heq | ].
  (* α̂'s entry against the EMPTY remainder *)
  inversion H6; subst.
  simpl in H0.
  destruct (α == α) as [_ | Hne]; [ | contradiction ].
  match goal with
  | Heqτ : _ = ptyp_var_f delta |- _ => rewrite Heqτ in *
  end.
  assert (Hin : delta `in` ftvar_in_ptyp (ptyp_var_f delta))
    by (simpl; fsetdec).
  match goal with
  | Hwfδ : a_wf_ptyp nil (ptyp_var_f delta) |- _ =>
      pose proof (a_wf_ptyp_ftv_tvarish Hwfδ Hin) as Hbt
  end.
  destruct Hbt as [Hb | [Hb | [t Hb]]]; inversion Hb.
Qed.

(* ------------------------------------------------------------------ *)
(*  5. THE ADOPTED SEMANTIC RULE DISSOLVES IT: the same instance         *)
(*     factors through  ζ = [()→()/α̂, ()/α̂]  — the binder middle is     *)
(*     matched up to ≡ᵗ (β1̂→() ≡ᵗ ()→() since β1̂ ≔ ()).                   *)
(* ------------------------------------------------------------------ *)

Definition zeta_sem : metasubst :=
  (alpha, ptyp_arrow ptyp_unit ptyp_unit) :: (α, ptyp_unit) :: nil.

Lemma cex_zeta_semantic : zeta_sem ∷ Th1 ⊑ Th.
Proof.
  unfold Th1, Th, zeta_sem.
  (* c : middle  β1̂→()  ≡ᵗ  ζ(α̂→()) = ()→()  over the remainder *)
  eapply a_inc__var with (Ξ := nil)
           (A' := ptyp_arrow (ptyp_var_f delta) ptyp_unit);
    [ | | constructor ].
  2:{ unfold tauP. simpl.
      destruct (α == alpha) as [Heq|_]; [ exfalso; auto | ].
      destruct (α == α) as [_|]; [ | contradiction ].
      apply a_tyequiv__arrow;
        [ | apply a_tyequiv__refl; constructor ].
      apply a_tyequiv__flex_def.
      unfold binds; simpl. left. reflexivity. }
  (* y : middle () ≡ᵗ () under the suffix β1̂≔() *)
  eapply a_inc__var with (Ξ := (delta ~ abind_flex_mono_def ptyp_unit))
           (A' := ptyp_unit).
  2:{ simpl. apply a_tyequiv__refl. constructor. }
  2:{ apply a_suffix__cons; constructor. }
  (* α̂ ≔ α̂→() : image ()→(), and ζ(α̂→()) = ()→() *)
  apply a_inc__flex_def.
  2:{ apply a_wf_ptyp__arrow; apply a_wf_ptyp__unit. }
  2:{ apply mono_ptyp__arrow; apply mono_ptyp__unit. }
  2:{ unfold tauP. simpl.
      destruct (α == alpha) as [Heq|_]; [ exfalso; auto | ].
      destruct (α == α) as [_|]; [ | contradiction ].
      apply a_tyequiv__refl. constructor; constructor. }
  (* α̂ : image () *)
  apply a_inc__flex.
  2:{ apply a_wf_ptyp__unit. }
  2:{ apply mono_ptyp__unit. }
  apply a_inc__empty. constructor.
Qed.

(* ------------------------------------------------------------------ *)
(*  6. THE PACKAGED REFUTATION of syntactic-middle optimality: the      *)
(*     algorithm runs, (κ; Θ) is a genuine competing solution (wf +      *)
(*     join + syntactic increment), and no syntactic factoring exists.  *)
(* ------------------------------------------------------------------ *)

Theorem cex_syn_middle_optimality_false :
  {{ Th0 ⊲[ nil ] alpha ≔ Pc ⊣ Th1 }}a /\
  a_inc_syn (nil ++ Th0) th Th /\
  {{ ⊢ Th }}a /\
  ({{ empty ⨟ Th ⊢ˢ (pskl_to_uskl (msubst_pskl th Pc))
              ∼ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup th alpha))) }}ad) /\
  (forall ζ, ~ a_inc_syn Th1 ζ Th).
Proof.
  repeat split.
  - exact cex_run.
  - exact cex_inc_syn.
  - exact cex_wfTh.
  - exact cex_join.
  - exact cex_no_zeta_syn.
Qed.

End Cex.
