(** COUNTEREXAMPLE: the OPTIMALITY half of [thm:complete-consistency]
    (part 3, assignment) is FALSE as stated — machine-checked below.

    ------------------------------------------------------------------------
    THE PROBLEM (paper level).

    Two ingredients of the paper conspire:

    1. FLEX MIGRATION.  [Assign-Depend] moves a payload flexible [X̂] into
       the pending suffix [Ξ]; [Assign-SkipTmVar] threads [Ξ] BELOW walked
       term binders; [Assign-SolveM] deposits it at the subject's position.
       Net effect: [X̂] moves from ABOVE a term binder [y] to BELOW it in
       the algorithm's output context.

    2. SYNTACTIC MIDDLES + POSITIONAL WF in information increase
       (algorithmic.tex:91-121).  The var rule

           Θ ⊑[θ] Θ'
           --------------------------------
           Θ,x:P ⊑[θ] Θ',x:θP,Ξ

       forces the target's binder payload to be SYNTACTICALLY [θP], and the
       flex rule demands each image be well-formed in the POSITIONAL
       REMAINDER of the target (everything below the enclosing splits).

    A competing solution may solve [X̂] with a name [δ̂] it allocates ABOVE
    [y] (legal: at [X̂]'s ORIGINAL position, [δ̂] is in scope).  The factoring
    [ζ : Θ₁ ⊑ Θ] the optimality lemma promises must then reproduce a walked
    binder payload mentioning [δ̂] — so [ζX̂ = δ̂] SYNTACTICALLY — while [X̂]
    now sits BELOW [y] in [Θ₁], where [δ̂] is out of scope.  No ζ exists.

    ------------------------------------------------------------------------
    THE INSTANCE.  Five distinct atoms c, X, y, α, δ.

      Θ₀ = c : X̂→(),  X̂,  y : (),  α̂          P = X̂→()      (assign α̂ ≔ P)

    Algorithm (SkipTmVar c; Depend X̂; SkipTmVar y; SolveM):

      Θ₁ = c : X̂→(),  y : (),  α̂ ≔ X̂→(),  X̂       (X̂ now BELOW y)

    Competing solution θ = [δ̂/X̂, ()→()/α̂] into

      Θ  = c : δ̂→(),  δ̂ ≔ (),  y : ()

    — a valid increment (δ̂ is in scope at X̂'s position, above y), Θ is wf,
    and the join θP ≈ θα̂ holds (δ̂ unfolds to ()).  But any ζ with
    [Θ₁ ⊑[ζ] Θ] must make c's payload [ζX̂→()] equal [δ̂→()], i.e. ζX̂ = δ̂,
    while X̂'s entry in Θ₁ is consumed at a point where the target remainder
    is EMPTY — so ζX̂ must be well-formed in the empty context.  Contradiction.

    ------------------------------------------------------------------------
    BLAST RADIUS.  This refutes [assign_optimal_post] (hence the a_assign
    conjunct of the (OPT) bundle) and the paper's part 3; the same
    construction transported through [Flex-Flex-Skip'] refutes part 2 for
    contexts with term binders.  The three previously-closed unify cases and
    all consis cases with payload-free walks are NOT affected.

    LIKELY FIX (for the authors; NOT applied here — flagged per protocol):
    make information increase's binder middles ≡ᵗ-tolerant, GMM-style
    (Gundry-McBride-McKinna, whose entries carry definitions compared up to
    equivalence, not syntax):

           Θ ⊑[θ] Θ'    Θ' ⊢ P' ≡ θP
           --------------------------------
           Θ,x:P ⊑[θ] Θ',x:P',Ξ

    With that rule ζ may use a depth-legal representative of [δ̂]'s ≡ᵗ-class
    (here: ()), and the counterexample dissolves.  The wf-side conditions and
    soundness proofs survive (they only ever USE the middle up to ≡ᵗ).

    Everything below is Qed and axiom-free. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_consis_complete.

Set Implicit Arguments.

Section Cex.

(* Five distinct names. *)
Variables c X y alpha delta : atom.
Hypothesis Hd1 : c <> X.    Hypothesis Hd2 : c <> y.
Hypothesis Hd3 : c <> alpha.  Hypothesis Hd4 : c <> delta.
Hypothesis Hd5 : X <> y.    Hypothesis Hd6 : X <> alpha.
Hypothesis Hd7 : X <> delta.  Hypothesis Hd8 : y <> alpha.
Hypothesis Hd9 : y <> delta.  Hypothesis Hd10 : alpha <> delta.

(* The assignment payload P = X̂ → (). *)
Definition Pc : pskl := pskl_arrow (pskl_var_f X) pskl_unit.
(* Its guess (a monotype). *)
Definition tauP : ptyp := ptyp_arrow (ptyp_var_f X) ptyp_unit.

(* The input context  Θ₀ = c : X̂→(), X̂, y : (), α̂. *)
Definition Th0 : aenv :=
  (c ~ abind_var_typ tauP) ++
  (X ~ abind_flex_mono) ++
  (y ~ abind_var_typ ptyp_unit) ++
  (alpha ~ abind_flex_mono) ++ nil.

(* The algorithm's output  Θ₁ = c : X̂→(), y : (), α̂ ≔ X̂→(), X̂. *)
Definition Th1 : aenv :=
  (c ~ abind_var_typ tauP) ++
  (y ~ abind_var_typ ptyp_unit) ++
  (alpha ~ abind_flex_mono_def tauP) ++
  (X ~ abind_flex_mono) ++ nil.

(* The algorithm's own (identity) solution witness. *)
Definition th1 : metasubst :=
  (X, ptyp_var_f X) :: (alpha, ptyp_var_f alpha) :: nil.

(* The competing solution:  θ = [δ̂/X̂, ()→()/α̂]  into
   Θ = c : δ̂→(), δ̂ ≔ (), y : (). *)
Definition th : metasubst :=
  (X, ptyp_var_f delta) :: (alpha, ptyp_arrow ptyp_unit ptyp_unit) :: nil.
Definition Th : aenv :=
  (c ~ abind_var_typ (ptyp_arrow (ptyp_var_f delta) ptyp_unit)) ++
  (delta ~ abind_flex_mono_def ptyp_unit) ++
  (y ~ abind_var_typ ptyp_unit) ++ nil.

(* ------------------------------------------------------------------ *)
(*  1. The algorithm's run:  Θ₀ ⊲[∅][·] α̂ ≔ P ⊣ Θ₁.                     *)
(* ------------------------------------------------------------------ *)

Lemma cex_run : Th0 ⊲[ empty ][ nil ] alpha ≔ Pc ⊣ Th1.
Proof.
  unfold Th0, Th1.
  (* SkipTmVar c *)
  apply a_assign__skip_tm_var.
  (* Depend X̂ (X ∈ ftv P) *)
  apply a_assign__depend;
    [ auto | unfold Pc; simpl; clear; fsetdec | ].
  (* SkipTmVar y (Ξ = [X̂] threads through) *)
  simpl. apply a_assign__skip_tm_var.
  (* SolveM at α̂ with Ξ = [X̂], β̄ = · *)
  change (((alpha ~ abind_flex_mono) ++ nil)
            ⊲[ add y (add c empty) ][ (X ~ abind_flex_mono) ] alpha ≔ Pc
            ⊣ ((alpha ~ abind_flex_mono_def tauP) ++ nil ++ (X ~ abind_flex_mono) ++ nil)).
  apply a_assign__solve_m.
  - unfold Pc; simpl. clear - Hd6. fsetdec.
  - unfold Pc, tauP.
    change (@nil (atom * abind)) with (@nil (atom * abind) ++ @nil (atom * abind)).
    apply a_guess_mono__arrow;
      [ apply a_guess_mono__var | apply a_guess_mono__unit ].
  - unfold tauP. apply mono_ptyp__arrow;
      [ apply mono_ptyp__var | apply mono_ptyp__unit ].
  - constructor.
  - intros γ Hγ. simpl in Hγ. exfalso. clear - Hγ. fsetdec.
Qed.

(* ------------------------------------------------------------------ *)
(*  2. The problem-side hypotheses (non-vacuity).                       *)
(* ------------------------------------------------------------------ *)

Lemma cex_wf0 : a_wf_aenv (nil ++ Th0).
Proof.
  simpl. unfold Th0, tauP.
  apply a_wf_aenv__var_typ; simpl.
  { clear - Hd1 Hd2 Hd3. fsetdec. }
  { apply a_wf_ptyp__arrow;
      [ apply a_wf_ptyp__var; right; left; unfold binds; left; reflexivity
      | apply a_wf_ptyp__unit ]. }
  apply a_wf_aenv__flex; simpl.
  { clear - Hd5 Hd6. fsetdec. }
  apply a_wf_aenv__var_typ; simpl.
  { clear - Hd8. fsetdec. }
  { apply a_wf_ptyp__unit. }
  apply a_wf_aenv__flex; simpl.
  { clear. fsetdec. }
  apply a_wf_aenv__nil.
Qed.

Lemma cex_wfP : (nil ++ Th0) ⨟ empty ⊢ₚₛᵃ Pc.
Proof.
  simpl. unfold Pc, Th0.
  apply ad_wf_pskl__arrow.
  - apply ad_wf_pskl__var. right. right. left.
    unfold binds; simpl; right; left; reflexivity.
  - apply ad_wf_pskl__unit.
Qed.

(* ------------------------------------------------------------------ *)
(*  3. The algorithm's own identity solution  Θ₀ ⊑[θ₁] Θ₁.              *)
(* ------------------------------------------------------------------ *)

Lemma cex_id1 : is_id_msubst th1.
Proof.
  unfold th1, is_id_msubst.
  repeat constructor.
Qed.

Lemma cex_msubst_th1_tauP :
  msubst_ptyp th1 tauP = tauP.
Proof.
  unfold th1, tauP. simpl.
  destruct (X == X); [ reflexivity | contradiction ].
Qed.

Lemma cex_inc1 : (nil ++ Th0) ≤[ th1 ] Th1.
Proof.
  simpl. unfold Th0, Th1.
  (* c : the middle payload is θ₁-invariant *)
  assert (D : ((c ~ abind_var_typ tauP) ++
               (X ~ abind_flex_mono) ++
               (y ~ abind_var_typ ptyp_unit) ++
               (alpha ~ abind_flex_mono) ++ nil)
              ≤[ th1 ]
              (nil ++
               (c ~ abind_var_typ (msubst_ptyp th1 tauP)) ++
               (y ~ abind_var_typ ptyp_unit) ++
               (alpha ~ abind_flex_mono_def tauP) ++
               (X ~ abind_flex_mono) ++ nil)).
  2:{ rewrite cex_msubst_th1_tauP in D. exact D. }
  apply a_inc__var; [ | constructor ].
  (* X̂ : identity image, in scope in the target *)
  unfold th1. apply a_inc__flex.
  2:{ apply a_wf_ptyp__var. right. left.
      unfold binds; simpl. right. right. left. reflexivity. }
  2:{ apply mono_ptyp__var. }
  (* y : payload () is substitution-invariant (definitionally) *)
  change ((y ~ abind_var_typ ptyp_unit) ++ (alpha ~ abind_flex_mono) ++ nil
          ≤[ ((alpha, ptyp_var_f alpha) :: nil) ]
          (nil ++
           (y ~ abind_var_typ
                  (msubst_ptyp ((alpha, ptyp_var_f alpha) :: nil) ptyp_unit)) ++
           (alpha ~ abind_flex_mono_def tauP) ++ (X ~ abind_flex_mono) ++ nil)).
  apply a_inc__var; [ | constructor ].
  (* α̂ : identity image onto its own (now defined) entry *)
  apply a_inc__flex.
  2:{ apply a_wf_ptyp__var. right. right. exists tauP.
      unfold binds; simpl. left. reflexivity. }
  2:{ apply mono_ptyp__var. }
  (* the leftover suffix α̂≔τP, X̂ is all-flexible *)
  apply a_inc__empty.
  apply a_suffix__cons; [ apply a_suffix__cons; [ constructor | constructor ] | constructor ].
Qed.

(* ------------------------------------------------------------------ *)
(*  4. The competing solution  (θ; Θ):  increment, wf, join.            *)
(* ------------------------------------------------------------------ *)

Lemma cex_msubst_th_tauP :
  msubst_ptyp th tauP = ptyp_arrow (ptyp_var_f delta) ptyp_unit.
Proof.
  unfold th, tauP. simpl.
  destruct (X == X); [ reflexivity | contradiction ].
Qed.

Lemma cex_inc : (nil ++ Th0) ≤[ th ] Th.
Proof.
  simpl. unfold Th0, Th.
  (* c : payload becomes δ̂→() *)
  assert (D : ((c ~ abind_var_typ tauP) ++
               (X ~ abind_flex_mono) ++
               (y ~ abind_var_typ ptyp_unit) ++
               (alpha ~ abind_flex_mono) ++ nil)
              ≤[ th ]
              (nil ++
               (c ~ abind_var_typ (msubst_ptyp th tauP)) ++
               (delta ~ abind_flex_mono_def ptyp_unit) ++
               (y ~ abind_var_typ ptyp_unit) ++ nil)).
  2:{ rewrite cex_msubst_th_tauP in D. exact D. }
  apply a_inc__var; [ | constructor ].
  (* X̂ ↦ δ̂ : in scope HERE (above y) *)
  unfold th. apply a_inc__flex.
  2:{ apply a_wf_ptyp__var. right. right. exists ptyp_unit.
      unfold binds; simpl. left. reflexivity. }
  2:{ apply mono_ptyp__var. }
  (* y : with the suffix δ̂≔() above it *)
  change ((y ~ abind_var_typ ptyp_unit) ++ (alpha ~ abind_flex_mono) ++ nil
          ≤[ ((alpha, ptyp_arrow ptyp_unit ptyp_unit) :: nil) ]
          ((delta ~ abind_flex_mono_def ptyp_unit) ++
           (y ~ abind_var_typ
                  (msubst_ptyp ((alpha, ptyp_arrow ptyp_unit ptyp_unit) :: nil)
                               ptyp_unit)) ++
           nil)).
  apply a_inc__var.
  2:{ apply a_suffix__cons; constructor. }
  (* α̂ ↦ ()→() : closed monotype *)
  apply a_inc__flex.
  2:{ apply a_wf_ptyp__arrow; apply a_wf_ptyp__unit. }
  2:{ apply mono_ptyp__arrow; apply mono_ptyp__unit. }
  apply a_inc__empty. constructor.
Qed.

Lemma cex_wfTh : a_wf_aenv Th.
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
  empty ⨟ Th ⊨ₛᵃ (pskl_to_uskl (msubst_pskl th Pc))
              ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup th alpha))).
Proof.
  unfold Pc, th. simpl.
  destruct (X == X) as [_|]; [ | contradiction ].
  destruct (alpha == X) as [Heq|_]; [ exfalso; auto | ].
  destruct (alpha == alpha) as [_|]; [ | contradiction ].
  simpl.
  (* uskl: δ̂ → ()   vs   bskl(syn): () → () *)
  apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty).
  - (* δ̂ ≈ () : unfold δ̂'s definition *)
    apply ad_pat_consis__flex_l with (τ := ptyp_unit).
    + unfold Th, binds; simpl. right. left. reflexivity.
    + apply ad_pat_consis__unit. clear; fsetdec.
  - apply ad_pat_consis__unit. clear; fsetdec.
  - clear; fsetdec.
Qed.

(* ------------------------------------------------------------------ *)
(*  5. NO FACTORING EXISTS:  ¬ ∃ζ, Θ₁ ⊑[ζ] Θ.                           *)
(*                                                                      *)
(*  c's middle forces ζX̂ = δ̂ syntactically; X̂'s entry in Θ₁ is consumed *)
(*  against the EMPTY target remainder, where δ̂ is not well-formed.     *)
(* ------------------------------------------------------------------ *)

Lemma cex_no_zeta : forall ζ, ~ (Th1 ≤[ ζ ] Th).
Proof.
  intros ζ Hζ. unfold Th1, Th in Hζ.
  inversion Hζ; subst.
  (* H4 : Ξ ++ c-middle :: Θ' = [c; δ; y]  —  Ξ must be nil *)
  destruct Ξ as [ | [ac bc] Ξ' ].
  2:{ simpl in H4. inversion H4; subst.
      inversion H5 as [ | ? ? ? Hs' Hb ]; subst. inversion Hb. }
  simpl in H4. inversion H4. subst Θ'.
  (* y-split of the tail increment *)
  inversion H3; subst.
  (* H8 : Ξ ++ (y,·)::Θ' = [δ; y]  —  Ξ must be exactly [δ] *)
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
  (* the α̂-entry peels off ζ; X̂'s image is next, and must be δ̂ *)
  simpl in H0.
  destruct (X == alpha) as [Heq | _]; [ exfalso; apply Hd6; exact Heq | ].
  (* X̂'s entry against the EMPTY remainder *)
  inversion H6; subst.
  simpl in H0.
  destruct (X == X) as [_ | Hne]; [ | contradiction ].
  (* δ̂ would have to be well-formed in the EMPTY context — absurd *)
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
(*  6. THE REFUTATION of [assign_optimal_post].                         *)
(* ------------------------------------------------------------------ *)

Theorem cex_assign_optimal_post_false :
  ~ assign_optimal_post empty Th0 nil alpha Pc Th1.
Proof.
  intros Hopt. unfold assign_optimal_post in Hopt.
  destruct (Hopt (a_decls__nil) cex_wf0 cex_wfP th1 th Th
                 cex_id1 cex_inc1 cex_inc cex_wfTh cex_join)
    as [ζ [Hζ _]].
  exact (cex_no_zeta Hζ).
Qed.

End Cex.

(* ------------------------------------------------------------------ *)
(*  Packaged, atom-free statement: the a_assign conjunct of the (OPT)   *)
(*  bundle — [forall ..., a_assign .. -> assign_optimal_post ..] — is   *)
(*  FALSE.  (The run [cex_run] discharges the a_assign premise, and the *)
(*  problem-side hypotheses all hold, so this is a genuine, reachable    *)
(*  refutation, not a vacuity artifact.)                                 *)
(* ------------------------------------------------------------------ *)

Theorem a_assign_optimal_conjunct_false :
  ~ (forall F Θ0 Ξ α P Θ1,
       Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 -> assign_optimal_post F Θ0 Ξ α P Θ1).
Proof.
  intros H.
  destruct (atom_fresh empty) as [c Hc].
  destruct (atom_fresh (singleton c)) as [X HX].
  destruct (atom_fresh (add X (singleton c))) as [y Hy].
  destruct (atom_fresh (add y (add X (singleton c)))) as [alpha Hα].
  destruct (atom_fresh (add alpha (add y (add X (singleton c))))) as [delta Hδ].
  assert (Hd1 : c <> X) by (clear - HX; fsetdec).
  assert (Hd2 : c <> y) by (clear - Hy; fsetdec).
  assert (Hd3 : c <> alpha) by (clear - Hα; fsetdec).
  assert (Hd4 : c <> delta) by (clear - Hδ; fsetdec).
  assert (Hd5 : X <> y) by (clear - Hy; fsetdec).
  assert (Hd6 : X <> alpha) by (clear - Hα; fsetdec).
  assert (Hd7 : X <> delta) by (clear - Hδ; fsetdec).
  assert (Hd8 : y <> alpha) by (clear - Hα; fsetdec).
  assert (Hd9 : y <> delta) by (clear - Hδ; fsetdec).
  assert (Hd10 : alpha <> delta) by (clear - Hδ; fsetdec).
  apply (@cex_assign_optimal_post_false c X y alpha delta
           Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd8 Hd9).
  apply H.
  apply cex_run; auto.
Qed.
