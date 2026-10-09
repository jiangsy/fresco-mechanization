(** EQUIVARIANCE — the swap kit (DESIGN.md §4.3 ⚙, P7a's K1–K4 replacement).

    ONE uniform renaming primitive for the whole algorithmic layer: the atom
    transposition [swap_atom a b] lifted through the syntax, and per-judgment
    EQUIVARIANCE lemmas ([J args → J (swap args)]).

    Why a transposition and not the substitution-shaped renames the tree
    already has: a swap is a BIJECTION on atoms, so it cannot collapse two
    names — the internal openers/generated names of a derivation (which no
    statement can see, and which exists-fresh rules fix) transport with NO
    side condition: distinctness, [uniq], [binds] and every input-only
    freshness condition [γ ∉ ftvar_in_aenv Θ] are preserved verbatim.  The
    substitution-shaped rename must either hand back an existential avoid-set
    (cluster 4's [a_assign_unify_consis_rename_tvar]) or lean on a decreasing
    measure (cluster 3) — neither of which exists for [a_sub]/[a_sub_flex],
    and neither of which is UNIFORM.  The consumption-shaped renames (a junk
    name renamed away from a delivered run's outputs, its inputs untouched)
    fall out as corollaries: when both atoms avoid a component's free atoms,
    [swap] is the identity on it ([swap_*_fresh_id]).

    LN is untouched: bound variables stay de Bruijn indices; [swap] acts on
    free atoms only and commutes with open/close/subst.

    NB no [Set Implicit Arguments] here, deliberately: the kit's lemmas are
    applied with explicit atom pairs at many call sites, and SIA would make
    every argument of the transport lemmas implicit (they are all inferable
    from the hypothesis), forcing [@]-applications everywhere.

    PROBE SCOPE (2026-08-02): §1–§4 syntax layer + [a_guess_mono]/[a_guess]
    equivariance (§5), as the viability probe for the full pass (look/solve/
    extract, the consis mutual, [a_sub]/[a_sub_flex], then the θ-algebra
    transports). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.ltac_utils.        (* destruct_if — §6's term-binder rows *)
Require Import src.fresco.prop_tag.         (* ⭐ §1's ATOM layer: the
    transposition on atoms and on atom SETS is sort-agnostic, so it is defined
    ONCE, upstream.  It used to be defined here TOO, under the same six names,
    and algo/prop_pat_sub.v imports both files — see prop_tag.v's header. *)
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.

(* ⚙ [Set Implicit Arguments] is SCOPED to §0.  The file deliberately has
   none globally (see the NB in the header), but these three lemmas came
   from files that had it, and their ~70 call sites apply them with every
   argument inferred from the hypothesis. *)
Set Implicit Arguments.

(* ===================================================================== *)
(*  §0  The two skeleton judgements: scoping facts and the wf → scope      *)
(*  bridge.  ⚙ These live HERE, beside [a_wf_ptyp_ftv_binds] /             *)
(*  [a_scope_pskl_ftv_binds] below, because this is the EARLIEST algo      *)
(*  proof file and [a_wf_aenv__var] stores the                             *)
(*  DISCIPLINED [{{ Θ ⨟ ∅ ⊢ₚₛ P }}a] — so every file that inverts a context's *)
(*  term entry needs them, this one included.  ⚠️ algo/prop_basic.v would be the *)
(*  topical home but it IMPORTS this file, so that direction is a cycle.   *)
(* ===================================================================== *)

(** A free variable of a well-formed skeleton is a type variable of the
    context — flexible or rigid ([a_binds_tvar] covers both): every variable
    occurrence is checked against the context, never against [Δ].  This is
    the scoping content of [a_wf_pskl], and the shape every freshness side
    condition is discharged through. *)
Lemma a_wf_pskl_ftv_binds : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ.
Proof.
  intros Θ Δ P H; induction H; intros β Hβ; simpl in Hβ.
  - fsetdec.
  - assert (β = α) by fsetdec. subst. auto.
  - destruct (union_1 Hβ); auto.
  - pick fresh α2 for (L `union` ftvar_in_pskl P `union` {{β}}).
    assert (HZL : α2 `notin` L) by fsetdec.
    assert (HY' : β `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α2))).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α2)).
      fsetdec. }
    assert (Hne : β <> α2) by fsetdec.
    destruct (H0 α2 HZL β HY') as [Hb | [Hb | [τ Hb]]];
      apply binds_cons_1 in Hb; destruct Hb as [[? ?] | Hb];
      try (subst; contradiction);
      [ left | right; left | right; right; exists τ ]; exact Hb.
  - fsetdec.
  - pose proof (IHa_wf_pskl β Hβ) as Htv.
    apply a_binds_tvar_aenv_minus in Htv. apply Htv.
Qed.

(** The disciplined judgement implies the scoping-only one — the EASY
    direction, and the only one available: [a_wf_pskl] additionally demands a
    [∀◇] body be guarded and well-formed at the EMPTY [Δ], and neither is
    recoverable ([∀α.∀◇.(α→α)] passes [a_scope_pskl] and is well-formed in NO
    context; docs/WF-SIDE-CONDITIONS.md §1).  Stated with a weakening built in
    so one application covers "same context" and "any extension". *)
Lemma a_wf_pskl_to_a_scope_pskl : forall Θ Δ P,
  a_wf_pskl Θ Δ P ->
  forall Θa,
  (forall x b, binds x b Θ -> binds x b Θa) ->
  (forall α, α `in` Δ -> a_binds_tvar α Θa) ->
  a_scope_pskl Θa P.
Proof.
  intros Θ Δ P Hwfd; induction Hwfd; intros Θa Hincl HΔ.
  - apply a_scope_pskl__unit.
  - apply a_scope_pskl__var.
    destruct H as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ];
      apply Hincl; exact Hb.
  - apply a_scope_pskl__arrow;
      [ apply IHHwfd1 | apply IHHwfd2 ]; assumption.
  - apply a_scope_pskl__all with (L := L).
    intros α Hα.
    apply H0; [ exact Hα | | ].
    + intros x b Hb. apply binds_app_iff in Hb. apply binds_app_iff.
      destruct Hb as [Hb | Hb]; [ left; exact Hb | right; apply Hincl; exact Hb ].
    + intros β Hβ. destruct (β == α) as [-> | Hne].
      * left. unfold binds. left. reflexivity.
      * destruct (HΔ β ltac:(clear - Hβ Hne; solve_notin_auto))
          as [Hb | [Hb | [τ Hb]]];
          [ left | right; left | right; right; exists τ ];
          apply binds_cons_3; exact Hb.
  - apply a_scope_pskl__ghost.
  - apply a_scope_pskl__univ_ghost.
    apply IHHwfd.
    + intros x b Hb. apply binds_aenv_minus in Hb. apply Hincl, Hb.
    + intros β Hβ. exfalso. clear - Hβ. fsetdec.
Qed.

(** The same conversion at the shape a context entry actually has: [Δ = ∅] and
    the context unchanged.  This is what [a_wf_aenv__var]'s consumers want —
    every site that used to read the entry's [a_scope_pskl] off the context. *)
Lemma a_scope_pskl_of_wf : forall Θ P,
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  a_scope_pskl Θ P.
Proof.
  intros Θ P H.
  apply (a_wf_pskl_to_a_scope_pskl H);
    [ intros x b Hb; exact Hb
    | intros α Hα; exfalso; clear - Hα; fsetdec ].
Qed.

(** ⭐ Exported as a HINT deliberately.  The conclusion's head is
    [a_scope_pskl], a distinctive one, so the hint fires nowhere else — and it
    lets every site that discharged an entry's [a_scope_pskl] by [eauto] keep
    its script unchanged now that the context stores the disciplined form. *)
#[export] Hint Resolve a_scope_pskl_of_wf : core.

Unset Implicit Arguments.

(* ===================================================================== *)
(*  §1  The atom transposition — the DEFINITION and its spec are upstream  *)
(*  in fresco/prop_tag.v §1 ([swap_atom], [swap_atom_invol],               *)
(*  [swap_atom_other], [swap_atoms], [swap_atoms_spec], …).  What is here  *)
(*  is only what the TYPE-variable side adds.                              *)
(* ===================================================================== *)

Lemma swap_atom_l : forall a b, swap_atom a b a = b.
Proof.
  intros. unfold swap_atom.
  destruct (a == a); [reflexivity | exfalso; apply n; reflexivity].
Qed.

Lemma swap_atom_r : forall a b, swap_atom a b b = a.
Proof.
  intros. unfold swap_atom.
  destruct (b == a); [congruence |].
  destruct (b == b); [reflexivity | exfalso; apply n0; reflexivity].
Qed.

Lemma swap_atom_inj : forall a b x y,
  swap_atom a b x = swap_atom a b y -> x = y.
Proof.
  intros * H.
  rewrite <- (swap_atom_invol a b x), <- (swap_atom_invol a b y), H.
  reflexivity.
Qed.

(** * The DIRECTED rename — the non-primitive sibling of [swap_aenv].

    ⚠️ WHICH TO REACH FOR: [swap_aenv γ β Θ] — the transposition — is THE
    renaming primitive by standing directive, because it is its own inverse and
    so needs no freshness side condition.  [rename_aenv γ β Θ] is DIRECTED (β
    is renamed away, and the caller must keep the TARGET γ fresh); it survives
    only where a proof genuinely needs the one-way form.  Prefer [swap_aenv]
    plus [swap_aenv_as_rename] in new code. *)

Definition rename_abind (γ β : atom) (bd : abind) : abind :=
  match bd with
  | abind_tvar            => abind_tvar
  | abind_var_typ A       => abind_var_typ (subst_ptyp_in_ptyp (ptyp_var_f γ) β A)
  | abind_var_skl P       => abind_var_skl (subst_pskl_in_pskl (pskl_var_f γ) β P)
  | abind_flex_mono       => abind_flex_mono
  | abind_flex_mono_def A => abind_flex_mono_def (subst_ptyp_in_ptyp (ptyp_var_f γ) β A)
  end.

(** [rename_aenv γ β Θ] — rename β to γ throughout Θ: the KEY and the
    PAYLOAD.  β may occur anywhere (it is the name being renamed away);
    it is the TARGET γ that callers must keep fresh. *)
Fixpoint rename_aenv (γ β : atom) (Θ : aenv) : aenv :=
  match Θ with
  | nil           => nil
  | (x, bd) :: Θ' => ((if x == β then γ else x), rename_abind γ β bd)
                       :: rename_aenv γ β Θ'
  end.

(** Local two-way union splitters (small unions only — the ⚙ rule about
    [fsetdec] and big unions does not apply at width 2). *)
Local Lemma notin_union_split : forall (x : atom) (s t : atoms),
  x `notin` (s `union` t) -> x `notin` s /\ x `notin` t.
Proof. intros; split; fsetdec. Qed.

Local Lemma notin_union_join : forall (x : atom) (s t : atoms),
  x `notin` s -> x `notin` t -> x `notin` (s `union` t).
Proof. intros; fsetdec. Qed.

(* ===================================================================== *)
(*  §2  Swap over the syntax                                              *)
(* ===================================================================== *)

Fixpoint swap_ptyp (a b : atom) (A : ptyp) : ptyp :=
  match A with
  | ptyp_unit => ptyp_unit
  | ptyp_var_b n => ptyp_var_b n
  | ptyp_var_f α => ptyp_var_f (swap_atom a b α)
  | ptyp_arrow A1 A2 => ptyp_arrow (swap_ptyp a b A1) (swap_ptyp a b A2)
  | ptyp_all A0 => ptyp_all (swap_ptyp a b A0)
  end.

Fixpoint swap_pskl (a b : atom) (P : pskl) : pskl :=
  match P with
  | pskl_unit => pskl_unit
  | pskl_var_b n => pskl_var_b n
  | pskl_var_f α => pskl_var_f (swap_atom a b α)
  | pskl_arrow P1 P2 => pskl_arrow (swap_pskl a b P1) (swap_pskl a b P2)
  | pskl_all_syn P0 => pskl_all_syn (swap_pskl a b P0)
  | pskl_ghost => pskl_ghost
  | pskl_univ_ghost P0 => pskl_univ_ghost (swap_pskl a b P0)
  end.

Definition swap_abind (a b : atom) (bd : abind) : abind :=
  match bd with
  | abind_tvar => abind_tvar
  | abind_var_typ A => abind_var_typ (swap_ptyp a b A)
  | abind_var_skl P => abind_var_skl (swap_pskl a b P)
  | abind_flex_mono => abind_flex_mono
  | abind_flex_mono_def τ => abind_flex_mono_def (swap_ptyp a b τ)
  end.

Definition swap_aenv (a b : atom) (Θ : aenv) : aenv :=
  List.map (fun e => (swap_atom a b (fst e), swap_abind a b (snd e))) Θ.

(* ---- involutions ---- *)

Lemma swap_ptyp_invol : forall a b A, swap_ptyp a b (swap_ptyp a b A) = A.
Proof.
  induction A; simpl; f_equal; auto using swap_atom_invol.
Qed.

Lemma swap_pskl_invol : forall a b P, swap_pskl a b (swap_pskl a b P) = P.
Proof.
  induction P; simpl; f_equal; auto using swap_atom_invol.
Qed.

Lemma swap_abind_invol : forall a b bd, swap_abind a b (swap_abind a b bd) = bd.
Proof.
  destruct bd; simpl; f_equal; auto using swap_ptyp_invol, swap_pskl_invol.
Qed.

(** The cons interface — rewrite with THIS, never [simpl], on a
    [swap_aenv _ _ (_ :: _)] (or [(x ~ bd) ++ Θ]) term: [simpl] unfolds
    [List.map] into its [fix] body and later rewrites stop matching. *)
Lemma swap_aenv_cons : forall a b x bd (Θ : aenv),
  swap_aenv a b ((x, bd) :: Θ)
  = (swap_atom a b x, swap_abind a b bd) :: swap_aenv a b Θ.
Proof. reflexivity. Qed.

(** The one-entry rigid block a binder rule pushes, swapped. *)
Lemma swap_aenv_one_tvar : forall a b,
  swap_aenv a b (a ~ abind_tvar) = b ~ abind_tvar.
Proof.
  intros a b. unfold swap_aenv, one. simpl.
  rewrite swap_atom_l. reflexivity.
Qed.

Lemma swap_aenv_invol : forall a b Θ, swap_aenv a b (swap_aenv a b Θ) = Θ.
Proof.
  induction Θ as [| [x bd] Θ']; [reflexivity |].
  rewrite !swap_aenv_cons, swap_atom_invol, swap_abind_invol, IHΘ'.
  reflexivity.
Qed.

(* ---- structural distribution ---- *)

Lemma swap_aenv_app : forall a b (Θ1 Θ2 : aenv),
  swap_aenv a b (Θ1 ++ Θ2) = swap_aenv a b Θ1 ++ swap_aenv a b Θ2.
Proof. intros. unfold swap_aenv. apply List.map_app. Qed.

(* ===================================================================== *)
(*  §3  Free-atom transport                                               *)
(* ===================================================================== *)

Lemma swap_ptyp_ftv_in : forall a b A x,
  x `in` ftvar_in_ptyp A ->
  swap_atom a b x `in` ftvar_in_ptyp (swap_ptyp a b A).
Proof.
  intros a b A; induction A; simpl; intros x Hx; try solve [fsetdec | auto].
  - (* var_f *) assert (x = α) by fsetdec. subst. fsetdec.
  - (* arrow *)
    assert (x `in` ftvar_in_ptyp A1 \/ x `in` ftvar_in_ptyp A2) as [h | h]
      by fsetdec;
      [ pose proof (IHA1 x h) | pose proof (IHA2 x h) ]; fsetdec.
Qed.

Lemma swap_pskl_ftv_in : forall a b P x,
  x `in` ftvar_in_pskl P ->
  swap_atom a b x `in` ftvar_in_pskl (swap_pskl a b P).
Proof.
  intros a b P; induction P; simpl; intros x Hx; try solve [fsetdec | auto].
  - (* var_f *) assert (x = α) by fsetdec. subst. fsetdec.
  - (* arrow *)
    assert (x `in` ftvar_in_pskl P1 \/ x `in` ftvar_in_pskl P2) as [h | h]
      by fsetdec;
      [ pose proof (IHP1 x h) | pose proof (IHP2 x h) ]; fsetdec.
Qed.

Lemma swap_ptyp_ftv_notin : forall a b A x,
  x `notin` ftvar_in_ptyp A ->
  swap_atom a b x `notin` ftvar_in_ptyp (swap_ptyp a b A).
Proof.
  intros * Hn Hin. apply Hn.
  pose proof (swap_ptyp_ftv_in a b (swap_ptyp a b A) (swap_atom a b x) Hin)
    as h.
  rewrite swap_ptyp_invol, swap_atom_invol in h. exact h.
Qed.

Lemma swap_pskl_ftv_notin : forall a b P x,
  x `notin` ftvar_in_pskl P ->
  swap_atom a b x `notin` ftvar_in_pskl (swap_pskl a b P).
Proof.
  intros * Hn Hin. apply Hn.
  pose proof (swap_pskl_ftv_in a b (swap_pskl a b P) (swap_atom a b x) Hin)
    as h.
  rewrite swap_pskl_invol, swap_atom_invol in h. exact h.
Qed.

(* ---- fresh-identity: both atoms absent ⇒ swap is the identity ---- *)

Lemma swap_ptyp_fresh_id : forall a b A,
  a `notin` ftvar_in_ptyp A -> b `notin` ftvar_in_ptyp A ->
  swap_ptyp a b A = A.
Proof.
  induction A; simpl; intros Ha Hb; f_equal;
    try solve
      [ reflexivity
      | apply swap_atom_other; intro; subst; fsetdec
      | apply IHA; fsetdec
      | apply IHA1; fsetdec
      | apply IHA2; fsetdec ].
Qed.

Lemma swap_pskl_fresh_id : forall a b P,
  a `notin` ftvar_in_pskl P -> b `notin` ftvar_in_pskl P ->
  swap_pskl a b P = P.
Proof.
  induction P; simpl; intros Ha Hb; f_equal;
    try solve
      [ reflexivity
      | apply swap_atom_other; intro; subst; fsetdec
      | apply IHP; fsetdec
      | apply IHP1; fsetdec
      | apply IHP2; fsetdec ].
Qed.

(* ---- aenv: dom / payload-ftv / binds / uniq transport ---- *)

Lemma swap_aenv_dom_in : forall a b (Θ : aenv) x,
  x `in` dom Θ -> swap_atom a b x `in` dom (swap_aenv a b Θ).
Proof.
  intros a b Θ; induction Θ as [| [y bd] Θ']; simpl; intros x Hx.
  - fsetdec.
  - assert (x = y \/ x `in` dom Θ') as [h | h] by fsetdec.
    + subst. fsetdec.
    + pose proof (IHΘ' x h). fsetdec.
Qed.

Lemma swap_aenv_dom_notin : forall a b (Θ : aenv) x,
  x `notin` dom Θ -> swap_atom a b x `notin` dom (swap_aenv a b Θ).
Proof.
  intros * Hn Hin. apply Hn.
  pose proof (swap_aenv_dom_in a b (swap_aenv a b Θ) (swap_atom a b x) Hin)
    as h.
  rewrite swap_aenv_invol, swap_atom_invol in h. exact h.
Qed.

Lemma swap_abind_ftv_in : forall a b bd x,
  x `in` ftvar_in_abind bd ->
  swap_atom a b x `in` ftvar_in_abind (swap_abind a b bd).
Proof.
  intros; destruct bd; simpl in *;
    auto using swap_ptyp_ftv_in, swap_pskl_ftv_in; fsetdec.
Qed.

Lemma swap_aenv_ftvar_in : forall a b (Θ : aenv) x,
  x `in` ftvar_in_aenv Θ ->
  swap_atom a b x `in` ftvar_in_aenv (swap_aenv a b Θ).
Proof.
  intros a b Θ; induction Θ as [| [y bd] Θ']; simpl; intros x Hx.
  - fsetdec.
  - assert (x = y \/ x `in` ftvar_in_abind bd \/ x `in` ftvar_in_aenv Θ')
      as [h | [h | h]] by fsetdec.
    + subst. fsetdec.
    + pose proof (swap_abind_ftv_in a b bd x h). fsetdec.
    + pose proof (IHΘ' x h). fsetdec.
Qed.

Lemma swap_aenv_ftvar_notin : forall a b (Θ : aenv) x,
  x `notin` ftvar_in_aenv Θ ->
  swap_atom a b x `notin` ftvar_in_aenv (swap_aenv a b Θ).
Proof.
  intros * Hn Hin. apply Hn.
  pose proof (swap_aenv_ftvar_in a b (swap_aenv a b Θ) (swap_atom a b x) Hin)
    as h.
  rewrite swap_aenv_invol, swap_atom_invol in h. exact h.
Qed.

Lemma swap_aenv_binds : forall a b x bd (Θ : aenv),
  binds x bd Θ ->
  binds (swap_atom a b x) (swap_abind a b bd) (swap_aenv a b Θ).
Proof.
  intros a b x bd Θ; unfold binds;
    induction Θ as [| [y byd] Θ']; simpl; intros H.
  - contradiction.
  - destruct H as [Heq | Hin].
    + inversion Heq; subst. left; reflexivity.
    + right; auto.
Qed.

Lemma swap_aenv_uniq : forall a b (Θ : aenv),
  uniq Θ -> uniq (swap_aenv a b Θ).
Proof.
  intros a b Θ H; induction H; simpl.
  - constructor.
  - constructor; auto using swap_aenv_dom_notin.
Qed.

(* ===================================================================== *)
(*  §4  Commutation with open / close and the paintings                   *)
(* ===================================================================== *)

Lemma swap_ptyp_open_rec : forall a b A2 A1 k,
  swap_ptyp a b (open_ptyp_wrt_ptyp_rec k A2 A1)
  = open_ptyp_wrt_ptyp_rec k (swap_ptyp a b A2) (swap_ptyp a b A1).
Proof.
  intros a b A2; induction A1; intros k; simpl;
    try solve [f_equal; auto].
  (* var_b *)
  destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; simpl; auto.
Qed.

Lemma swap_pskl_open_rec : forall a b P2 P1 k,
  swap_pskl a b (open_pskl_wrt_pskl_rec k P2 P1)
  = open_pskl_wrt_pskl_rec k (swap_pskl a b P2) (swap_pskl a b P1).
Proof.
  intros a b P2; induction P1; intros k; simpl;
    try solve [f_equal; auto].
  (* var_b *)
  destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; simpl; auto.
Qed.

Lemma swap_ptyp_open : forall a b A1 A2,
  swap_ptyp a b (open_ptyp_wrt_ptyp A1 A2)
  = open_ptyp_wrt_ptyp (swap_ptyp a b A1) (swap_ptyp a b A2).
Proof. intros. unfold open_ptyp_wrt_ptyp. apply swap_ptyp_open_rec. Qed.

Lemma swap_pskl_open : forall a b P1 P2,
  swap_pskl a b (open_pskl_wrt_pskl P1 P2)
  = open_pskl_wrt_pskl (swap_pskl a b P1) (swap_pskl a b P2).
Proof. intros. unfold open_pskl_wrt_pskl. apply swap_pskl_open_rec. Qed.

Lemma swap_pskl_open_var : forall a b P β,
  swap_pskl a b (open_pskl_wrt_pskl P (pskl_var_f β))
  = open_pskl_wrt_pskl (swap_pskl a b P) (pskl_var_f (swap_atom a b β)).
Proof. intros. apply swap_pskl_open. Qed.

Lemma swap_ptyp_close_rec : forall a b x A k,
  swap_ptyp a b (close_ptyp_wrt_ptyp_rec k x A)
  = close_ptyp_wrt_ptyp_rec k (swap_atom a b x) (swap_ptyp a b A).
Proof.
  intros a b x; induction A; intros k; simpl.
  - reflexivity.
  - (* var_b *) destruct (lt_ge_dec n k); reflexivity.
  - (* var_f — NB the goal's [==] tests carry prop_ln's own instance term,
       so they are destructed by CAPTURE ([if ?t then _ else _]), never by
       re-elaborating the test in this file. *)
    destruct (x == α) as [e | n0].
    + rewrite e. simpl.
      match goal with
      | |- context [if ?t then _ else _] => destruct t as [_ | n1]
      end; [reflexivity | exfalso; apply n1; reflexivity].
    + simpl.
      match goal with
      | |- context [if ?t then _ else _] => destruct t as [e1 | ?]
      end; [exfalso; apply n0; exact (swap_atom_inj a b x α e1) | reflexivity].
  - (* arrow *) f_equal; auto.
  - (* all *) f_equal; auto.
Qed.

Lemma swap_ptyp_close : forall a b x A,
  swap_ptyp a b (close_ptyp_wrt_ptyp x A)
  = close_ptyp_wrt_ptyp (swap_atom a b x) (swap_ptyp a b A).
Proof. intros. unfold close_ptyp_wrt_ptyp. apply swap_ptyp_close_rec. Qed.

Lemma swap_pskl_close_rec : forall a b x P k,
  swap_pskl a b (close_pskl_wrt_pskl_rec k x P)
  = close_pskl_wrt_pskl_rec k (swap_atom a b x) (swap_pskl a b P).
Proof.
  intros a b x; induction P; intros k; simpl.
  - reflexivity.
  - (* var_b *) destruct (lt_ge_dec n k); reflexivity.
  - (* var_f — capture the goal's own test, cf. the ptyp twin *)
    destruct (x == α) as [e | n0].
    + rewrite e. simpl.
      match goal with
      | |- context [if ?t then _ else _] => destruct t as [_ | n1]
      end; [reflexivity | exfalso; apply n1; reflexivity].
    + simpl.
      match goal with
      | |- context [if ?t then _ else _] => destruct t as [e1 | ?]
      end; [exfalso; apply n0; exact (swap_atom_inj a b x α e1) | reflexivity].
  - (* arrow *) f_equal; auto.
  - (* all_syn *) f_equal; auto.
  - (* ghost *) reflexivity.
  - (* univ_ghost *) f_equal; auto.
Qed.

Lemma swap_pskl_close : forall a b x P,
  swap_pskl a b (close_pskl_wrt_pskl x P)
  = close_pskl_wrt_pskl (swap_atom a b x) (swap_pskl a b P).
Proof. intros. unfold close_pskl_wrt_pskl. apply swap_pskl_close_rec. Qed.

Lemma swap_pskl_ptyp_to_pskl : forall a b A,
  swap_pskl a b (ptyp_to_pskl A) = ptyp_to_pskl (swap_ptyp a b A).
Proof. induction A; simpl; f_equal; auto. Qed.

(* ===================================================================== *)
(*  §5  Equivariance: [a_guess_mono] / [a_guess] (the viability probe)     *)
(* ===================================================================== *)

Lemma a_guess_mono_swap : forall a b Θ P Ξ τ,
  a_guess_mono Θ P Ξ τ ->
  a_guess_mono (swap_aenv a b Θ) (swap_pskl a b P)
               (swap_aenv a b Ξ) (swap_ptyp a b τ).
Proof.
  intros * H; induction H; simpl.
  - (* ghost: the generated flexible transports with its avoid-input *)
    apply a_guess_mono__ghost. auto using swap_aenv_ftvar_notin.
  - (* univ_ghost *) apply a_guess_mono__univ_ghost; auto.
  - (* var *) apply a_guess_mono__var.
  - (* unit *) apply a_guess_mono__unit.
  - (* arrow *)
    rewrite swap_aenv_app. apply a_guess_mono__arrow; auto.
  - (* forall: the ONE fixed binder transports — no re-picking, no L *)
    rewrite swap_ptyp_close.
    apply a_guess_mono__forall.
    + apply notin_union_split in H as [h1 h2].
      apply notin_union_join;
        auto using swap_aenv_ftvar_notin, swap_pskl_ftv_notin.
    + rewrite swap_pskl_open_var in IHa_guess_mono. exact IHa_guess_mono.
Qed.

Lemma a_guess_swap : forall a b Θ NM Q Ξ Q',
  a_guess Θ NM Q Ξ Q' ->
  a_guess (swap_aenv a b Θ) NM (swap_pskl a b Q)
          (swap_aenv a b Ξ) (swap_pskl a b Q').
Proof.
  intros * H; destruct H; simpl.
  - apply a_guess__sk.
  - rewrite swap_pskl_ptyp_to_pskl. apply a_guess__ty.
    apply a_guess_mono_swap; auto.
Qed.

(* ===================================================================== *)
(*  §6  Swap over atom SETS (the F / Δ1 / Δ2 indexes)                      *)
(*                                                                        *)
(*  [swap_atoms] and its membership SPEC [swap_atoms_spec] are upstream in *)
(*  fresco/prop_tag.v §1; what is here is the EXTENSIONAL packaging this   *)
(*  side needs.  [atoms] is opaque, so [swap_atoms] cannot be a Leibniz    *)
(*  homomorphism: judgments indexed by sets take the swapped set           *)
(*  extensionally ([S' [=] swap_atoms a b S]) in their equivariance lemmas.*)
(* ===================================================================== *)

Lemma empty_eq_swap_atoms_empty : forall a b,
  empty [=] swap_atoms a b empty.
Proof. intros. symmetry. apply swap_atoms_empty. Qed.

(** The [add] homomorphism, extensionally — the shape every [add]-indexed
    rule case needs. *)
Lemma eq_swap_atoms_add : forall a b x (S S' : atoms),
  S' [=] swap_atoms a b S ->
  add (swap_atom a b x) S' [=] swap_atoms a b (add x S).
Proof.
  intros * HS y. split; intros Hy.
  - apply swap_atoms_spec.
    assert (y = swap_atom a b x \/ y `in` S') as [h | h] by fsetdec.
    + subst. rewrite swap_atom_invol. fsetdec.
    + assert (y `in` swap_atoms a b S) by fsetdec.
      apply swap_atoms_spec in H. fsetdec.
  - apply swap_atoms_spec in Hy.
    assert (swap_atom a b y = x \/ swap_atom a b y `in` S) as [h | h]
      by fsetdec.
    + assert (y = swap_atom a b x)
        by (rewrite <- h, swap_atom_invol; reflexivity).
      fsetdec.
    + assert (y `in` swap_atoms a b S) by (apply swap_atoms_spec; exact h).
      fsetdec.
Qed.

(** Transport of a [∉]-condition into an extensionally-given swapped set. *)
Lemma swap_notin_eq : forall a b x (S S' : atoms),
  S' [=] swap_atoms a b S ->
  x `notin` S ->
  swap_atom a b x `notin` S'.
Proof.
  intros * HS Hn Hin.
  assert (h0 : swap_atom a b x `in` swap_atoms a b S) by fsetdec.
  pose proof (proj1 (swap_atoms_spec a b S (swap_atom a b x)) h0) as h.
  rewrite swap_atom_invol in h. contradiction.
Qed.

(* ===================================================================== *)
(*  §7  Swap over constraint lists                                        *)
(* ===================================================================== *)

Definition swap_cstr (a b : atom) (c : a_cstr) : a_cstr :=
  match c with
  | a_cstr_sub m P => a_cstr_sub m (swap_pskl a b P)
  | a_cstr_eq P => a_cstr_eq (swap_pskl a b P)
  end.

Definition swap_cstrs (a b : atom) (C : a_cstrs) : a_cstrs :=
  List.map (swap_cstr a b) C.

Lemma swap_cstrs_cons : forall a b c (C : a_cstrs),
  swap_cstrs a b (c :: C) = swap_cstr a b c :: swap_cstrs a b C.
Proof. reflexivity. Qed.

(** ⭐ THE CROSS-HALF GUARD TRAVELS ALONG A TRANSPOSITION.  A swap is a
    BIJECTION on atoms, so a disjointness between a constraint list's free
    variables and a block's domain survives it — which is exactly what the
    two collection ARROW rows now owe in the equivariance proof below. *)
Lemma swap_cstrs_ftv_notin : forall a b (C : a_cstrs) x,
  x `notin` ftvar_in_a_cstrs C ->
  swap_atom a b x `notin` ftvar_in_a_cstrs (swap_cstrs a b C).
Proof.
  induction C as [ | c C IH ]; intros x Hx; simpl in *; [ fsetdec | ].
  pose proof (IH x ltac:(clear - Hx; fsetdec)) as Hc.
  destruct c as [m P | P]; simpl in *;
    pose proof (swap_pskl_ftv_notin a b P x ltac:(clear - Hx; fsetdec)) as Hp;
    clear - Hc Hp; fsetdec.
Qed.

Lemma swap_look_guard : forall a b (C : a_cstrs) (Ξ : aenv),
  ftvar_in_a_cstrs C ∩ dom Ξ [=] empty ->
  ftvar_in_a_cstrs (swap_cstrs a b C) ∩ dom (swap_aenv a b Ξ) [=] empty.
Proof.
  intros a b C Ξ H.
  assert (Hkey : forall x, x `in` ftvar_in_a_cstrs (swap_cstrs a b C) ->
                           x `in` dom (swap_aenv a b Ξ) -> False).
  { intros x Hc Hd.
    assert (Hc' : swap_atom a b x `in` ftvar_in_a_cstrs C).
    { destruct (AtomSetProperties.In_dec (swap_atom a b x)
                  (ftvar_in_a_cstrs C)) as [Hy | Hn]; [ exact Hy | ].
      pose proof (swap_cstrs_ftv_notin a b C (swap_atom a b x) Hn) as Hno.
      rewrite swap_atom_invol in Hno. contradiction. }
    assert (Hd' : swap_atom a b x `in` dom Ξ).
    { destruct (AtomSetProperties.In_dec (swap_atom a b x) (dom Ξ))
        as [Hy | Hn]; [ exact Hy | ].
      pose proof (swap_aenv_dom_notin a b Ξ (swap_atom a b x) Hn) as Hno.
      rewrite swap_atom_invol in Hno. contradiction. }
    clear - H Hc' Hd'. fsetdec. }
  intros x; split; intros Hin;
    [ exfalso; apply (Hkey x); clear - Hin; fsetdec
    | clear - Hin; fsetdec ].
Qed.

(** ⭐ The GUESS's half of the cross-layer guard travels too (2026-08-21). *)
Lemma swap_guess_guard : forall a b (C : a_cstrs) (Q : pskl) (Ξ : aenv),
  (ftvar_in_a_cstrs C ∪ ftvar_in_pskl Q) ∩ dom Ξ [=] empty ->
  (ftvar_in_a_cstrs (swap_cstrs a b C) ∪ ftvar_in_pskl (swap_pskl a b Q))
    ∩ dom (swap_aenv a b Ξ) [=] empty.
Proof.
  intros a b C Q Ξ H.
  assert (Hkey : forall x,
            x `in` (ftvar_in_a_cstrs (swap_cstrs a b C)
                    ∪ ftvar_in_pskl (swap_pskl a b Q)) ->
            x `in` dom (swap_aenv a b Ξ) -> False).
  { intros x Hc Hd.
    assert (Hc' : swap_atom a b x
                  `in` (ftvar_in_a_cstrs C ∪ ftvar_in_pskl Q)).
    { destruct (AtomSetProperties.In_dec (swap_atom a b x)
                  (ftvar_in_a_cstrs C ∪ ftvar_in_pskl Q)) as [Hy | Hn];
        [ exact Hy | exfalso ].
      pose proof (swap_cstrs_ftv_notin a b C (swap_atom a b x)
                    ltac:(clear - Hn; fsetdec)) as Hno1.
      pose proof (swap_pskl_ftv_notin a b Q (swap_atom a b x)
                    ltac:(clear - Hn; fsetdec)) as Hno2.
      rewrite swap_atom_invol in Hno1. rewrite swap_atom_invol in Hno2.
      clear - Hc Hno1 Hno2. fsetdec. }
    assert (Hd' : swap_atom a b x `in` dom Ξ).
    { destruct (AtomSetProperties.In_dec (swap_atom a b x) (dom Ξ))
        as [Hy | Hn]; [ exact Hy | ].
      pose proof (swap_aenv_dom_notin a b Ξ (swap_atom a b x) Hn) as Hno.
      rewrite swap_atom_invol in Hno. contradiction. }
    clear - H Hc' Hd'. fsetdec. }
  intros x; split; intros Hin;
    [ exfalso; apply (Hkey x); clear - Hin; fsetdec
    | clear - Hin; fsetdec ].
Qed.

Lemma swap_cstrs_app : forall a b (C1 C2 : a_cstrs),
  swap_cstrs a b (C1 ++ C2) = swap_cstrs a b C1 ++ swap_cstrs a b C2.
Proof. intros. unfold swap_cstrs. apply List.map_app. Qed.

(* ===================================================================== *)
(*  §8  Commutation with substitution                                     *)
(* ===================================================================== *)

Lemma swap_ptyp_subst : forall a b A x B,
  swap_ptyp a b (subst_ptyp_in_ptyp A x B)
  = subst_ptyp_in_ptyp (swap_ptyp a b A) (swap_atom a b x) (swap_ptyp a b B).
Proof.
  intros a b A x; induction B; simpl; try solve [reflexivity | f_equal; auto].
  (* var_f — capture the goal's own tests, as in the close lemmas *)
  match goal with
  | |- context [if ?t then _ else _] => destruct t as [e | n0]
  end.
  - rewrite e. simpl.
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [_ | n1]
    end; [reflexivity | exfalso; apply n1; reflexivity].
  - simpl.
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [e1 | ?]
    end; [exfalso; apply n0; exact (swap_atom_inj a b _ _ e1) | reflexivity].
Qed.

(** A swap IS the rename, when the TARGET is fresh for the subject: the
    transposition's other half acts as the identity there.  This is the
    bridge that lets a rename lemma be DERIVED from equivariance instead of
    re-proved by a size induction — which matters now that the solve's
    binder rows push their witness into the context, so a rename whose
    SOURCE is that witness can no longer satisfy "source dodges Θ". *)
Lemma swap_pskl_as_subst : forall a b P,
  b `notin` ftvar_in_pskl P ->
  swap_pskl a b P = subst_pskl_in_pskl (pskl_var_f b) a P.
Proof.
  induction P; simpl; intros Hb; f_equal;
    try solve [ reflexivity | apply IHP; fsetdec
              | apply IHP1; fsetdec | apply IHP2; fsetdec ].
  destruct (α == a) as [-> | Hne].
  - rewrite swap_atom_l. reflexivity.
  - rewrite swap_atom_other; [ reflexivity | assumption | ].
    intros ->. clear - Hb; fsetdec.
Qed.

(** Same bridge at the TYPE sort — [a_guess_mono]'s output lives there. *)
Lemma swap_ptyp_as_subst : forall a b A,
  b `notin` ftvar_in_ptyp A ->
  swap_ptyp a b A = subst_ptyp_in_ptyp (ptyp_var_f b) a A.
Proof.
  induction A; simpl; intros Hb; f_equal;
    try solve [ reflexivity | apply IHA; fsetdec
              | apply IHA1; fsetdec | apply IHA2; fsetdec ].
  destruct (α == a) as [-> | Hne].
  - rewrite swap_atom_l. reflexivity.
  - rewrite swap_atom_other; [ reflexivity | assumption | ].
    intros ->. clear - Hb; fsetdec.
Qed.

(** The CONTEXT bridge: [swap_aenv] IS [rename_aenv] (just above) when
    the TARGET is fresh for the context — the KEY and the PAYLOAD alike, since
    [ftvar_in_aenv] counts both.  With it a substitution-shaped CONTEXT rename
    is a corollary of equivariance with its statement UNCHANGED, so consumers
    keep their [rename_aenv_*] rewriting ritual and the size inductions that
    used to prove those renames go away. *)
Lemma swap_aenv_as_rename : forall β γ (Θ : aenv),
  γ `notin` ftvar_in_aenv Θ ->
  swap_aenv β γ Θ = rename_aenv γ β Θ.
Proof.
  induction Θ as [| [x bd] Θ' IH]; intros Hγ; [reflexivity |].
  simpl in Hγ. rewrite swap_aenv_cons. cbn [rename_aenv].
  f_equal; [ f_equal | apply IH; clear - Hγ; fsetdec ].
  - (* the key *)
    unfold swap_atom. destruct (x == β) as [-> | Hne].
    + destruct (β == β) as [_ | Hc]; [ reflexivity | contradiction ].
    + destruct (x == γ) as [-> | _]; [ exfalso; clear - Hγ; fsetdec | ].
      destruct (x == β) as [Hc | _]; [ contradiction | reflexivity ].
  - (* the payload *)
    destruct bd; simpl in Hγ |- *.
    + reflexivity.
    + f_equal. apply swap_ptyp_as_subst. fsetdec.
    + f_equal. apply swap_pskl_as_subst. fsetdec.
    + reflexivity.
    + f_equal. apply swap_ptyp_as_subst. fsetdec.
Qed.

Lemma swap_pskl_subst : forall a b P x Q,
  swap_pskl a b (subst_pskl_in_pskl P x Q)
  = subst_pskl_in_pskl (swap_pskl a b P) (swap_atom a b x) (swap_pskl a b Q).
Proof.
  intros a b P x; induction Q; simpl; try solve [reflexivity | f_equal; auto].
  (* var_f *)
  match goal with
  | |- context [if ?t then _ else _] => destruct t as [e | n0]
  end.
  - rewrite e. simpl.
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [_ | n1]
    end; [reflexivity | exfalso; apply n1; reflexivity].
  - simpl.
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [e1 | ?]
    end; [exfalso; apply n0; exact (swap_atom_inj a b _ _ e1) | reflexivity].
Qed.

(* ===================================================================== *)
(*  §9  Equivariance: the small predicates                                *)
(* ===================================================================== *)

Lemma lc_ptyp_swap : forall a b A, lc_ptyp A -> lc_ptyp (swap_ptyp a b A).
Proof.
  intros * H; induction H; simpl; try solve [constructor; auto].
  (* all *)
  constructor. intros α0.
  specialize (H0 (swap_atom a b α0)).
  rewrite swap_ptyp_open in H0. simpl in H0.
  rewrite swap_atom_invol in H0. exact H0.
Qed.

Lemma lc_pskl_swap : forall a b P, lc_pskl P -> lc_pskl (swap_pskl a b P).
Proof.
  intros * H; induction H; simpl; try solve [constructor; auto].
  (* all_syn *)
  constructor. intros α0.
  specialize (H0 (swap_atom a b α0)).
  rewrite swap_pskl_open in H0. simpl in H0.
  rewrite swap_atom_invol in H0. exact H0.
Qed.

Lemma mono_ptyp_swap : forall a b A, mono_ptyp A -> mono_ptyp (swap_ptyp a b A).
Proof. intros * H; induction H; simpl; constructor; auto. Qed.

Lemma guarded_pskl_swap : forall a b P,
  guarded_pskl P -> guarded_pskl (swap_pskl a b P).
Proof.
  intros * H; destruct H; simpl; constructor; auto using lc_pskl_swap.
Qed.

Lemma nonghost_pskl_swap : forall a b P,
  nonghost_pskl P -> nonghost_pskl (swap_pskl a b P).
Proof. intros * H; destruct H; simpl; constructor. Qed.

(** The [<> ◇] guard the consistency FlexL/FlexR rows carry (def_rules.v)
    transports along a swap: a transposition is structural, so it maps a
    ghost to a ghost and everything else to its own constructor. *)
Lemma swap_pskl_not_ghost : forall a b P,
  P <> pskl_ghost -> swap_pskl a b P <> pskl_ghost.
Proof.
  intros * H. destruct P; simpl; try discriminate. congruence.
Qed.

(** A swap only renames free variables, so it cannot create or destroy a
    ghost — the TYPE sort of the [Check] / [ForallR] / [GhostL] rows is
    swap-stable, which is what those rows' side conditions need here. *)
Lemma pskl_ghost_free_swap : forall a b P,
  pskl_ghost_free P -> pskl_ghost_free (swap_pskl a b P).
Proof.
  induction P; intros H; simpl in *; try contradiction; auto.
  destruct H; split; auto.
Qed.

Lemma a_binds_tvar_swap : forall a b α (Θ : aenv),
  a_binds_tvar α Θ -> a_binds_tvar (swap_atom a b α) (swap_aenv a b Θ).
Proof.
  intros * [h | [h | [τ h]]];
    [ left | right; left | right; right; exists (swap_ptyp a b τ) ];
    apply (swap_aenv_binds a b) in h; exact h.
Qed.

Lemma a_flex_tvar_swap : forall a b (Θ : aenv) α,
  a_flex_tvar Θ α -> a_flex_tvar (swap_aenv a b Θ) (swap_atom a b α).
Proof.
  intros * [h | [τ h]];
    [ left | right; exists (swap_ptyp a b τ) ];
    apply (swap_aenv_binds a b) in h; exact h.
Qed.

Lemma a_flex_swap : forall a b (Θ : aenv) P,
  a_flex Θ P -> a_flex (swap_aenv a b Θ) (swap_pskl a b P).
Proof.
  intros * H; destruct H; simpl.
  - apply a_flex__var. apply (swap_aenv_binds a b) in H. exact H.
  - apply a_flex__var_def with (τ := swap_ptyp a b τ).
    apply (swap_aenv_binds a b) in H. exact H.
Qed.

Lemma a_non_flex_swap : forall a b (Θ : aenv) P,
  a_non_flex Θ P -> a_non_flex (swap_aenv a b Θ) (swap_pskl a b P).
Proof.
  intros * [Hlc Hnf]. split; [auto using lc_pskl_swap |].
  intros Hf. apply Hnf.
  apply (a_flex_swap a b) in Hf.
  rewrite swap_aenv_invol, swap_pskl_invol in Hf. exact Hf.
Qed.

Lemma a_suffix_swap : forall a b (Ξ : aenv),
  a_suffix Ξ -> a_suffix (swap_aenv a b Ξ).
Proof.
  intros * H; induction H; simpl; [constructor |].
  constructor; [exact IHa_suffix |].
  destruct H0; simpl; constructor.
Qed.

Lemma swap_aenv_minus : forall a b (Θ : aenv) Δ,
  swap_aenv a b (aenv_minus Θ Δ) = aenv_minus (swap_aenv a b Θ) (swap_atoms a b Δ).
Proof.
  intros a b Θ Δ. induction Θ as [| [x bd] Θ IH]; [ reflexivity | ].
  rewrite swap_aenv_cons. unfold aenv_minus in *. simpl.
  destruct (AtomSetImpl.mem x Δ) eqn:Hm;
    destruct (AtomSetImpl.mem (swap_atom a b x) (swap_atoms a b Δ)) eqn:Hm';
    simpl; try exact IH; try (f_equal; exact IH).
  all: exfalso.
  - apply AtomSetFacts.mem_iff in Hm. apply AtomSetFacts.not_mem_iff in Hm'.
    apply Hm'. apply swap_atoms_in. exact Hm.
  - apply AtomSetFacts.not_mem_iff in Hm. apply AtomSetFacts.mem_iff in Hm'.
    apply (proj1 (swap_atoms_spec a b Δ _)) in Hm'. rewrite swap_atom_invol in Hm'.
    contradiction.
Qed.

Lemma a_wf_pskl_swap : forall a b (Θ : aenv) (Δ : atoms) P,
  a_wf_pskl Θ Δ P ->
  forall Δ', Δ' [=] swap_atoms a b Δ ->
  a_wf_pskl (swap_aenv a b Θ) Δ' (swap_pskl a b P).
Proof.
  intros a b Θ Δ P H; induction H; intros Δ' HΔ; simpl.
  - constructor.
  - constructor. auto using a_binds_tvar_swap.
  - constructor; auto.
  - apply a_wf_pskl__all with (L := swap_atoms a b L).
    intros α0 Hα0.
    assert (hin : swap_atom a b α0 `notin` L)
      by (intro hc; apply Hα0; apply swap_atoms_spec; exact hc).
    pose proof (eq_swap_atoms_add a b (swap_atom a b α0) _ _ HΔ) as Hadd.
    rewrite swap_atom_invol in Hadd.
    specialize (H0 _ hin _ Hadd).
    rewrite swap_pskl_open in H0. simpl in H0.
    rewrite swap_atom_invol in H0. exact H0.
  - constructor.
  - constructor; [auto using guarded_pskl_swap |].
    rewrite (aenv_minus_eq _ HΔ), <- swap_aenv_minus.
    apply IHa_wf_pskl. rewrite swap_atoms_empty. fsetdec.
Qed.

(* ===================================================================== *)
(*  §10  Equivariance: the look / solve / extract cluster                  *)
(* ===================================================================== *)

Lemma swap_atom_neq : forall a b x y,
  x <> y -> swap_atom a b x <> swap_atom a b y.
Proof. intros * Hne He. apply Hne. exact (swap_atom_inj a b _ _ He). Qed.

Lemma swap_pskl_neq_var : forall a b P α,
  P <> pskl_var_f α ->
  swap_pskl a b P <> pskl_var_f (swap_atom a b α).
Proof.
  intros * Hne He. apply Hne.
  rewrite <- (swap_pskl_invol a b P), He. simpl.
  rewrite swap_atom_invol. reflexivity.
Qed.

(** …and its ghost sibling, for the ◇-DISPATCH GUARD: a swap is structural,
    so it maps [◇] to [◇] and nothing else to it. *)
Lemma swap_pskl_neq_ghost : forall a b P,
  P <> pskl_ghost ->
  swap_pskl a b P <> pskl_ghost.
Proof.
  intros * Hne He. apply Hne.
  rewrite <- (swap_pskl_invol a b P), He. reflexivity.
Qed.

(** …and its ForallR sibling, for the ForallR-PRIORITY GUARD: a swap is
    structural, so it maps a [∀] to a [∀] and preserves ghost-freeness in
    both directions ([pskl_ghost_free_swap] + [swap_pskl_invol]). *)
(** The FlexR-priority guard transports too, and needs the REVERSE of
    [a_flex_tvar_swap] — which involutivity supplies. *)
Lemma flex_r_off_swap : forall a b Θ P',
  flex_r_off Θ P' -> flex_r_off (swap_aenv a b Θ) (swap_pskl a b P').
Proof.
  intros a b Θ P' H β Heq Hf.
  destruct P' as [ | | γ | | | | ]; simpl in Heq; try discriminate Heq.
  injection Heq as <-.
  apply (H γ eq_refl).
  apply (a_flex_tvar_swap a b) in Hf.
  rewrite swap_aenv_invol, swap_atom_invol in Hf. exact Hf.
Qed.

Lemma forall_r_off_swap : forall a b m P',
  forall_r_off m P' -> forall_r_off m (swap_pskl a b P').
Proof.
  intros a b m P' H B Heq Hm.
  destruct P' as [ | | | | P0 | | ]; simpl in Heq; try discriminate.
  injection Heq as Heq0; subst B.
  intro Hgf. apply (H P0 eq_refl Hm).
  simpl in Hgf |- *.
  apply (pskl_ghost_free_swap a b) in Hgf.
  rewrite swap_pskl_invol in Hgf. exact Hgf.
Qed.

(** ⭐ The SOLVE-DISPATCH guards are pure SHAPE predicates, so a swap moves
    them for free — the head constructor is what they read, and a swap
    preserves it. *)
Lemma peel_l_off_swap : forall a b P,
  peel_l_off P -> peel_l_off (swap_pskl a b P).
Proof.
  intros a b P [H1 H2]; destruct P; simpl;
    try solve [ split; intros; discriminate ];
    [ exfalso; exact (H1 _ eq_refl) | exfalso; exact (H2 _ eq_refl) ].
Qed.

Lemma solve_l_off_swap : forall a b P,
  solve_l_off P -> solve_l_off (swap_pskl a b P).
Proof.
  intros a b P [H0 [H1 H2]]; destruct P; simpl;
    try solve [ split;
                [ intros; discriminate | split; intros; discriminate ] ];
    [ exfalso; exact (H0 _ eq_refl)
    | exfalso; exact (H1 _ eq_refl)
    | exfalso; exact (H2 _ eq_refl) ].
Qed.

Local Lemma notin_add_split : forall (x y : atom) (S : atoms),
  x `notin` add y S -> x <> y /\ x `notin` S.
Proof. intros; split; fsetdec. Qed.

Local Lemma notin_add_join : forall (x y : atom) (S : atoms),
  x <> y -> x `notin` S -> x `notin` add y S.
Proof. intros; fsetdec. Qed.

(** Discharge a swapped freshness side condition: shatter the hypothesis
    into atomic ∉/≠ facts, rebuild the goal structurally, close the leaves
    with the atomic transports.  No [fsetdec] on unions (⚙ DESIGN §4.3). *)
Ltac swap_freshness :=
  repeat match goal with
         | H : _ `notin` add _ _ |- _ =>
             apply notin_add_split in H; destruct H
         | H : _ `notin` (_ `union` _) |- _ =>
             apply notin_union_split in H; destruct H
         end;
  repeat match goal with
         | |- _ `notin` add _ _ => apply notin_add_join
         | |- _ `notin` (_ `union` _) => apply notin_union_join
         end;
  auto using swap_aenv_ftvar_notin, swap_pskl_ftv_notin,
             swap_ptyp_ftv_notin, swap_aenv_dom_notin, swap_atom_neq.

Scheme a_looksub_sind := Induction for a_looksub Sort Prop
  with a_lookeq_sind := Induction for a_lookeq Sort Prop.
Combined Scheme a_looksub_lookeq_sind from a_looksub_sind, a_lookeq_sind.

Lemma a_looksub_lookeq_swap : forall a b,
  (forall Θ α m P P' Ξ C,
     a_looksub Θ α m P P' Ξ C ->
     a_looksub (swap_aenv a b Θ) (swap_atom a b α) m
       (swap_pskl a b P) (swap_pskl a b P')
       (swap_aenv a b Ξ) (swap_cstrs a b C)) /\
  (forall Θ α P P' Ξ C,
     a_lookeq Θ α P P' Ξ C ->
     a_lookeq (swap_aenv a b Θ) (swap_atom a b α)
       (swap_pskl a b P) (swap_pskl a b P')
       (swap_aenv a b Ξ) (swap_cstrs a b C)).
Proof.
  intros a b.
  apply (a_looksub_lookeq_sind
           (fun Θ α m P P' Ξ C _ =>
              a_looksub (swap_aenv a b Θ) (swap_atom a b α) m
                (swap_pskl a b P) (swap_pskl a b P')
                (swap_aenv a b Ξ) (swap_cstrs a b C))
           (fun Θ α P P' Ξ C _ =>
              a_lookeq (swap_aenv a b Θ) (swap_atom a b α)
                (swap_pskl a b P) (swap_pskl a b P')
                (swap_aenv a b Ξ) (swap_cstrs a b C)));
    intros; simpl.
  (* -------- a_looksub -------- *)
  - (* var *) apply a_looksub__var.
  - (* absent *) apply a_looksub__absent. auto using swap_pskl_ftv_notin.
  - (* vacuous *) apply a_looksub__vacuous.
    apply swap_pskl_neq_var; assumption.
  - (* check *)
    apply a_looksub__check;
      auto using swap_pskl_neq_var, guarded_pskl_swap, pskl_ghost_free_swap.
  - (* forall_r *)
    apply a_looksub__forall_r with (β := swap_atom a b β);
      [ apply pskl_ghost_free_swap; assumption | swap_freshness
      | apply swap_pskl_ftv_in; assumption
      | apply swap_pskl_neq_var; assumption
      |].
    rewrite swap_pskl_open_var in H. exact H.
  - (* arrow *)
    rewrite swap_aenv_app, swap_cstrs_app.
    apply a_looksub__arrow; auto using swap_look_guard.
  - (* forall_l *)
    apply a_looksub__forall_l with (β := swap_atom a b β);
      [ swap_freshness
      | apply swap_pskl_ftv_in; assumption
      | apply swap_pskl_neq_ghost; assumption
      | apply forall_r_off_swap; assumption
      |].
    rewrite swap_pskl_open_var in H. exact H.
  - (* univ_ghost_l *)
    apply a_looksub__univ_ghost_l;
      [ apply swap_pskl_neq_ghost; assumption
      | apply forall_r_off_swap; assumption | auto ].
  (* -------- a_lookeq -------- *)
  - (* var *) apply a_lookeq__var.
  - (* absent *) apply a_lookeq__absent. auto using swap_pskl_ftv_notin.
  - (* vacuous *) apply a_lookeq__vacuous.
    apply swap_pskl_neq_var; assumption.
  - (* flex_r *)
    apply a_lookeq__flex_r;
      [ swap_freshness
      | auto using a_flex_tvar_swap
      | auto using swap_pskl_neq_var
      | auto using swap_pskl_ftv_in ].
  - (* arrow *)
    rewrite swap_aenv_app, swap_cstrs_app.
    apply a_lookeq__arrow; auto using swap_look_guard.
  - (* forall_inh *)
    apply a_lookeq__forall_inh with (β := swap_atom a b β);
      [ swap_freshness
      | apply swap_pskl_ftv_in; assumption
      |].
    rewrite !swap_pskl_open_var in H. exact H.
  - (* forall_syn *)
    apply a_lookeq__forall_syn with (β := swap_atom a b β);
      [ swap_freshness
      | apply swap_pskl_ftv_in; assumption
      |].
    rewrite swap_pskl_open_var in H. exact H.
  - (* univ_ghost *) apply a_lookeq__univ_ghost; auto.
  - (* univ_ghost1 *)
    apply a_lookeq__univ_ghost1 with (β := swap_atom a b β);
      [ swap_freshness
      | apply swap_pskl_ftv_in; assumption
      |].
    rewrite swap_pskl_open_var in H. exact H.
  - (* univ_ghost2 *)
    apply a_lookeq__univ_ghost2;
      auto using guarded_pskl_swap, flex_r_off_swap.
  - (* univ_ghost_r *)
    apply a_lookeq__univ_ghost_r;
      auto using swap_pskl_neq_var, guarded_pskl_swap.
Qed.

Scheme a_solve_sub_sind := Induction for a_solve_sub Sort Prop
  with a_solve_eq_sind := Induction for a_solve_eq Sort Prop.
Combined Scheme a_solve_sub_eq_sind from a_solve_sub_sind, a_solve_eq_sind.

(** ⭐ [Ξ] is swapped too (2026-08-04).  Equivariance is what the solve's
    binder rows now need in place of the double-rename witness-move: with
    the witness IN the premise's context ([(β ~ tvar) ++ Θ]) a rename whose
    SOURCE is that witness violates the "source dodges the context" side
    condition, whereas a swap has no such condition — it renames the
    context along with everything else.  (USER DIRECTIVE, swap kit:
    equivariance is THE ONE renaming primitive.) *)
Lemma a_solve_sub_eq_swap : forall a b,
  (forall Θ m P Q Ξ P',
     a_solve_sub Θ m P Q Ξ P' ->
     a_solve_sub (swap_aenv a b Θ) m (swap_pskl a b P) (swap_pskl a b Q)
       (swap_aenv a b Ξ) (swap_pskl a b P')) /\
  (forall Θ P Q Ξ P',
     a_solve_eq Θ P Q Ξ P' ->
     a_solve_eq (swap_aenv a b Θ) (swap_pskl a b P) (swap_pskl a b Q)
       (swap_aenv a b Ξ) (swap_pskl a b P')).
Proof.
  intros a b.
  apply (a_solve_sub_eq_sind
           (fun Θ m P Q Ξ P' _ =>
              a_solve_sub (swap_aenv a b Θ) m (swap_pskl a b P)
                (swap_pskl a b Q) (swap_aenv a b Ξ) (swap_pskl a b P'))
           (fun Θ P Q Ξ P' _ =>
              a_solve_eq (swap_aenv a b Θ) (swap_pskl a b P)
                (swap_pskl a b Q) (swap_aenv a b Ξ) (swap_pskl a b P')));
    intros; simpl;
    (* the THREADING rows split the block; the BINDER rows push a witness *)
    rewrite ? swap_aenv_app in *; rewrite ? swap_aenv_cons in *; simpl in *.
  (* -------- a_solve_sub -------- *)
  - (* var *) apply a_solve_sub__var.
  - (* forall_l: close in the output *)
    rewrite swap_pskl_close.
    apply a_solve_sub__forall_l; [ swap_freshness |].
    rewrite swap_pskl_open_var in H. exact H.
  - (* univ_ghost_l *) apply a_solve_sub__univ_ghost_l; auto.
  - (* vacuous *) apply a_solve_sub__vacuous. apply peel_l_off_swap. assumption.
  - (* check *) apply a_solve_sub__check;
      auto using guarded_pskl_swap, pskl_ghost_free_swap.
  - (* forall_r: the binder LEAKS into the output — no close, no re-bind *)
    apply a_solve_sub__forall_r with (β := swap_atom a b β);
      [ apply pskl_ghost_free_swap; assumption
      | apply solve_l_off_swap; assumption | swap_freshness |].
    rewrite swap_pskl_open_var in H. exact H.
  - (* arrow *) apply a_solve_sub__arrow; auto.
  - (* ghost_l_fn *) apply a_solve_sub__ghost_l_fn; auto.
  - (* ghost_l *) apply a_solve_sub__ghost_l;
      auto using guarded_pskl_swap, pskl_ghost_free_swap.
  (* -------- a_solve_eq -------- *)
  - (* unit *) apply a_solve_eq__unit.
  - (* var *) apply a_solve_eq__var.
  - (* flex_r : the output is guess^TY's, read back through the coercion *)
    rewrite swap_pskl_ptyp_to_pskl.
    apply a_solve_eq__flex_r;
      auto using a_flex_tvar_swap, a_non_flex_swap, nonghost_pskl_swap,
                 a_guess_mono_swap.
  - (* ghost_l *) apply a_solve_eq__ghost_l.
  - (* ghost_r *) apply a_solve_eq__ghost_r.
  - (* arrow *) apply a_solve_eq__arrow; auto.
  - (* forall *)
    rewrite swap_pskl_close.
    apply a_solve_eq__forall; [ swap_freshness |].
    rewrite !swap_pskl_open_var in H. exact H.
  - (* univ_ghost_both *) apply a_solve_eq__univ_ghost_both; auto.
  - (* univ_ghost_l_all *)
    rewrite swap_pskl_close.
    apply a_solve_eq__univ_ghost_l_all; [ swap_freshness |].
    rewrite swap_pskl_open_var in H. exact H.
  - (* univ_ghost_l_guarded *)
    apply a_solve_eq__univ_ghost_l_guarded; auto using guarded_pskl_swap.
  - (* all_l_univ_ghost *)
    rewrite swap_pskl_close.
    apply a_solve_eq__all_l_univ_ghost; [ swap_freshness |].
    rewrite swap_pskl_open_var in H. exact H.
  - (* univ_ghost_r_guarded *)
    apply a_solve_eq__univ_ghost_r_guarded; auto using guarded_pskl_swap.
Qed.

Lemma a_solve_cstr_swap : forall a b Θ C P Ξ Q,
  a_solve_cstr Θ C P Ξ Q ->
  a_solve_cstr (swap_aenv a b Θ) (swap_cstrs a b C)
    (swap_pskl a b P) (swap_aenv a b Ξ) (swap_pskl a b Q).
Proof.
  intros * H; induction H; simpl.
  - apply a_solve_cstr__empty.
  - apply a_solve_cstr__sub. apply (proj1 (a_solve_sub_eq_swap a b)); auto.
  - rewrite swap_aenv_app.
    apply a_solve_cstr__eq with (P'' := swap_pskl a b P'');
      [ apply (proj2 (a_solve_sub_eq_swap a b)); auto
      | rewrite <- swap_aenv_app; exact IHa_solve_cstr ].
Qed.

Lemma a_extract_swap : forall a b Θ NM α m P P' Ξ Q,
  a_extract Θ NM α m P P' Ξ Q ->
  a_extract (swap_aenv a b Θ) NM (swap_atom a b α) m
    (swap_pskl a b P) (swap_pskl a b P')
    (swap_aenv a b Ξ) (swap_pskl a b Q).
Proof.
  intros * H; destruct H.
  rewrite ! swap_aenv_app.
  apply a_extract__solve with (C := swap_cstrs a b C) (Q := swap_pskl a b Q).
  - apply (proj1 (a_looksub_lookeq_swap a b)); auto.
  - rewrite <- swap_aenv_app.
    pose proof (a_solve_cstr_swap a b _ _ _ _ _ H0) as h. exact h.
  - rewrite <- ! swap_aenv_app. apply a_guess_swap; auto.
  - (* the CROSS-LAYER guard travels: a transposition is a bijection *)
    apply swap_look_guard; assumption.
  - (* and so does the GUESS's half *)
    apply swap_guess_guard; assumption.
Qed.

(* ===================================================================== *)
(*  §11  Equivariance: the consis mutual (assign / unify / consis)         *)
(*                                                                        *)
(*  The set indexes F / Δ1 / Δ2 are taken EXTENSIONALLY (see §6): each     *)
(*  motive quantifies the swapped set together with a [=]-proof, and the   *)
(*  [add]-extending rules instantiate it through [eq_swap_atoms_add].      *)
(* ===================================================================== *)

(** Reverse dom transport (via involution). *)
Lemma swap_aenv_dom_in_rev : forall a b (Θ : aenv) x,
  x `in` dom (swap_aenv a b Θ) -> swap_atom a b x `in` dom Θ.
Proof.
  intros * Hx.
  pose proof (swap_aenv_dom_in a b (swap_aenv a b Θ) x Hx) as h.
  rewrite swap_aenv_invol in h. exact h.
Qed.

(** Reverse ftv transport for [pskl] (via involution). *)
Lemma swap_pskl_ftv_in_rev : forall a b P x,
  x `in` ftvar_in_pskl (swap_pskl a b P) -> swap_atom a b x `in` ftvar_in_pskl P.
Proof.
  intros * Hx.
  pose proof (swap_pskl_ftv_in a b (swap_pskl a b P) x Hx) as h.
  rewrite swap_pskl_invol in h. exact h.
Qed.

(** The Ghost/GhostR side condition, transported extensionally. *)
Lemma swap_inter_ftv_empty : forall a b (Δ Δ' : atoms) P,
  Δ' [=] swap_atoms a b Δ ->
  Δ ∩ ftvar_in_pskl P [=] empty ->
  Δ' ∩ ftvar_in_pskl (swap_pskl a b P) [=] empty.
Proof.
  intros * HΔ Hemp y. split; intros Hy; [| fsetdec].
  exfalso.
  assert (h1 : y `in` Δ') by fsetdec.
  assert (h2 : y `in` ftvar_in_pskl (swap_pskl a b P)) by fsetdec.
  assert (h1' : y `in` swap_atoms a b Δ) by fsetdec.
  pose proof (proj1 (swap_atoms_spec a b Δ y) h1') as h1''.
  pose proof (swap_pskl_ftv_in_rev a b P y h2) as h2'.
  assert (swap_atom a b y `in` (Δ ∩ ftvar_in_pskl P)) by (apply inter_3; auto).
  fsetdec.
Qed.

Lemma a_assign_unify_consis_swap : forall a b,
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
     {{ (swap_aenv a b Θ0) ⊲[ swap_aenv a b Ξ ]
       (swap_atom a b α) ≔ (swap_pskl a b P) ⊣ (swap_aenv a b Θ1) }}a) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
     {{ (swap_aenv a b Θ0) ⊲
       (swap_atom a b α) ≈ᵘ (swap_atom a b β) ⊣ (swap_aenv a b Θ1) }}a) /\
  (forall Δ1 Δ2 Θ0 P0 P Q Θ1,
     a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 ->
     forall Δ1' Δ2',
       Δ1' [=] swap_atoms a b Δ1 ->
       Δ2' [=] swap_atoms a b Δ2 ->
     a_consis Δ1' Δ2' (swap_aenv a b Θ0) (swap_pskl a b P0)
       (swap_pskl a b P) (swap_pskl a b Q) (swap_aenv a b Θ1)).
Proof.
  intros a b.
  apply (a_assign_unify_consis_mutind
           (fun Θ0 Ξ α P Θ1 _ =>
              {{ (swap_aenv a b Θ0) ⊲[ swap_aenv a b Ξ ]
                (swap_atom a b α) ≔ (swap_pskl a b P) ⊣ (swap_aenv a b Θ1) }}a)
           (fun Θ0 α β Θ1 _ =>
              {{ (swap_aenv a b Θ0) ⊲
                (swap_atom a b α) ≈ᵘ (swap_atom a b β) ⊣ (swap_aenv a b Θ1) }}a)
           (fun Δ1 Δ2 Θ0 P0 P Q Θ1 _ =>
              forall Δ1' Δ2',
                Δ1' [=] swap_atoms a b Δ1 ->
                Δ2' [=] swap_atoms a b Δ2 ->
              a_consis Δ1' Δ2' (swap_aenv a b Θ0) (swap_pskl a b P0)
                (swap_pskl a b P) (swap_pskl a b Q) (swap_aenv a b Θ1))).
  (* ==================== a_assign ==================== *)
  - (* univ_ghost_id *)
    intros Θ0 α. simpl.
    apply a_assign__univ_ghost_id.
  - (* solve_m *)
    intros Θ0 Ξ α P βs τ Hnα Hg Hmono Huniq Hfr. simpl.
    rewrite !swap_aenv_app.
    apply a_assign__solve_m;
      auto using swap_pskl_ftv_notin, a_guess_mono_swap, mono_ptyp_swap,
                 swap_aenv_uniq.
    intros α1 Hα1.
    pose proof (swap_aenv_dom_in_rev a b βs α1 Hα1) as hdom.
    specialize (Hfr _ hdom).
    apply notin_add_split in Hfr; destruct Hfr as [hne hdom0].
    apply notin_add_join.
    + (* ≠ swap α *)
      intros he. apply hne.
      rewrite he, swap_atom_invol. reflexivity.
    + (* ∉ dom (swap (Ξ ++ Θ0)) *)
      rewrite <- swap_aenv_app.
      intros hc.
      pose proof (swap_aenv_dom_in_rev a b (Ξ ++ Θ0) α1 hc). contradiction.
  - (* assign *)
    intros Θ0 Θ1 Ξ α β τ P Q Hflex Hnd Hd IH. simpl.
    eapply a_assign__assign.
    + exact (a_flex_tvar_swap a b _ _ Hflex).
    + apply swap_aenv_dom_notin; exact Hnd.
    + specialize (IH empty empty
                     (empty_eq_swap_atoms_empty a b)
                     (empty_eq_swap_atoms_empty a b)).
      rewrite swap_aenv_app in IH.
      rewrite !swap_pskl_subst in IH.
      rewrite !swap_pskl_ptyp_to_pskl in IH.
      change (swap_pskl a b (pskl_var_f α)) with
        (pskl_var_f (swap_atom a b α)) in IH.
      exact IH.
  - (* depend *)
    intros Θ0 Θ1 Ξ α β P Hne Hin Hd IH. simpl.
    rewrite swap_aenv_app in IH.
    apply a_assign__depend;
      [ auto using swap_atom_neq | auto using swap_pskl_ftv_in | exact IH ].
  - (* skip *)
    intros Θ0 Θ1 Ξ α β P Hne Hnf Hnd Hd IH. simpl.
    apply a_assign__skip;
      [ auto using swap_atom_neq | auto using swap_pskl_ftv_notin
      | apply swap_aenv_dom_notin; exact Hnd | exact IH ].
  - (* skip_rigid *)
    intros Θ0 Θ1 Ξ α β P Hnf Hnd Hd IH. simpl.
    apply a_assign__skip_rigid;
      [ auto using swap_pskl_ftv_notin
      | apply swap_aenv_dom_notin; exact Hnd | exact IH ].
  - (* skip_tm_var *)
    intros Θ0 Θ1 Ξ α x Q P Hnd Hd IH. simpl.
    apply a_assign__skip_tm_var;
      [ apply swap_aenv_dom_notin; exact Hnd | exact IH ].
  - (* skip_tm_skl *)
    intros Θ0 Θ1 Ξ α x Q P Hnd Hd IH. simpl.
    apply a_assign__skip_tm_skl;
      [ apply swap_aenv_dom_notin; exact Hnd | exact IH ].
  (* ==================== a_unify ==================== *)
  - (* flex_id *)
    intros Θ0 α Hflex.
    apply a_unify__flex_id. auto using a_flex_tvar_swap.
  - (* flex_l *)
    intros Θ0 α β Hne Hflex. simpl.
    apply a_unify__flex_l; auto using swap_atom_neq, a_flex_tvar_swap.
  - (* flex_r *)
    intros Θ0 α β Hne Hflex. simpl.
    apply a_unify__flex_r; auto using swap_atom_neq, a_flex_tvar_swap.
  - (* flex_assign *)
    intros Θ0 Θ1 α1 τ α β Q Hfα Hfβ Hnd Hd IH. simpl.
    eapply a_unify__flex_assign.
    + exact (a_flex_tvar_swap a b _ _ Hfα).
    + exact (a_flex_tvar_swap a b _ _ Hfβ).
    + apply swap_aenv_dom_notin; exact Hnd.
    + specialize (IH empty empty
                     (empty_eq_swap_atoms_empty a b)
                     (empty_eq_swap_atoms_empty a b)).
      rewrite !swap_pskl_ptyp_to_pskl in IH.
      rewrite !swap_ptyp_subst in IH.
      change (swap_ptyp a b (ptyp_var_f α)) with
        (ptyp_var_f (swap_atom a b α)) in IH.
      change (swap_ptyp a b (ptyp_var_f β)) with
        (ptyp_var_f (swap_atom a b β)) in IH.
      exact IH.
  - (* flex_skip *)
    intros Θ0 Θ1 α1 α β Hne1 Hne2 Hnd Hd IH. simpl.
    apply a_unify__flex_skip;
      [ auto using swap_atom_neq | auto using swap_atom_neq
      | apply swap_aenv_dom_notin; exact Hnd | exact IH ].
  - (* skip_other *)
    intros Θ0 Θ1 c bd α β Hb Hnd Hd IH. simpl.
    apply a_unify__skip_other.
    + destruct Hb as [-> | [[Q ->] | [Q ->]]]; simpl.
      * left; reflexivity.
      * right; left; eexists; reflexivity.
      * right; right; eexists; reflexivity.
    + apply swap_aenv_dom_notin; exact Hnd.
    + exact IH.
  (* ==================== a_consis ==================== *)
  - (* ghost *)
    intros Δ1 Δ2 Θ0 P0 Hemp Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__ghost. eauto using swap_inter_ftv_empty.
  - (* unit *)
    intros Δ1 Δ2 Θ0 Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__unit.
  - (* rigid *)
    intros Δ1 Δ2 Θ0 α Hb Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__rigid.
    pose proof (swap_aenv_binds a b _ _ _ Hb) as h. exact h.
  - (* arrow *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hd1 IH1 Hd2 IH2
           Δ1' Δ2' HΔ1 HΔ2. simpl.
    eapply a_consis__arrow;
      [ exact (IH1 _ _ HΔ1 HΔ2) | exact (IH2 _ _ HΔ1 HΔ2) ].
  - (* forall_inh *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    rewrite swap_pskl_close.
    apply a_consis__forall_inh.
    + swap_freshness; eauto using swap_notin_eq.
    + specialize (IH (add (swap_atom a b α) Δ1') (add (swap_atom a b α) Δ2')
                     (eq_swap_atoms_add a b α _ _ HΔ1)
                        (eq_swap_atoms_add a b α _ _ HΔ2)).
      rewrite !swap_pskl_open_var in IH. exact IH.
  - (* forall_syn *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    rewrite swap_pskl_close.
    apply a_consis__forall_syn.
    + swap_freshness; eauto using swap_notin_eq.
    + specialize (IH Δ1' (add (swap_atom a b α) Δ2')
                     HΔ1 (eq_swap_atoms_add a b α _ _ HΔ2)).
      rewrite !swap_pskl_open_var in IH. exact IH.
  - (* univ_ghost *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__univ_ghost; auto.
  - (* univ_ghost1 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    rewrite swap_pskl_close.
    apply a_consis__univ_ghost1.
    + swap_freshness; eauto using swap_notin_eq.
    + specialize (IH (add (swap_atom a b α) Δ1') Δ2'
                     (eq_swap_atoms_add a b α _ _ HΔ1) HΔ2).
      rewrite !swap_pskl_open_var in IH. exact IH.
  - (* univ_ghost2 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__univ_ghost2;
      auto using guarded_pskl_swap, a_non_flex_swap.
  - (* flex *)
    intros Δ1 Δ2 Θ0 Θ1 α β Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__flex; auto.
  - (* flex_l *)
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hnh Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__flex_l;
      [ auto using a_non_flex_swap | auto using swap_pskl_not_ghost
      | exact IH ].
  - (* flex_r *)
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hnh Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__flex_r;
      [ auto using a_non_flex_swap | auto using swap_pskl_not_ghost
      | exact IH ].
  - (* ghost_r *)
    intros Δ1 Δ2 Θ0 P Hemp Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__ghost_r. eauto using swap_inter_ftv_empty.
  - (* univ_ghost_r *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hd IH Δ1' Δ2' HΔ1 HΔ2. simpl.
    apply a_consis__univ_ghost_r;
      auto using guarded_pskl_swap, a_non_flex_swap.
Qed.

(* ===================================================================== *)
(*  §12  Equivariance: [a_sub] / [a_sub_flex]                              *)
(* ===================================================================== *)

Lemma a_consis_empty_swap : forall a b Θ0 P0 P Q Θ1,
  {{ Θ0 ⊢[ P0 ] P ∼ Q ⊣ Θ1 }}a ->
  {{ (swap_aenv a b Θ0) ⊢[ swap_pskl a b P0 ]
    (swap_pskl a b P) ∼ (swap_pskl a b Q) ⊣ (swap_aenv a b Θ1) }}a.
Proof.
  intros * H.
  apply (proj2 (proj2 (a_assign_unify_consis_swap a b)) _ _ _ _ _ _ _ H);
    apply empty_eq_swap_atoms_empty.
Qed.

Lemma a_consis_chk_swap : forall a b Θ0 A B Θ1,
  a_consis_chk Θ0 A B Θ1 ->
  a_consis_chk (swap_aenv a b Θ0) (swap_pskl a b A) (swap_pskl a b B)
    (swap_aenv a b Θ1).
Proof.
  intros * [Q H]. exists (swap_pskl a b Q). apply a_consis_empty_swap; auto.
Qed.

Scheme a_sub_sind := Induction for a_sub Sort Prop
  with a_sub_flex_sind := Induction for a_sub_flex Sort Prop.
Combined Scheme a_sub_sub_flex_sind from a_sub_sind, a_sub_flex_sind.

Lemma a_sub_sub_flex_swap : forall a b,
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 ->
     a_sub NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
       (swap_pskl a b P) (swap_pskl a b Q) (swap_aenv a b Θ1)) /\
  (forall NM M P0 Θ0 Ξ α A Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
     a_sub_flex NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
       (swap_aenv a b Ξ) (swap_atom a b α) (swap_pskl a b A)
       (swap_aenv a b Θ1)).
Proof.
  intros a b.
  apply (a_sub_sub_flex_sind
           (fun NM M P0 Θ0 P Q Θ1 _ =>
              a_sub NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
                (swap_pskl a b P) (swap_pskl a b Q) (swap_aenv a b Θ1))
           (fun NM M P0 Θ0 Ξ α A Θ1 _ =>
              a_sub_flex NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
                (swap_aenv a b Ξ) (swap_atom a b α) (swap_pskl a b A)
                (swap_aenv a b Θ1))).
  (* -------- a_sub -------- *)
  - (* infer *)
    intros NM P Θ0. simpl. apply a_sub__infer.
  - (* check *)
    intros Θ0 Θ1 A B Hgfa Hgfb Hga Hgb Hchk. simpl.
    apply a_sub__check;
      auto using guarded_pskl_swap, pskl_ghost_free_swap, a_consis_chk_swap.
  - (* forall_r *)
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huniq Hfr Hd IH. simpl.
    apply a_sub__forall_r with (α := swap_atom a b α) (Ξ := swap_aenv a b Ξ).
    + apply pskl_ghost_free_swap; exact Hgf.
    + auto using a_suffix_swap.
    + rewrite <- swap_aenv_app. auto using swap_aenv_uniq.
    + swap_freshness.
    + rewrite !swap_pskl_open_var in IH.
      rewrite !swap_aenv_app in IH. exact IH.
  - (* univ_ghost_r *)
    intros Θ0 P Hg. simpl.
    apply a_sub__univ_ghost_r; auto using guarded_pskl_swap.
  - (* flex_mono *)
    intros NM M P0 Θ0 Θ1 α A Hd IH. simpl.
    apply a_sub__flex_mono. exact IH.
  - (* arrow *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hd IH. simpl.
    eapply a_sub__arrow;
      [ exact (a_consis_empty_swap a b _ _ _ _ _ Hc) | exact IH ].
  - (* forall_l *)
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hm Hg Hfr Hex Huniq Hwf Hd IH. simpl.
    apply a_sub__forall_l with (α := swap_atom a b α)
      (Ξ := swap_aenv a b Ξ) (P1 := swap_pskl a b P1); auto.
    + destruct Hg as [hg | ->];
        [ left; auto using guarded_pskl_swap | right; reflexivity ].
    + swap_freshness.
    + pose proof (a_extract_swap a b _ _ _ _ _ _ _ _ Hex) as h.
      rewrite swap_pskl_open_var in h. exact h.
    + rewrite <- swap_aenv_app. auto using swap_aenv_uniq.
    + rewrite <- swap_aenv_app.
      apply (a_wf_pskl_swap a b _ _ _ Hwf).
      apply empty_eq_swap_atoms_empty.
    + rewrite swap_pskl_open in IH.
      rewrite swap_aenv_app in IH. exact IH.
  - (* ghost *)
    intros M Θ0 P0 Hm. simpl. apply a_sub__ghost; exact Hm.
  - (* univ_ghost_l *)
    intros M Θ0 Θ1 P0 P Q Hm Hd IH. simpl.
    apply a_sub__univ_ghost_l; auto.
  (* -------- a_sub_flex -------- *)
  - (* solve *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β A Hne Hfα Hfβ Hd IH. simpl.
    apply a_sub_flex__solve
      with (α := swap_atom a b α) (β := swap_atom a b β);
      [ auto using swap_atom_neq | | |].
    + rewrite <- swap_aenv_app. swap_freshness.
    + rewrite <- swap_aenv_app. swap_freshness.
    + rewrite !swap_aenv_app in IH. exact IH.
  - (* assign *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ A Hout Hd IH. simpl.
    apply a_sub_flex__assign; auto using swap_aenv_dom_notin.
    rewrite !swap_pskl_subst in IH.
    rewrite !swap_pskl_ptyp_to_pskl in IH.
    change (swap_pskl a b (pskl_var_f α)) with
      (pskl_var_f (swap_atom a b α)) in IH.
    rewrite swap_aenv_app in IH. exact IH.
  - (* depend *)
    intros NM M P0 Θ0 Θ1 Ξ α β A Hne Hin Hd IH. simpl.
    apply a_sub_flex__depend;
      auto using swap_atom_neq, swap_pskl_ftv_in.
    rewrite swap_aenv_app in IH. exact IH.
  - (* skip *)
    intros NM M P0 Θ0 Θ1 Ξ α β A Hne Hnf Hout Hd IH. simpl.
    apply a_sub_flex__skip;
      auto using swap_atom_neq, swap_pskl_ftv_notin, swap_aenv_dom_notin.
  - (* skip_rigid *)
    intros NM M P0 Θ0 Θ1 Ξ α β A Hne Hnf Hout Hd IH. simpl.
    apply a_sub_flex__skip_rigid;
      auto using swap_atom_neq, swap_pskl_ftv_notin, swap_aenv_dom_notin.
  - (* skip_tm_var *)
    intros NM M P0 Θ0 Θ1 Ξ α x Q A Hout Hd IH. simpl.
    apply a_sub_flex__skip_tm_var;
      [ apply swap_aenv_dom_notin; exact Hout | exact IH ].
  - (* skip_tm_skl *)
    intros NM M P0 Θ0 Θ1 Ξ α x Q A Hout Hd IH. simpl.
    apply a_sub_flex__skip_tm_skl;
      [ apply swap_aenv_dom_notin; exact Hout | exact IH ].
Qed.

(* ===================================================================== *)
(*  §13  The junk rename (K3) — the consumption shape for P7a              *)
(*                                                                        *)
(*  A run delivered by an IH may mention the walked-out β as an           *)
(*  incidentally-colliding junk name in its OUTPUTS; its INPUTS cannot     *)
(*  mention it.  Swapping β with a β1 fresh for the statement's data      *)
(*  fixes every input pointwise ([swap_*_fresh_id]) and renames the        *)
(*  outputs, so the rule's Barendregt output premise [β ∉ dom Θ1] becomes  *)
(*  provable.                                                             *)
(* ===================================================================== *)

Lemma swap_abind_fresh_id : forall a b bd,
  a `notin` ftvar_in_abind bd -> b `notin` ftvar_in_abind bd ->
  swap_abind a b bd = bd.
Proof.
  intros; destruct bd; simpl in *; f_equal;
    auto using swap_ptyp_fresh_id, swap_pskl_fresh_id.
Qed.

Lemma swap_aenv_fresh_id : forall a b (Θ : aenv),
  a `notin` ftvar_in_aenv Θ -> b `notin` ftvar_in_aenv Θ ->
  swap_aenv a b Θ = Θ.
Proof.
  intros a b Θ; induction Θ as [| [x bd] Θ']; intros Ha Hb; [reflexivity |].
  simpl in Ha, Hb. rewrite swap_aenv_cons.
  rewrite swap_atom_other; [| fsetdec | fsetdec].
  rewrite swap_abind_fresh_id; [| fsetdec | fsetdec].
  rewrite IHΘ'; [reflexivity | fsetdec | fsetdec].
Qed.

Lemma a_sub_swap_junk : forall β0 β1 NM M P0 Θ0 P Q Θ1,
  a_sub NM M P0 Θ0 P Q Θ1 ->
  β0 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
     `union` ftvar_in_pskl P ->
  β1 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
     `union` ftvar_in_pskl P ->
  a_sub NM M P0 Θ0 P (swap_pskl β0 β1 Q) (swap_aenv β0 β1 Θ1).
Proof.
  intros * Hd H0 H1.
  apply notin_union_split in H0; destruct H0 as [h0 H0].
  apply notin_union_split in H0; destruct H0 as [h0' h0''].
  apply notin_union_split in H1; destruct H1 as [h1 H1].
  apply notin_union_split in H1; destruct H1 as [h1' h1''].
  pose proof (proj1 (a_sub_sub_flex_swap β0 β1) _ _ _ _ _ _ _ Hd) as h.
  rewrite (swap_aenv_fresh_id β0 β1 Θ0) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P0) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P) in h; auto.
Qed.

Lemma a_sub_flex_swap_junk : forall β0 β1 NM M P0 Θ0 Ξ α A Θ1,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  β0 <> α -> β1 <> α ->
  β0 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P0 ->
  β1 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P0 ->
  a_sub_flex NM M P0 Θ0 Ξ α (swap_pskl β0 β1 A) (swap_aenv β0 β1 Θ1).
Proof.
  intros * Hd Hne0 Hne1 H0 H1.
  apply notin_union_split in H0; destruct H0 as [h0 H0].
  apply notin_union_split in H0; destruct H0 as [h0' h0''].
  apply notin_union_split in H1; destruct H1 as [h1 H1].
  apply notin_union_split in H1; destruct H1 as [h1' h1''].
  pose proof (proj2 (a_sub_sub_flex_swap β0 β1) _ _ _ _ _ _ _ _ Hd) as h.
  rewrite (swap_aenv_fresh_id β0 β1 Θ0) in h; auto.
  rewrite (swap_aenv_fresh_id β0 β1 Ξ) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P0) in h; auto.
  rewrite (swap_atom_other β0 β1 α) in h; auto.
Qed.

(** The consumer's Barendregt fact: after the junk swap, the walked-out β0
    is out of the output's domain — provided β1 was picked fresh for it. *)
Lemma swap_junk_dom_out : forall β0 β1 (Θ1 : aenv),
  β1 `notin` dom Θ1 ->
  β0 `notin` dom (swap_aenv β0 β1 Θ1).
Proof.
  intros * Hn Hc.
  pose proof (swap_aenv_dom_in_rev β0 β1 Θ1 β0 Hc) as h.
  rewrite swap_atom_l in h. contradiction.
Qed.

(** A set index is fixed by a swap of two atoms outside it.  Stated in the
    [S' [=] swap_atoms a b S] orientation the set-indexed equivariance
    lemmas consume (cf. [eq_swap_atoms_add]). *)
Lemma eq_swap_atoms_fresh : forall a b (S : atoms),
  a `notin` S -> b `notin` S -> S [=] swap_atoms a b S.
Proof.
  intros * Ha Hb y. split; intros Hy.
  - apply swap_atoms_spec.
    destruct (y == a); [ subst; contradiction | ].
    destruct (y == b); [ subst; contradiction | ].
    rewrite swap_atom_other; auto.
  - apply swap_atoms_spec in Hy.
    destruct (y == a); [ subst; rewrite swap_atom_l in Hy; contradiction | ].
    destruct (y == b); [ subst; rewrite swap_atom_r in Hy; contradiction | ].
    rewrite swap_atom_other in Hy; auto.
Qed.

(** The consis mutual's junk renames — the same consumption shape as the
    [a_sub] pair above, for the eight re-attaching rules of the
    assign/unify walk.  Every INPUT (context, pending suffix, subjects,
    skeletons, set indexes) is fixed pointwise; only the OUTPUTS move. *)
Lemma a_assign_swap_junk : forall β0 β1 Θ0 Ξ α P Θ1,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  β0 <> α -> β1 <> α ->
  β0 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  β1 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ (swap_aenv β0 β1 Θ1) }}a.
Proof.
  intros * Hd Hne0 Hne1 H0 H1.
  apply notin_union_split in H0; destruct H0 as [h0 H0].
  apply notin_union_split in H0; destruct H0 as [h0' h0''].
  apply notin_union_split in H1; destruct H1 as [h1 H1].
  apply notin_union_split in H1; destruct H1 as [h1' h1''].
  pose proof (proj1 (a_assign_unify_consis_swap β0 β1) _ _ _ _ _ Hd) as h.
  rewrite (swap_aenv_fresh_id β0 β1 Θ0) in h; auto.
  rewrite (swap_aenv_fresh_id β0 β1 Ξ) in h; auto.
  rewrite (swap_atom_other β0 β1 α) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P) in h; auto.
Qed.

Lemma a_unify_swap_junk : forall β0 β1 Θ0 α β Θ1,
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  β0 <> α -> β1 <> α -> β0 <> β -> β1 <> β ->
  β0 `notin` ftvar_in_aenv Θ0 -> β1 `notin` ftvar_in_aenv Θ0 ->
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ (swap_aenv β0 β1 Θ1) }}a.
Proof.
  intros * Hd Hnα0 Hnα1 Hnβ0 Hnβ1 H0 H1.
  pose proof (proj1 (proj2 (a_assign_unify_consis_swap β0 β1))
                _ _ _ _ Hd) as h.
  rewrite (swap_aenv_fresh_id β0 β1 Θ0) in h; auto.
  rewrite (swap_atom_other β0 β1 α) in h; auto.
  rewrite (swap_atom_other β0 β1 β) in h; auto.
Qed.

Lemma a_consis_swap_junk : forall β0 β1 Δ1 Δ2 Θ0 P0 P Q Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
  β0 `notin` Δ1 `union` Δ2 ->
  β1 `notin` Δ1 `union` Δ2 ->
  β0 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
     `union` ftvar_in_pskl P ->
  β1 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
     `union` ftvar_in_pskl P ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ (swap_pskl β0 β1 Q)
    ⊣ (swap_aenv β0 β1 Θ1) }}a.
Proof.
  intros * Hd HS0 HS1 H0 H1.
  apply notin_union_split in H0; destruct H0 as [h0 H0].
  apply notin_union_split in H0; destruct H0 as [h0' h0''].
  apply notin_union_split in H1; destruct H1 as [h1 H1].
  apply notin_union_split in H1; destruct H1 as [h1' h1''].
  pose proof (proj2 (proj2 (a_assign_unify_consis_swap β0 β1))
                _ _ _ _ _ _ _ Hd Δ1 Δ2
                (eq_swap_atoms_fresh β0 β1 Δ1 ltac:(solve_notin_auto) ltac:(solve_notin_auto))
                (eq_swap_atoms_fresh β0 β1 Δ2 ltac:(solve_notin_auto) ltac:(solve_notin_auto)))
    as h.
  rewrite (swap_aenv_fresh_id β0 β1 Θ0) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P0) in h; auto.
  rewrite (swap_pskl_fresh_id β0 β1 P) in h; auto.
Qed.

(* ===================================================================== *)
(*  §13b  The Barendregt output premises LOSE NOTHING                     *)
(*                                                                        *)
(*  [a_sub_flex__assign] / [__skip] / [__skip_rigid] constrain their own   *)
(*  OUTPUT ([β ∉ dom Θ1]), which a reader is right to be suspicious of:    *)
(*  a rule that filters what its premise produced can, a priori, REJECT    *)
(*  where the reference implementation succeeds (there a global counter    *)
(*  makes the collision impossible, so no check is ever needed).           *)
(*                                                                        *)
(*  It cannot.  A derivation is finitely supported, so a γ fresh for its   *)
(*  whole output always exists, and equivariance moves the run to that γ   *)
(*  ([a_sub_swap_junk] / [a_sub_flex_swap_junk] fix every INPUT pointwise) *)
(*  — whereupon [swap_junk_dom_out] discharges the premise.  So the rule   *)
(*  fires whenever the premise-free version would, with the run's          *)
(*  GENERATED names transposed and nothing else touched: the premise is    *)
(*  an honest statement of the paper's Barendregt convention, not a        *)
(*  strengthening of the algorithm.  (This is why the encoding is          *)
(*  admissible at all; see DESIGN.md §4.3.)                                *)
(*                                                                        *)
(*  ⭐ THEY ARE ALSO HALF OF AN OPEN TODO.  What this section argues ABOUT  *)
(*  the encoding is what docs/HANDOFF-extractable-algo-encoding.md proposes *)
(*  to MAKE the encoding: a second rule set whose freshness does not        *)
(*  constrain its own output, bridged to this one.  If that lands, these    *)
(*  eleven stop being reader-facing justification and become the bridge's   *)
(*  proof obligations — and this ⛔ note goes with them.                     *)
(*                                                                        *)
(*  ⛔ ALL ELEVEN [*_no_loss] LEMMAS BELOW ARE UNREFERENCED ON PURPOSE and  *)
(*  MUST NOT BE DELETED BY AN ORPHAN SWEEP.  They are consumed by the       *)
(*  READER, not by a proof: they are the argument that the exists-fresh     *)
(*  encoding is admissible, so having no consumer is exactly what they are  *)
(*  for.  ⭐ THE SUFFIX IS THE MARKER — [_no_loss] means "encoding          *)
(*  justification, keep"; see CLAUDE.md's lemma-naming rules and the [E]    *)
(*  legend in docs/AUDIT-dead-names.txt.                                    *)
(* ===================================================================== *)

Lemma a_sub_flex_skip_no_loss : forall NM M P0 Θ0 Θ1 Ξ α β A,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  α <> β ->
  β `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P0 ->
  exists γ, γ `notin` dom Θ1 /\
    a_sub_flex NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α
      (swap_pskl β γ A) ((β ~ abind_flex_mono) ++ swap_aenv β γ Θ1).
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P0 `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_sub_flex__skip.
  - exact Hne.
  - clear - Hfr; fsetdec.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_sub_flex_swap_junk;
      [ exact Hd | auto | clear - Fr; fsetdec | exact Hfr
      | clear - Fr; fsetdec ].
Qed.

Lemma a_sub_flex_skip_rigid_no_loss : forall NM M P0 Θ0 Θ1 Ξ α β A,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  α <> β ->
  β `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P0 ->
  exists γ, γ `notin` dom Θ1 /\
    a_sub_flex NM M P0 ((β ~ abind_tvar) ++ Θ0) Ξ α
      (swap_pskl β γ A) ((β ~ abind_tvar) ++ swap_aenv β γ Θ1).
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P0 `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_sub_flex__skip_rigid.
  - exact Hne.
  - clear - Hfr; fsetdec.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_sub_flex_swap_junk;
      [ exact Hd | auto | clear - Fr; fsetdec | exact Hfr
      | clear - Fr; fsetdec ].
Qed.

(** Flex-Assign's premise is the MAIN judgment over the merged context; the
    walked definition [τ] cannot mention its own [β̂] (scope discipline), and
    that is the only extra hypothesis.  [α = β] is allowed, exactly as in the
    rule — there the subject reduces to [τ], which is [β]-free too. *)
Lemma a_sub_flex_assign_no_loss : forall NM M P0 Θ0 Θ1 Ξ α β τ A,
  a_sub NM (mode_fn M) (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
    (Ξ ++ Θ0) (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) A Θ1 ->
  (* stated on the premise's own MERGED context, since [ftvar_in_aenv]'s
     app-distribution lives downstream of this file *)
  β `notin` ftvar_in_aenv (Ξ ++ Θ0)
     `union` ftvar_in_pskl (ptyp_to_pskl τ) ->
  exists γ, γ `notin` dom Θ1 /\
    a_sub_flex NM M P0 ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α
      (swap_pskl β γ A) ((β ~ abind_flex_mono_def τ) ++ swap_aenv β γ Θ1).
Proof.
  intros * Hd Hfr.
  (* the substituted slots are β-free: every β of [P0] is replaced, and the
     replacement [τ] is β-free *)
  assert (Hsub0 : β `notin` ftvar_in_pskl
                    (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  P0 (ptyp_to_pskl τ) β) as Hup.
    clear - Hup Hfr. fsetdec. }
  assert (Hsubs : β `notin` ftvar_in_pskl
                    (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  (pskl_var_f α) (ptyp_to_pskl τ) β) as Hup.
    clear - Hup Hfr. simpl in Hup. fsetdec. }
  assert (HΞΘ : β `notin` ftvar_in_aenv (Ξ ++ Θ0)) by (clear - Hfr; fsetdec).
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv (Ξ ++ Θ0)
                    `union` ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
                    `union` ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                           (pskl_var_f α))).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_sub_flex__assign.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_sub_swap_junk;
      [ exact Hd
      | clear - HΞΘ Hsub0 Hsubs; fsetdec
      | clear - Fr; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §13c  The same argument for the assign/unify WALK's eight rules        *)
(*                                                                        *)
(*  §13b settled the three [a_sub_flex] rows; these are the eight rows     *)
(*  the [F]-deletion put the premise on ([a_assign__assign] / [__skip] /   *)
(*  [__skip_rigid] / [__skip_tm_var] / [__skip_tm_skl],                    *)
(*  [a_unify__flex_assign] / [__flex_skip] / [__skip_other]).  Same six    *)
(*  lines each, over §13's junk-swap corollaries: a fresh γ exists         *)
(*  because a derivation is finitely supported, equivariance moves the     *)
(*  run to it fixing every INPUT, and [swap_junk_dom_out] discharges the   *)
(*  premise.  So none of the eight can reject where a premise-free         *)
(*  version would fire.                                                    *)
(* ===================================================================== *)

(* ---------------------------------------------------------- a_assign --- *)

Lemma a_assign_skip_no_loss : forall Θ0 Θ1 Ξ α β P,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  α <> β ->
  β `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((β ~ abind_flex_mono) ++ swap_aenv β γ Θ1) }}a.
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_assign__skip.
  - exact Hne.
  - clear - Hfr; fsetdec.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_assign_swap_junk;
      [ exact Hd | clear - Hne; auto | clear - Fr; fsetdec
      | exact Hfr | clear - Fr; fsetdec ].
Qed.

Lemma a_assign_skip_rigid_no_loss : forall Θ0 Θ1 Ξ α β P,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  α <> β ->
  β `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((β ~ abind_tvar) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((β ~ abind_tvar) ++ swap_aenv β γ Θ1) }}a.
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_assign__skip_rigid.
  - clear - Hfr; fsetdec.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_assign_swap_junk;
      [ exact Hd | clear - Hne; auto | clear - Fr; fsetdec
      | exact Hfr | clear - Fr; fsetdec ].
Qed.

Lemma a_assign_skip_tm_var_no_loss : forall Θ0 Θ1 Ξ α x Q P,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  α <> x ->
  x `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((x ~ abind_var_typ Q) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((x ~ abind_var_typ Q) ++ swap_aenv x γ Θ1) }}a.
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_assign__skip_tm_var.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_assign_swap_junk;
      [ exact Hd | clear - Hne; auto | clear - Fr; fsetdec
      | exact Hfr | clear - Fr; fsetdec ].
Qed.

Lemma a_assign_skip_tm_skl_no_loss : forall Θ0 Θ1 Ξ α x Q P,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  α <> x ->
  x `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
     `union` ftvar_in_pskl P ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((x ~ abind_var_skl Q) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((x ~ abind_var_skl Q) ++ swap_aenv x γ Θ1) }}a.
Proof.
  intros * Hd Hne Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
                    `union` ftvar_in_pskl P `union` singleton α).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_assign__skip_tm_skl.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_assign_swap_junk;
      [ exact Hd | clear - Hne; auto | clear - Fr; fsetdec
      | exact Hfr | clear - Fr; fsetdec ].
Qed.

(** Assign-Assign's premise is CONSISTENCY over the merged context; as in
    §13b's [a_sub_flex_assign_no_loss], the substituted slots are β-free
    because every [β] of [P] is replaced and the replacement [τ] is β-free.
    [α = β] is allowed, exactly as in the rule. *)
Lemma a_assign_assign_no_loss : forall Θ0 Θ1 Ξ α β τ P Q,
  {{ (Ξ ++ Θ0) ⊢[ empty | empty
       | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) ]
    (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ∼ Q ⊣ Θ1 }}a ->
  a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α ->
  β `notin` ftvar_in_aenv (Ξ ++ Θ0)
     `union` ftvar_in_pskl (ptyp_to_pskl τ) ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((β ~ abind_flex_mono_def τ) ++ swap_aenv β γ Θ1) }}a.
Proof.
  intros * Hd Hfl Hfr.
  assert (Hsub0 : β `notin` ftvar_in_pskl
                    (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  P (ptyp_to_pskl τ) β) as Hup.
    clear - Hup Hfr. fsetdec. }
  assert (Hsubs : β `notin` ftvar_in_pskl
                    (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  (pskl_var_f α) (ptyp_to_pskl τ) β) as Hup.
    clear - Hup Hfr. simpl in Hup. fsetdec. }
  assert (HΞΘ : β `notin` ftvar_in_aenv (Ξ ++ Θ0)) by (clear - Hfr; fsetdec).
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv (Ξ ++ Θ0)
                    `union` ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
                    `union` ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                           (pskl_var_f α))).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_assign__assign with (τ := τ) (Q := swap_pskl β γ Q).
  - exact Hfl.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_consis_swap_junk;
      [ exact Hd | clear; fsetdec | clear; fsetdec
      | clear - HΞΘ Hsub0 Hsubs; fsetdec
      | clear - Fr; fsetdec ].
Qed.

(* ----------------------------------------------------------- a_unify --- *)

Lemma a_unify_flex_skip_no_loss : forall Θ0 Θ1 α1 α β,
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  α1 <> α -> α1 <> β ->
  α1 `notin` ftvar_in_aenv Θ0 ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((α1 ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
      ⊣ ((α1 ~ abind_flex_mono) ++ swap_aenv α1 γ Θ1) }}a.
Proof.
  intros * Hd Hnα Hnβ Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0
                    `union` singleton α `union` singleton β).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_unify__flex_skip.
  - exact Hnα.
  - exact Hnβ.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_unify_swap_junk;
      [ exact Hd | exact Hnα | clear - Fr; fsetdec | exact Hnβ
      | clear - Fr; fsetdec | exact Hfr | clear - Fr; fsetdec ].
Qed.

Lemma a_unify_skip_other_no_loss : forall Θ0 Θ1 c b α β,
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  (b = abind_tvar \/
   (exists Q, b = abind_var_typ Q) \/
   (exists Q, b = abind_var_skl Q)) ->
  c <> α -> c <> β ->
  c `notin` ftvar_in_aenv Θ0 ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((c ~ b) ++ Θ0) ⊲ α ≈ᵘ β ⊣ ((c ~ b) ++ swap_aenv c γ Θ1) }}a.
Proof.
  intros * Hd Hb Hnα Hnβ Hfr.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0
                    `union` singleton α `union` singleton β).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_unify__skip_other.
  - exact Hb.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_unify_swap_junk;
      [ exact Hd | exact Hnα | clear - Fr; fsetdec | exact Hnβ
      | clear - Fr; fsetdec | exact Hfr | clear - Fr; fsetdec ].
Qed.

(** Flex-Flex-Assign, the back-edge into consistency.  Both substituted
    slots are α1-free: the substitution rewrites the two subjects, which the
    rule's own [α1 ≠ α] / [α1 ≠ β] keep apart from [α1], and the walked
    definition [τ] cannot mention its own [α1] (scope discipline) — the same
    extra hypothesis §13b's [a_sub_flex_assign_no_loss] carries. *)
Lemma a_unify_flex_assign_no_loss : forall Θ0 Θ1 α1 τ α β Q,
  {{ Θ0 ⊢[ empty | empty
       | (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β))) ]
    (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))) ∼ Q ⊣ Θ1 }}a ->
  a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) α ->
  a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β ->
  α1 <> α -> α1 <> β ->
  α1 `notin` ftvar_in_aenv Θ0 `union` ftvar_in_ptyp τ ->
  exists γ, γ `notin` dom Θ1 /\
    {{ ((α1 ~ abind_flex_mono_def τ) ++ Θ0) ⊲ α ≈ᵘ β
      ⊣ ((α1 ~ abind_flex_mono_def τ) ++ swap_aenv α1 γ Θ1) }}a.
Proof.
  intros * Hd Hflα Hflβ Hnα Hnβ Hfr.
  assert (Hs : forall x, α1 <> x ->
            α1 `notin` ftvar_in_pskl
              (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f x)))).
  { intros x Hx. rewrite ftvar_ptyp_to_pskl.
    pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                  (ptyp_var_f x) τ α1) as Hup.
    clear - Hup Hx Hfr. simpl in Hup. fsetdec. }
  pose proof (Hs α Hnα) as Hsα. pose proof (Hs β Hnβ) as Hsβ.
  pick fresh γ for (dom Θ1 `union` ftvar_in_aenv Θ0
                    `union` ftvar_in_pskl
                        (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
                    `union` ftvar_in_pskl
                        (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1
                                         (ptyp_var_f α)))).
  exists γ. split; [ clear - Fr; fsetdec | ].
  apply a_unify__flex_assign with (τ := τ) (Q := swap_pskl α1 γ Q).
  - exact Hflα.
  - exact Hflβ.
  - apply swap_junk_dom_out. clear - Fr; fsetdec.
  - apply a_consis_swap_junk;
      [ exact Hd | clear; fsetdec | clear; fsetdec
      | clear - Hfr Hsα Hsβ; fsetdec
      | clear - Fr; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §14  Equivariance: the θ-algebra (metasubstitutions, ≡ᵗ/≡ˢ, a_inc)     *)
(* ===================================================================== *)

Lemma a_tyequiv_swap : forall a b Θ A B,
  {{ Θ ⊢ A ≡ᵗ B }}a ->
  {{ (swap_aenv a b Θ) ⊢ (swap_ptyp a b A) ≡ᵗ (swap_ptyp a b B) }}a.
Proof.
  intros * H; induction H; simpl.
  - apply a_tyequiv__refl. auto using lc_ptyp_swap.
  - apply a_tyequiv__sym; auto.
  - eapply a_tyequiv__trans; eauto.
  - apply a_tyequiv__flex_def.
    exact (swap_aenv_binds a b _ _ _ H).
  - apply a_tyequiv__arrow; auto.
  - apply a_tyequiv__all with (L := swap_atoms a b L).
    intros α0 Hα0.
    assert (hin : swap_atom a b α0 `notin` L)
      by (intro hc; apply Hα0; apply swap_atoms_spec; exact hc).
    specialize (H0 _ hin).
    rewrite !swap_ptyp_open in H0. simpl in H0.
    rewrite swap_atom_invol in H0. exact H0.
Qed.

(* ===================================================================== *)
(*  §15  The KEY-swap (source-only) transport for ζ ∷ Θ1 ⊑ Θ               *)
(*                                                                        *)
(*  In the P7a rows the OUTPUT context Θ1 is junk-swapped but the SOLUTION *)
(*  Θ is not — and for Flex-SkipRigid the walked β may legitimately occur  *)
(*  in Θ (rigids pair by name), so ζ cannot be fully swapped.  The mixed   *)
(*  transport swaps ζ's KEYS and the SOURCE only; its per-payload          *)
(*  obligations reduce to POINTWISE lookup equalities, discharged from     *)
(*  source well-formedness — an occurrence of the junk name in a payload   *)
(*  is flex-bound in the tail, hence ζ-keyed.                              *)
(* ===================================================================== *)

Definition kswap_msubst (a b : atom) (ζ : metasubst) : metasubst :=
  List.map (fun e => (swap_atom a b (fst e), snd e)) ζ.

Lemma msubst_lookup_kswap_other : forall a b (ζ : metasubst) γ,
  γ <> a -> γ <> b ->
  msubst_lookup (kswap_msubst a b ζ) γ = msubst_lookup ζ γ.
Proof.
  intros a b ζ γ Ha Hb; induction ζ as [| [y τ] ζ']; simpl; [reflexivity |].
  destruct (γ == y) as [e | n0].
  - rewrite <- e. rewrite (swap_atom_other a b γ Ha Hb).
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [_ | n1]
    end; [reflexivity | exfalso; apply n1; reflexivity].
  - match goal with
    | |- (if ?t then _ else _) = _ => destruct t as [e1 | n1]
    end.
    + exfalso. apply n0.
      rewrite <- (swap_atom_invol a b y), <- e1.
      symmetry. apply swap_atom_other; auto.
    + exact IHζ'.
Qed.

Lemma msubst_lookup_kswap_keyed : forall a b (ζ : metasubst),
  a <> b ->
  ~ List.In b (List.map fst ζ) ->
  List.In a (List.map fst ζ) ->
  msubst_lookup (kswap_msubst a b ζ) b = msubst_lookup ζ a.
Proof.
  intros a b ζ Hne; induction ζ as [| [y τ] ζ']; intros Hnb Hin;
    simpl in *.
  - contradiction.
  - destruct (a == y) as [e | n0].
    + rewrite <- e. rewrite swap_atom_l.
      match goal with
      | |- context [if ?t then _ else _] => destruct t as [_ | n1]
      end; [reflexivity | exfalso; apply n1; reflexivity].
    + destruct Hin as [e | Hin']; [exfalso; congruence |].
      assert (hyb : y <> b) by (intro; apply Hnb; left; auto).
      assert (hya : y <> a) by congruence.
      match goal with
      | |- (if ?t then _ else _) = _ => destruct t as [e1 | n1]
      end.
      * exfalso. rewrite (swap_atom_other a b y) in e1 by auto. congruence.
      * apply IHζ'; auto.
Qed.

Lemma msubst_ptyp_kswap : forall a b (ζ : metasubst) A,
  a <> b ->
  ~ List.In b (List.map fst ζ) ->
  b `notin` ftvar_in_ptyp A ->
  (a `notin` ftvar_in_ptyp A \/ List.In a (List.map fst ζ)) ->
  msubst_ptyp (kswap_msubst a b ζ) (swap_ptyp a b A) = msubst_ptyp ζ A.
Proof.
  intros a b ζ A Hne Hnb; induction A; simpl; intros HbA HaA;
    try solve [reflexivity].
  - (* var_f *)
    destruct (α == a) as [e | n0].
    + subst α. rewrite swap_atom_l.
      apply msubst_lookup_kswap_keyed; auto.
      destruct HaA as [h | h]; [exfalso; fsetdec | exact h].
    + assert (α <> b) by fsetdec.
      rewrite (swap_atom_other a b α) by auto.
      apply msubst_lookup_kswap_other; auto.
  - (* arrow *)
    f_equal; [apply IHA1 | apply IHA2]; try fsetdec;
      destruct HaA as [h | h]; auto; left; fsetdec.
  - (* all *)
    f_equal. apply IHA; [fsetdec |].
    destruct HaA as [h | h]; [left; fsetdec | right; exact h].
Qed.

Lemma msubst_pskl_kswap : forall a b (ζ : metasubst) P,
  a <> b ->
  ~ List.In b (List.map fst ζ) ->
  b `notin` ftvar_in_pskl P ->
  (a `notin` ftvar_in_pskl P \/ List.In a (List.map fst ζ)) ->
  msubst_pskl (kswap_msubst a b ζ) (swap_pskl a b P) = msubst_pskl ζ P.
Proof.
  intros a b ζ P Hne Hnb; induction P; simpl; intros HbP HaP;
    try solve [reflexivity].
  - (* var_f *)
    destruct (α == a) as [e | n0].
    + subst α. rewrite swap_atom_l. f_equal.
      apply msubst_lookup_kswap_keyed; auto.
      destruct HaP as [h | h]; [exfalso; fsetdec | exact h].
    + assert (α <> b) by fsetdec.
      rewrite (swap_atom_other a b α) by auto.
      f_equal. apply msubst_lookup_kswap_other; auto.
  - (* arrow *)
    f_equal; [apply IHP1 | apply IHP2]; try fsetdec;
      destruct HaP as [h | h]; auto; left; fsetdec.
  - (* all_syn *)
    f_equal. apply IHP; [fsetdec |].
    destruct HaP as [h | h]; [left; fsetdec | right; exact h].
  - (* univ_ghost *)
    f_equal. apply IHP; [fsetdec |].
    destruct HaP as [h | h]; [left; fsetdec | right; exact h].
Qed.

(** ζ's keys are source names (both directions). *)
Lemma a_inc_keys_dom : forall (κ : metasubst) (Θs Θt : aenv) γ,
  κ ∷ Θs ⊑ Θt -> List.In γ (List.map fst κ) -> γ `in` dom Θs.
Proof.
  intros * H; induction H; simpl; intros Hin; try contradiction;
    try solve [ destruct Hin as [e | Hin]; [subst; fsetdec |
                pose proof (IHa_inc Hin); fsetdec ]
              | pose proof (IHa_inc Hin); fsetdec ].
Qed.

Lemma a_inc_flex_in_keys : forall (κ : metasubst) (Θs Θt : aenv) γ,
  κ ∷ Θs ⊑ Θt -> a_flex_tvar Θs γ -> List.In γ (List.map fst κ).
Proof.
  intros * H; induction H; simpl; intros Hf;
    destruct Hf as [Hf | [τ0 Hf]];
    try solve [ inversion Hf ];
    destruct Hf as [Heq | Hf];
    try solve [ inversion Heq; subst; left; reflexivity
              | inversion Heq
              | right; apply IHa_inc; left; assumption
              | right; apply IHa_inc; right; eexists; eassumption
              | apply IHa_inc; left; assumption
              | apply IHa_inc; right; eexists; eassumption ].
Qed.

(** Free variables of a wf type / scoped skeleton are tvar-ish bound. *)
Lemma a_wf_ptyp_ftv_binds : forall (Θ : aenv) A γ,
  a_wf_ptyp Θ A -> γ `in` ftvar_in_ptyp A -> a_binds_tvar γ Θ.
Proof.
  intros * H; induction H; simpl; intros Hγ; try solve [fsetdec].
  - (* var *) assert (γ = α) by fsetdec. subst. exact H.
  - (* arrow *)
    assert (γ `in` ftvar_in_ptyp A1 \/ γ `in` ftvar_in_ptyp A2) as [h | h]
      by fsetdec; auto.
  - (* all *)
    destruct (atom_fresh (L `union` singleton γ)) as [α Hα].
    assert (hγ : γ `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A (ptyp_var_f α))).
    { pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A (ptyp_var_f α)).
      fsetdec. }
    assert (hb : a_binds_tvar γ ((α ~ abind_tvar) ++ Θ))
      by (apply H0; auto).
    destruct hb as [hb | [hb | [τ hb]]];
      (destruct hb as [heq | hb];
       [ inversion heq; subst; exfalso; fsetdec
       | unfold a_binds_tvar; auto; right; right; exists τ; exact hb ]).
Qed.

Lemma a_scope_pskl_ftv_binds : forall (Θ : aenv) P γ,
  a_scope_pskl Θ P -> γ `in` ftvar_in_pskl P -> a_binds_tvar γ Θ.
Proof.
  intros * H; induction H; simpl; intros Hγ; try solve [fsetdec | auto].
  - (* var *) assert (γ = α) by fsetdec. subst. exact H.
  - (* arrow *)
    assert (γ `in` ftvar_in_pskl P1 \/ γ `in` ftvar_in_pskl P2) as [h | h]
      by fsetdec; auto.
  - (* all *)
    destruct (atom_fresh (L `union` singleton γ)) as [α Hα].
    assert (hγ : γ `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α)).
      fsetdec. }
    assert (hb : a_binds_tvar γ ((α ~ abind_tvar) ++ Θ))
      by (apply H0; auto).
    destruct hb as [hb | [hb | [τ hb]]];
      (destruct hb as [heq | hb];
       [ inversion heq; subst; exfalso; fsetdec
       | unfold a_binds_tvar; auto; right; right; exists τ; exact hb ]).
Qed.

(** The precision component's term equality: swapping the run's output
    skeleton and ζ's keys leaves the ζ-image unchanged. *)
Lemma msubst_bskl_kswap_paint : forall a b (ζ : metasubst) P,
  a <> b ->
  ~ List.In b (List.map fst ζ) ->
  b `notin` ftvar_in_pskl P ->
  (a `notin` ftvar_in_pskl P \/ List.In a (List.map fst ζ)) ->
  msubst_bskl (kswap_msubst a b ζ) (pskl_to_bskl_syn (swap_pskl a b P))
  = msubst_bskl ζ (pskl_to_bskl_syn P).
Proof.
  intros a b ζ P Hne Hnb; induction P; simpl; intros HbP HaP;
    try solve [reflexivity].
  - (* var_f *)
    destruct (α == a) as [e | n0].
    + subst α. rewrite swap_atom_l. f_equal. f_equal.
      apply msubst_lookup_kswap_keyed; auto.
      destruct HaP as [h | h]; [exfalso; fsetdec | exact h].
    + assert (α <> b) by fsetdec.
      rewrite (swap_atom_other a b α) by auto.
      f_equal. f_equal. apply msubst_lookup_kswap_other; auto.
  - (* arrow *)
    f_equal; [apply IHP1 | apply IHP2]; try fsetdec;
      destruct HaP as [h | h]; auto; left; fsetdec.
  - (* all_syn *)
    f_equal. apply IHP; [fsetdec |].
    destruct HaP as [h | h]; [left; fsetdec | right; exact h].
  - (* univ_ghost *)
    f_equal. apply IHP; [fsetdec |].
    destruct HaP as [h | h]; [left; fsetdec | right; exact h].
Qed.

(** A head entry whose key avoids the target is inert. *)
Lemma msubst_bskl_head_notin : forall β τβ (ζ : metasubst) Q,
  β `notin` ftvar_in_bskl Q ->
  msubst_bskl ((β, τβ) :: ζ) Q = msubst_bskl ζ Q.
Proof.
  intros β τβ ζ Q; induction Q; simpl; intros Hn; f_equal;
    try solve [reflexivity | apply IHQ; fsetdec
              | apply IHQ1; fsetdec | apply IHQ2; fsetdec].
  (* var_f *)
  match goal with
  | |- context [if ?t then _ else _] => destruct t as [e | ?]
  end; [exfalso; fsetdec | reflexivity].
Qed.

(** The equivalence component: composing with an id metasubstitution keyed
    away from the swap pair erases the key-swap. *)
Lemma msubst_compose_kswap_id : forall a b (ζ κ1 : metasubst),
  is_id_msubst κ1 ->
  (forall α, List.In α (List.map fst κ1) -> α <> a /\ α <> b) ->
  msubst_compose (kswap_msubst a b ζ) κ1 = msubst_compose ζ κ1.
Proof.
  intros a b ζ κ1; induction κ1 as [| [α τ] κ1']; intros Hid Hk;
    [reflexivity |].
  inversion Hid as [| e κl he hl]; subst.
  unfold is_id_entry in he; simpl in he. subst τ.
  unfold msubst_compose; simpl.
  destruct (Hk α (or_introl eq_refl)) as [ha hb].
  f_equal.
  - f_equal. apply msubst_lookup_kswap_other; auto.
  - apply IHκ1'; auto.
    intros α0 h0. apply Hk. right. exact h0.
Qed.

Local Lemma dom_ftvar_aenv : forall Θ : aenv, dom Θ [<=] ftvar_in_aenv Θ.
Proof. induction Θ as [| [x bd] Θ']; simpl; fsetdec. Qed.

(** §15's HEADLINE — the source-only transport.  Hypotheses:
    the source is well formed; b avoids everything the source mentions;
    a's bindings in the source (if any) are FLEXIBLE (in the P7a rows a is
    the walked-out β: never rigid in the output — rigids of an output come
    from the input, which excludes β — and never a term variable). *)
Lemma a_inc_kswap : forall a b (ζ : metasubst) (Θ1 Θ : aenv),
  ζ ∷ Θ1 ⊑ Θ ->
  a <> b ->
  {{ ⊢ Θ1 }}a ->
  b `notin` ftvar_in_aenv Θ1 ->
  (forall bd, binds a bd Θ1 ->
     bd = abind_flex_mono \/ exists τ, bd = abind_flex_mono_def τ) ->
  (kswap_msubst a b ζ) ∷ (swap_aenv a b Θ1) ⊑ Θ.
Proof.
  intros a b ζ Θ1 Θ Hinc; induction Hinc; intros Hne Hwf Hb Ha; simpl.
  - (* empty *) apply a_inc__empty; auto.
  - (* flex *)
    apply a_inc__flex; auto.
    apply IHHinc;
      [ exact Hne
      | inversion Hwf; auto
      | simpl in Hb; fsetdec
      | intros bd hbd; apply Ha; right; exact hbd ].
  - (* flex_def: the payload equality via the pointwise kswap lemma *)
    inversion Hwf; subst.
    assert (hkeys : ~ List.In b (List.map fst κ)).
    { intro hc. pose proof (a_inc_keys_dom _ _ _ _ Hinc hc) as hd.
      simpl in Hb. pose proof (dom_ftvar_aenv Θ). fsetdec. }
    apply a_inc__flex_def; auto.
    + apply IHHinc;
        [ exact Hne
        | assumption
        | simpl in Hb; fsetdec
        | intros bd hbd; apply Ha; right; exact hbd ].
    + rewrite msubst_ptyp_kswap; auto.
      * simpl in Hb. fsetdec.
      * destruct (AtomSetProperties.In_dec a (ftvar_in_ptyp τ)) as [hin | hout];
          [right | left; exact hout].
        match goal with
        | h : a_wf_ptyp _ τ |- _ =>
            pose proof (a_wf_ptyp_ftv_binds _ _ _ h hin) as hbt
        end.
        destruct hbt as [hbt | [hbt | [τ0 hbt]]].
        -- exfalso.
           destruct (Ha abind_tvar) as [hc | [τ1 hc]];
             [right; exact hbt | discriminate | discriminate].
        -- eapply a_inc_flex_in_keys; eauto. left; exact hbt.
        -- eapply a_inc_flex_in_keys; eauto. right; eexists; exact hbt.
  - (* var (type entry) *)
    inversion Hwf; subst.
    assert (hxa : x <> a).
    { intro; subst x.
      destruct (Ha (abind_var_typ A)) as [hc | [τ1 hc]];
        [left; reflexivity | discriminate | discriminate]. }
    assert (hxb : x <> b) by (simpl in Hb; fsetdec).
    assert (hkeys : ~ List.In b (List.map fst κ)).
    { intro hc. pose proof (a_inc_keys_dom _ _ _ _ Hinc hc) as hd.
      simpl in Hb. pose proof (dom_ftvar_aenv Θ). fsetdec. }
    rewrite (swap_atom_other a b x) by auto.
    apply a_inc__var; auto.
    + apply IHHinc;
        [ exact Hne
        | assumption
        | simpl in Hb; fsetdec
        | intros bd hbd; apply Ha; right; exact hbd ].
    + rewrite msubst_ptyp_kswap; auto.
      * simpl in Hb. fsetdec.
      * destruct (AtomSetProperties.In_dec a (ftvar_in_ptyp A)) as [hin | hout];
          [right | left; exact hout].
        match goal with
        | h : a_wf_ptyp _ A |- _ =>
            pose proof (a_wf_ptyp_ftv_binds _ _ _ h hin) as hbt
        end.
        destruct hbt as [hbt | [hbt | [τ0 hbt]]].
        -- exfalso.
           destruct (Ha abind_tvar) as [hc | [τ1 hc]];
             [right; exact hbt | discriminate | discriminate].
        -- eapply a_inc_flex_in_keys; eauto. left; exact hbt.
        -- eapply a_inc_flex_in_keys; eauto. right; eexists; exact hbt.
  - (* var_skl (skeleton entry) *)
    inversion Hwf; subst.
    assert (hxa : x <> a).
    { intro; subst x.
      destruct (Ha (abind_var_skl P)) as [hc | [τ1 hc]];
        [left; reflexivity | discriminate | discriminate]. }
    assert (hxb : x <> b) by (simpl in Hb; fsetdec).
    assert (hkeys : ~ List.In b (List.map fst κ)).
    { intro hc. pose proof (a_inc_keys_dom _ _ _ _ Hinc hc) as hd.
      simpl in Hb. pose proof (dom_ftvar_aenv Θ). fsetdec. }
    rewrite (swap_atom_other a b x) by auto.
    apply a_inc__var_skl; auto.
    + apply IHHinc;
        [ exact Hne
        | assumption
        | simpl in Hb; fsetdec
        | intros bd hbd; apply Ha; right; exact hbd ].
    + rewrite msubst_pskl_kswap; auto.
      * simpl in Hb. fsetdec.
      * destruct (AtomSetProperties.In_dec a (ftvar_in_pskl P)) as [hin | hout];
          [right | left; exact hout].
        match goal with
        | h : {{ _ ⨟ empty ⊢ₚₛ P }}a |- _ =>
            pose proof (a_scope_pskl_ftv_binds _ _ _ (a_scope_pskl_of_wf h) hin)
              as hbt
        end.
        destruct hbt as [hbt | [hbt | [τ0 hbt]]].
        -- exfalso.
           destruct (Ha abind_tvar) as [hc | [τ1 hc]];
             [right; exact hbt | discriminate | discriminate].
        -- eapply a_inc_flex_in_keys; eauto. left; exact hbt.
        -- eapply a_inc_flex_in_keys; eauto. right; eexists; exact hbt.
  - (* tvar *)
    inversion Hwf; subst.
    assert (hxa : α <> a).
    { intro; subst α.
      destruct (Ha abind_tvar) as [hc | [τ1 hc]];
        [left; reflexivity | discriminate | discriminate]. }
    assert (hxb : α <> b) by (simpl in Hb; fsetdec).
    rewrite (swap_atom_other a b α) by auto.
    apply a_inc__tvar; auto.
    apply IHHinc;
      [ exact Hne
      | assumption
      | simpl in Hb; fsetdec
      | intros bd hbd; apply Ha; right; exact hbd ].
Qed.

(* ##################################################################### *)
(*  §6 — TERM BINDERS.                                                    *)
(*                                                                        *)
(*  The term-variable half of the equivariance primitive: a swap of two   *)
(*  atoms fresh for a binding or a context leaves it unchanged.           *)
(*                                                                        *)
(*  ⚠️ These were elaborated under [Set Implicit Arguments] in their old    *)
(*  home, and this file deliberately has none (see the header); their     *)
(*  callers rely on the arguments it makes implicit.  So the flag is      *)
(*  turned on for this section ONLY and off again at the end: §1–§5 keep  *)
(*  the explicit-argument policy the header argues for, and §6 keeps the  *)
(*  elaboration it was written under.                                     *)
(* ##################################################################### *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  K6 — TERM-VARIABLE RENAMING for cofinite binder rows.                *)
(*                                                                       *)
(*  ⭐ The route is the standing directive's: EQUIVARIANCE is the one     *)
(*  renaming primitive.  prop_swap.v already proves it for the whole      *)
(*  algorithmic tower; what was missing is the bridge that turns a SWAP   *)
(*  of two atoms into the RENAMING of a term binder — which it is        *)
(*  exactly when both atoms are fresh for everything else in sight.       *)
(*                                                                       *)
(*  ⚙ ITS CONSUMER RETIRED 2026-08-13 — see the ⛔ note at the end of      *)
(*  this section.  [a_pat] went exists-fresh, and with it went            *)
(*  [a_pat_rename_tm], the only lemma this bridge was built for.          *)
(* ===================================================================== *)

(** A binding the two swapped atoms do not occur in is untouched. *)
Lemma swap_abind_fresh_eq : forall x y (b : abind),
  x `notin` ftvar_in_abind b ->
  y `notin` ftvar_in_abind b ->
  swap_abind x y b = b.
Proof.
  intros x y b Hx Hy; destruct b; simpl in *; try reflexivity; f_equal;
    first [ apply swap_ptyp_fresh_id | apply swap_pskl_fresh_id ];
    assumption.
Qed.

(** …hence a whole context the two atoms are fresh for. *)
Lemma swap_aenv_fresh_eq : forall x y Θ,
  x `notin` (dom Θ `union` ftvar_in_aenv Θ) ->
  y `notin` (dom Θ `union` ftvar_in_aenv Θ) ->
  swap_aenv x y Θ = Θ.
Proof.
  induction Θ as [ | [z c] Θ' IH ]; intros Hx Hy; simpl in *;
    [ reflexivity | ].
  f_equal.
  - f_equal.
    + unfold swap_atom.
      destruct (z == x) as [->|Hzx]; [ exfalso; clear - Hx; fsetdec | ].
      destruct (z == y) as [->|Hzy]; [ exfalso; clear - Hy; fsetdec | ].
      reflexivity.
    + apply swap_abind_fresh_eq; [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  - apply IH; [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
Qed.

(* ===================================================================== *)
(*  K6, LAST PIECE — RETIRED 2026-08-13 with the exists-fresh conversion   *)
(*  of [a_pat]'s four binder rows (fresco/algo/def_rules.v).                *)
(*                                                                        *)
(*  ⛔ [a_pat_rename_tm] IS GONE, AND IT CANNOT COME BACK IN THIS SHAPE.   *)
(*  It renamed a term binder across an [a_pat] run — the hybrid that       *)
(*  SWAPS the type-level data and SUBSTITUTES in the term — and its ONLY   *)
(*  consumers were the four binder rows of [a_pat_complete], which used it *)
(*  to REGENERATE a cofinite family from the IH's one instance.            *)
(*  Exists-fresh rows need one instance, so all four calls went with the   *)
(*  conversion.                                                            *)
(*                                                                        *)
(*  ⚠️ AND IT IS NOT MERELY UNUSED — restated over the converted rules it   *)
(*  is NOT PROVABLE.  Its binder rows needed [b ∉ fvar_in_exp (open e x)], *)
(*  i.e. [b <> x].  Cofinitely that was free: the row picked its own [x]   *)
(*  away from [b].  Exists-fresh the row HANDS OVER an [x] the statement   *)
(*  cannot constrain, and no hypothesis on [Θ0]/[Θ1]/[e] bounds it — the   *)
(*  conclusion's output [Ξ ++ Θ2] has had [x] removed.  A size induction    *)
(*  does not rescue it either: the inner rename would need                 *)
(*  [x ∉ ftvar_in_exp e], which the row does not state.                    *)
(*                                                                        *)
(*  ⚙ WHAT STAYED, and why it is not orphan sweepings.                     *)
(*  [swap_aenv_fresh_eq] has three live consumers in                       *)
(*  typing/prop_completeness_typing.v (theorem 4 keeps its own K6, over    *)
(*  the DECLARATIVE cofinite rows, which is a different lemma).            *)
(*  [swap_abind_fresh_eq] is its helper.                                   *)
(* ===================================================================== *)


Unset Implicit Arguments.

(* ##################################################################### *)
(*  §16  THE TRANSPOSITION ON TERMS                                       *)
(*                                                                       *)
(*  [swap_exp] and the facts the extractable encoding's equivariance      *)
(*  lemmas for skeleton inference and typing need (ext_algo/prop_pat.v    *)
(*  §4, ext_algo/prop_typing.v §3).                                       *)
(*                                                                       *)
(*  ⚠️ THOSE ROWS BIND A TERM VARIABLE, so equivariance has to act on the  *)
(*  SUBJECT too.  A statement with the term held fixed does NOT work: the *)
(*  binder rows recurse on [open_exp_wrt_exp e (exp_var_f x)], and the    *)
(*  hypothesis would then need [a <> x] and [b <> x] for a binder the row *)
(*  chooses.  Swapping the term makes the row's own binder move with      *)
(*  everything else, which is what a transposition is for.               *)
(* ##################################################################### *)

Set Implicit Arguments.

Fixpoint swap_exp (a b : atom) (e : exp) : exp :=
  match e with
  | exp_unit          => exp_unit
  | exp_var_b n       => exp_var_b n
  | exp_var_f x       => exp_var_f (swap_atom a b x)
  | exp_abs e1        => exp_abs (swap_exp a b e1)
  | exp_abs_anno A e1 => exp_abs_anno (swap_ptyp a b A) (swap_exp a b e1)
  | exp_app e1 e2     => exp_app (swap_exp a b e1) (swap_exp a b e2)
  | exp_anno e1 A     => exp_anno (swap_exp a b e1) (swap_ptyp a b A)
  | exp_freeze e1     => exp_freeze (swap_exp a b e1)
  end.

Lemma swap_exp_open_rec : forall a b e u k,
  swap_exp a b (open_exp_wrt_exp_rec k u e)
  = open_exp_wrt_exp_rec k (swap_exp a b u) (swap_exp a b e).
Proof.
  intros a b e; induction e; intros u k; simpl; f_equal; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma swap_exp_open_var : forall a b e x,
  swap_exp a b (open_exp_wrt_exp e (exp_var_f x))
  = open_exp_wrt_exp (swap_exp a b e) (exp_var_f (swap_atom a b x)).
Proof. intros. apply swap_exp_open_rec. Qed.

(** A term neither atom occurs in — as a TERM variable or inside an
    annotation — is fixed. *)
Lemma swap_exp_fresh_id : forall a b e,
  a `notin` fvar_in_exp e `union` ftvar_in_exp e ->
  b `notin` fvar_in_exp e `union` ftvar_in_exp e ->
  swap_exp a b e = e.
Proof.
  intros a b e; induction e; simpl; intros Ha Hb; f_equal;
    solve [ reflexivity
          | apply IHe; clear - Ha Hb; fsetdec
          | apply IHe1; clear - Ha Hb; fsetdec
          | apply IHe2; clear - Ha Hb; fsetdec
          | apply swap_ptyp_fresh_id; clear - Ha Hb; fsetdec
          | apply swap_atom_other; clear - Ha Hb; fsetdec ].
Qed.

(** The check rows' γ-FILTER on the discarded suffix transports.  ⚙ It is
    not a set fact: the filter quantifies over [dom Ξ], and an atom of
    [dom (swap Ξ)] is the swap-image of one of [dom Ξ] only by INVOLUTION. *)
Lemma swap_block_ftv_filter : forall a b (Ξ : aenv) A,
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
  forall γ, γ `in` dom (swap_aenv a b Ξ) ->
            γ `notin` ftvar_in_ptyp (swap_ptyp a b A).
Proof.
  intros a b Ξ A Hf γ Hγ.
  pose proof (swap_ptyp_ftv_notin a b A (swap_atom a b γ)
                (Hf _ (swap_aenv_dom_in_rev a b Ξ γ Hγ))) as h.
  rewrite swap_atom_invol in h. exact h.
Qed.

Unset Implicit Arguments.
