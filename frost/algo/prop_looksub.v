(** BASICS for the constraint-collection layer
    ([a_looksub]/[a_lookeq]/[a_extract]) — docs/DESIGN-subtyping.md P2.

    The declaration-shape facts every re-attachment of a look output [Ξ] to
    a context needs: look only ever generates FLEXIBLE declarations (the
    single generative rule is LE-FlexR), and [a_extract] appends [guess]'s
    declarations ([a_guess_mono_decls]). *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_consis_sound.

Set Implicit Arguments.

Scheme a_looksub_mutind := Induction for a_looksub Sort Prop
  with a_lookeq_mutind := Induction for a_lookeq Sort Prop.

Combined Scheme a_looksub_lookeq_mutind
  from a_looksub_mutind, a_lookeq_mutind.

(* ===================================================================== *)
(*  §1  Look outputs are declaration-only contexts                        *)
(* ===================================================================== *)

Lemma a_looksub_lookeq_decls :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ => a_decls Ξ)
           (fun Θ α P P' Ξ 𝒞 _ => a_decls Ξ));
    intros; try solve [ assumption ]; try solve [ apply a_decls__nil ];
    try solve [ apply a_decls_app; assumption ];
    try solve [ destruct (atom_fresh L) as [β0 Hβ0]; eauto ].
  (* LE-FlexR : the single generative rule *)
  econstructor; apply a_decls__nil.
Qed.

Lemma a_looksub_decls : forall Θ α m P P' Ξ 𝒞,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_decls); eauto. Qed.

Lemma a_lookeq_decls : forall Θ α P P' Ξ 𝒞,
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ.
Proof. intros; eapply (proj2 a_looksub_lookeq_decls); eauto. Qed.

(** [guess] generates only declarations ([SK]: none; [TY]: the fresh mono
    flexibles of [a_guess_mono]). *)
Lemma a_guess_decls : forall Θ NM P Ξ P',
  a_guess Θ NM P Ξ P' -> a_decls Ξ.
Proof.
  intros Θ NM P Ξ P' H; destruct H;
    [ apply a_decls__nil | eapply a_guess_mono_decls; eauto ].
Qed.

(** The collected block holds only bare flexibles (LE-FlexR is the single
    generative rule), so it mentions exactly its own domain — the look
    counterpart of [a_guess_mono_generated_ftvar].  This is what lets the
    consumers of the TARGET-only rename below phrase their premise as the
    [dom Ξ] freshness they already have. *)
Lemma a_looksub_lookeq_generated_ftvar :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> ftvar_in_aenv Ξ [<=] dom Ξ) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> ftvar_in_aenv Ξ [<=] dom Ξ).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ => ftvar_in_aenv Ξ [<=] dom Ξ)
           (fun Θ α P P' Ξ 𝒞 _ => ftvar_in_aenv Ξ [<=] dom Ξ));
    intros; simpl; try solve [ fsetdec ];
    try solve [ destruct (atom_fresh L) as [β0 Hβ0]; eauto ];
    rewrite ftvar_in_aenv_app, dom_app; fsetdec.
Qed.

Lemma a_looksub_generated_ftvar : forall Θ α m P P' Ξ 𝒞,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_generated_ftvar); eauto. Qed.

Lemma a_lookeq_generated_ftvar : forall Θ α P P' Ξ 𝒞,
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros; eapply (proj2 a_looksub_lookeq_generated_ftvar); eauto. Qed.

Lemma a_extract_decls : forall Θ0 NM α m P P' Ξ P0,
  Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ P0 -> a_decls Ξ.
Proof.
  intros Θ0 NM α m P P' Ξ P0 H; destruct H.
  apply a_decls_app;
    [ eapply a_looksub_decls; eauto | eapply a_guess_decls; eauto ].
Qed.

(* ===================================================================== *)
(*  §2  Free variables of the collected constraints                       *)
(*                                                                        *)
(*  Every variable in a collected constraint comes from the RHS being     *)
(*  compared against, or is one of the freshly-generated flexibles in Ξ   *)
(*  (LE-FlexR).  Needed for freshness bookkeeping when re-attaching Ξ.     *)
(* ===================================================================== *)

Definition ftvar_in_cstr (c : a_cstr) : atoms :=
  match c with
  | a_cstr_sub _ P => ftvar_in_pskl P
  | a_cstr_eq P     => ftvar_in_pskl P
  end.

Fixpoint ftvar_in_cstrs (C : a_cstrs) : atoms :=
  match C with
  | nil     => empty
  | c :: C' => ftvar_in_cstr c `union` ftvar_in_cstrs C'
  end.

Lemma ftvar_in_cstrs_app : forall C1 C2,
  ftvar_in_cstrs (C1 ++ C2) [=] ftvar_in_cstrs C1 `union` ftvar_in_cstrs C2.
Proof. induction C1; intros; simpl; [ fsetdec | rewrite IHC1; fsetdec ]. Qed.

(** Renaming a variable throughout a collected constraint list.  Needed by
    the TARGET-only rename below: the collected [𝒞] is an OUTPUT, so a
    canonical renaming lemma must rename it rather than demand the source
    be absent from it (DESIGN.md §4.3, canon rule 3). *)
Definition subst_cstr (γ β : atom) (c : a_cstr) : a_cstr :=
  match c with
  | a_cstr_sub m P => a_cstr_sub m (subst_pskl_in_pskl (pskl_var_f γ) β P)
  | a_cstr_eq P    => a_cstr_eq (subst_pskl_in_pskl (pskl_var_f γ) β P)
  end.

Fixpoint subst_cstrs (γ β : atom) (C : a_cstrs) : a_cstrs :=
  match C with
  | nil     => nil
  | c :: C' => subst_cstr γ β c :: subst_cstrs γ β C'
  end.

Lemma subst_cstrs_app : forall γ β C1 C2,
  subst_cstrs γ β (C1 ++ C2) = subst_cstrs γ β C1 ++ subst_cstrs γ β C2.
Proof. induction C1; intros; simpl; [ reflexivity | rewrite IHC1; reflexivity ]. Qed.

Lemma subst_cstrs_fresh_eq : forall γ β C,
  β `notin` ftvar_in_cstrs C -> subst_cstrs γ β C = C.
Proof.
  induction C as [ | c C' IH ]; intros Hβ; simpl in *; [ reflexivity | ].
  rewrite IH by (clear - Hβ; fsetdec).
  destruct c; simpl; rewrite subst_pskl_in_pskl_fresh_eq
    by (clear - Hβ; simpl in Hβ; fsetdec); reflexivity.
Qed.

Lemma ftvar_in_cstrs_subst_upper : forall γ β C,
  ftvar_in_cstrs (subst_cstrs γ β C)
    [<=] singleton γ `union` remove β (ftvar_in_cstrs C).
Proof.
  induction C as [ | c C' IH ]; simpl; [ fsetdec | ].
  destruct c; simpl;
    match goal with |- context[ftvar_in_pskl (subst_pskl_in_pskl _ _ ?P)] =>
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f γ) β) as Hup
    end; simpl in Hup; clear - IH Hup; fsetdec.
Qed.

(* DISJUNCTIVE since the freshness campaign's cluster 3, and necessarily so:
   the five ∀ rules LEAK their binder, so a collected constraint really can
   name a variable the conclusion's target no longer shows —

     Θ ⊢ ∀b. α  ∼[α]  ∀b. b  ⤳ ·  ⨾  [ b0 ≐ ]        (LE-ForallInh, LE-Var)

   has [ftvar_in_cstrs 𝒞 = {b0}] while [ftv (∀b.b) ∪ dom · = ∅].  The exact
   bound is therefore FALSE and the repair is the same one cluster 2 made
   for [a_solve_sub_eq_ftv] / [a_solve_cstr_ftv]: an escaping variable is
   one the RUN INVENTED, and the avoid-input [Θ] is what lets us say so.
   (This lemma is exactly why look needed a context: without [Θ] the second
   disjunct cannot even be STATED, and [a_extract_output_fresh] below — the
   paper's lemma:look-output-fresh, subtyping-proofs:522 — loses its proof.) *)
Lemma a_looksub_lookeq_ftv :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall α0, α0 `in` ftvar_in_cstrs 𝒞 ->
       α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
       α0 `notin` ftvar_in_aenv Θ) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall α0, α0 `in` ftvar_in_cstrs 𝒞 ->
       α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
       α0 `notin` ftvar_in_aenv Θ).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ =>
              forall α0, α0 `in` ftvar_in_cstrs 𝒞 ->
                α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
                α0 `notin` ftvar_in_aenv Θ)
           (fun Θ α P P' Ξ 𝒞 _ =>
              forall α0, α0 `in` ftvar_in_cstrs 𝒞 ->
                α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
                α0 `notin` ftvar_in_aenv Θ));
    intros; simpl in *;
    (* the non-binder rows: constraints come from the target or from Ξ *)
    try solve [ left; match goal with Hin : _ `in` _ |- _ =>
                  clear - Hin; fsetdec end ].
  (* Twelve rows survive: five that repeat their premise verbatim, the two
     arrows, and the five BINDER rows — three of which open the TARGET, and
     those are exactly where a leaked binder can show up in 𝒞. *)
  all: try solve [ exact (H α0 H0) ].
  all: try solve [ (* the arrows: split the constraint list *)
         rewrite ftvar_in_cstrs_app in H1; rewrite dom_app;
         destruct (AtomSetProperties.In_dec α0 (ftvar_in_cstrs C1))
           as [Hin | Hin];
         [ destruct (H α0 Hin) as [Hd | Hd]
         | destruct (H0 α0 ltac:(clear - H1 Hin; fsetdec)) as [Hd | Hd] ];
         solve [ left; clear - Hd; fsetdec | right; exact Hd ] ].
  (* The five BINDER rows.  [n] is the rule's own side condition, and the
     right disjunct is inherited because the premise's context only GREW. *)
  all: destruct (H α0 H0) as [Hl | Hr].
  all: try solve [ right; clear - Hr; fsetdec ].
  all: try solve [ left; exact Hl ].   (* LS-ForallL / LE-ForallSyn: target untouched *)
  (* what remains: the three rows that OPEN THE TARGET, where the escapee may
     BE the binder — and there the rule's own freshness is the witness *)
  all: match goal with
       | Hl : _ `in` union (ftvar_in_pskl (open_pskl_wrt_pskl ?B _)) _ |- _ =>
           pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β))
             as Hup
       end; simpl in Hup;
       destruct (α0 == β) as [-> | Hne];
         [ right; clear - n; fsetdec | left; clear - Hl Hup Hne; fsetdec ].
Qed.

(* A CONSISTENCY collection only ever deposits eq constraints.  MOVED here
   from prop_look_complete_cstr.v (2026-08-01): it is a basic property of the
   judgment, and the source-substitution lemma of prop_decorate_sub.v needs it
   for its arrow rows — that file is UPSTREAM of P6-Cs.
   EXISTS-FRESH SIMPLIFICATION (cluster 3): the three ∀ rows used to hand back
   a cofinite family, and each needed a representative picked off [L]; now the
   IH is the premise's own, and the rows are plain [assumption]. *)
Lemma a_lookeq_cstr_eq : forall Θ α P P' Ξ 𝒞,
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  Forall (fun c => exists Q, c = a_cstr_eq Q) 𝒞.
Proof.
  intros Θ α P P' Ξ 𝒞 H; induction H.
  - constructor; [ eexists; reflexivity | constructor ].  (* var *)
  - constructor.                                          (* absent *)
  - constructor.                                          (* vacuous *)
  - constructor; [ eexists; reflexivity | constructor ].  (* flex_r *)
  - apply Forall_app; split; assumption.                 (* arrow *)
  - assumption.                                           (* forall_inh *)
  - assumption.                                           (* forall_syn *)
  - assumption.                                           (* univ_ghost *)
  - assumption.                                           (* univ_ghost1 *)
  - assumption.                                           (* univ_ghost2 *)
  - assumption.                                           (* univ_ghost_r *)
Qed.

Lemma a_looksub_ftv : forall Θ α m P P' Ξ 𝒞,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  forall α0, α0 `in` ftvar_in_cstrs 𝒞 ->
    α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/ α0 `notin` ftvar_in_aenv Θ.
Proof. intros * H; eapply (proj1 a_looksub_lookeq_ftv); eauto. Qed.

(* The EXACT bound, restored for the names the ambient context already
   holds.  The escape disjunct above says "the run INVENTED this name", and
   a variable of [dom Θ] is precisely one it cannot have invented — every
   generating rule avoids [ftvar_in_aenv Θ ⊇ dom Θ].  Consumers that carry a
   variable known to live in the context (the ρ-replaced variables of P6-Cs /
   P6-Ss, the extract's [α1 ∈ dom Θ0]) should use these rather than the raw
   disjunction. *)
Lemma a_looksub_ftv_ctx : forall Θ α m P P' Ξ 𝒞 α0,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  α0 `in` dom Θ ->
  α0 `notin` ftvar_in_pskl P' ->
  α0 `notin` dom Ξ ->
  α0 `notin` ftvar_in_cstrs 𝒞.
Proof.
  intros * H Hdom HP' HΞ Hin.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hdf.
  destruct (a_looksub_ftv H Hin) as [Hl | Hr];
    [ clear - Hl HP' HΞ | clear - Hdom Hdf Hr ]; fsetdec.
Qed.

Lemma a_lookeq_ftv_ctx : forall Θ α P P' Ξ 𝒞 α0,
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  α0 `in` dom Θ ->
  α0 `notin` ftvar_in_pskl P' ->
  α0 `notin` dom Ξ ->
  α0 `notin` ftvar_in_cstrs 𝒞.
Proof.
  intros * H Hdom HP' HΞ Hin.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hdf.
  destruct ((proj2 a_looksub_lookeq_ftv) _ _ _ _ _ _ H _ Hin) as [Hl | Hr];
    [ clear - Hl HP' HΞ | clear - Hdom Hdf Hr ]; fsetdec.
Qed.

(* ===================================================================== *)
(*  §3  Look freshness (lemma:look-output-fresh, subtyping-proofs:522)    *)
(*                                                                        *)
(*  The extract output's free variables come from the input skeleton      *)
(*  [P0] and the collected/guessed flexibles [Ξ] only — in particular     *)
(*  the looked-for variable α (or any variable fresh for [P0] and [Ξ])    *)
(*  does not survive into the instantiation candidate.                    *)
(* ===================================================================== *)

(* DISJUNCTIVE since the freshness campaign: [SS-ForallR] deliberately
   leaks its binder into the result (see the constructor comment), so an
   output variable is an input variable OR fresh for the solve context.
   The EXACT bound survives for eq-only constraint lists
   ([a_solve_cstr_ftv_eq]) — consistency's collections are all-eq, so the
   P6-Cs paths keep the strong form. *)
Lemma a_solve_cstr_ftv : forall Θ 𝒞 P P',
  Θ ⊩ 𝒞 ⨾ P ⤳ P' ->
  forall α, α `in` ftvar_in_pskl P' ->
    α `in` (ftvar_in_pskl P `union` ftvar_in_cstrs 𝒞) \/ α `notin` dom Θ.
Proof.
  intros Θ 𝒞 P P' H; induction H; simpl; intros α0 Hα0.
  - left; fsetdec.
  - destruct (a_solve_sub_ftv H Hα0) as [Hl | Hr];
      [ left; clear - Hl; fsetdec | right; exact Hr ].
  - pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ H) as He.
    destruct (IHa_solve_cstr α0 Hα0) as [Hl | Hr];
      [ left; clear - Hl He; fsetdec | right; exact Hr ].
Qed.

Lemma a_solve_cstr_ftv_eq : forall Θ 𝒞 P P',
  Θ ⊩ 𝒞 ⨾ P ⤳ P' ->
  Forall (fun c => exists Q, c = a_cstr_eq Q) 𝒞 ->
  ftvar_in_pskl P' [<=] ftvar_in_pskl P `union` ftvar_in_cstrs 𝒞.
Proof.
  intros Θ 𝒞 P P' H; induction H; simpl; intros Hall.
  - fsetdec.
  - (* a sub constraint contradicts the all-eq hypothesis *)
    exfalso. inversion Hall as [ | c cs Hc _ ]; subst.
    destruct Hc as [Q0 Hc]. discriminate Hc.
  - inversion Hall as [ | c cs Hc Htl ]; subst.
    pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ H) as He.
    specialize (IHa_solve_cstr Htl).
    clear - He IHa_solve_cstr. fsetdec.
Qed.

Lemma ptyp_to_pskl_ftv : forall A,
  ftvar_in_pskl (ptyp_to_pskl A) [<=] ftvar_in_ptyp A.
Proof. induction A; simpl; fsetdec. Qed.

(* The paper's lemma pins its variable only against [P0] and [Ξ]
   (subtyping-proofs:522); the mech additionally pins it inside [dom Θ0] —
   the Barendregt rendering that separates it from the LEAKED binders of
   [SS-ForallR] and of look's five ∀ rules, which avoid the whole ambient
   context by their side conditions.  Every name the consumers care about
   (the looked-for variable, context binders) lives in [dom Θ0].
   Since cluster 3 this discharges TWO "…or the run invented it" arms —
   the solve's ([a_solve_cstr_ftv]) and the look's ([a_looksub_ftv]) — and
   both die the same way: [α1 ∈ dom Θ0 ⊆ ftvar_in_aenv Θ0]. *)
Lemma a_extract_output_fresh : forall Θ0 NM α M P P0 Ξ P1 α1,
  Θ0 ⊢ P ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 ->
  α1 `in` dom Θ0 ->
  α1 `notin` ftvar_in_pskl P0 ->
  α1 `notin` dom Ξ ->
  α1 `notin` ftvar_in_pskl P1.
Proof.
  intros * Hex Hdom Hγ0 Hα1Ξ. inversion Hex; subst.
  simpl_env in Hα1Ξ.
  match goal with
  | Hlk : _ ⊢ _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ , Hsc : _ ⊩ _ ⨾ _ ⤳ _ |- _ =>
      pose proof (a_looksub_ftv Hlk) as Hb1;
      pose proof (a_solve_cstr_ftv Hsc) as Hb2
  end.
  pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdf.
  (* the shared refutation: a variable of the SOLVE's output is either an
     input variable (⇒ in 𝒞, and then the LOOK's bound applies) or a name
     one of the two runs invented (⇒ outside the ambient context) *)
  match goal with
  | Hsc : _ ⊩ ?Cx ⨾ _ ⤳ ?Qx |- _ =>
      assert (Hcore : α1 `notin` ftvar_in_pskl Qx);
      [ intro Hin; destruct (Hb2 α1 Hin) as [Hl | Hr];
        [ | apply Hr; rewrite dom_app; clear - Hdom; fsetdec ];
        assert (Hc : α1 `in` ftvar_in_cstrs Cx)
          by (clear - Hl; simpl in Hl; fsetdec);
        destruct (Hb1 α1 Hc) as [Hl2 | Hr2];
        [ clear - Hl2 Hγ0 Hα1Ξ; fsetdec | clear - Hr2 Hdom Hdf; fsetdec ]
      | ]
  end.
  match goal with
  | Hg : a_guess _ _ _ _ _ |- _ => inversion Hg; subst
  end.
  - (* SK : output = solve output *) exact Hcore.
  - (* TY : output = guessed monotype *)
    match goal with
    | Hgm : a_guess_mono _ _ _ _ |- _ =>
        pose proof (a_guess_mono_ftv Hgm) as Hb3
    end.
    intro Hin.
    match goal with
    | Hgm : a_guess_mono _ ?q _ _ |- False =>
        assert (HinQ : α1 `in` ftvar_in_pskl q)
          by (pose proof (ptyp_to_pskl_ftv A) as Hb4';
              clear - Hb3 Hb4' Hin Hα1Ξ; fsetdec)
    end.
    exact (Hcore HinQ).
Qed.

(* ===================================================================== *)
(*  §4  Stability of constraint collection under substitution             *)
(*  (lemma:constraint-collection-stable-substitution, tex:504-520,        *)
(*  forward direction).  Substituting an α-free [Q] for β ≠ α preserves   *)
(*  the collected constraints; when the substitution destroys a           *)
(*  guardedness side condition the source has become α-free, so the       *)
(*  derivation switches to the Absent rule (the paper's remark).          *)
(* ===================================================================== *)

(** An α-free source collects nothing. *)
Lemma a_looksub_lookeq_absent_nil :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ =>
              α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil)
           (fun Θ α P P' Ξ 𝒞 _ =>
              α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil));
    intros; simpl in *;
    try solve [ auto ];
    try solve [ exfalso; fsetdec ];
    try match goal with
        | IH1 : _ -> ?Ξ1 = nil /\ ?C1 = nil,
          IH2 : _ -> ?Ξ2 = nil /\ ?C2 = nil
          |- ?Ξ1 ++ ?Ξ2 = nil /\ ?C1 ++ ?C2 = nil =>
            destruct IH1 as [-> ->]; [ fsetdec | ];
            destruct IH2 as [-> ->]; [ fsetdec | ];
            auto
        end;
    (* The BINDER rows.  A source-opening rule re-derives the α-freshness of
       the opened body from its OWN side condition (which pins β ≠ α); a
       target-opening rule leaves the source alone. *)
    try match goal with
        | IH : _ `notin` ftvar_in_pskl (open_pskl_wrt_pskl ?Pb _) -> _ ,
          Hn : _ `notin` ftvar_in_pskl _ ,
          Hsc : _ `notin` add _ _ |- _ =>
            apply IH;
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          Pb (pskl_var_f β)) as Hup;
            simpl in Hup; clear - Hup Hn Hsc; fsetdec
        end;
    try match goal with
        | IH : _ -> _ = nil /\ _ = nil |- _ => apply IH; assumption
        end.
Qed.

Lemma guarded_pskl_subst : forall P P' β,
  guarded_pskl P ->
  lc_pskl P' ->
  P <> pskl_var_f β ->
  guarded_pskl (subst_pskl_in_pskl P' β P).
Proof.
  intros P P' β Hg Hlc Hne; inversion Hg; subst; simpl.
  - constructor.
  - destruct_if; [ exfalso; congruence | constructor ].
  - constructor; apply subst_pskl_in_pskl_lc_pskl; auto.
Qed.

(** The SCOPE premise [ftv P0 ⊆ α ∪ ftvar_in_aenv Θ] is the paper's Barendregt
    convention spelled out, and it is LOAD-BEARING since cluster 3: with a
    LEAKING exists-fresh binder the unconditional form is FALSE
    (cex/cex_look_subst_stable_leak.v, Qed) — a [P0] carrying the
    derivation's own binder cannot be re-derived, because every binder the
    rule may pick avoids [ftv (subst P0 β P)].  The premise is exactly what
    the ∀ rules' own side condition bites on ("the substituted skeleton
    introduces no name the judgment does not already mention"), so
    [β0 ∉ ftv P0] is DERIVED.  It names the CONTEXT (not the input
    skeletons) because only the context is MONOTONE under descent: an arrow
    row shrinks the skeletons, a binder row grows the context, and
    [ftvar_in_aenv Θ] therefore threads through both. *)

Lemma a_looksub_lookeq_subst_stable :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
     ftvar_in_pskl P0 [<=] add α (ftvar_in_aenv Θ) ->
     Θ ⊢ (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
     ftvar_in_pskl P0 [<=] add α (ftvar_in_aenv Θ) ->
     Θ ⊢ (subst_pskl_in_pskl P0 β P) ∼[ α ] P' ⤳ Ξ ⨾ 𝒞).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ =>
              forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
              ftvar_in_pskl P0 [<=] add α (ftvar_in_aenv Θ) ->
              Θ ⊢ (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞)
           (fun Θ α P P' Ξ 𝒞 _ =>
              forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
              ftvar_in_pskl P0 [<=] add α (ftvar_in_aenv Θ) ->
              Θ ⊢ (subst_pskl_in_pskl P0 β P) ∼[ α ] P' ⤳ Ξ ⨾ 𝒞));
    intros; simpl.
  - (* LS-Var *)
    destruct_if; [ exfalso; congruence | apply a_looksub__var ].
  - (* LS-Absent *)
    apply a_looksub__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β).
    fsetdec.
  - (* LS-Vacuous *)
    apply a_looksub__vacuous.
  - (* LS-Check : switch to Absent when the source was the substituted var *)
    match goal with Hg : guarded_pskl A |- _ => inversion Hg; subst end;
      simpl.
    + (* unit *)
      apply a_looksub__check;
        [ intro Hc; discriminate Hc | constructor | assumption | auto ].
    + (* var α *)
      destruct_if as [-> | HneX].
      * (* α = β : the source became α-free — switch to Absent *)
        match goal with
        | Hl : _ ⊢ _ ∼[ _ ] _ ⤳ _ ⨾ _ |- _ =>
            destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hl)
              as [-> ->]; [ simpl; fsetdec | ]
        end.
        apply a_looksub__absent. assumption.
      * apply a_looksub__check;
          [ assumption | constructor | assumption | auto ].
    + (* arrow *)
      apply a_looksub__check;
        [ intro Hc; discriminate Hc
        | constructor; apply subst_pskl_in_pskl_lc_pskl; auto
        | assumption
        | match goal with
          | IH : forall (b : atom) (q : pskl), _ |- _ =>
              let HI := fresh "HI" in
              pose proof (IH _ _ ltac:(eassumption) ltac:(eassumption)
                            ltac:(eassumption) ltac:(eassumption)) as HI;
              simpl in HI; exact HI
          end ].
  - (* LS-ForallR : only the SOURCE changes, and the scope premise keeps
       [P0] inside what the binder already avoids — so the SAME binder
       serves, no re-freshening (and hence no output renaming). *)
    apply a_looksub__forall_r with (β := β);
      [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper A P0 β0) as Hup;
        match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end | ].
    apply H; auto. match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
      clear - Hsc; cbn; fsetdec end.
  - (* LS-Arrow *)
    apply a_looksub__arrow; auto.
  - (* LS-ForallL : the source opens.  If the substituted variable IS the
       binder the substitution is vacuous (the binder avoids [ftv P]);
       otherwise it commutes with the opening. *)
    destruct (β0 == β) as [-> | Hne].
    + rewrite subst_pskl_in_pskl_fresh_eq by (clear - n; cbn; fsetdec).
      apply a_looksub__forall_l with (β := β); assumption.
    + apply a_looksub__forall_l with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup;
          match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end | ].
      rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
        [ | auto | assumption ].
      apply H; auto. match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
      clear - Hsc; cbn; fsetdec end.
  - (* LS-UnivGhostL *)
    apply a_looksub__univ_ghost_l. auto.
  - (* LE-Var *)
    destruct_if; [ exfalso; congruence | apply a_lookeq__var ].
  - (* LE-Absent *)
    apply a_lookeq__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β).
    fsetdec.
  - (* LE-Vacuous *)
    apply a_lookeq__vacuous.
  - (* LE-FlexR *)
    apply a_lookeq__flex_r.
    + (* the generated flexible still avoids the SUBSTITUTED source *)
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup.
      match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end.
    + intro Hc. destruct P; simpl in Hc; try discriminate Hc.
      revert Hc.
      destruct_if as [-> | HneX]; intro Hc.
      * (* α = β : then α ∈ ftv (var β) forces α = β, contradiction *)
        simpl in *. fsetdec.
      * inversion Hc; subst. congruence.
    + match goal with
      | |- _ `in` ftvar_in_pskl (subst_pskl_in_pskl ?Qx ?bx ?Px) =>
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Px Qx bx)
      end.
      fsetdec.
  - (* LE-Arrow *)
    apply a_lookeq__arrow; auto.
  - (* LE-ForallInh : the source opens (as LS-ForallL) *)
    destruct (β0 == β) as [-> | Hne].
    + rewrite subst_pskl_in_pskl_fresh_eq by (clear - n; cbn; fsetdec).
      apply a_lookeq__forall_inh with (β := β); assumption.
    + apply a_lookeq__forall_inh with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup;
          match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end | ].
      rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
        [ | auto | assumption ].
      apply H; auto. match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
      clear - Hsc; cbn; fsetdec end.
  - (* LE-ForallSyn : the source opens *)
    destruct (β0 == β) as [-> | Hne].
    + rewrite subst_pskl_in_pskl_fresh_eq by (clear - n; cbn; fsetdec).
      apply a_lookeq__forall_syn with (β := β); assumption.
    + apply a_lookeq__forall_syn with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup;
          match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end | ].
      rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
        [ | auto | assumption ].
      apply H; auto. match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
      clear - Hsc; cbn; fsetdec end.
  - (* LE-UnivGhost *)
    apply a_lookeq__univ_ghost. auto.
  - (* LE-UnivGhost1 : the TARGET opens; the source ∀◇ is substituted *)
    apply a_lookeq__univ_ghost1 with (β := β);
      [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup;
        match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end | ].
    match goal with
    | IH : forall (b : atom) (q : pskl), _ |- _ =>
        let HI := fresh "HI" in
        pose proof (IH _ _ ltac:(eassumption) ltac:(eassumption)
                      ltac:(eassumption) ltac:(match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
      clear - Hsc; cbn; fsetdec end)) as HI;
        simpl in HI; exact HI
    end.
  - (* LE-UnivGhost2 *)
    apply a_lookeq__univ_ghost2; auto.
  - (* LE-UnivGhostR : switch to Absent when the source was β *)
    match goal with Hg : guarded_pskl P |- _ => inversion Hg; subst end;
      simpl.
    + (* unit *)
      apply a_lookeq__univ_ghost_r;
        [ intro Hc; discriminate Hc | constructor | auto ].
    + (* var α *)
      destruct_if as [-> | HneX].
      * (* α = β : the source became α-free — switch to Absent *)
        match goal with
        | Hl : _ ⊢ _ ∼[ _ ] _ ⤳ _ ⨾ _ |- _ =>
            destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hl)
              as [-> ->]; [ simpl; fsetdec | ]
        end.
        apply a_lookeq__absent. assumption.
      * apply a_lookeq__univ_ghost_r;
          [ assumption | constructor | auto ].
    + (* arrow *)
      apply a_lookeq__univ_ghost_r;
        [ intro Hc; discriminate Hc
        | constructor; apply subst_pskl_in_pskl_lc_pskl; auto
        | match goal with
          | IH : forall (b : atom) (q : pskl), _ |- _ =>
              let HI := fresh "HI" in
              pose proof (IH _ _ ltac:(eassumption) ltac:(eassumption)
                            ltac:(eassumption) ltac:(eassumption)) as HI;
              simpl in HI; exact HI
          end ].
Qed.

Lemma a_looksub_subst_stable : forall Θ α m P P' Ξ 𝒞 β P0,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
  ftvar_in_pskl P0 [<=] add α (ftvar_in_aenv Θ) ->
  Θ ⊢ (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof. intros; eapply (proj1 a_looksub_lookeq_subst_stable); eauto. Qed.

(* ===================================================================== *)
(*  §4b  The REVERSE direction of                                         *)
(*  lemma:constraint-collection-stable-substitution                       *)
(*                                                                        *)
(*  The subtyping-completeness ForallL case (P6-Ss) needs the converse of  *)
(*  §4: a run collected on a subject in which an α-free guess has already  *)
(*  been substituted for a rigid β ≠ α can be UNDONE, recovering the very  *)
(*  same Ξ ⨾ 𝒞 at the un-substituted subject.  Only two shapes of the      *)
(*  un-substituted subject matter: it IS the binder ([pskl_var_f βg]),     *)
(*  where the run happened entirely inside the α-free guess, so §4's       *)
(*  [a_looksub_lookeq_absent_nil] empties it and LS-Absent rebuilds; or it *)
(*  is anything else, where the substitution is STRUCTURAL and the rule    *)
(*  that fired is pinned by the subject's own top constructor.            *)
(*  (subtyping-proofs.tex:2632 uses exactly this direction.)               *)
(* ===================================================================== *)

(** A subject that IS the substituted binder collects nothing: the guess is
    α-free, so [a_looksub_lookeq_absent_nil] empties the run and LS-Absent
    rebuilds it at the bare variable (βg ≠ α). *)
Lemma a_looksub_subst_var : forall Θ α m βg P' Ξ 𝒞 Pg,
  Θ ⊢ Pg ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  α `notin` ftvar_in_pskl Pg -> βg <> α ->
  Θ ⊢ (pskl_var_f βg) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof.
  intros Θ α m βg P' Ξ 𝒞 Pg H Hα Hβ.
  destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ H Hα) as [-> ->].
  apply a_looksub__absent. simpl. clear - Hβ. fsetdec.
Qed.

Lemma a_lookeq_subst_var : forall Θ α βg P' Ξ 𝒞 Pg,
  Θ ⊢ Pg ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  α `notin` ftvar_in_pskl Pg -> βg <> α ->
  Θ ⊢ (pskl_var_f βg) ∼[ α ] P' ⤳ Ξ ⨾ 𝒞.
Proof.
  intros Θ α βg P' Ξ 𝒞 Pg H Hα Hβ.
  destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ H Hα) as [-> ->].
  apply a_lookeq__absent. simpl. clear - Hβ. fsetdec.
Qed.

(** The REVERSE direction of
    [lemma:constraint-collection-stable-substitution]. *)
Lemma a_looksub_lookeq_subst_stable_rev :
  (forall Θ α m Ps P' Ξ 𝒞, Θ ⊢ Ps ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall Pu βg Pg, Ps = subst_pskl_in_pskl Pg βg Pu ->
     βg <> α -> βg `in` ftvar_in_aenv Θ ->
     α `notin` ftvar_in_pskl Pg -> lc_pskl Pg -> lc_pskl Pu ->
     Θ ⊢ Pu ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞) /\
  (forall Θ α Ps P' Ξ 𝒞, Θ ⊢ Ps ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall Pu βg Pg, Ps = subst_pskl_in_pskl Pg βg Pu ->
     βg <> α -> βg `in` ftvar_in_aenv Θ ->
     α `notin` ftvar_in_pskl Pg -> lc_pskl Pg -> lc_pskl Pu ->
     Θ ⊢ Pu ∼[ α ] P' ⤳ Ξ ⨾ 𝒞).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m Ps P' Ξ 𝒞 _ =>
              forall Pu βg Pg, Ps = subst_pskl_in_pskl Pg βg Pu ->
              βg <> α -> βg `in` ftvar_in_aenv Θ ->
              α `notin` ftvar_in_pskl Pg -> lc_pskl Pg -> lc_pskl Pu ->
              Θ ⊢ Pu ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞)
           (fun Θ α Ps P' Ξ 𝒞 _ =>
              forall Pu βg Pg, Ps = subst_pskl_in_pskl Pg βg Pu ->
              βg <> α -> βg `in` ftvar_in_aenv Θ ->
              α `notin` ftvar_in_pskl Pg -> lc_pskl Pg -> lc_pskl Pu ->
              Θ ⊢ Pu ∼[ α ] P' ⤳ Ξ ⨾ 𝒞)).
  - (* LS-Var *)
    intros Θ α m P Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    destruct (β' == βg) as [-> | Hne'].
    + subst Pg. exfalso. cbn in Hα. clear - Hα. fsetdec.
    + injection Heq as Heq'. subst β'. apply a_looksub__var.
  - (* LS-Absent *)
    intros Θ α m P P' Hnin Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    subst P. apply a_looksub__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pu Pg βg) as Hlow.
    clear - Hnin Hlow Hβ. fsetdec.
  - (* LS-Vacuous *)
    intros; apply a_looksub__vacuous.
  - (* LS-Check *)
    intros Θ α A B Ξ C Hne Hg Hg0 Hlk IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq; subst A.
    + apply a_looksub__check; assumption.
    + inversion Hg.
    + destruct (β' == βg) as [-> | Hne'].
      * eapply a_looksub_subst_var;
          [ apply a_looksub__check; eassumption | assumption | assumption ].
      * apply a_looksub__check; assumption.
    + inversion HlcPu as [ | | ? ? HlcPa HlcPb | | | ]; subst.
      apply a_looksub__check;
        [ discriminate
        | apply guarded_pskl__arrow; assumption
        | assumption
        | apply (IH (pskl_arrow Pa Pb) βg Pg);
            [ reflexivity | assumption | assumption | assumption | assumption
            | assumption ] ].
    + inversion Hg.
    + inversion Hg.
    + inversion Hg.
  - (* LS-ForallR *)
    intros Θ α A B Ξ C β Hsc Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    (* target-opening: the source is only UN-substituted, and the binder
       still avoids it because [βg] itself is a context name *)
    subst A.
    assert (Hne1 : βg <> β) by (clear - Hsc Hβin; fsetdec).
    apply a_looksub__forall_r with (β := β);
      [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pu Pg βg) as Hlow;
        clear - Hsc Hlow Hne1; fsetdec | ].
    apply (IH Pu βg Pg);
      solve [ assumption | reflexivity | clear - Hβin; cbn; fsetdec ].
  - (* LS-Arrow *)
    intros Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hlk1 IH1 Hlk2 IH2
           Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_looksub_subst_var;
        [ apply a_looksub__arrow; eassumption | assumption | assumption ].
    + inversion HlcPu as [ | | ? ? HlcPa HlcPb | | | ]; subst.
      injection Heq as Heq1 Heq2. subst P1. subst P2.
      apply a_looksub__arrow.
      * apply (IH1 Pa βg Pg); solve [ assumption | reflexivity ].
      * apply (IH2 Pb βg Pg); solve [ assumption | reflexivity ].
  - (* LS-ForallL *)
    intros Θ α m P P' Ξ C β Hsc Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_looksub_subst_var;
        [ apply a_looksub__forall_l with (β := β); [ exact Hsc | exact Hpre ]
        | assumption | assumption ].
    + inversion HlcPu as [ | | | ? Hopen | | ]; subst.
      injection Heq as Heq0. subst P.
      assert (Hne1 : βg <> β) by (clear - Hsc Hβin; fsetdec).
      apply a_looksub__forall_l with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pb Pg βg) as Hlow;
          clear - Hsc Hlow Hne1; fsetdec | ].
      apply (IH (open_pskl_wrt_pskl Pb (pskl_var_f β)) βg Pg);
        [ apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
            [ exact Hne1 | assumption ]
        | assumption | clear - Hβin; cbn; fsetdec
        | assumption | assumption | apply Hopen ].
  - (* LS-UnivGhostL *)
    intros Θ α m P P' Ξ C Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_looksub_subst_var;
        [ apply a_looksub__univ_ghost_l; exact Hpre
        | assumption | assumption ].
    + inversion HlcPu as [ | | | | | ? HlcPb ]; subst.
      injection Heq as Heq0. subst P.
      apply a_looksub__univ_ghost_l.
      apply (IH Pb βg Pg); solve [ assumption | reflexivity ].
  - (* LE-Var *)
    intros Θ α P Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    destruct (β' == βg) as [-> | Hne'].
    + subst Pg. exfalso. cbn in Hα. clear - Hα. fsetdec.
    + injection Heq as Heq'. subst β'. apply a_lookeq__var.
  - (* LE-Absent *)
    intros Θ α P P' Hnin Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    subst P. apply a_lookeq__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pu Pg βg) as Hlow.
    clear - Hnin Hlow Hβ. fsetdec.
  - (* LE-Vacuous *)
    intros; apply a_lookeq__vacuous.
  - (* LE-FlexR *)
    intros Θ α P β α1 Hfr Hne Hin Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    subst P. apply a_lookeq__flex_r.
    + (* the generated flexible avoids the UN-substituted source too: it
         avoids [ftvar_in_aenv Θ], where [βg] lives *)
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pu Pg βg) as Hlow.
      assert (Hα1βg : α1 <> βg) by (clear - Hfr Hβin; fsetdec).
      clear - Hfr Hlow Hα1βg; fsetdec.
    + intro Hc. subst Pu. cbn in Hne.
      (* destruct the scrutinee IN Hne, so its [if] actually reduces *)
      match type of Hne with context[if ?e then _ else _] => destruct e end;
        [ congruence | apply Hne; reflexivity ].
    + pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Pu Pg βg) as Hup.
      clear - Hin Hα Hup. fsetdec.
  - (* LE-Arrow *)
    intros Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hlk1 IH1 Hlk2 IH2
           Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__arrow; eassumption | assumption | assumption ].
    + inversion HlcPu as [ | | ? ? HlcPa HlcPb | | | ]; subst.
      injection Heq as Heq1 Heq2. subst P1. subst P2.
      apply a_lookeq__arrow.
      * apply (IH1 Pa βg Pg); solve [ assumption | reflexivity ].
      * apply (IH2 Pb βg Pg); solve [ assumption | reflexivity ].
  - (* LE-ForallInh *)
    intros Θ α P P' Ξ C β Hsc Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__forall_inh with (β := β); [ exact Hsc | exact Hpre ]
        | assumption | assumption ].
    + inversion HlcPu as [ | | | ? Hopen | | ]; subst.
      injection Heq as Heq0. subst P.
      assert (Hne1 : βg <> β) by (clear - Hsc Hβin; fsetdec).
      apply a_lookeq__forall_inh with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pb Pg βg) as Hlow;
          clear - Hsc Hlow Hne1; fsetdec | ].
      apply (IH (open_pskl_wrt_pskl Pb (pskl_var_f β)) βg Pg);
        [ apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
            [ exact Hne1 | assumption ]
        | assumption | clear - Hβin; cbn; fsetdec
        | assumption | assumption | apply Hopen ].
  - (* LE-ForallSyn *)
    intros Θ α P P' Ξ C β Hsc Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__forall_syn with (β := β); [ exact Hsc | exact Hpre ]
        | assumption | assumption ].
    + inversion HlcPu as [ | | | ? Hopen | | ]; subst.
      injection Heq as Heq0. subst P.
      assert (Hne1 : βg <> β) by (clear - Hsc Hβin; fsetdec).
      apply a_lookeq__forall_syn with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pb Pg βg) as Hlow;
          clear - Hsc Hlow Hne1; fsetdec | ].
      apply (IH (open_pskl_wrt_pskl Pb (pskl_var_f β)) βg Pg);
        [ apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
            [ exact Hne1 | assumption ]
        | assumption | clear - Hβin; cbn; fsetdec
        | assumption | assumption | apply Hopen ].
  - (* LE-UnivGhost *)
    intros Θ α P P' Ξ C Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__univ_ghost; exact Hpre | assumption | assumption ].
    + inversion HlcPu as [ | | | | | ? HlcPb ]; subst.
      injection Heq as Heq0. subst P.
      apply a_lookeq__univ_ghost.
      apply (IH Pb βg Pg); solve [ assumption | reflexivity ].
  - (* LE-UnivGhost1 *)
    intros Θ α P P' Ξ C β Hsc Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__univ_ghost1 with (β := β); [ exact Hsc | exact Hpre ]
        | assumption | assumption ].
    + injection Heq as Heq0. subst P.
      assert (Hne1 : βg <> β) by (clear - Hsc Hβin; fsetdec).
      apply a_lookeq__univ_ghost1 with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pb Pg βg) as Hlow;
          cbn in Hsc |- *; clear - Hsc Hlow Hne1; fsetdec | ].
      apply (IH (pskl_tophole Pb) βg Pg);
        [ reflexivity | assumption | clear - Hβin; cbn; fsetdec
        | assumption | assumption | assumption ].
  - (* LE-UnivGhost2 *)
    intros Θ α P P' Ξ C Hg Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__univ_ghost2; eassumption
        | assumption | assumption ].
    + inversion HlcPu as [ | | | | | ? HlcPb ]; subst.
      injection Heq as Heq0. subst P.
      apply a_lookeq__univ_ghost2; [ assumption | ].
      apply (IH Pb βg Pg); solve [ assumption | reflexivity ].
  - (* LE-UnivGhostR *)
    intros Θ α P P' Ξ C Hne Hg Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq; subst P.
    + apply a_lookeq__univ_ghost_r; assumption.
    + inversion Hg.
    + destruct (β' == βg) as [-> | Hne'].
      * eapply a_lookeq_subst_var;
          [ apply a_lookeq__univ_ghost_r; eassumption
          | assumption | assumption ].
      * apply a_lookeq__univ_ghost_r; assumption.
    + inversion HlcPu as [ | | ? ? HlcPa HlcPb | | | ]; subst.
      apply a_lookeq__univ_ghost_r;
        [ discriminate
        | apply guarded_pskl__arrow; assumption
        | apply (IH (pskl_arrow Pa Pb) βg Pg);
            [ reflexivity | assumption | assumption | assumption | assumption
            | assumption ] ].
    + inversion Hg.
    + inversion Hg.
    + inversion Hg.
Qed.

Lemma a_looksub_subst_stable_rev : forall Θ α m P' Ξ 𝒞 Pu βg Pg,
  Θ ⊢ (subst_pskl_in_pskl Pg βg Pu) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  βg <> α -> βg `in` ftvar_in_aenv Θ ->
  α `notin` ftvar_in_pskl Pg -> lc_pskl Pg -> lc_pskl Pu ->
  Θ ⊢ Pu ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof.
  intros; eapply (proj1 a_looksub_lookeq_subst_stable_rev);
    try eassumption; reflexivity.
Qed.

(* ===================================================================== *)
(*  §5  Rigid renames of a look run (moved from prop_look_complete_cstr,  *)
(*  2026-07-31 — the exists-fresh ForallR consumers need them below the   *)
(*  decoration layer).  This is the CANONICAL rename asset of the cluster: *)
(*  §6's rename of the looked-for variable has to MOVE binders, and it     *)
(*  moves them with the lemma proved here.                                 *)
(* ===================================================================== *)

Lemma ftv_subst_var_keep : forall P β α1 α,
  α `in` ftvar_in_pskl P -> β <> α ->
  α `in` ftvar_in_pskl (subst_pskl_in_pskl (pskl_var_f α1) β P).
Proof.
  intros P β α1 α Hin Hne.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower P (pskl_var_f α1) β) as Hlo.
  clear - Hlo Hin Hne; fsetdec.
Qed.

Lemma subst_var_pskl_neq_var : forall P β α1 α,
  P <> pskl_var_f α -> α1 <> α -> β <> α ->
  subst_pskl_in_pskl (pskl_var_f α1) β P <> pskl_var_f α.
Proof.
  intros P β α1 α Hne Hα1 Hβ Hc.
  destruct P; simpl in Hc; try discriminate Hc.
  destruct (α0 == β) as [-> | Hne2];
    [ inversion Hc; congruence | inversion Hc; subst; congruence ].
Qed.

(* (viii) SIMULTANEOUS renaming of a rigid variable on BOTH sides —
   the canonical TARGET-only form (DESIGN.md §4.3, canon rule 3): it renames
   the CONTEXT, the GENERATED block [Ξ] and the collected constraints [𝒞]
   too, and it inducts on the SUBJECT'S SIZE.

   Two campaign shapes meet here.  (1) SIZE INDUCTION, because a binder row
   may have to MOVE its binder, and a re-freshened premise is no
   sub-derivation.  (2) An OUTPUT-freshness premise on the TARGET
   ([α1 ∉ dom Ξ ∪ ftv 𝒞]) — LOAD-BEARING, and this is exactly where the LEAK
   shows: a rule's binder that ESCAPED into Ξ or 𝒞 can no longer be moved
   (moving it would change the outputs), so the target must simply differ
   from it; a binder that did NOT escape can be moved, and then the outputs
   stay fixed.  The proof does that case split at every binder row.  Without
   the premise the claim is FALSE — take the run of
   cex/cex_look_subst_stable_leak.v and rename to its own leaked binder. *)
(** Identities the rename degenerates to, and the one-step context facts the
    binder rows need. *)
Lemma subst_cstrs_same : forall β 𝒞, subst_cstrs β β 𝒞 = 𝒞.
Proof.
  induction 𝒞 as [ | c 𝒞' IH ]; cbn; [ reflexivity | ].
  rewrite IH; destruct c; cbn; rewrite subst_pskl_var_same; reflexivity.
Qed.

Lemma rename_aenv_same : forall β Θ, rename_aenv β β Θ = Θ.
Proof.
  induction Θ as [ | [x bd] Θ' IH ]; cbn; [ reflexivity | ].
  rewrite IH. destruct (x == β) as [-> | _];
    destruct bd; cbn; try rewrite subst_ptyp_in_ptyp_self;
    try rewrite subst_pskl_var_same; reflexivity.
Qed.

(** One-step context facts the binder rows need in the shape [fsetdec] can
    use (reducing [ftvar_in_aenv] under a [cons] with [cbn] would unfold the
    atom-set operations themselves). *)
Lemma ftvar_in_aenv_cons_tvar : forall β Θ,
  ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] add β (ftvar_in_aenv Θ).
Proof. intros; simpl; fsetdec. Qed.

(** ⚙ The freshness kit the binder rows run on.  Their side conditions are
    five-way unions over a context, two skeletons, a generated block and a
    constraint list, and a single [fsetdec] against five such OVERLAPPING
    hypotheses does not terminate in reasonable time (measured: >100s for one
    row).  So the rows never hand a union to [fsetdec]: [look_fresh] SPLITS
    the goal structurally with these one-liners and closes each leaf from an
    atomic hypothesis. *)
Lemma notin_union_both : forall (γ : atom) S1 S2,
  γ `notin` S1 -> γ `notin` S2 -> γ `notin` S1 `union` S2.
Proof. intros; fsetdec. Qed.

Lemma notin_add_atom : forall (γ δ : atom) S,
  γ <> δ -> γ `notin` S -> γ `notin` add δ S.
Proof. intros; fsetdec. Qed.

Lemma notin_ftvar_in_aenv_cons_tvar : forall γ δ Θ,
  γ <> δ -> γ `notin` ftvar_in_aenv Θ ->
  γ `notin` ftvar_in_aenv ((δ ~ abind_tvar) ++ Θ).
Proof. intros; simpl; fsetdec. Qed.

Lemma notin_ftvar_in_aenv_rename : forall γ α1 β Θ,
  γ <> α1 -> γ `notin` ftvar_in_aenv Θ ->
  γ `notin` ftvar_in_aenv (rename_aenv α1 β Θ).
Proof.
  intros γ α1 β Θ Hne HΘ.
  pose proof (@ftvar_in_aenv_rename_aenv Θ α1 β) as H. fsetdec.
Qed.

Lemma notin_ftvar_open_var : forall γ δ P,
  γ <> δ -> γ `notin` ftvar_in_pskl P ->
  γ `notin` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f δ)).
Proof.
  intros γ δ P Hne HP.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f δ)) as H.
  simpl in H. fsetdec.
Qed.

Lemma notin_ftvar_subst_var : forall γ α1 β P,
  γ <> α1 -> γ `notin` ftvar_in_pskl P ->
  γ `notin` ftvar_in_pskl (subst_pskl_in_pskl (pskl_var_f α1) β P).
Proof.
  intros γ α1 β P Hne HP.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f α1) β) as H.
  simpl in H. fsetdec.
Qed.

(** A variable SUBSTITUTED AWAY in a constraint list is gone from it — the
    shape a consumer that moved a leaked binder needs. *)
Lemma notin_ftvar_in_cstrs_subst_away : forall γ δ 𝒞,
  γ <> δ -> γ `notin` ftvar_in_cstrs (subst_cstrs δ γ 𝒞).
Proof.
  intros γ δ 𝒞 Hne.
  pose proof (ftvar_in_cstrs_subst_upper δ γ 𝒞) as H. fsetdec.
Qed.

Lemma notin_ftvar_in_cstrs_subst : forall γ δ β 𝒞,
  γ <> δ -> γ `notin` ftvar_in_cstrs 𝒞 ->
  γ `notin` ftvar_in_cstrs (subst_cstrs δ β 𝒞).
Proof.
  intros γ δ β 𝒞 Hne H𝒞.
  pose proof (ftvar_in_cstrs_subst_upper δ β 𝒞) as H. fsetdec.
Qed.

Ltac look_fresh_leaf :=
  first [ solve [ assumption ]
        | solve [ congruence ]
        | solve [ match goal with
                  | H : _ `notin` _ |- _ => clear - H; fsetdec
                  end ] ].

(* NB the LEAF attempt comes before the structural descents: a caller often
   holds the composite freshness ALREADY (e.g. [β ∉ ftv (open P b)] verbatim),
   and descending through [open]/[subst] would replace it by the STRICTLY
   STRONGER [β ∉ ftv P] the caller need not have. *)
Ltac look_fresh :=
  repeat first
    [ apply notin_union_both
    | apply notin_add_atom
    | look_fresh_leaf
    | apply notin_ftvar_in_aenv_cons_tvar
    | apply notin_ftvar_in_aenv_rename
    | apply notin_ftvar_open_var
    | apply notin_ftvar_in_cstrs_subst_away
    | apply notin_ftvar_in_cstrs_subst
    | apply notin_ftvar_subst_var ].

(** The look judgment reads its context ONLY through the avoid-inputs of its
    generative rules, so it is stable under any context whose [ftvar_in_aenv]
    is no LARGER — and in particular under EXCHANGE, which is what a consumer
    that opens two binders in the other order needs.  (Contexts are lists, so
    [(β~tvar) ++ (b~tvar) ++ Θ] and [(b~tvar) ++ (β~tvar) ++ Θ] are different
    terms with the same [ftvar_in_aenv].) *)
Lemma a_looksub_lookeq_ctx_ftv_mono :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall Θ', ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     Θ' ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall Θ', ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     Θ' ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞).
Proof.
  (* the binder rows all discharge the same way: the premise's context grows
     by the SAME witness on both sides, so the inclusion is preserved *)
  assert (Hcons : forall (β : atom) Θ Θ',
            ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
            ftvar_in_aenv ((β ~ abind_tvar) ++ Θ')
              [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (intros; rewrite ! ftvar_in_aenv_cons_tvar; fsetdec).
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ => forall Θ',
              ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
              Θ' ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞)
           (fun Θ α P P' Ξ 𝒞 _ => forall Θ',
              ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
              Θ' ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞)).
  - (* LS-Var *) intros. apply a_looksub__var.
  - (* LS-Absent *) intros Θ α m P P' Hnf Θ' Hm.
    apply a_looksub__absent; exact Hnf.
  - (* LS-Vacuous *) intros. apply a_looksub__vacuous.
  - (* LS-Check *) intros Θ α A B Ξ C Hne Hg Hg0 Hp IH Θ' Hm.
    apply a_looksub__check; solve [ assumption | apply IH; exact Hm ].
  - (* LS-ForallR *) intros Θ α A B Ξ C β Hfr Hp IH Θ' Hm.
    apply a_looksub__forall_r with (β := β);
      [ clear - Hfr Hm; fsetdec | apply IH; apply Hcons; exact Hm ].
  - (* LS-Arrow *) intros Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hp1 IH1 Hp2 IH2 Θ' Hm.
    apply a_looksub__arrow; [ apply IH1 | apply IH2 ]; exact Hm.
  - (* LS-ForallL *) intros Θ α m P P' Ξ C β Hfr Hp IH Θ' Hm.
    apply a_looksub__forall_l with (β := β);
      [ clear - Hfr Hm; fsetdec | apply IH; apply Hcons; exact Hm ].
  - (* LS-UnivGhostL *) intros Θ α m P P' Ξ C Hp IH Θ' Hm.
    apply a_looksub__univ_ghost_l; apply IH; exact Hm.
  - (* LE-Var *) intros. apply a_lookeq__var.
  - (* LE-Absent *) intros Θ α P P' Hnf Θ' Hm.
    apply a_lookeq__absent; exact Hnf.
  - (* LE-Vacuous *) intros. apply a_lookeq__vacuous.
  - (* LE-FlexR *) intros Θ α P β α1 Hfr Hne Hin Θ' Hm.
    apply a_lookeq__flex_r; [ clear - Hfr Hm; fsetdec | exact Hne | exact Hin ].
  - (* LE-Arrow *) intros Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hp1 IH1 Hp2 IH2 Θ' Hm.
    apply a_lookeq__arrow; [ apply IH1 | apply IH2 ]; exact Hm.
  - (* LE-ForallInh *) intros Θ α P P' Ξ C β Hfr Hp IH Θ' Hm.
    apply a_lookeq__forall_inh with (β := β);
      [ clear - Hfr Hm; fsetdec | apply IH; apply Hcons; exact Hm ].
  - (* LE-ForallSyn *) intros Θ α P P' Ξ C β Hfr Hp IH Θ' Hm.
    apply a_lookeq__forall_syn with (β := β);
      [ clear - Hfr Hm; fsetdec | apply IH; apply Hcons; exact Hm ].
  - (* LE-UnivGhost *) intros Θ α P P' Ξ C Hp IH Θ' Hm.
    apply a_lookeq__univ_ghost; apply IH; exact Hm.
  - (* LE-UnivGhost1 *) intros Θ α P P' Ξ C β Hfr Hp IH Θ' Hm.
    apply a_lookeq__univ_ghost1 with (β := β);
      [ clear - Hfr Hm; fsetdec | apply IH; apply Hcons; exact Hm ].
  - (* LE-UnivGhost2 *) intros Θ α P P' Ξ C Hg Hp IH Θ' Hm.
    apply a_lookeq__univ_ghost2; [ exact Hg | apply IH; exact Hm ].
  - (* LE-UnivGhostR *) intros Θ α P P' Ξ C Hne Hg Hp IH Θ' Hm.
    apply a_lookeq__univ_ghost_r; [ exact Hne | exact Hg | apply IH; exact Hm ].
Qed.

Lemma a_looksub_ctx_ftv_mono : forall Θ α m P P' Ξ 𝒞 Θ',
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
  Θ' ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof. intros; eapply (proj1 a_looksub_lookeq_ctx_ftv_mono); eauto. Qed.

Lemma a_lookeq_ctx_ftv_mono : forall Θ α P P' Ξ 𝒞 Θ',
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
  Θ' ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞.
Proof. intros; eapply (proj2 a_looksub_lookeq_ctx_ftv_mono); eauto. Qed.

(** EXCHANGE, the shape consumers use. *)
Lemma a_looksub_ctx_exchange : forall Θ α m P P' Ξ 𝒞 β1 β2,
  ((β1 ~ abind_tvar) ++ (β2 ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  ((β2 ~ abind_tvar) ++ (β1 ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof.
  intros. eapply a_looksub_ctx_ftv_mono; [ eassumption | ].
  rewrite ! ftvar_in_aenv_cons_tvar. fsetdec.
Qed.

Lemma a_lookeq_ctx_exchange : forall Θ α P P' Ξ 𝒞 β1 β2,
  ((β1 ~ abind_tvar) ++ (β2 ~ abind_tvar) ++ Θ) ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  ((β2 ~ abind_tvar) ++ (β1 ~ abind_tvar) ++ Θ) ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞.
Proof.
  intros. eapply a_lookeq_ctx_ftv_mono; [ eassumption | ].
  rewrite ! ftvar_in_aenv_cons_tvar. fsetdec.
Qed.

(** DERIVED junk-freeness for the look cluster (cluster 1's principle, cluster
    3's judgment): every name the run GENERATES avoids the ambient context,
    because LE-FlexR — the single generative rule — avoids [ftvar_in_aenv Θ]
    and the ∀ rules only GROW that context.  In particular a ∀ rule's own
    binder is not in the block its premise produces, which is what lets a
    consumer MOVE that binder with [Ξ] left fixed. *)
Lemma a_looksub_lookeq_generated_fresh :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall γ, γ `in` ftvar_in_aenv Θ -> γ `notin` dom Ξ) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall γ, γ `in` ftvar_in_aenv Θ -> γ `notin` dom Ξ).
Proof.
  assert (Hgrow : forall (β γ : atom) Θ,
            γ `in` ftvar_in_aenv Θ ->
            γ `in` ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (intros; rewrite ftvar_in_aenv_cons_tvar; fsetdec).
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ =>
              forall γ, γ `in` ftvar_in_aenv Θ -> γ `notin` dom Ξ)
           (fun Θ α P P' Ξ 𝒞 _ =>
              forall γ, γ `in` ftvar_in_aenv Θ -> γ `notin` dom Ξ)).
  - (* LS-Var *) intros; simpl; fsetdec.
  - (* LS-Absent *) intros; simpl; fsetdec.
  - (* LS-Vacuous *) intros; simpl; fsetdec.
  - (* LS-Check *) intros Θ α A B Ξ C Hne Hg Hg0 Hp IH γ Hγ. exact (IH γ Hγ).
  - (* LS-ForallR *) intros Θ α A B Ξ C β Hfr Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  - (* LS-Arrow *) intros Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hp1 IH1 Hp2 IH2 γ Hγ.
    rewrite dom_app.
    pose proof (IH1 γ Hγ); pose proof (IH2 γ Hγ). fsetdec.
  - (* LS-ForallL *) intros Θ α m P P' Ξ C β Hfr Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  - (* LS-UnivGhostL *) intros Θ α m P P' Ξ C Hp IH γ Hγ. exact (IH γ Hγ).
  - (* LE-Var *) intros; simpl; fsetdec.
  - (* LE-Absent *) intros; simpl; fsetdec.
  - (* LE-Vacuous *) intros; simpl; fsetdec.
  - (* LE-FlexR — the single generative rule *)
    intros Θ α P β α1 Hfr Hne Hin γ Hγ.
    simpl. clear - Hfr Hγ. fsetdec.
  - (* LE-Arrow *) intros Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hp1 IH1 Hp2 IH2 γ Hγ.
    rewrite dom_app.
    pose proof (IH1 γ Hγ); pose proof (IH2 γ Hγ). fsetdec.
  - (* LE-ForallInh *) intros Θ α P P' Ξ C β Hfr Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  - (* LE-ForallSyn *) intros Θ α P P' Ξ C β Hfr Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  - (* LE-UnivGhost *) intros Θ α P P' Ξ C Hp IH γ Hγ. exact (IH γ Hγ).
  - (* LE-UnivGhost1 *) intros Θ α P P' Ξ C β Hfr Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  - (* LE-UnivGhost2 *) intros Θ α P P' Ξ C Hg Hp IH γ Hγ. exact (IH γ Hγ).
  - (* LE-UnivGhostR *) intros Θ α P P' Ξ C Hne Hg Hp IH γ Hγ. exact (IH γ Hγ).
Qed.

(** The shape the ∀-binder consumers use: a rule's own witness is not in the
    block its premise generated, nor free in it. *)
Lemma a_looksub_binder_not_generated : forall β Θ α m P P' Ξ 𝒞,
  ((β ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  β `notin` ftvar_in_aenv Ξ.
Proof.
  intros β Θ α m P P' Ξ 𝒞 Hlk.
  pose proof (a_looksub_generated_ftvar Hlk) as Hftv.
  assert (Hin : β `in` ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (rewrite ftvar_in_aenv_cons_tvar; fsetdec).
  pose proof ((proj1 a_looksub_lookeq_generated_fresh) _ _ _ _ _ _ _ Hlk β Hin).
  fsetdec.
Qed.

Lemma a_lookeq_binder_not_generated : forall β Θ α P P' Ξ 𝒞,
  ((β ~ abind_tvar) ++ Θ) ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  β `notin` ftvar_in_aenv Ξ.
Proof.
  intros β Θ α P P' Ξ 𝒞 Hlk.
  pose proof (a_lookeq_generated_ftvar Hlk) as Hftv.
  assert (Hin : β `in` ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (rewrite ftvar_in_aenv_cons_tvar; fsetdec).
  pose proof ((proj2 a_looksub_lookeq_generated_fresh) _ _ _ _ _ _ Hlk β Hin).
  fsetdec.
Qed.

(* Every binder row takes the SAME three cases, and the split is FORCED:

     β = b   the rename's SOURCE is the rule's own binder.  [Hfr0] makes the
             substitution the identity on Θ, P and P', and the rule re-fires
             at the TARGET α1 (fresh for them by the target premise); the
             premise comes from the IH renaming b ⤳ α1, whose context is
             [rename α1 b ((b~tvar)++Θ) = (α1~tvar)++Θ].

     α1 = b  the rename's TARGET is the binder, so the binder must MOVE.  This
             is where the target's OUTPUT-freshness premise pays: α1 ∉ dom Ξ ∪
             ftv 𝒞 and α1 = b together say the binder did NOT leak, so moving
             it to a fresh δ leaves Ξ and 𝒞 fixed ([rename_aenv_fresh_eq],
             [subst_cstrs_fresh_eq] via [a_looksub_lookeq_generated_ftvar]).
             Two IH applications — b ⤳ δ, then β ⤳ α1 — and the second is
             applied to the RESULT of the first, which is why the induction
             must be on SIZE.

     else    the binder stays put; one IH application, and the side condition
             is re-established from [Hfr0] plus the ftv-upper bounds and b ≠ α1.

   The pattern is [a_solve_sub_eq_rename_size]'s (prop_solve_sub.v) and
   [a_guess_mono_rename_tvar_size]'s (prop_flex.v) — the latter is the closer
   model, since it renames the CONTEXT too. *)
Lemma a_looksub_lookeq_rename_tvar_size : forall n,
  (forall Θ α m P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') + 1 <= n ->
     Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β α1, β <> α -> α1 <> α ->
     α1 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union`
                ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
     (rename_aenv α1 β Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ≼[ α , m ]
       (subst_pskl_in_pskl (pskl_var_f α1) β P')
       ⤳ (rename_aenv α1 β Ξ) ⨾ (subst_cstrs α1 β 𝒞)) /\
  (forall Θ α P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') <= n ->
     Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β α1, β <> α -> α1 <> α ->
     α1 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union`
                ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
     (rename_aenv α1 β Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ∼[ α ]
       (subst_pskl_in_pskl (pskl_var_f α1) β P')
       ⤳ (rename_aenv α1 β Ξ) ⨾ (subst_cstrs α1 β 𝒞)).
Proof.
  induction n as [ | n IHn ].
  { split;
      [ intros Θ α m P P' Ξ 𝒞 Hn Hd | intros Θ α P P' Ξ 𝒞 Hn Hd ];
      exfalso; pose proof (size_pskl_min P); pose proof (size_pskl_min P'); lia. }
  destruct IHn as [IHs IHe].
  split.
  (* ==================== the [a_looksub] half ==================== *)
  { intros Θ α m P P' Ξ 𝒞 Hn Hd β α1 Hβα Hα1α Hfr.
    (* renaming a variable to ITSELF is the identity on all four components *)
    destruct (β == α1) as [-> | Hne0];
      [ rewrite ! rename_aenv_same, ! subst_pskl_var_same, subst_cstrs_same;
        exact Hd | ].
    destruct Hd as
      [ Θ α m Q                                   (* LS-Var *)
      | Θ α m Q Q' Hnf                            (* LS-Absent *)
      | Θ α m Q                                   (* LS-Vacuous *)
      | Θ α A B Ξ0 C0 Hne Hg Hg0 Hp               (* LS-Check *)
      | Θ α A B Ξ0 C0 b Hfr0 Hp                   (* LS-ForallR *)
      | Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hp1 Hp2   (* LS-Arrow *)
      | Θ α m Q Q' Ξ0 C0 b Hfr0 Hp                (* LS-ForallL *)
      | Θ α m Q Q' Ξ0 C0 Hp ];                    (* LS-UnivGhostL *)
      cbn in Hn, Hfr |- *.
    - (* LS-Var *)
      destruct_if; [ exfalso; congruence | apply a_looksub__var ].
    - (* LS-Absent *)
      apply a_looksub__absent.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Q (pskl_var_f α1) β)
        as Hup; cbn in Hup; clear - Hup Hnf Hα1α; fsetdec.
    - (* LS-Vacuous *) apply a_looksub__vacuous.
    - (* LS-Check *)
      apply a_looksub__check;
        [ apply subst_var_pskl_neq_var; auto
        | apply guarded_pskl_subst_var; assumption
        | apply guarded_pskl_subst_var; assumption
        | apply IHe with (Θ := Θ); solve [ lia | assumption ] ].
    - (* LS-ForallR — the TARGET opens; the binder LEAKS *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbA : b `notin` ftvar_in_pskl A) by (clear - Hfr0; fsetdec).
      assert (HbB : b `notin` ftvar_in_pskl B) by (clear - Hfr0; fsetdec).
      assert (Hα1Θ : α1 `notin` ftvar_in_aenv Θ) by (clear - Hfr; fsetdec).
      assert (Hα1A : α1 `notin` ftvar_in_pskl A) by (clear - Hfr; fsetdec).
      assert (Hα1B : α1 `notin` ftvar_in_pskl B) by (clear - Hfr; fsetdec).
      assert (Hα1Ξ : α1 `notin` dom Ξ0) by (clear - Hfr; fsetdec).
      assert (Hα1C : α1 `notin` ftvar_in_cstrs C0) by (clear - Hfr; fsetdec).
      clear Hfr Hfr0.
      destruct (β == b) as [-> | Hβb].
      + (* (i) SOURCE = the rule's own binder: every substitution is the
           identity on the inputs, and the rule re-fires at the TARGET *)
        rewrite (@rename_aenv_fresh_eq Θ α1 b) by exact HbΘ.
        rewrite (subst_pskl_in_pskl_fresh_eq A) by exact HbA.
        rewrite (subst_pskl_in_pskl_fresh_eq B) by exact HbB.
        assert (Hsz1 : 2 * (size_pskl A
                            + size_pskl (open_pskl_wrt_pskl B (pskl_var_f b)))
                       + 1 <= n)
          by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
        pose proof (IHs _ _ _ _ _ _ _ Hsz1 Hp b α1 Hbα Hα1α
                      ltac:(look_fresh)) as H1.
        rewrite rename_aenv_cons_tvar_eq in H1.
        rewrite (@rename_aenv_fresh_eq Θ α1 b) in H1 by exact HbΘ.
        rewrite (subst_pskl_in_pskl_fresh_eq A) in H1 by exact HbA.
        rewrite <- (subst_pskl_in_pskl_intro b B (pskl_var_f α1)) in H1
          by exact HbB.
        apply a_looksub__forall_r with (β := α1); [ look_fresh | exact H1 ].
      + destruct (α1 == b) as [-> | Hα1b].
        * (* (ii) TARGET = the rule's own binder.  [b ∉ dom Ξ0 ∪ ftv C0] — the
             lemma's OUTPUT-freshness premise — says the binder did NOT leak,
             so it can be moved to a fresh δ with the outputs left fixed. *)
          assert (HbΞf : b `notin` ftvar_in_aenv Ξ0)
            by (pose proof (a_looksub_generated_ftvar Hp) as HΞ;
                clear - Hα1Ξ HΞ; fsetdec).
          pick fresh δ for
            (add α (add β (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl A
               `union` ftvar_in_pskl B `union` dom Ξ0
               `union` ftvar_in_cstrs C0)))).
          assert (Hδα : δ <> α) by (clear - Fr; fsetdec).
          assert (Hδβ : δ <> β) by (clear - Fr; fsetdec).
          assert (Hδb : δ <> b) by (clear - Fr; fsetdec).
          assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; fsetdec).
          assert (HδA : δ `notin` ftvar_in_pskl A) by (clear - Fr; fsetdec).
          assert (HδB : δ `notin` ftvar_in_pskl B) by (clear - Fr; fsetdec).
          assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; fsetdec).
          assert (HδC : δ `notin` ftvar_in_cstrs C0) by (clear - Fr; fsetdec).
          clear Fr.
          assert (Hsz1 : 2 * (size_pskl A
                              + size_pskl (open_pskl_wrt_pskl B (pskl_var_f b)))
                         + 1 <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
          (* rename #1: the witness b ⤳ δ, residue-free *)
          pose proof (IHs _ _ _ _ _ _ _ Hsz1 Hp b δ Hbα Hδα
                        ltac:(look_fresh)) as H1.
          rewrite rename_aenv_cons_tvar_eq in H1.
          rewrite (@rename_aenv_fresh_eq Θ δ b) in H1 by exact HbΘ.
          rewrite (@rename_aenv_fresh_eq Ξ0 δ b) in H1 by exact HbΞf.
          rewrite (@subst_cstrs_fresh_eq δ b C0) in H1 by exact Hα1C.
          rewrite (subst_pskl_in_pskl_fresh_eq A) in H1 by exact HbA.
          rewrite <- (subst_pskl_in_pskl_intro b B (pskl_var_f δ)) in H1
            by exact HbB.
          assert (Hsz2 : 2 * (size_pskl A
                              + size_pskl (open_pskl_wrt_pskl B (pskl_var_f δ)))
                         + 1 <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
          (* rename #2: the requested β ⤳ b, on the RESULT of #1 *)
          pose proof (IHs _ _ _ _ _ _ _ Hsz2 H1 β b Hβα Hα1α
                        ltac:(look_fresh)) as H2.
          rewrite rename_aenv_cons_tvar_neq in H2 by congruence.
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var B (pskl_var_f b))
            in H2 by (solve [ congruence | constructor ]).
          apply a_looksub__forall_r with (β := δ); [ look_fresh | exact H2 ].
        * (* (iii) the binder stays put *)
          apply a_looksub__forall_r with (β := b); [ look_fresh | ].
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var B (pskl_var_f α1))
            by (solve [ congruence | constructor ]).
          rewrite <- rename_aenv_cons_tvar_neq by congruence.
          apply IHs with (Θ := (b ~ abind_tvar) ++ Θ);
            [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
            | exact Hp | exact Hβα | exact Hα1α | look_fresh ].
    - (* LS-Arrow *)
      rewrite rename_aenv_app, subst_cstrs_app.
      rewrite ftvar_in_cstrs_app, dom_app in Hfr.
      apply a_looksub__arrow;
        [ apply IHe with (Θ := Θ); solve [ lia | assumption
                                         | clear - Hfr; fsetdec ]
        | apply IHs with (Θ := Θ); solve [ lia | assumption
                                         | clear - Hfr; fsetdec ] ].
    - (* LS-ForallL — the SOURCE opens; the binder LEAKS *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      assert (Hα1Θ : α1 `notin` ftvar_in_aenv Θ) by (clear - Hfr; fsetdec).
      assert (Hα1Q : α1 `notin` ftvar_in_pskl Q) by (clear - Hfr; fsetdec).
      assert (Hα1Q' : α1 `notin` ftvar_in_pskl Q') by (clear - Hfr; fsetdec).
      assert (Hα1Ξ : α1 `notin` dom Ξ0) by (clear - Hfr; fsetdec).
      assert (Hα1C : α1 `notin` ftvar_in_cstrs C0) by (clear - Hfr; fsetdec).
      clear Hfr Hfr0.
      destruct (β == b) as [-> | Hβb].
      + (* (i) SOURCE = the rule's own binder *)
        rewrite (@rename_aenv_fresh_eq Θ α1 b) by exact HbΘ.
        rewrite (subst_pskl_in_pskl_fresh_eq Q) by exact HbQ.
        rewrite (subst_pskl_in_pskl_fresh_eq Q') by exact HbQ'.
        assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f b))
                            + size_pskl Q') + 1 <= n)
          by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
        pose proof (IHs _ _ _ _ _ _ _ Hsz1 Hp b α1 Hbα Hα1α
                      ltac:(look_fresh)) as H1.
        rewrite rename_aenv_cons_tvar_eq in H1.
        rewrite (@rename_aenv_fresh_eq Θ α1 b) in H1 by exact HbΘ.
        rewrite (subst_pskl_in_pskl_fresh_eq Q') in H1 by exact HbQ'.
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f α1)) in H1
          by exact HbQ.
        apply a_looksub__forall_l with (β := α1); [ look_fresh | exact H1 ].
      + destruct (α1 == b) as [-> | Hα1b].
        * (* (ii) TARGET = the rule's own binder: it did not leak, so move it *)
          assert (HbΞf : b `notin` ftvar_in_aenv Ξ0)
            by (pose proof (a_looksub_generated_ftvar Hp) as HΞ;
                clear - Hα1Ξ HΞ; fsetdec).
          pick fresh δ for
            (add α (add β (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
               `union` ftvar_in_pskl Q' `union` dom Ξ0
               `union` ftvar_in_cstrs C0)))).
          assert (Hδα : δ <> α) by (clear - Fr; fsetdec).
          assert (Hδβ : δ <> β) by (clear - Fr; fsetdec).
          assert (Hδb : δ <> b) by (clear - Fr; fsetdec).
          assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; fsetdec).
          assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; fsetdec).
          assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; fsetdec).
          assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; fsetdec).
          assert (HδC : δ `notin` ftvar_in_cstrs C0) by (clear - Fr; fsetdec).
          clear Fr.
          assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f b))
                              + size_pskl Q') + 1 <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
          pose proof (IHs _ _ _ _ _ _ _ Hsz1 Hp b δ Hbα Hδα
                        ltac:(look_fresh)) as H1.
          rewrite rename_aenv_cons_tvar_eq in H1.
          rewrite (@rename_aenv_fresh_eq Θ δ b) in H1 by exact HbΘ.
          rewrite (@rename_aenv_fresh_eq Ξ0 δ b) in H1 by exact HbΞf.
          rewrite (@subst_cstrs_fresh_eq δ b C0) in H1 by exact Hα1C.
          rewrite (subst_pskl_in_pskl_fresh_eq Q') in H1 by exact HbQ'.
          rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
            by exact HbQ.
          assert (Hsz2 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f δ))
                              + size_pskl Q') + 1 <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
          pose proof (IHs _ _ _ _ _ _ _ Hsz2 H1 β b Hβα Hα1α
                        ltac:(look_fresh)) as H2.
          rewrite rename_aenv_cons_tvar_neq in H2 by congruence.
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
            in H2 by (solve [ congruence | constructor ]).
          apply a_looksub__forall_l with (β := δ); [ look_fresh | exact H2 ].
        * (* (iii) the binder stays put *)
          apply a_looksub__forall_l with (β := b); [ look_fresh | ].
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α1))
            by (solve [ congruence | constructor ]).
          rewrite <- rename_aenv_cons_tvar_neq by congruence.
          apply IHs with (Θ := (b ~ abind_tvar) ++ Θ);
            [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
            | exact Hp | exact Hβα | exact Hα1α | look_fresh ].
    - (* LS-UnivGhostL *)
      apply a_looksub__univ_ghost_l;
        apply IHs with (Θ := Θ); solve [ lia | assumption ]. }
  (* ==================== the [a_lookeq] half ==================== *)
  { intros Θ α P P' Ξ 𝒞 Hn Hd β α1 Hβα Hα1α Hfr.
    destruct (β == α1) as [-> | Hne0];
      [ rewrite ! rename_aenv_same, ! subst_pskl_var_same, subst_cstrs_same;
        exact Hd | ].
    destruct Hd as
      [ Θ α Q                                     (* LE-Var *)
      | Θ α Q Q' Hnf                              (* LE-Absent *)
      | Θ α Q                                     (* LE-Vacuous *)
      | Θ α Q b γ Hfr0 Hne Hin                    (* LE-FlexR *)
      | Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hp1 Hp2     (* LE-Arrow *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hp                  (* LE-ForallInh *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hp                  (* LE-ForallSyn *)
      | Θ α Q Q' Ξ0 C0 Hp                         (* LE-UnivGhost *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hp                  (* LE-UnivGhost1 *)
      | Θ α Q Q' Ξ0 C0 Hg Hp                      (* LE-UnivGhost2 *)
      | Θ α Q Q' Ξ0 C0 Hne Hg Hp ];               (* LE-UnivGhostR *)
      cbn in Hn, Hfr |- *.
    - (* LE-Var *)
      destruct_if; [ exfalso; congruence | apply a_lookeq__var ].
    - (* LE-Absent *)
      apply a_lookeq__absent.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Q (pskl_var_f α1) β)
        as Hup; cbn in Hup; clear - Hup Hnf Hα1α; fsetdec.
    - (* LE-Vacuous *) apply a_lookeq__vacuous.
    - (* LE-FlexR : the GENERATED name is renamed with everything else — it
         may itself BE β, and the rule constrains it in no way *)
      cbn in Hfr0 |- *.
      assert (Hγb : γ <> b) by (clear - Hfr0; fsetdec).
      assert (HγΘ : γ `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HγQ : γ `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (Hγα : γ <> α) by (clear - Hfr0; fsetdec).
      assert (Hα1Θ : α1 `notin` ftvar_in_aenv Θ) by (clear - Hfr; fsetdec).
      assert (Hα1Q : α1 `notin` ftvar_in_pskl Q) by (clear - Hfr; fsetdec).
      assert (Hα1b : α1 <> b) by (clear - Hfr; fsetdec).
      assert (Hα1γ : α1 <> γ) by (clear - Hfr; fsetdec).
      destruct (γ == β) as [-> | Hγβ].
      + (* the run INVENTED β: the rule's own condition then says β occurs in
           neither the context nor the subject, so both are untouched *)
        rewrite (@rename_aenv_fresh_eq Θ α1 β) by exact HγΘ.
        rewrite (subst_pskl_in_pskl_fresh_eq Q) by exact HγQ.
        repeat destruct_if; try solve [ exfalso; congruence ];
          apply a_lookeq__flex_r; solve [ look_fresh | assumption ].
      + repeat destruct_if; try solve [ exfalso; congruence ];
          apply a_lookeq__flex_r;
            solve [ look_fresh
                  | apply subst_var_pskl_neq_var; auto
                  | apply ftv_subst_var_keep; auto ].
    - (* LE-Arrow *)
      rewrite rename_aenv_app, subst_cstrs_app.
      rewrite ftvar_in_cstrs_app, dom_app in Hfr.
      apply a_lookeq__arrow;
        [ apply IHe with (Θ := Θ); solve [ lia | assumption
                                         | clear - Hfr; fsetdec ]
        | apply IHe with (Θ := Θ); solve [ lia | assumption
                                         | clear - Hfr; fsetdec ] ].
    - (* LE-ForallInh — BOTH sides open; the binder LEAKS *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      assert (Hα1Θ : α1 `notin` ftvar_in_aenv Θ) by (clear - Hfr; fsetdec).
      assert (Hα1Q : α1 `notin` ftvar_in_pskl Q) by (clear - Hfr; fsetdec).
      assert (Hα1Q' : α1 `notin` ftvar_in_pskl Q') by (clear - Hfr; fsetdec).
      assert (Hα1Ξ : α1 `notin` dom Ξ0) by (clear - Hfr; fsetdec).
      assert (Hα1C : α1 `notin` ftvar_in_cstrs C0) by (clear - Hfr; fsetdec).
      clear Hfr Hfr0.
      destruct (β == b) as [-> | Hβb].
      + (* (i) SOURCE = the rule's own binder *)
        rewrite (@rename_aenv_fresh_eq Θ α1 b) by exact HbΘ.
        rewrite (subst_pskl_in_pskl_fresh_eq Q) by exact HbQ.
        rewrite (subst_pskl_in_pskl_fresh_eq Q') by exact HbQ'.
        assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f b))
                       + size_pskl (open_pskl_wrt_pskl Q' (pskl_var_f b))) <= n)
          by (rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia).
        pose proof (IHe _ _ _ _ _ _ Hsz1 Hp b α1 Hbα Hα1α
                      ltac:(look_fresh)) as H1.
        rewrite rename_aenv_cons_tvar_eq in H1.
        rewrite (@rename_aenv_fresh_eq Θ α1 b) in H1 by exact HbΘ.
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f α1)) in H1
          by exact HbQ.
        rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f α1)) in H1
          by exact HbQ'.
        apply a_lookeq__forall_inh with (β := α1); [ look_fresh | exact H1 ].
      + destruct (α1 == b) as [-> | Hα1b].
        * (* (ii) TARGET = the rule's own binder: it did not leak, so move it *)
          assert (HbΞf : b `notin` ftvar_in_aenv Ξ0)
            by (pose proof (a_lookeq_generated_ftvar Hp) as HΞ;
                clear - Hα1Ξ HΞ; fsetdec).
          pick fresh δ for
            (add α (add β (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
               `union` ftvar_in_pskl Q' `union` dom Ξ0
               `union` ftvar_in_cstrs C0)))).
          assert (Hδα : δ <> α) by (clear - Fr; fsetdec).
          assert (Hδβ : δ <> β) by (clear - Fr; fsetdec).
          assert (Hδb : δ <> b) by (clear - Fr; fsetdec).
          assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; fsetdec).
          assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; fsetdec).
          assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; fsetdec).
          assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; fsetdec).
          assert (HδC : δ `notin` ftvar_in_cstrs C0) by (clear - Fr; fsetdec).
          clear Fr.
          assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f b))
                       + size_pskl (open_pskl_wrt_pskl Q' (pskl_var_f b))) <= n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia).
          pose proof (IHe _ _ _ _ _ _ Hsz1 Hp b δ Hbα Hδα
                        ltac:(look_fresh)) as H1.
          rewrite rename_aenv_cons_tvar_eq in H1.
          rewrite (@rename_aenv_fresh_eq Θ δ b) in H1 by exact HbΘ.
          rewrite (@rename_aenv_fresh_eq Ξ0 δ b) in H1 by exact HbΞf.
          rewrite (@subst_cstrs_fresh_eq δ b C0) in H1 by exact Hα1C.
          rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
            by exact HbQ.
          rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f δ)) in H1
            by exact HbQ'.
          assert (Hsz2 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f δ))
                       + size_pskl (open_pskl_wrt_pskl Q' (pskl_var_f δ))) <= n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia).
          pose proof (IHe _ _ _ _ _ _ Hsz2 H1 β b Hβα Hα1α
                        ltac:(look_fresh)) as H2.
          rewrite rename_aenv_cons_tvar_neq in H2 by congruence.
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
            in H2 by (solve [ congruence | constructor ]).
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q' (pskl_var_f b))
            in H2 by (solve [ congruence | constructor ]).
          apply a_lookeq__forall_inh with (β := δ); [ look_fresh | exact H2 ].
        * (* (iii) the binder stays put *)
          apply a_lookeq__forall_inh with (β := b); [ look_fresh | ].
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α1))
            by (solve [ congruence | constructor ]).
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q' (pskl_var_f α1))
            by (solve [ congruence | constructor ]).
          rewrite <- rename_aenv_cons_tvar_neq by congruence.
          apply IHe with (Θ := (b ~ abind_tvar) ++ Θ);
            [ rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia
            | exact Hp | exact Hβα | exact Hα1α | look_fresh ].
    - (* LE-ForallSyn — the SOURCE opens; the ∀◇ target is carried through *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      assert (Hα1Θ : α1 `notin` ftvar_in_aenv Θ) by (clear - Hfr; fsetdec).
      assert (Hα1Q : α1 `notin` ftvar_in_pskl Q) by (clear - Hfr; fsetdec).
      assert (Hα1Q' : α1 `notin` ftvar_in_pskl Q') by (clear - Hfr; fsetdec).
      assert (Hα1Ξ : α1 `notin` dom Ξ0) by (clear - Hfr; fsetdec).
      assert (Hα1C : α1 `notin` ftvar_in_cstrs C0) by (clear - Hfr; fsetdec).
      clear Hfr Hfr0.
      destruct (β == b) as [-> | Hβb].
      + (* (i) SOURCE = the rule's own binder *)
        rewrite (@rename_aenv_fresh_eq Θ α1 b) by exact HbΘ.
        rewrite (subst_pskl_in_pskl_fresh_eq Q) by exact HbQ.
        rewrite (subst_pskl_in_pskl_fresh_eq Q') by exact HbQ'.
        assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f b))
                            + size_pskl (pskl_tophole Q')) <= n)
          by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
        pose proof (IHe _ _ _ _ _ _ Hsz1 Hp b α1 Hbα Hα1α
                      ltac:(look_fresh)) as H1.
        rewrite rename_aenv_cons_tvar_eq in H1.
        rewrite (@rename_aenv_fresh_eq Θ α1 b) in H1 by exact HbΘ.
        rewrite (subst_pskl_in_pskl_fresh_eq (pskl_tophole Q')) in H1
          by exact HbQ'.
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f α1)) in H1
          by exact HbQ.
        apply a_lookeq__forall_syn with (β := α1); [ look_fresh | exact H1 ].
      + destruct (α1 == b) as [-> | Hα1b].
        * (* (ii) TARGET = the rule's own binder: it did not leak, so move it *)
          assert (HbΞf : b `notin` ftvar_in_aenv Ξ0)
            by (pose proof (a_lookeq_generated_ftvar Hp) as HΞ;
                clear - Hα1Ξ HΞ; fsetdec).
          pick fresh δ for
            (add α (add β (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
               `union` ftvar_in_pskl Q' `union` dom Ξ0
               `union` ftvar_in_cstrs C0)))).
          assert (Hδα : δ <> α) by (clear - Fr; fsetdec).
          assert (Hδβ : δ <> β) by (clear - Fr; fsetdec).
          assert (Hδb : δ <> b) by (clear - Fr; fsetdec).
          assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; fsetdec).
          assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; fsetdec).
          assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; fsetdec).
          assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; fsetdec).
          assert (HδC : δ `notin` ftvar_in_cstrs C0) by (clear - Fr; fsetdec).
          clear Fr.
          assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f b))
                              + size_pskl (pskl_tophole Q')) <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
          pose proof (IHe _ _ _ _ _ _ Hsz1 Hp b δ Hbα Hδα
                        ltac:(look_fresh)) as H1.
          rewrite rename_aenv_cons_tvar_eq in H1.
          rewrite (@rename_aenv_fresh_eq Θ δ b) in H1 by exact HbΘ.
          rewrite (@rename_aenv_fresh_eq Ξ0 δ b) in H1 by exact HbΞf.
          rewrite (@subst_cstrs_fresh_eq δ b C0) in H1 by exact Hα1C.
          rewrite (subst_pskl_in_pskl_fresh_eq (pskl_tophole Q')) in H1
            by exact HbQ'.
          rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
            by exact HbQ.
          assert (Hsz2 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f δ))
                              + size_pskl (pskl_tophole Q')) <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
          pose proof (IHe _ _ _ _ _ _ Hsz2 H1 β b Hβα Hα1α
                        ltac:(look_fresh)) as H2.
          rewrite rename_aenv_cons_tvar_neq in H2 by congruence.
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
            in H2 by (solve [ congruence | constructor ]).
          apply a_lookeq__forall_syn with (β := δ); [ look_fresh | exact H2 ].
        * (* (iii) the binder stays put *)
          apply a_lookeq__forall_syn with (β := b); [ look_fresh | ].
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α1))
            by (solve [ congruence | constructor ]).
          rewrite <- rename_aenv_cons_tvar_neq by congruence.
          apply IHe with (Θ := (b ~ abind_tvar) ++ Θ) (P' := pskl_tophole Q');
            [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
            | exact Hp | exact Hβα | exact Hα1α | look_fresh ].
    - (* LE-UnivGhost *)
      apply a_lookeq__univ_ghost;
        apply IHe with (Θ := Θ); solve [ lia | assumption ].
    - (* LE-UnivGhost1 — the TARGET opens; the binder LEAKS *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      assert (Hα1Θ : α1 `notin` ftvar_in_aenv Θ) by (clear - Hfr; fsetdec).
      assert (Hα1Q : α1 `notin` ftvar_in_pskl Q) by (clear - Hfr; fsetdec).
      assert (Hα1Q' : α1 `notin` ftvar_in_pskl Q') by (clear - Hfr; fsetdec).
      assert (Hα1Ξ : α1 `notin` dom Ξ0) by (clear - Hfr; fsetdec).
      assert (Hα1C : α1 `notin` ftvar_in_cstrs C0) by (clear - Hfr; fsetdec).
      clear Hfr Hfr0.
      destruct (β == b) as [-> | Hβb].
      + (* (i) SOURCE = the rule's own binder *)
        rewrite (@rename_aenv_fresh_eq Θ α1 b) by exact HbΘ.
        rewrite (subst_pskl_in_pskl_fresh_eq Q) by exact HbQ.
        rewrite (subst_pskl_in_pskl_fresh_eq Q') by exact HbQ'.
        assert (Hsz1 : 2 * (size_pskl (pskl_tophole Q)
                       + size_pskl (open_pskl_wrt_pskl Q' (pskl_var_f b))) <= n)
          by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
        pose proof (IHe _ _ _ _ _ _ Hsz1 Hp b α1 Hbα Hα1α
                      ltac:(look_fresh)) as H1.
        rewrite rename_aenv_cons_tvar_eq in H1.
        rewrite (@rename_aenv_fresh_eq Θ α1 b) in H1 by exact HbΘ.
        rewrite (subst_pskl_in_pskl_fresh_eq (pskl_tophole Q)) in H1
          by exact HbQ.
        rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f α1)) in H1
          by exact HbQ'.
        apply a_lookeq__univ_ghost1 with (β := α1); [ look_fresh | exact H1 ].
      + destruct (α1 == b) as [-> | Hα1b].
        * (* (ii) TARGET = the rule's own binder: it did not leak, so move it *)
          assert (HbΞf : b `notin` ftvar_in_aenv Ξ0)
            by (pose proof (a_lookeq_generated_ftvar Hp) as HΞ;
                clear - Hα1Ξ HΞ; fsetdec).
          pick fresh δ for
            (add α (add β (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
               `union` ftvar_in_pskl Q' `union` dom Ξ0
               `union` ftvar_in_cstrs C0)))).
          assert (Hδα : δ <> α) by (clear - Fr; fsetdec).
          assert (Hδβ : δ <> β) by (clear - Fr; fsetdec).
          assert (Hδb : δ <> b) by (clear - Fr; fsetdec).
          assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; fsetdec).
          assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; fsetdec).
          assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; fsetdec).
          assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; fsetdec).
          assert (HδC : δ `notin` ftvar_in_cstrs C0) by (clear - Fr; fsetdec).
          clear Fr.
          assert (Hsz1 : 2 * (size_pskl (pskl_tophole Q)
                       + size_pskl (open_pskl_wrt_pskl Q' (pskl_var_f b))) <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
          pose proof (IHe _ _ _ _ _ _ Hsz1 Hp b δ Hbα Hδα
                        ltac:(look_fresh)) as H1.
          rewrite rename_aenv_cons_tvar_eq in H1.
          rewrite (@rename_aenv_fresh_eq Θ δ b) in H1 by exact HbΘ.
          rewrite (@rename_aenv_fresh_eq Ξ0 δ b) in H1 by exact HbΞf.
          rewrite (@subst_cstrs_fresh_eq δ b C0) in H1 by exact Hα1C.
          rewrite (subst_pskl_in_pskl_fresh_eq (pskl_tophole Q)) in H1
            by exact HbQ.
          rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f δ)) in H1
            by exact HbQ'.
          assert (Hsz2 : 2 * (size_pskl (pskl_tophole Q)
                       + size_pskl (open_pskl_wrt_pskl Q' (pskl_var_f δ))) <= n)
            by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
          pose proof (IHe _ _ _ _ _ _ Hsz2 H1 β b Hβα Hα1α
                        ltac:(look_fresh)) as H2.
          rewrite rename_aenv_cons_tvar_neq in H2 by congruence.
          rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q' (pskl_var_f b))
            in H2 by (solve [ congruence | constructor ]).
          apply a_lookeq__univ_ghost1 with (β := δ); [ look_fresh | exact H2 ].
        * (* (iii) the binder stays put *)
          apply a_lookeq__univ_ghost1 with (β := b); [ look_fresh | ].
          rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q' (pskl_var_f α1))
            by (solve [ congruence | constructor ]).
          rewrite <- rename_aenv_cons_tvar_neq by congruence.
          apply IHe with (Θ := (b ~ abind_tvar) ++ Θ) (P := pskl_tophole Q);
            [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
            | exact Hp | exact Hβα | exact Hα1α | look_fresh ].
    - (* LE-UnivGhost2 *)
      apply a_lookeq__univ_ghost2;
        [ apply guarded_pskl_subst_var; assumption
        | apply IHe with (Θ := Θ); solve [ lia | assumption ] ].
    - (* LE-UnivGhostR *)
      apply a_lookeq__univ_ghost_r;
        [ apply subst_var_pskl_neq_var; auto
        | apply guarded_pskl_subst_var; assumption
        | apply IHe with (Θ := Θ); solve [ lia | assumption ] ]. }
Qed.

(** The size-free forms. *)
Lemma a_looksub_rename_tvar : forall Θ α m P P' Ξ 𝒞 β α1,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  β <> α -> α1 <> α ->
  α1 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union`
             ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
  (rename_aenv α1 β Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ≼[ α , m ]
    (subst_pskl_in_pskl (pskl_var_f α1) β P')
    ⤳ (rename_aenv α1 β Ξ) ⨾ (subst_cstrs α1 β 𝒞).
Proof.
  intros. eapply (proj1 (a_looksub_lookeq_rename_tvar_size
                           (2 * (size_pskl P + size_pskl P') + 1))); eauto.
Qed.

Lemma a_lookeq_rename_tvar : forall Θ α P P' Ξ 𝒞 β α1,
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  β <> α -> α1 <> α ->
  α1 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union`
             ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
  (rename_aenv α1 β Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ∼[ α ]
    (subst_pskl_in_pskl (pskl_var_f α1) β P')
    ⤳ (rename_aenv α1 β Ξ) ⨾ (subst_cstrs α1 β 𝒞).
Proof.
  intros. eapply (proj2 (a_looksub_lookeq_rename_tvar_size
                           (2 * (size_pskl P + size_pskl P')))); eauto.
Qed.

(** The CONSUMER form: when the source occurs in NEITHER the ambient context
    NOR the run's own outputs, the rename leaves [Θ], [Ξ] and [𝒞] fixed.  This
    is the shape every call site wants, and it is DERIVED from the canonical
    target-only lemma rather than assumed — the [β] conditions are about the
    caller's own variable, and the [α1] one is the OUTPUT-freshness the leak
    forces (see the cases of the lemma above). *)
Corollary a_looksub_rename_tvar_keep : forall Θ α m P P' Ξ 𝒞 β α1,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  β <> α -> α1 <> α ->
  β `notin` ftvar_in_aenv Θ ->
  β `notin` dom Ξ -> β `notin` ftvar_in_cstrs 𝒞 ->
  α1 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union`
             ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
  Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ≼[ α , m ]
    (subst_pskl_in_pskl (pskl_var_f α1) β P') ⤳ Ξ ⨾ 𝒞.
Proof.
  intros * Hlk Hβ Hα1 HβΘ HβΞ Hβ𝒞 Hfr.
  pose proof (a_looksub_generated_ftvar Hlk) as Hftv.
  pose proof (a_looksub_rename_tvar Hlk Hβ Hα1 Hfr) as Hr.
  rewrite (@rename_aenv_fresh_eq Θ α1 β) in Hr by exact HβΘ.
  rewrite (@rename_aenv_fresh_eq Ξ α1 β) in Hr by (clear - Hftv HβΞ; fsetdec).
  rewrite (@subst_cstrs_fresh_eq α1 β 𝒞) in Hr by exact Hβ𝒞.
  exact Hr.
Qed.

Corollary a_lookeq_rename_tvar_keep : forall Θ α P P' Ξ 𝒞 β α1,
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  β <> α -> α1 <> α ->
  β `notin` ftvar_in_aenv Θ ->
  β `notin` dom Ξ -> β `notin` ftvar_in_cstrs 𝒞 ->
  α1 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union`
             ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
  Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ∼[ α ]
    (subst_pskl_in_pskl (pskl_var_f α1) β P') ⤳ Ξ ⨾ 𝒞.
Proof.
  intros * Hlk Hβ Hα1 HβΘ HβΞ Hβ𝒞 Hfr.
  pose proof (a_lookeq_generated_ftvar Hlk) as Hftv.
  pose proof (a_lookeq_rename_tvar Hlk Hβ Hα1 Hfr) as Hr.
  rewrite (@rename_aenv_fresh_eq Θ α1 β) in Hr by exact HβΘ.
  rewrite (@rename_aenv_fresh_eq Ξ α1 β) in Hr by (clear - Hftv HβΞ; fsetdec).
  rewrite (@subst_cstrs_fresh_eq α1 β 𝒞) in Hr by exact Hβ𝒞.
  exact Hr.
Qed.

(** ⭐ MOVE a look run's ∀ binder to a GIVEN opener.  The decl-side judgments
    the decoration lemmas build (a_consistag / a_subtag) are COFINITE, so every
    ∀ row has to serve a whole family of openers from the look run's ONE
    binder.  These three lemmas are that service, in the three shapes the ∀
    rules take (both sides open / only the source / only the target).

    Two things make them work: the block [Ξ] survives untouched, because a
    generated flexible can never BE an enclosing binder
    ([a_lookeq_binder_not_generated]); and the constraints 𝒞 do NOT survive —
    the binder legitimately leaks into them — so the conclusion hands back
    [subst_cstrs β b 𝒞], which a solvetag run does not mind
    ([a_solvetag_subst_cstrs], prop_decorate_sub.v).

    They are stated with the premise's skeletons ALREADY OPENED, because that
    is the shape a consumer holds after [inversion … ; subst] has eliminated
    the un-opened body's name. *)
Lemma a_lookeq_forall_move : forall Θ α P P' Ξ 𝒞 b β,
  ((b ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f b)) ∼[ α ]
    (open_pskl_wrt_pskl P' (pskl_var_f b)) ⤳ Ξ ⨾ 𝒞 ->
  b `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  β <> α ->
  β `notin` ftvar_in_aenv Θ
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P' (pskl_var_f b))
            `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
  ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
    (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ (subst_cstrs β b 𝒞).
Proof.
  intros Θ α P P' Ξ 𝒞 b β Hp Hb Hβα Hβ.
  destruct (β == b) as [-> | Hβb];
    [ rewrite subst_cstrs_same; exact Hp | ].
  assert (Hbα : b <> α) by (clear - Hb; fsetdec).
  assert (HbΞ : b `notin` ftvar_in_aenv Ξ)
    by (eapply a_lookeq_binder_not_generated; exact Hp).
  pose proof (a_lookeq_rename_tvar Hp Hbα Hβα ltac:(look_fresh)) as Hr.
  rewrite rename_aenv_cons_tvar_eq in Hr.
  rewrite (@rename_aenv_fresh_eq Θ β b) in Hr by (clear - Hb; fsetdec).
  rewrite (@rename_aenv_fresh_eq Ξ β b) in Hr by exact HbΞ.
  rewrite <- (subst_pskl_in_pskl_intro b P (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  rewrite <- (subst_pskl_in_pskl_intro b P' (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  exact Hr.
Qed.

Lemma a_lookeq_forall_move_l : forall Θ α P Pt Ξ 𝒞 b β,
  ((b ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f b)) ∼[ α ] Pt
    ⤳ Ξ ⨾ 𝒞 ->
  b `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl Pt) ->
  β <> α ->
  β `notin` ftvar_in_aenv Θ
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
            `union` ftvar_in_pskl Pt `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
  ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ] Pt
    ⤳ Ξ ⨾ (subst_cstrs β b 𝒞).
Proof.
  intros Θ α P Pt Ξ 𝒞 b β Hp Hb Hβα Hβ.
  destruct (β == b) as [-> | Hβb];
    [ rewrite subst_cstrs_same; exact Hp | ].
  assert (Hbα : b <> α) by (clear - Hb; fsetdec).
  assert (HbΞ : b `notin` ftvar_in_aenv Ξ)
    by (eapply a_lookeq_binder_not_generated; exact Hp).
  pose proof (a_lookeq_rename_tvar Hp Hbα Hβα ltac:(look_fresh)) as Hr.
  rewrite rename_aenv_cons_tvar_eq in Hr.
  rewrite (@rename_aenv_fresh_eq Θ β b) in Hr by (clear - Hb; fsetdec).
  rewrite (@rename_aenv_fresh_eq Ξ β b) in Hr by exact HbΞ.
  rewrite (subst_pskl_in_pskl_fresh_eq Pt) in Hr by (clear - Hb; fsetdec).
  rewrite <- (subst_pskl_in_pskl_intro b P (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  exact Hr.
Qed.

Lemma a_lookeq_forall_move_r : forall Θ α Ps P' Ξ 𝒞 b β,
  ((b ~ abind_tvar) ++ Θ) ⊢ Ps ∼[ α ] (open_pskl_wrt_pskl P' (pskl_var_f b))
    ⤳ Ξ ⨾ 𝒞 ->
  b `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
                     `union` ftvar_in_pskl P') ->
  β <> α ->
  β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P' (pskl_var_f b))
            `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
  ((β ~ abind_tvar) ++ Θ) ⊢ Ps ∼[ α ] (open_pskl_wrt_pskl P' (pskl_var_f β))
    ⤳ Ξ ⨾ (subst_cstrs β b 𝒞).
Proof.
  intros Θ α Ps P' Ξ 𝒞 b β Hp Hb Hβα Hβ.
  destruct (β == b) as [-> | Hβb];
    [ rewrite subst_cstrs_same; exact Hp | ].
  assert (Hbα : b <> α) by (clear - Hb; fsetdec).
  assert (HbΞ : b `notin` ftvar_in_aenv Ξ)
    by (eapply a_lookeq_binder_not_generated; exact Hp).
  pose proof (a_lookeq_rename_tvar Hp Hbα Hβα ltac:(look_fresh)) as Hr.
  rewrite rename_aenv_cons_tvar_eq in Hr.
  rewrite (@rename_aenv_fresh_eq Θ β b) in Hr by (clear - Hb; fsetdec).
  rewrite (@rename_aenv_fresh_eq Ξ β b) in Hr by exact HbΞ.
  rewrite (subst_pskl_in_pskl_fresh_eq Ps) in Hr by (clear - Hb; fsetdec).
  rewrite <- (subst_pskl_in_pskl_intro b P' (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  exact Hr.
Qed.

(* ===================================================================== *)
(*  §6  Renaming the looked-for variable                                  *)
(*                                                                        *)
(*  Collected constraints mention only input residuals, never the looked  *)
(*  variable itself, so the look run is stable under renaming it — the    *)
(*  Barendregt device that keeps the KEY decoration's substitution        *)
(*  variable clear of guessed flexible names.                             *)
(*                                                                        *)
(*  Since the freshness campaign the lemma needs the SAME two shapes §5   *)
(*  needed, and for the same reason.  (1) An OUTPUT-freshness premise on  *)
(*  the NEW name, [α' ∉ dom Ξ ∪ ftv 𝒞]: renaming the looked-for variable  *)
(*  onto a name the run itself INVENTED is not derivable — LE-FlexR's     *)
(*  generated flexible and the five ∀ rules' leaked binders both avoid    *)
(*  the looked-for variable by their own side conditions, so they would   *)
(*  have to avoid it AFTER the rename too, and cannot.  (2) SIZE          *)
(*  induction: a binder that happens to BE the new name has to be MOVED,  *)
(*  and §5's rename moves it to a derivation that is no sub-derivation of *)
(*  this one.                                                             *)
(* ===================================================================== *)

Lemma ftv_subst_var_in : forall P α α',
  α `in` ftvar_in_pskl P ->
  α' `in` ftvar_in_pskl (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  induction P as [ | | α1 | | | | ]; intros α α' Hin; simpl in *;
    try solve [ exfalso; fsetdec ].
  - destruct_if as [-> | Hne]; simpl; [ fsetdec | exfalso; fsetdec ].
  - destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P1)) as [Hi | Hni];
      [ pose proof (IHP1 _ α' Hi) | ];
      destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P2)) as [Hi2 | Hni2];
      try pose proof (IHP2 _ α' Hi2); try fsetdec.
  - eauto.
  - eauto.
Qed.

(** The renamed subject is not the NEW variable either: a subject that was
    not the old one is a different variable, and the new one is fresh for it. *)
Lemma subst_var_neq_new : forall P α α',
  P <> pskl_var_f α -> α' `notin` ftvar_in_pskl P ->
  subst_pskl_in_pskl (pskl_var_f α') α P <> pskl_var_f α'.
Proof.
  intros P α α' Hne Hα' Hc.
  destruct P; simpl in Hc; try discriminate Hc.
  destruct (α0 == α) as [-> | Hne2];
    [ congruence | inversion Hc; subst; simpl in Hα'; fsetdec ].
Qed.

Lemma a_looksub_lookeq_rename_var_size : forall n,
  (forall Θ α m P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') + 1 <= n ->
     Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall α', α' `notin` ftvar_in_pskl P ->
     α' `notin` dom Ξ -> α' `notin` ftvar_in_cstrs 𝒞 ->
     Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞) /\
  (forall Θ α P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') <= n ->
     Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall α', α' `notin` ftvar_in_pskl P ->
     α' `notin` dom Ξ -> α' `notin` ftvar_in_cstrs 𝒞 ->
     Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ∼[ α' ] P' ⤳ Ξ ⨾ 𝒞).
Proof.
  induction n as [ | n IHn ].
  { split;
      [ intros Θ α m P P' Ξ 𝒞 Hn Hd | intros Θ α P P' Ξ 𝒞 Hn Hd ];
      exfalso; pose proof (size_pskl_min P); pose proof (size_pskl_min P'); lia. }
  destruct IHn as [IHs IHe].
  split.
  (* ==================== the [a_looksub] half ==================== *)
  { intros Θ α m P P' Ξ 𝒞 Hn Hd α' Hα'P Hα'Ξ Hα'C.
    destruct Hd as
      [ Θ α m Q                                   (* LS-Var *)
      | Θ α m Q Q' Hnf                            (* LS-Absent *)
      | Θ α m Q                                   (* LS-Vacuous *)
      | Θ α A B Ξ0 C0 Hne Hg Hg0 Hp               (* LS-Check *)
      | Θ α A B Ξ0 C0 b Hfr0 Hp                   (* LS-ForallR *)
      | Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hp1 Hp2   (* LS-Arrow *)
      | Θ α m Q Q' Ξ0 C0 b Hfr0 Hp                (* LS-ForallL *)
      | Θ α m Q Q' Ξ0 C0 Hp ];                    (* LS-UnivGhostL *)
      cbn in Hn, Hα'P |- *.
    - (* LS-Var *)
      destruct_if as [_ | Hne]; [ | exfalso; congruence ].
      apply a_looksub__var.
    - (* LS-Absent *)
      rewrite subst_pskl_in_pskl_fresh_eq by exact Hnf.
      apply a_looksub__absent; exact Hα'P.
    - (* LS-Vacuous *) apply a_looksub__vacuous.
    - (* LS-Check *)
      apply a_looksub__check;
        [ apply subst_var_neq_new; assumption
        | apply guarded_pskl_subst_var; assumption
        | assumption
        | apply IHe; solve [ lia | assumption ] ].
    - (* LS-ForallR — the TARGET opens; the binder LEAKS *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbA : b `notin` ftvar_in_pskl A) by (clear - Hfr0; fsetdec).
      assert (HbB : b `notin` ftvar_in_pskl B) by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + (* the NEW name IS the rule's binder: [Hα'Ξ]/[Hα'C] say the binder
           did not leak, so it can be moved to a fresh δ first (§5) *)
        assert (HbΞf : b `notin` ftvar_in_aenv Ξ0)
          by (pose proof (a_looksub_generated_ftvar Hp) as HΞ;
              clear - Hα'Ξ HΞ; fsetdec).
        pick fresh δ for
          (add α (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl A
             `union` ftvar_in_pskl B `union` dom Ξ0
             `union` ftvar_in_cstrs C0))).
        assert (Hδα : δ <> α) by (clear - Fr; fsetdec).
        assert (Hδb : δ <> b) by (clear - Fr; fsetdec).
        assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; fsetdec).
        assert (HδA : δ `notin` ftvar_in_pskl A) by (clear - Fr; fsetdec).
        assert (HδB : δ `notin` ftvar_in_pskl B) by (clear - Fr; fsetdec).
        assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; fsetdec).
        assert (HδC : δ `notin` ftvar_in_cstrs C0) by (clear - Fr; fsetdec).
        clear Fr.
        pose proof (a_looksub_rename_tvar Hp Hbα Hδα ltac:(look_fresh)) as H1.
        rewrite rename_aenv_cons_tvar_eq in H1.
        rewrite (@rename_aenv_fresh_eq Θ δ b) in H1 by exact HbΘ.
        rewrite (@rename_aenv_fresh_eq Ξ0 δ b) in H1 by exact HbΞf.
        rewrite (@subst_cstrs_fresh_eq δ b C0) in H1 by exact Hα'C.
        rewrite (subst_pskl_in_pskl_fresh_eq A) in H1 by exact HbA.
        rewrite <- (subst_pskl_in_pskl_intro b B (pskl_var_f δ)) in H1
          by exact HbB.
        apply a_looksub__forall_r with (β := δ); [ look_fresh | ].
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact H1 | exact HbA | exact Hα'Ξ | exact Hα'C ].
      + (* the binder stays put *)
        apply a_looksub__forall_r with (β := b); [ look_fresh | ].
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact Hp | exact Hα'P | exact Hα'Ξ | exact Hα'C ].
    - (* LS-Arrow *)
      rewrite dom_app in Hα'Ξ. rewrite ftvar_in_cstrs_app in Hα'C.
      apply a_looksub__arrow;
        [ apply IHe | apply IHs ];
        solve [ lia | assumption
              | clear - Hα'P; fsetdec | clear - Hα'Ξ; fsetdec
              | clear - Hα'C; fsetdec ].
    - (* LS-ForallL — the SOURCE opens; the binder LEAKS *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + assert (HbΞf : b `notin` ftvar_in_aenv Ξ0)
          by (pose proof (a_looksub_generated_ftvar Hp) as HΞ;
              clear - Hα'Ξ HΞ; fsetdec).
        pick fresh δ for
          (add α (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
             `union` ftvar_in_pskl Q' `union` dom Ξ0
             `union` ftvar_in_cstrs C0))).
        assert (Hδα : δ <> α) by (clear - Fr; fsetdec).
        assert (Hδb : δ <> b) by (clear - Fr; fsetdec).
        assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; fsetdec).
        assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; fsetdec).
        assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; fsetdec).
        assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; fsetdec).
        assert (HδC : δ `notin` ftvar_in_cstrs C0) by (clear - Fr; fsetdec).
        clear Fr.
        pose proof (a_looksub_rename_tvar Hp Hbα Hδα ltac:(look_fresh)) as H1.
        rewrite rename_aenv_cons_tvar_eq in H1.
        rewrite (@rename_aenv_fresh_eq Θ δ b) in H1 by exact HbΘ.
        rewrite (@rename_aenv_fresh_eq Ξ0 δ b) in H1 by exact HbΞf.
        rewrite (@subst_cstrs_fresh_eq δ b C0) in H1 by exact Hα'C.
        rewrite (subst_pskl_in_pskl_fresh_eq Q') in H1 by exact HbQ'.
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
          by exact HbQ.
        apply a_looksub__forall_l with (β := δ); [ look_fresh | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
          by (solve [ congruence | constructor ]).
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact H1 | look_fresh | exact Hα'Ξ | exact Hα'C ].
      + apply a_looksub__forall_l with (β := b); [ look_fresh | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α'))
          by (solve [ congruence | constructor ]).
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact Hp | look_fresh | exact Hα'Ξ | exact Hα'C ].
    - (* LS-UnivGhostL *)
      apply a_looksub__univ_ghost_l; apply IHs;
        solve [ lia | assumption ]. }
  (* ==================== the [a_lookeq] half ==================== *)
  { intros Θ α P P' Ξ 𝒞 Hn Hd α' Hα'P Hα'Ξ Hα'C.
    destruct Hd as
      [ Θ α Q                                     (* LE-Var *)
      | Θ α Q Q' Hnf                              (* LE-Absent *)
      | Θ α Q                                     (* LE-Vacuous *)
      | Θ α Q b γ Hfr0 Hne Hin                    (* LE-FlexR *)
      | Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hp1 Hp2     (* LE-Arrow *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hp                  (* LE-ForallInh *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hp                  (* LE-ForallSyn *)
      | Θ α Q Q' Ξ0 C0 Hp                         (* LE-UnivGhost *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hp                  (* LE-UnivGhost1 *)
      | Θ α Q Q' Ξ0 C0 Hg Hp                      (* LE-UnivGhost2 *)
      | Θ α Q Q' Ξ0 C0 Hne Hg Hp ];               (* LE-UnivGhostR *)
      cbn in Hn, Hα'P |- *.
    - (* LE-Var *)
      destruct_if as [_ | Hne]; [ | exfalso; congruence ].
      apply a_lookeq__var.
    - (* LE-Absent *)
      rewrite subst_pskl_in_pskl_fresh_eq by exact Hnf.
      apply a_lookeq__absent; exact Hα'P.
    - (* LE-Vacuous *) apply a_lookeq__vacuous.
    - (* LE-FlexR — the new name must dodge the GENERATED flexible, which is
         exactly what the output-freshness premise supplies *)
      cbn in Hfr0, Hα'Ξ |- *.
      apply a_lookeq__flex_r;
        [ look_fresh
        | apply subst_var_neq_new; assumption
        | apply ftv_subst_var_in; exact Hin ].
    - (* LE-Arrow *)
      rewrite dom_app in Hα'Ξ. rewrite ftvar_in_cstrs_app in Hα'C.
      apply a_lookeq__arrow; apply IHe;
        solve [ lia | assumption
              | clear - Hα'P; fsetdec | clear - Hα'Ξ; fsetdec
              | clear - Hα'C; fsetdec ].
    - (* LE-ForallInh — BOTH sides open *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + assert (HbΞf : b `notin` ftvar_in_aenv Ξ0)
          by (pose proof (a_lookeq_generated_ftvar Hp) as HΞ;
              clear - Hα'Ξ HΞ; fsetdec).
        pick fresh δ for
          (add α (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
             `union` ftvar_in_pskl Q' `union` dom Ξ0
             `union` ftvar_in_cstrs C0))).
        assert (Hδα : δ <> α) by (clear - Fr; fsetdec).
        assert (Hδb : δ <> b) by (clear - Fr; fsetdec).
        assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; fsetdec).
        assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; fsetdec).
        assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; fsetdec).
        assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; fsetdec).
        assert (HδC : δ `notin` ftvar_in_cstrs C0) by (clear - Fr; fsetdec).
        clear Fr.
        pose proof (a_lookeq_rename_tvar Hp Hbα Hδα ltac:(look_fresh)) as H1.
        rewrite rename_aenv_cons_tvar_eq in H1.
        rewrite (@rename_aenv_fresh_eq Θ δ b) in H1 by exact HbΘ.
        rewrite (@rename_aenv_fresh_eq Ξ0 δ b) in H1 by exact HbΞf.
        rewrite (@subst_cstrs_fresh_eq δ b C0) in H1 by exact Hα'C.
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
          by exact HbQ.
        rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f δ)) in H1
          by exact HbQ'.
        apply a_lookeq__forall_inh with (β := δ); [ look_fresh | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
          by (solve [ congruence | constructor ]).
        apply IHe;
          [ rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia
          | exact H1 | look_fresh | exact Hα'Ξ | exact Hα'C ].
      + apply a_lookeq__forall_inh with (β := b); [ look_fresh | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α'))
          by (solve [ congruence | constructor ]).
        apply IHe;
          [ rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia
          | exact Hp | look_fresh | exact Hα'Ξ | exact Hα'C ].
    - (* LE-ForallSyn — the SOURCE opens *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + assert (HbΞf : b `notin` ftvar_in_aenv Ξ0)
          by (pose proof (a_lookeq_generated_ftvar Hp) as HΞ;
              clear - Hα'Ξ HΞ; fsetdec).
        pick fresh δ for
          (add α (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
             `union` ftvar_in_pskl Q' `union` dom Ξ0
             `union` ftvar_in_cstrs C0))).
        assert (Hδα : δ <> α) by (clear - Fr; fsetdec).
        assert (Hδb : δ <> b) by (clear - Fr; fsetdec).
        assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; fsetdec).
        assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; fsetdec).
        assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; fsetdec).
        assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; fsetdec).
        assert (HδC : δ `notin` ftvar_in_cstrs C0) by (clear - Fr; fsetdec).
        clear Fr.
        pose proof (a_lookeq_rename_tvar Hp Hbα Hδα ltac:(look_fresh)) as H1.
        rewrite rename_aenv_cons_tvar_eq in H1.
        rewrite (@rename_aenv_fresh_eq Θ δ b) in H1 by exact HbΘ.
        rewrite (@rename_aenv_fresh_eq Ξ0 δ b) in H1 by exact HbΞf.
        rewrite (@subst_cstrs_fresh_eq δ b C0) in H1 by exact Hα'C.
        rewrite (subst_pskl_in_pskl_fresh_eq (pskl_tophole Q')) in H1
          by exact HbQ'.
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
          by exact HbQ.
        apply a_lookeq__forall_syn with (β := δ); [ look_fresh | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
          by (solve [ congruence | constructor ]).
        apply IHe with (P' := pskl_tophole Q');
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact H1 | look_fresh | exact Hα'Ξ | exact Hα'C ].
      + apply a_lookeq__forall_syn with (β := b); [ look_fresh | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α'))
          by (solve [ congruence | constructor ]).
        apply IHe with (P' := pskl_tophole Q');
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hp | look_fresh | exact Hα'Ξ | exact Hα'C ].
    - (* LE-UnivGhost *)
      apply a_lookeq__univ_ghost; apply IHe; solve [ lia | assumption ].
    - (* LE-UnivGhost1 — the TARGET opens *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + assert (HbΞf : b `notin` ftvar_in_aenv Ξ0)
          by (pose proof (a_lookeq_generated_ftvar Hp) as HΞ;
              clear - Hα'Ξ HΞ; fsetdec).
        pick fresh δ for
          (add α (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
             `union` ftvar_in_pskl Q' `union` dom Ξ0
             `union` ftvar_in_cstrs C0))).
        assert (Hδα : δ <> α) by (clear - Fr; fsetdec).
        assert (Hδb : δ <> b) by (clear - Fr; fsetdec).
        assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; fsetdec).
        assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; fsetdec).
        assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; fsetdec).
        assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; fsetdec).
        assert (HδC : δ `notin` ftvar_in_cstrs C0) by (clear - Fr; fsetdec).
        clear Fr.
        pose proof (a_lookeq_rename_tvar Hp Hbα Hδα ltac:(look_fresh)) as H1.
        rewrite rename_aenv_cons_tvar_eq in H1.
        rewrite (@rename_aenv_fresh_eq Θ δ b) in H1 by exact HbΘ.
        rewrite (@rename_aenv_fresh_eq Ξ0 δ b) in H1 by exact HbΞf.
        rewrite (@subst_cstrs_fresh_eq δ b C0) in H1 by exact Hα'C.
        rewrite (subst_pskl_in_pskl_fresh_eq (pskl_tophole Q)) in H1
          by exact HbQ.
        rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f δ)) in H1
          by exact HbQ'.
        apply a_lookeq__univ_ghost1 with (β := δ); [ look_fresh | ].
        apply IHe with (P := pskl_tophole Q);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact H1 | cbn; exact HbQ | exact Hα'Ξ | exact Hα'C ].
      + apply a_lookeq__univ_ghost1 with (β := b); [ look_fresh | ].
        apply IHe with (P := pskl_tophole Q);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hp | cbn; exact Hα'P | exact Hα'Ξ | exact Hα'C ].
    - (* LE-UnivGhost2 *)
      apply a_lookeq__univ_ghost2;
        [ exact Hg | apply IHe; solve [ lia | assumption ] ].
    - (* LE-UnivGhostR *)
      apply a_lookeq__univ_ghost_r;
        [ apply subst_var_neq_new; assumption
        | apply guarded_pskl_subst_var; exact Hg
        | apply IHe; solve [ lia | assumption ] ]. }
Qed.

Lemma a_looksub_rename_var : forall Θ α m P P' Ξ 𝒞 α',
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  α' `notin` ftvar_in_pskl P ->
  α' `notin` dom Ξ -> α' `notin` ftvar_in_cstrs 𝒞 ->
  Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof.
  intros. eapply (proj1 (a_looksub_lookeq_rename_var_size
                           (2 * (size_pskl P + size_pskl P') + 1))); eauto.
Qed.

Lemma a_lookeq_rename_var : forall Θ α P P' Ξ 𝒞 α',
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  α' `notin` ftvar_in_pskl P ->
  α' `notin` dom Ξ -> α' `notin` ftvar_in_cstrs 𝒞 ->
  Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ∼[ α' ] P' ⤳ Ξ ⨾ 𝒞.
Proof.
  intros. eapply (proj2 (a_looksub_lookeq_rename_var_size
                           (2 * (size_pskl P + size_pskl P')))); eauto.
Qed.

(* ===================================================================== *)
(*  §11. The [a_extract] FAMILY from one instance                         *)
(*  (moved here from prop_look_complete_extract.v, campaign cluster 5:    *)
(*   [prop_decorate_key.v] needs it too, and that file is a sibling of    *)
(*   P6-L's, not a consumer.)                                            *)
(* ===================================================================== *)

(* ⚙ The family HANDS BACK its own avoid-set (cluster 3).  Renaming the
   looked-for variable is an OUTPUT-freshness lemma: the look's ∀ rules may
   LEAK a binder into the collected constraints, and a leaked binder is
   precisely a name no input mentions, so it cannot be excluded by any
   condition on [P]/[P0].  The instance knows its own [Ξl ⨾ 𝒞l], so it is the
   one that can name the set; consumers union it into their own [L].

   This is also the machine check behind cluster 5's QUESTION ZERO: it says
   ONE instance generates the WHOLE cofinite family with the SAME [Ξ] and
   [P1], i.e. the cofinite rendering of [a_sub__forall_l] /
   [a_subtag__forall_l_*] was FAITHFUL and the exists-fresh conversion is a
   uniformity change, not a repair.  (DESIGN §4.3.) *)
Lemma a_extract_family_of_instance : forall Θ0 NM M α P P0 Ξ P1,
  Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α)) ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 ->
  α `notin` ftvar_in_pskl P ->
  exists L, forall α',
    α' `notin` (singleton α `union` ftvar_in_pskl P `union` L) ->
    Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α')) ⊳[ NM , α' , M ] P0 ⤳ Ξ ↪ P1.
Proof.
  intros Θ0 NM M α P P0 Ξ P1 Hex Hfr.
  inversion Hex as [ Θ0' NM' α'' m' Ps Ps' Ξl Ξg 𝒞l Q Q' Hlk Hsol Hgu
                     HeqΘ HeqNM Heqα Heqm HeqP HeqP0 ]; subst.
  exists (dom Ξl `union` ftvar_in_cstrs 𝒞l).
  intros α' Hα'.
  eapply a_extract__solve; [ | eassumption | eassumption ].
  assert (Hα'P : α' `notin`
                   ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                  P (pskl_var_f α)) as Hup.
    simpl in Hup. clear - Hα' Hup; fsetdec. }
  pose proof (a_looksub_rename_var Hlk Hα'P
                ltac:(clear - Hα'; fsetdec) ltac:(clear - Hα'; fsetdec))
    as Hlk'.
  rewrite <- (subst_pskl_in_pskl_intro α P (pskl_var_f α') Hfr) in Hlk'.
  exact Hlk'.
Qed.
