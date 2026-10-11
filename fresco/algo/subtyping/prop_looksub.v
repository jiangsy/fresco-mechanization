(** BASICS for the constraint-collection layer
    ([a_looksub]/[a_lookeq]/[a_extract]) — docs/DESIGN-subtyping.md P2.

    The declaration-shape facts every re-attachment of a look output [Ξ] to
    a context needs: look only ever generates FLEXIBLE declarations (the
    single generative rule is LE-FlexR), and [a_extract] appends [guess]'s
    declarations ([a_guess_mono_decls]). *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.prop_tag.   (* swap_atom_other — the ATOM layer *)
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.consistency.prop_soundness_consis.

Set Implicit Arguments.

Scheme a_looksub_mutind := Induction for a_looksub Sort Prop
  with a_lookeq_mutind := Induction for a_lookeq Sort Prop.

Combined Scheme a_looksub_lookeq_mutind
  from a_looksub_mutind, a_lookeq_mutind.

(* ===================================================================== *)
(*  §1  Look outputs are declaration-only contexts                        *)
(* ===================================================================== *)

Lemma a_looksub_lookeq_decls :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a -> a_decls Ξ) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a -> a_decls Ξ).
Proof.
  apply a_looksub_lookeq_mutind;
    intros; try solve [ assumption ]; try solve [ apply a_decls__nil ];
    try solve [ apply a_decls_app; assumption ];
    try solve [ destruct (atom_fresh L) as [β0 Hβ0]; eauto ].
  (* LE-FlexR : the single generative rule *)
  econstructor; apply a_decls__nil.
Qed.

Lemma a_looksub_decls : forall Θ α m P P' Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a -> a_decls Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_decls); eauto. Qed.

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
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a -> ftvar_in_aenv Ξ [<=] dom Ξ) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a -> ftvar_in_aenv Ξ [<=] dom Ξ).
Proof.
  apply a_looksub_lookeq_mutind;
    intros; simpl; try solve [ fsetdec ];
    try solve [ destruct (atom_fresh L) as [β0 Hβ0]; eauto ];
    rewrite ftvar_in_aenv_app, dom_app; fsetdec.
Qed.

Lemma a_looksub_generated_ftvar : forall Θ α m P P' Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_generated_ftvar); eauto. Qed.

Lemma a_lookeq_generated_ftvar : forall Θ α P P' Ξ 𝒞,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros; eapply (proj2 a_looksub_lookeq_generated_ftvar); eauto. Qed.

(** The constraint-LIST solve's block, assembled from the per-constraint
    ones ([a_solve_sub_decls] / [a_solve_eq_decls], prop_solve_sub.v). *)
(** ⭐ THREE blocks now (2026-08-04): collection, SOLVING, final guess. *)
Lemma a_extract_decls : forall Θ0 NM α m P P' Ξ P0,
  {{ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ P0 }}a -> a_decls Ξ.
Proof.
  intros Θ0 NM α m P P' Ξ P0 H; destruct H.
  apply a_decls_app; [ eapply a_looksub_decls; eauto | ].
  apply a_decls_app;
    [ eapply a_solve_cstr_decls; eauto | eapply a_guess_decls; eauto ].
Qed.

(* ===================================================================== *)
(*  §2  Free variables of the collected constraints                       *)
(*                                                                        *)
(*  Every variable in a collected constraint comes from the RHS being     *)
(*  compared against, or is one of the freshly-generated flexibles in Ξ   *)
(*  (LE-FlexR).  Needed for freshness bookkeeping when re-attaching Ξ.     *)
(* ===================================================================== *)

(* ⚙ [ftvar_in_a_cstr] / [ftvar_in_a_cstrs] / [ftvar_in_a_cstrs_app] MOVED
   to fresco/algo/def_rules.v (2026-08-19): the collection's arrow rows now
   read the function, so it has to sit above them.  This file's copy was
   spelled [ftvar_in_cstrs]; the two were identical. *)

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

Lemma subst_cstrs_fresh_eq : forall γ β C,
  β `notin` ftvar_in_a_cstrs C -> subst_cstrs γ β C = C.
Proof.
  induction C as [ | c C' IH ]; intros Hβ; simpl in *; [ reflexivity | ].
  rewrite IH by (clear - Hβ; fsetdec).
  destruct c; simpl; rewrite subst_pskl_in_pskl_fresh_eq
    by (clear - Hβ; simpl in Hβ; fsetdec); reflexivity.
Qed.

Lemma ftvar_in_a_cstrs_subst_upper : forall γ β C,
  ftvar_in_a_cstrs (subst_cstrs γ β C)
    [<=] singleton γ `union` remove β (ftvar_in_a_cstrs C).
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

   has [ftvar_in_a_cstrs 𝒞 = {b0}] while [ftv (∀b.b) ∪ dom · = ∅].  The exact
   bound is therefore FALSE and the repair is the same one cluster 2 made
   for [a_solve_sub_eq_ftv] / [a_solve_cstr_ftv]: an escaping variable is
   one the RUN INVENTED, and the avoid-input [Θ] is what lets us say so.
   (This lemma is exactly why look needed a context: without [Θ] the second
   disjunct cannot even be STATED, and [a_extract_output_fresh] below — the
   paper's lemma:look-output-fresh, subtyping-proofs:522 — loses its proof.) *)
Lemma a_looksub_lookeq_ftv :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall α0, α0 `in` ftvar_in_a_cstrs 𝒞 ->
       α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
       α0 `notin` ftvar_in_aenv Θ) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall α0, α0 `in` ftvar_in_a_cstrs 𝒞 ->
       α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
       α0 `notin` ftvar_in_aenv Θ).
Proof.
  apply a_looksub_lookeq_mutind;
    intros; simpl in *;
    (* the non-binder rows: constraints come from the target or from Ξ *)
    try solve [ left; match goal with Hin : _ `in` _ |- _ =>
                  clear - Hin; fsetdec end ].
  (* Twelve rows survive: five that repeat their premise verbatim, the two
     arrows, and the five BINDER rows — three of which open the TARGET, and
     those are exactly where a leaked binder can show up in 𝒞. *)
  all: try solve [ exact (H α0 H0) ].
  all: try solve [ (* the arrows: split the constraint list *)
         rewrite ftvar_in_a_cstrs_app in H1; rewrite dom_app;
         destruct (AtomSetProperties.In_dec α0 (ftvar_in_a_cstrs C1))
           as [Hin | Hin];
         [ destruct (H α0 Hin) as [Hd | Hd]
         | destruct (H0 α0 ltac:(clear - H1 Hin; solve_notin_auto)) as [Hd | Hd] ];
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

(* A CONSISTENCY collection only ever deposits eq constraints.  ⚙ The three ∀
   rows are plain [assumption]: the rules are EXISTS-FRESH, so the IH is the
   premise's own and no representative has to be picked off [L]. *)
Lemma a_lookeq_cstr_eq : forall Θ α P P' Ξ 𝒞,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
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
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  forall α0, α0 `in` ftvar_in_a_cstrs 𝒞 ->
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
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  α0 `in` dom Θ ->
  α0 `notin` ftvar_in_pskl P' ->
  α0 `notin` dom Ξ ->
  α0 `notin` ftvar_in_a_cstrs 𝒞.
Proof.
  intros * H Hdom HP' HΞ Hin.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hdf.
  destruct (a_looksub_ftv H Hin) as [Hl | Hr];
    [ clear - Hl HP' HΞ | clear - Hdom Hdf Hr ]; fsetdec.
Qed.

Lemma a_lookeq_ftv_ctx : forall Θ α P P' Ξ 𝒞 α0,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  α0 `in` dom Θ ->
  α0 `notin` ftvar_in_pskl P' ->
  α0 `notin` dom Ξ ->
  α0 `notin` ftvar_in_a_cstrs 𝒞.
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
Lemma a_solve_cstr_ftv : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  forall α, α `in` ftvar_in_pskl P' ->
    α `in` (ftvar_in_pskl P `union` ftvar_in_a_cstrs 𝒞) \/ α `notin` dom Θ.
Proof.
  intros Θ 𝒞 P Ξ P' H; induction H; simpl; intros α0 Hα0.
  - left; fsetdec.
  - destruct (a_solve_sub_ftv H Hα0) as [Hl | Hr];
      [ left; clear - Hl; fsetdec | right; exact Hr ].
  - (* ⭐ two new ways out (2026-08-04): the eq-row's yield may now carry a
       name SE-FlexR generated, and the tail runs at the THREADED context *)
    pose proof (a_solve_eq_ftv H) as He.
    destruct (IHa_solve_cstr α0 Hα0) as [Hl | Hr];
      [ | right; rewrite dom_app in Hr; clear - Hr; fsetdec ].
    destruct (AtomSetProperties.In_dec α0 (dom Ξ1)) as [Hd | Hd];
      [ right; eapply a_solve_eq_generated_notin_dom; eassumption
      | left; clear - Hl He Hd; fsetdec ].
Qed.

Lemma a_solve_cstr_ftv_eq : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  Forall (fun c => exists Q, c = a_cstr_eq Q) 𝒞 ->
  ftvar_in_pskl P' [<=]
    ftvar_in_pskl P `union` ftvar_in_a_cstrs 𝒞 `union` dom Ξ.
Proof.
  intros Θ 𝒞 P Ξ P' H; induction H; simpl; intros Hall.
  - clear; fsetdec.
  - (* a sub constraint contradicts the all-eq hypothesis *)
    exfalso. inversion Hall as [ | c cs Hc _ ]; subst.
    destruct Hc as [Q0 Hc]. discriminate Hc.
  - inversion Hall as [ | c cs Hc Htl ]; subst.
    pose proof (a_solve_eq_ftv H) as He.
    specialize (IHa_solve_cstr Htl).
    rewrite dom_app. clear - He IHa_solve_cstr. fsetdec.
Qed.

Lemma ptyp_to_pskl_ftv : forall A,
  ftvar_in_pskl (ptyp_to_pskl A) [<=] ftvar_in_ptyp A.
Proof. induction A; simpl; fsetdec. Qed.

(* ===================================================================== *)
(*  §4  Stability of constraint collection under substitution             *)
(*  (lemma:constraint-collection-stable-substitution, tex:504-520,        *)
(*  forward direction).  Substituting an α-free [Q] for β ≠ α preserves   *)
(*  the collected constraints; when the substitution destroys a           *)
(*  guardedness side condition the source has become α-free, so the       *)
(*  derivation switches to the Absent rule (the paper's remark).          *)
(* ===================================================================== *)

(** An α-free source collects nothing. *)
(** ⭐ THE ◇-DISPATCH GUARD'S TRANSPORT KIT — the two ways a rule rebuilds
    its SUBJECT, for the [P <> α] half of the guard.  (The [P' <> ◇] half
    needs no transport: the counterpart is carried verbatim by every row
    that owes it.) *)
Lemma subst_neq_var_keep : forall P P0 β α,
  P <> pskl_var_f α -> α `notin` ftvar_in_pskl P0 ->
  subst_pskl_in_pskl P0 β P <> pskl_var_f α.
Proof.
  intros P P0 β α Hne Hα Hc.
  destruct P; simpl in Hc; try discriminate Hc.
  destruct (α0 == β) as [-> | Hne2].
  - rewrite Hc in Hα. simpl in Hα. clear - Hα. fsetdec.
  - inversion Hc; subst. congruence.
Qed.

Lemma a_looksub_lookeq_absent_nil :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil).
Proof.
  apply a_looksub_lookeq_mutind;
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

(** ⭐⭐ A GHOST TARGET COLLECTS ALMOST NOTHING — the inversion the
    ◇-DISPATCH GUARD buys, and the one P6-Ss's ForallL row needs.

    Under the guard the runner answers a [◇] counterpart immediately, and the
    rules now say so: [LS-ForallL] and [LS-UnivGhostL] carry [P' ≠ ◇], and
    [LS-Check] cannot fire because [◇] is not [guarded].  So at a ghost target
    exactly THREE rows survive — Var, Absent, Vacuous — and only Var emits
    anything, at the looked-for variable itself.

    ⭐⭐ WHAT MAKES IT USABLE: the emitting row PINS THE SUBJECT to [α].  So at
    any subject that is not the looked-for variable — a ∀ or a ⫯, which is
    exactly where P6's ForallL / UnivGhostL rows work — the collection is
    FORCED to be [· ⨾ ·], and one collection derivation can be swapped for
    another without moving the answer the solve computes from it. *)
Lemma a_looksub_ghost_target : forall Θ α m P Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , m ] pskl_ghost ⤳ Ξ ⨾ 𝒞 }}a ->
  Ξ = nil /\ (𝒞 = nil
              \/ (P = pskl_var_f α /\ 𝒞 = a_cstr_sub m pskl_ghost :: nil)).
Proof.
  intros Θ α m P Ξ 𝒞 H.
  remember pskl_ghost as T eqn:HT.
  induction H; subst; try discriminate HT.
  - (* LS-Var — the ONE emitting row at a ghost target, and it PINS the
       subject to the looked-for variable *)
    split; [ reflexivity | right; split; reflexivity ].
  - (* LS-Absent *) split; [ reflexivity | left; reflexivity ].
  - (* LS-Vacuous *) split; [ reflexivity | left; reflexivity ].
  - (* LS-Check — [◇] is not guarded *)
    match goal with Hg : guarded_pskl pskl_ghost |- _ => inversion Hg end.
  - (* LS-ForallL — blocked by the ◇-dispatch guard *)
    match goal with Hnh : pskl_ghost <> pskl_ghost |- _ =>
      exfalso; exact (Hnh eq_refl) end.
  - (* LS-UnivGhostL — likewise *)
    match goal with Hnh : pskl_ghost <> pskl_ghost |- _ =>
      exfalso; exact (Hnh eq_refl) end.
Qed.

(* ===================================================================== *)
(*  §2b  ⭐⭐ THE ABSENCE-FIRST GUARD IS ADMISSIBLE                        *)
(*                                                                        *)
(*  The five LEAKING rows carry [α ∈ ftv <subject>] (the implementation's *)
(*  absence-first dispatch, rendered as a premise — see def_rules.v and   *)
(*  docs/PAPER-GAPS.md).  That premise is what makes the collection stop  *)
(*  SPENDING supply it never needed; what it must NOT do is cost the      *)
(*  CONSUMERS anything, and the five lemmas below are why it does not.    *)
(*                                                                        *)
(*  Each reinstates its rule in the PRE-GUARD form, by the one case split *)
(*  the guard introduces:                                                 *)
(*                                                                        *)
(*    α ∈ ftv <subject>   — fire the guarded rule                         *)
(*    α ∉ ftv <subject>   — the premise's subject is α-free too (the      *)
(*                          opener is fresh for α), so it collected       *)
(*                          NOTHING ([a_looksub_lookeq_absent_nil]) and   *)
(*                          LS/LE-Absent gives the very same answer       *)
(*                                                                        *)
(*  ⭐ SO EVERY CONSTRUCTION SITE IS UNCHANGED: a caller that cannot see   *)
(*  an occurrence — P6's completeness chain is the big one, whose         *)
(*  induction carries no such datum — swaps the CONSTRUCTOR for the       *)
(*  lemma of the same name and is otherwise untouched.  This is what      *)
(*  keeps the guard from re-opening subtyping completeness.               *)
(*                                                                        *)
(*  ⚠️ These are NOT [_no_loss] lemmas: they have real consumers.  What    *)
(*  they share with that family is the moral — the added premise rejects  *)
(*  no ANSWER the premise-free rule accepted, only a wasteful DERIVATION  *)
(*  of it.                                                                *)
(* ===================================================================== *)

(** The opener is fresh for [α], so an α-free subject stays α-free when the
    binder is opened — the side condition every one of the five rows
    already carries. *)
Lemma ftv_open_absent : forall α β P,
  β `notin` add α (ftvar_in_pskl P) ->
  α `notin` ftvar_in_pskl (pskl_all_syn P) ->
  α `notin` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f β)).
Proof.
  intros α β P Hβ Hα.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
  simpl in *. clear - Hβ Hα Hup. fsetdec.
Qed.

Lemma a_looksub_forall_r_adm : forall Θ α A B Ξ C β,
  pskl_ghost_free (pskl_all_syn B) ->
  A <> pskl_var_f α ->
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl A
                     `union` ftvar_in_pskl B) ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ A ≼[ α , mode_tc ]
     (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ A ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α A B Ξ C β Hgf Hnv Hβ Hp.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl A)) as [Hin | Hni].
  - apply a_looksub__forall_r with (β := β); assumption.
  - (* the SUBJECT is untouched by this row, so it was α-free in the premise *)
    destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ Hp Hni)
      as [-> ->].
    apply a_looksub__absent; exact Hni.
Qed.

(** ⚠️ [forall_r_off] is a REAL premise here, not an admissible one: the
    ForallR-PRIORITY guard changes WHICH RULE fires, so unlike the
    absence-first guard it cannot be reinstated by a case split.  Only the
    [α ∈ ftv] conjunct is discharged below. *)
Lemma a_looksub_forall_l_adm : forall Θ α m P P' Ξ C β,
  P' <> pskl_ghost ->
  forall_r_off m P' ->
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β))
     ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ (pskl_all_syn P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α m P P' Ξ C β Hnh Hfr Hβ Hp.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_all_syn P)))
    as [Hin | Hni].
  - apply a_looksub__forall_l with (β := β); assumption.
  - assert (Hno : α `notin` ftvar_in_pskl
                    (open_pskl_wrt_pskl P (pskl_var_f β)))
      by (apply ftv_open_absent; [ clear - Hβ; fsetdec | exact Hni ]).
    destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ Hp Hno)
      as [-> ->].
    apply a_looksub__absent; exact Hni.
Qed.

Lemma a_lookeq_forall_inh_adm : forall Θ α P P' Ξ C β,
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
     (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α P P' Ξ C β Hβ Hp.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_all_syn P)))
    as [Hin | Hni].
  - apply a_lookeq__forall_inh with (β := β); assumption.
  - assert (Hno : α `notin` ftvar_in_pskl
                    (open_pskl_wrt_pskl P (pskl_var_f β)))
      by (apply ftv_open_absent; [ clear - Hβ; fsetdec | exact Hni ]).
    destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hp Hno)
      as [-> ->].
    apply a_lookeq__absent; exact Hni.
Qed.

Lemma a_lookeq_forall_syn_adm : forall Θ α P P' Ξ C β,
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
     (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α P P' Ξ C β Hβ Hp.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_all_syn P)))
    as [Hin | Hni].
  - apply a_lookeq__forall_syn with (β := β); assumption.
  - assert (Hno : α `notin` ftvar_in_pskl
                    (open_pskl_wrt_pskl P (pskl_var_f β)))
      by (apply ftv_open_absent; [ clear - Hβ; fsetdec | exact Hni ]).
    destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hp Hno)
      as [-> ->].
    apply a_lookeq__absent; exact Hni.
Qed.

Lemma a_lookeq_univ_ghost1_adm : forall Θ α P P' Ξ C β,
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (pskl_univ_ghost P) ∼[ α ]
     (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
  {{ Θ ⊢ (pskl_univ_ghost P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}a.
Proof.
  intros Θ α P P' Ξ C β Hβ Hp.
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_univ_ghost P)))
    as [Hin | Hni].
  - apply a_lookeq__univ_ghost1 with (β := β); assumption.
  - (* the SUBJECT is untouched by this row *)
    destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hp Hni)
      as [-> ->].
    apply a_lookeq__absent; exact Hni.
Qed.

(* ===================================================================== *)
(*  §2c  ⭐⭐ THE TARGET PEEL — what the ForallR-PRIORITY GUARD buys        *)
(*                                                                        *)
(*  Under the guard, a collection at a GHOST-FREE ∀ counterpart in CHECK   *)
(*  mode has only THREE possible roots: LS-Var, LS-Absent and LS-ForallR.  *)
(*  LS-Check wants a [guarded] counterpart and a ∀ is not guarded,         *)
(*  LS-Vacuous wants a ghost one, LS-Arrow an arrow — and LS-ForallL /     *)
(*  LS-UnivGhostL are exactly what the guard forbids there.  So such a     *)
(*  derivation ALREADY peels the counterpart, and one peel is an           *)
(*  INVERSION.                                                             *)
(* ===================================================================== *)

(** ⭐ AT THE LOOKED-FOR VARIABLE ITSELF ONLY LS-Var FIRES — and it is the
    ◇-DISPATCH GUARD that makes this true, since LS-Vacuous, LS-Check and
    LS-ForallR all carry [_ <> pskl_var_f α].  The collection at the leaf is
    therefore PINNED, which is what lets the α-stack cell be rebuilt at a
    counterpart the run has moved. *)
Lemma a_looksub_var_subject_inv : forall Θ α m P' Ξ 𝒞,
  {{ Θ ⊢ (pskl_var_f α) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  Ξ = nil /\ 𝒞 = a_cstr_sub m P' :: nil.
Proof.
  intros Θ α m P' Ξ 𝒞 H.
  remember (pskl_var_f α) as S eqn:HS.
  destruct H; try discriminate HS.
  - (* LS-Var *) split; reflexivity.
  - (* LS-Absent — the subject IS the looked-for variable *)
    exfalso. subst P. simpl in H. clear - H. fsetdec.
  - (* LS-Vacuous — ◇-dispatch guard *) exfalso. congruence.
  - (* LS-Check — ◇-dispatch guard *) exfalso. congruence.
  - (* LS-ForallR — ◇-dispatch guard *) exfalso. congruence.
Qed.

(** ⭐⭐ ONE PEEL OF THE COUNTERPART, and the block and the collected
    constraints come through UNTOUCHED.

    ⚠️ The opener is EXISTENTIAL, and deliberately so: [LS-ForallR] LEAKS its
    binder into 𝒞, so re-picking it would replace 𝒞 by a substitution
    instance.  Handing the rule's OWN binder back keeps the outputs on the
    nose, which is what the P6-Ss consumer needs (its other conjuncts are
    stated about that very 𝒞).

    ⚠️ ONE cell escapes: at the looked-for variable itself LS-Var fires and the
    deposited constraint NAMES the counterpart, so it moves with it.  That is
    the α-STACK leaf, and the statement RETURNS it as the left disjunct rather
    than excluding it — which spares every consumer a decidable equality on
    skeletons. *)
Lemma a_looksub_open_target : forall Θ α P B Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ 𝒞 }}a ->
  pskl_ghost_free (pskl_all_syn B) ->
  (P = pskl_var_f α /\ Ξ = nil
     /\ 𝒞 = a_cstr_sub mode_tc (pskl_all_syn B) :: nil)
  \/ (exists β,
        β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                           `union` ftvar_in_pskl B)
        /\ {{ ((β ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , mode_tc ]
              (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ 𝒞 }}a).
Proof.
  intros Θ α P B Ξ 𝒞 H Hgf.
  remember (pskl_all_syn B) as T eqn:HT.
  remember mode_tc as m0 eqn:Hm0.
  destruct H as
    [ Θ0 α0 m1 Q                                       (* LS-Var *)
    | Θ0 α0 m1 Q Q' Hnf                                (* LS-Absent *)
    | Θ0 α0 m1 Q Hnv0                                  (* LS-Vacuous *)
    | Θ0 α0 A0 B0 Ξ0 C0 Hgf0 Hne0 Hg1 Hg2 Hp           (* LS-Check *)
    | Θ0 α0 A0 B0 Ξ0 C0 b Hgf0 Hfr0 Hocc0 Hnv0 Hp      (* LS-ForallR *)
    | Θ0 α0 m1 P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 Hp2       (* LS-Arrow *)
    | Θ0 α0 m1 Q Q' Ξ0 C0 b Hfr0 Hocc0 Hnh0 Hfr3 Hp    (* LS-ForallL *)
    | Θ0 α0 m1 Q Q' Ξ0 C0 Hnh0 Hfr3 Hp ];              (* LS-UnivGhostL *)
    try discriminate HT; try discriminate Hm0.
  - (* LS-Var — THE α-STACK LEAF: the deposited constraint names the
       counterpart, so it moves with the peel *)
    left. rewrite HT. split; [ reflexivity | split; reflexivity ].
  - (* LS-Absent — the subject stays α-free, so any opener serves *)
    right.
    pick fresh β for
      (add α0 (ftvar_in_aenv Θ0 `union` ftvar_in_pskl Q
                 `union` ftvar_in_pskl B)).
    exists β. split; [ clear - Fr; solve_notin | ].
    apply a_looksub__absent; exact Hnf.
  - (* LS-Check — a ∀ counterpart is never [guarded] *)
    exfalso. rewrite HT in Hg2. inversion Hg2.
  - (* LS-ForallR — THE ROW: hand its own binder back *)
    right. injection HT as HTB; subst B0.
    exists b. split; [ exact Hfr0 | exact Hp ].
  - (* LS-ForallL — ⛔ blocked by the ForallR-PRIORITY GUARD *)
    exfalso. rewrite HT in Hgf. exact (Hfr3 B HT Hm0 Hgf).
  - (* LS-UnivGhostL — likewise *)
    exfalso. rewrite HT in Hgf. exact (Hfr3 B HT Hm0 Hgf).
Qed.

(* ===================================================================== *)
(*  §4 / §4b — THE PAPER'S LEMMA E.8, "Stability of constraint collection" *)
(*  (subtyping-proofs.tex:504).                                            *)
(*                                                                        *)
(*  ⛔ DO NOT DELETE EITHER HALF FOR BEING UNREFERENCED.  Both are Qed and  *)
(*  axiom-free and NEITHER has a consumer; that is the expected state, not *)
(*  rot, and an orphan sweep has already had to be told so twice.          *)
(*                                                                        *)
(*  E.8 is an IFF, and the paper uses each direction once — forward at     *)
(*  subtyping-proofs.tex:890, reverse at :2632 ("by the reverse direction  *)
(*  of ...").  So the tree owes both, and deleting one would leave         *)
(*  PROGRESS.md Part 1 marking E.8 ✅ while half of it is unproved.         *)
(*                                                                        *)
(*  WHY NEITHER IS CALLED:                                                 *)
(*   - §4 (forward) HAD two consumers — the decoration layer's ForallL      *)
(*     rows.  ⚠️ They did NOT stop needing the FACT; §4 stopped being        *)
(*     APPLICABLE to them, which is a different thing and the reason the    *)
(*     lemma is still here.  The chain (56b0b3b):                           *)
(*       (a) the look cluster went cofinite -> exists-fresh, so a ∀ row now  *)
(*           OWNS its binder and LEAKS it into 𝒞;                           *)
(*       (b) that makes the unconditional E.8 FALSE                         *)
(*           (cex/cex_look_subst_stable_leak.v), so §4 must carry the       *)
(*           Barendregt premise [ftv P0 ⊆ add α (ftvar_in_aenv Θ)];         *)
(*       (c) at those rows the premise is UNSUPPLIABLE — the substituted    *)
(*           skeleton is a ForallL node's GUESS, and its variables live in  *)
(*           the extract's fresh block, generated AFTER the run by an       *)
(*           independent generator, hence not in [ftvar_in_aenv Θ].         *)
(*     So the rows moved to [a_looksub_lookeq_subst_gen_size]               *)
(*     (deco_algo/prop_decorate_sub.v:2925, used :3391), which buys         *)
(*     applicability by WEAKENING THE CONCLUSION: it drops the context      *)
(*     premise and lets [Ξ ⨾ 𝒞] go EXISTENTIAL — the ∀ rows re-pick their   *)
(*     binder away from [P0] and hand back RENAMED outputs, which the leak  *)
(*     witness does not touch.  ⭐ That sibling is NOT the paper's           *)
(*     statement; §4, which keeps [Ξ ⨾ 𝒞] FIXED, is.  Hence: the mech does  *)
(*     the work with §8's form and owes E.8 in §4's.                        *)
(*   - §4b (reverse) never had one.  The paper's route through that case    *)
(*     ENDS by un-substituting; the mech proves P6 by the ρ-route, which    *)
(*     carries the rigid-variable substitution explicitly and keeps the     *)
(*     looksub side on VAR-OPENED subjects — so it is never holding a       *)
(*     substituted source that has to be undone.  Recorded as a deliberate  *)
(*     decision at docs/PAPER-GAPS.md:2257.                                 *)
(*                                                                        *)
(*  ⚠️ What is mechanized is NOT the paper's statement verbatim: it carries  *)
(*  one extra premise, and the unconditional form is FALSE.  See the note   *)
(*  directly below, and docs/PAPER-GAPS.md:2567 (PROSE-COMPLETION).         *)
(* ===================================================================== *)

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
    [ftvar_in_aenv Θ] therefore threads through both.

    ⛔ §4, the FORWARD half of the paper's E.8 — consumer-free because THIS
    premise is unsuppliable at the two rows that used to call it, not because
    they stopped needing the fact.  Kept on purpose: it is the paper's own
    statement, with [Ξ ⨾ 𝒞] FIXED.  Read the banner above before deleting. *)

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

(* ===================================================================== *)
(*  §5  Rigid renames of a look run (the exists-fresh ForallR consumers    *)
(*  need them below the decoration layer).  This is the CANONICAL rename   *)
(*  asset of the cluster:                                                 *)
(*  §6's rename of the looked-for variable has to MOVE binders, and it     *)
(*  moves them with the lemma proved here.                                 *)
(* ===================================================================== *)

(* (viii) SIMULTANEOUS renaming of a rigid variable on BOTH sides —
   the canonical TARGET-only form (DESIGN.md §4.3, canon rule 3): it renames
   the CONTEXT, the GENERATED block [Ξ] and the collected constraints [𝒞] too.

   Its OUTPUT-freshness premise on the TARGET ([α1 ∉ dom Ξ ∪ ftv 𝒞]) is
   LOAD-BEARING, and this is exactly where the LEAK shows: a rule's binder
   that ESCAPED into Ξ or 𝒞 can no longer be moved (moving it would change
   the outputs), so the target must simply differ from it.  Without the
   premise the claim is FALSE — take the run of
   cex/cex_look_subst_stable_leak.v and rename to its own leaked binder.

   ⚙ It used to be a SIZE INDUCTION whose every binder row split three ways
   (source = binder / target = binder / neither), because a substitution can
   COLLAPSE two names.  Since 2026-08-06 it is derived from equivariance
   instead ([a_looksub_lookeq_swap]) and the split is gone; see the
   §5-closing block below. *)
(** Identities the rename degenerates to, and the one-step context facts the
    binder rows need. *)
Lemma subst_cstrs_same : forall β 𝒞, subst_cstrs β β 𝒞 = 𝒞.
Proof.
  induction 𝒞 as [ | c 𝒞' IH ]; cbn; [ reflexivity | ].
  rewrite IH; destruct c; cbn; rewrite subst_pskl_var_same; reflexivity.
Qed.

(** One-step context facts the binder rows need in the shape [fsetdec] can
    use (reducing [ftvar_in_aenv] under a [cons] with [cbn] would unfold the
    atom-set operations themselves). *)

(** ⚙ The freshness kit the binder rows run on.  Their side conditions are
    five-way unions over a context, two skeletons, a generated block and a
    constraint list, and a single [fsetdec] against five such OVERLAPPING
    hypotheses does not terminate in reasonable time (measured: >100s for one
    row).  So the rows never hand a union to [fsetdec]: [look_fresh] SPLITS
    the goal structurally with these one-liners and closes each leaf from an
    atomic hypothesis. *)
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
Lemma notin_ftvar_in_a_cstrs_subst_away : forall γ δ 𝒞,
  γ <> δ -> γ `notin` ftvar_in_a_cstrs (subst_cstrs δ γ 𝒞).
Proof.
  intros γ δ 𝒞 Hne.
  pose proof (ftvar_in_a_cstrs_subst_upper δ γ 𝒞) as H. fsetdec.
Qed.

Lemma notin_ftvar_in_a_cstrs_subst : forall γ δ β 𝒞,
  γ <> δ -> γ `notin` ftvar_in_a_cstrs 𝒞 ->
  γ `notin` ftvar_in_a_cstrs (subst_cstrs δ β 𝒞).
Proof.
  intros γ δ β 𝒞 Hne H𝒞.
  pose proof (ftvar_in_a_cstrs_subst_upper δ β 𝒞) as H. fsetdec.
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
    [ apply notin_union_3
    | apply notin_add_atom
    | look_fresh_leaf
    | apply notin_ftvar_in_aenv_cons_tvar
    | apply notin_ftvar_in_aenv_rename
    | apply notin_ftvar_open_pskl_var
    | apply notin_ftvar_in_a_cstrs_subst_away
    | apply notin_ftvar_in_a_cstrs_subst
    | apply notin_ftvar_subst_var ].

(** The look judgment reads its context ONLY through the avoid-inputs of its
    generative rules, so it is stable under any context whose [ftvar_in_aenv]
    is no LARGER — and in particular under EXCHANGE, which is what a consumer
    that opens two binders in the other order needs.  (Contexts are lists, so
    [(β~tvar) ++ (b~tvar) ++ Θ] and [(b~tvar) ++ (β~tvar) ++ Θ] are different
    terms with the same [ftvar_in_aenv].) *)
(** ⚠️ AND IT NOW CARRIES A FLEX-AGREEMENT SIDE CONDITION (2026-08-18).  The
    ftvar inclusion alone is no longer enough: under the FlexR-PRIORITY GUARD
    the eq layer reads its context for HATTEDNESS — [LE-FlexR] wants the
    counterpart hatted and [LE-UnivGhost2] wants it not — and an
    ftvar-shrinking context can turn a flexible into a rigid.

    ⭐ AND IT IS SCOPED TO THE COUNTERPART'S FREE VARIABLES, which is exactly
    what the collection reads.  A GLOBAL iff would be unusable: two consumers
    move to a context that DROPS flexibles wholesale (the P6 arrow row peels
    off its own all-flex blocks; the decoration-soundness proof shrinks the
    run's context to [·]).  The scoped condition is preserved by the
    induction — [LE-Arrow] SHRINKS [ftv P'], and every binder row adds an
    opener that is RIGID on both sides ([a_flex_tvar_cons_tvar_any]). *)
Lemma a_looksub_lookeq_ctx_ftv_mono :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall Θ', ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     (forall β, β `in` ftvar_in_pskl P' ->
        (a_flex_tvar Θ β <-> a_flex_tvar Θ' β)) ->
     {{ Θ' ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall Θ', ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     (forall β, β `in` ftvar_in_pskl P' ->
        (a_flex_tvar Θ β <-> a_flex_tvar Θ' β)) ->
     {{ Θ' ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a).
Proof.
  (* the binder rows all discharge the same way: the premise's context grows
     by the SAME witness on both sides, so the inclusion is preserved *)
  assert (Hcons : forall (β : atom) Θ Θ',
            ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
            ftvar_in_aenv ((β ~ abind_tvar) ++ Θ')
              [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (intros; rewrite ! ftvar_in_aenv_cons_tvar; fsetdec).
  (* ⭐ and the flex-agreement rides through an OPENING: the opener is rigid on
     both sides, and it is fresh for the LARGER context, hence for both *)
  assert (Hfopen : forall (b : atom) (Θa Θb : aenv) (B : pskl),
            ftvar_in_aenv Θb [<=] ftvar_in_aenv Θa ->
            b `notin` ftvar_in_aenv Θa ->
            (forall β, β `in` ftvar_in_pskl B ->
               (a_flex_tvar Θa β <-> a_flex_tvar Θb β)) ->
            forall β,
              β `in` ftvar_in_pskl (open_pskl_wrt_pskl B (pskl_var_f b)) ->
              (a_flex_tvar ((b ~ abind_tvar) ++ Θa) β
               <-> a_flex_tvar ((b ~ abind_tvar) ++ Θb) β)).
  { intros b Θa Θb B Hincl Hb Hf β Hβ.
    rewrite ! a_flex_tvar_cons_tvar_any.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
      as Hup.
    destruct (β == b) as [-> | Hne].
    - (* the opener: flex-free on BOTH sides, since it dodges the larger one *)
      pose proof (dom_subset_ftvar_in_aenv Θa) as HdA.
      pose proof (dom_subset_ftvar_in_aenv Θb) as HdB.
      split; intro Hfx; exfalso; apply a_flex_tvar_in_dom in Hfx;
        [ clear - Hb HdA Hfx | clear - Hb HdA HdB Hincl Hfx ]; fsetdec.
    - apply Hf. simpl in Hup. clear - Hup Hβ Hne. fsetdec. }
  apply a_looksub_lookeq_mutind.
  - (* LS-Var *) intros. apply a_looksub__var.
  - (* LS-Absent *) intros Θ α m P P' Hnf Θ' Hm Hf.
    apply a_looksub__absent; exact Hnf.
  - (* LS-Vacuous *) intros. apply a_looksub__vacuous. assumption.
  - (* LS-Check *) intros Θ α A B Ξ C Hgf Hne Hg Hg0 Hp IH Θ' Hm Hf.
    apply a_looksub__check;
      solve [ assumption | apply IH; [ exact Hm | exact Hf ] ].
  - (* LS-ForallR *) intros Θ α A B Ξ C β Hgf Hfr Hocc Hnv Hp IH Θ' Hm Hf.
    apply a_looksub__forall_r with (β := β);
      [ exact Hgf | clear - Hfr Hm; fsetdec | exact Hocc | exact Hnv
      | apply IH;
        [ apply Hcons; exact Hm
        | apply Hfopen;
          [ exact Hm | clear - Hfr; fsetdec | exact Hf ] ] ].
  - (* LS-Arrow *)
    intros Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 IH1 Hp2 IH2 Θ' Hm Hf.
    apply a_looksub__arrow;
      [ exact Hg1 | exact Hg2 | apply IH1 | apply IH2 ]; solve
      [ exact Hm | intros β0 Hβ0; apply Hf; simpl; clear - Hβ0; fsetdec ].
  - (* LS-ForallL *) intros Θ α m P P' Ξ C β Hfr Hocc Hnh Hfr3 Hp IH Θ' Hm Hf.
    apply a_looksub__forall_l with (β := β);
      [ clear - Hfr Hm; fsetdec | exact Hocc | exact Hnh | exact Hfr3
      | apply IH;
        [ apply Hcons; exact Hm
        | intros β0 Hβ0; rewrite ! a_flex_tvar_cons_tvar_any;
          exact (Hf β0 Hβ0) ] ].
  - (* LS-UnivGhostL *) intros Θ α m P P' Ξ C Hnh Hfr3 Hp IH Θ' Hm Hf.
    apply a_looksub__univ_ghost_l;
      [ exact Hnh | exact Hfr3 | apply IH; [ exact Hm | exact Hf ] ].
  - (* LE-Var *) intros. apply a_lookeq__var.
  - (* LE-Absent *) intros Θ α P P' Hnf Θ' Hm Hf.
    apply a_lookeq__absent; exact Hnf.
  - (* LE-Vacuous *) intros. apply a_lookeq__vacuous. assumption.
  - (* LE-FlexR — ⭐ the row the flex-agreement is FOR *)
    intros Θ α P β α1 Hfr Hflx Hne Hin Θ' Hm Hf.
    apply a_lookeq__flex_r;
      [ clear - Hfr Hm; fsetdec
      | apply (proj1 (Hf β ltac:(simpl; clear; fsetdec))); exact Hflx
      | exact Hne | exact Hin ].
  - (* LE-Arrow *)
    intros Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 IH1 Hp2 IH2 Θ' Hm Hf.
    apply a_lookeq__arrow;
      [ exact Hg1 | exact Hg2 | apply IH1 | apply IH2 ]; solve
      [ exact Hm | intros β0 Hβ0; apply Hf; simpl; clear - Hβ0; fsetdec ].
  - (* LE-ForallInh *) intros Θ α P P' Ξ C β Hfr Hocc Hp IH Θ' Hm Hf.
    apply a_lookeq__forall_inh with (β := β);
      [ clear - Hfr Hm; fsetdec | exact Hocc
      | apply IH;
        [ apply Hcons; exact Hm
        | apply Hfopen;
          [ exact Hm | clear - Hfr; fsetdec | exact Hf ] ] ].
  - (* LE-ForallSyn *) intros Θ α P P' Ξ C β Hfr Hocc Hp IH Θ' Hm Hf.
    apply a_lookeq__forall_syn with (β := β);
      [ clear - Hfr Hm; fsetdec | exact Hocc
      | apply IH;
        [ apply Hcons; exact Hm
        | intros β0 Hβ0; rewrite ! a_flex_tvar_cons_tvar_any;
          exact (Hf β0 Hβ0) ] ].
  - (* LE-UnivGhost *) intros Θ α P P' Ξ C Hp IH Θ' Hm Hf.
    apply a_lookeq__univ_ghost; apply IH; [ exact Hm | exact Hf ].
  - (* LE-UnivGhost1 *) intros Θ α P P' Ξ C β Hfr Hocc Hp IH Θ' Hm Hf.
    apply a_lookeq__univ_ghost1 with (β := β);
      [ clear - Hfr Hm; fsetdec | exact Hocc
      | apply IH;
        [ apply Hcons; exact Hm
        | apply Hfopen;
          [ exact Hm | clear - Hfr; fsetdec | exact Hf ] ] ].
  - (* LE-UnivGhost2 — ⭐ the guard needs the OTHER direction *)
    intros Θ α P P' Ξ C Hg Hfx Hp IH Θ' Hm Hf.
    apply a_lookeq__univ_ghost2;
      [ exact Hg
      | intros β Heq Hflx; subst P';
        exact (Hfx β eq_refl
                 (proj2 (Hf β ltac:(simpl; clear; fsetdec)) Hflx))
      | apply IH; [ exact Hm | exact Hf ] ].
  - (* LE-UnivGhostR *) intros Θ α P P' Ξ C Hne Hg Hp IH Θ' Hm Hf.
    apply a_lookeq__univ_ghost_r;
      [ exact Hne | exact Hg | apply IH; [ exact Hm | exact Hf ] ].
Qed.

Lemma a_looksub_ctx_ftv_mono : forall Θ α m P P' Ξ 𝒞 Θ',
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
  (forall β, β `in` ftvar_in_pskl P' ->
     (a_flex_tvar Θ β <-> a_flex_tvar Θ' β)) ->
  {{ Θ' ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a.
Proof. intros; eapply (proj1 a_looksub_lookeq_ctx_ftv_mono); eauto. Qed.

Lemma a_lookeq_ctx_ftv_mono : forall Θ α P P' Ξ 𝒞 Θ',
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
  (forall β, β `in` ftvar_in_pskl P' ->
     (a_flex_tvar Θ β <-> a_flex_tvar Θ' β)) ->
  {{ Θ' ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a.
Proof. intros; eapply (proj2 a_looksub_lookeq_ctx_ftv_mono); eauto. Qed.

(** EXCHANGE, the shape consumers use. *)
Lemma a_looksub_ctx_exchange : forall Θ α m P P' Ξ 𝒞 β1 β2,
  {{ ((β1 ~ abind_tvar) ++ (β2 ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ ((β2 ~ abind_tvar) ++ (β1 ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a.
Proof.
  intros. eapply a_looksub_ctx_ftv_mono; [ eassumption | | ].
  - rewrite ! ftvar_in_aenv_cons_tvar. fsetdec.
  - (* ⭐ FREE: the two entries exchanged are RIGID, so flexibility is
       untouched in both directions. *)
    intros β0 _; rewrite ! a_flex_tvar_cons_tvar_any; reflexivity.
Qed.

(** DERIVED junk-freeness for the look cluster (cluster 1's principle, cluster
    3's judgment): every name the run GENERATES avoids the ambient context,
    because LE-FlexR — the single generative rule — avoids [ftvar_in_aenv Θ]
    and the ∀ rules only GROW that context.  In particular a ∀ rule's own
    binder is not in the block its premise produces, which is what lets a
    consumer MOVE that binder with [Ξ] left fixed. *)
Lemma a_looksub_lookeq_generated_fresh :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall γ, γ `in` ftvar_in_aenv Θ -> γ `notin` dom Ξ) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall γ, γ `in` ftvar_in_aenv Θ -> γ `notin` dom Ξ).
Proof.
  assert (Hgrow : forall (β γ : atom) Θ,
            γ `in` ftvar_in_aenv Θ ->
            γ `in` ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (intros; rewrite ftvar_in_aenv_cons_tvar; fsetdec).
  apply a_looksub_lookeq_mutind.
  - (* LS-Var *) intros; simpl; fsetdec.
  - (* LS-Absent *) intros; simpl; fsetdec.
  - (* LS-Vacuous *) intros; simpl; fsetdec.
  - (* LS-Check *) intros Θ α A B Ξ C Hgf Hne Hg Hg0 Hp IH γ Hγ. exact (IH γ Hγ).
  - (* LS-ForallR *) intros Θ α A B Ξ C β Hgf Hfr Hocc Hnv Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  - (* LS-Arrow *) intros Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 IH1 Hp2 IH2 γ Hγ.
    rewrite dom_app.
    pose proof (IH1 γ Hγ); pose proof (IH2 γ Hγ). fsetdec.
  - (* LS-ForallL *) intros Θ α m P P' Ξ C β Hfr Hocc Hnh Hfr3 Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  - (* LS-UnivGhostL *) intros Θ α m P P' Ξ C Hnh Hfr3 Hp IH γ Hγ.
    exact (IH γ Hγ).
  - (* LE-Var *) intros; simpl; fsetdec.
  - (* LE-Absent *) intros; simpl; fsetdec.
  - (* LE-Vacuous *) intros; simpl; fsetdec.
  - (* LE-FlexR — the single generative rule *)
    intros Θ α P β α1 Hfr Hflx Hne Hin γ Hγ.
    simpl. clear - Hfr Hγ. fsetdec.
  - (* LE-Arrow *) intros Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 IH1 Hp2 IH2 γ Hγ.
    rewrite dom_app.
    pose proof (IH1 γ Hγ); pose proof (IH2 γ Hγ). fsetdec.
  - (* LE-ForallInh *) intros Θ α P P' Ξ C β Hfr Hocc Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  - (* LE-ForallSyn *) intros Θ α P P' Ξ C β Hfr Hocc Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  - (* LE-UnivGhost *) intros Θ α P P' Ξ C Hp IH γ Hγ. exact (IH γ Hγ).
  - (* LE-UnivGhost1 *) intros Θ α P P' Ξ C β Hfr Hocc Hp IH γ Hγ.
    apply IH; apply Hgrow; exact Hγ.
  - (* LE-UnivGhost2 *) intros Θ α P P' Ξ C Hg Hfx Hp IH γ Hγ. exact (IH γ Hγ).
  - (* LE-UnivGhostR *) intros Θ α P P' Ξ C Hne Hg Hp IH γ Hγ. exact (IH γ Hγ).
Qed.

(** The shape the ∀-binder consumers use: a rule's own witness is not in the
    block its premise generated, nor free in it. *)
Lemma a_looksub_binder_not_generated : forall β Θ α m P P' Ξ 𝒞,
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
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
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  β `notin` ftvar_in_aenv Ξ.
Proof.
  intros β Θ α P P' Ξ 𝒞 Hlk.
  pose proof (a_lookeq_generated_ftvar Hlk) as Hftv.
  assert (Hin : β `in` ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (rewrite ftvar_in_aenv_cons_tvar; fsetdec).
  pose proof ((proj2 a_looksub_lookeq_generated_fresh) _ _ _ _ _ _ Hlk β Hin).
  fsetdec.
Qed.

(** * MOVING A LOOK RUN'S BINDER — derived from EQUIVARIANCE.

    The decl-side judgments the decoration lemmas build ([a_consistag] /
    [a_subtag]) are COFINITE, so a ∀ row must serve a whole family of openers
    from the look run's ONE exists-fresh binder: the binder has to MOVE.

    ⚙ Until 2026-08-06 that was a 528-line SIZE INDUCTION
    ([a_looksub_lookeq_rename_tvar_size]) over a substitution-shaped rename,
    whose ∀ rows each had to split three ways (source = binder / target =
    binder / neither) because a substitution can COLLAPSE two names.  A
    TRANSPOSITION cannot, so [a_looksub_lookeq_swap] (prop_swap.v) proves the
    same content with no case split at all, and the two rename lemmas below —
    STATEMENTS UNCHANGED, so every call site is untouched — fall out of it by
    the three "swap is the rename when the target is fresh" bridges
    ([swap_aenv_as_rename], [swap_pskl_as_subst], [swap_cstrs_as_subst]).
    The looked-for variable [α] is fixed by [swap_atom_other] ([β ≠ α],
    [α1 ≠ α]), and [Ξ]'s payload-freshness comes from
    [a_look*_generated_ftvar] as before. *)

(** [swap_cstrs] IS [subst_cstrs] when the target is fresh for the list — the
    constraint-list half of the bridge (the syntactic halves are in
    prop_swap.v; [subst_cstrs] is defined here, so this one is too). *)
Lemma swap_cstrs_as_subst : forall β γ (C : a_cstrs),
  γ `notin` ftvar_in_a_cstrs C ->
  swap_cstrs β γ C = subst_cstrs γ β C.
Proof.
  induction C as [| c C' IH]; intros Hγ; [reflexivity |].
  simpl in Hγ. rewrite swap_cstrs_cons. cbn [subst_cstrs].
  f_equal; [ | apply IH; clear - Hγ; fsetdec ].
  destruct c; simpl in Hγ |- *; f_equal; apply swap_pskl_as_subst; fsetdec.
Qed.

Lemma a_looksub_rename_tvar : forall Θ α m P P' Ξ 𝒞 β α1,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  β <> α -> α1 <> α ->
  α1 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union`
             ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ (rename_aenv α1 β Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ≼[ α , m ]
    (subst_pskl_in_pskl (pskl_var_f α1) β P')
    ⤳ (rename_aenv α1 β Ξ) ⨾ (subst_cstrs α1 β 𝒞) }}a.
Proof.
  intros Θ α m P P' Ξ 𝒞 β α1 Hlk Hβα Hα1α Hfr.
  pose proof (a_looksub_generated_ftvar Hlk) as HΞ.
  pose proof (proj1 (a_looksub_lookeq_swap β α1) _ _ _ _ _ _ _ Hlk) as Hr.
  rewrite (swap_atom_other β α1 α ltac:(auto) ltac:(auto)) in Hr.
  rewrite (swap_aenv_as_rename β α1 Θ) in Hr by (clear - Hfr; fsetdec).
  rewrite (swap_aenv_as_rename β α1 Ξ) in Hr by (clear - Hfr HΞ; fsetdec).
  rewrite (swap_pskl_as_subst β α1 P) in Hr by (clear - Hfr; fsetdec).
  rewrite (swap_pskl_as_subst β α1 P') in Hr by (clear - Hfr; fsetdec).
  rewrite (@swap_cstrs_as_subst β α1 𝒞) in Hr by (clear - Hfr; fsetdec).
  exact Hr.
Qed.

Lemma a_lookeq_rename_tvar : forall Θ α P P' Ξ 𝒞 β α1,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  β <> α -> α1 <> α ->
  α1 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union`
             ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ (rename_aenv α1 β Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ∼[ α ]
    (subst_pskl_in_pskl (pskl_var_f α1) β P')
    ⤳ (rename_aenv α1 β Ξ) ⨾ (subst_cstrs α1 β 𝒞) }}a.
Proof.
  intros Θ α P P' Ξ 𝒞 β α1 Hlk Hβα Hα1α Hfr.
  pose proof (a_lookeq_generated_ftvar Hlk) as HΞ.
  pose proof (proj2 (a_looksub_lookeq_swap β α1) _ _ _ _ _ _ Hlk) as Hr.
  rewrite (swap_atom_other β α1 α ltac:(auto) ltac:(auto)) in Hr.
  rewrite (swap_aenv_as_rename β α1 Θ) in Hr by (clear - Hfr; fsetdec).
  rewrite (swap_aenv_as_rename β α1 Ξ) in Hr by (clear - Hfr HΞ; fsetdec).
  rewrite (swap_pskl_as_subst β α1 P) in Hr by (clear - Hfr; fsetdec).
  rewrite (swap_pskl_as_subst β α1 P') in Hr by (clear - Hfr; fsetdec).
  rewrite (@swap_cstrs_as_subst β α1 𝒞) in Hr by (clear - Hfr; fsetdec).
  exact Hr.
Qed.

(** MOVE a look run's ∀ binder [b] (the head of its context) to a fresh
    [β]: the subjects and the constraints are renamed, the generated block
    [Ξ] survives untouched ([a_look*_binder_not_generated]). *)
Lemma a_looksub_move_binder : forall Θ α m P P' Ξ 𝒞 b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  b <> α -> b `notin` ftvar_in_aenv Θ -> β <> α -> β <> b ->
  β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl P'
            `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f β) b P) ≼[ α , m ]
    (subst_pskl_in_pskl (pskl_var_f β) b P') ⤳ Ξ ⨾ (subst_cstrs β b 𝒞) }}a.
Proof.
  intros * Hp Hbα HbΘ Hβα Hβb Hβ.
  assert (Hfr : β `notin` ftvar_in_aenv ((b ~ abind_tvar) ++ Θ) `union` ftvar_in_pskl P
                 `union` ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞)
    by look_fresh.
  pose proof (a_looksub_rename_tvar Hp Hbα Hβα Hfr) as Hr.
  rewrite rename_aenv_cons_tvar_eq, (@rename_aenv_fresh_eq Θ β b HbΘ),
    (@rename_aenv_fresh_eq Ξ β b (a_looksub_binder_not_generated Hp)) in Hr.
  exact Hr.
Qed.

Lemma a_lookeq_move_binder : forall Θ α P P' Ξ 𝒞 b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  b <> α -> b `notin` ftvar_in_aenv Θ -> β <> α -> β <> b ->
  β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl P'
            `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f β) b P) ∼[ α ]
    (subst_pskl_in_pskl (pskl_var_f β) b P') ⤳ Ξ ⨾ (subst_cstrs β b 𝒞) }}a.
Proof.
  intros * Hp Hbα HbΘ Hβα Hβb Hβ.
  assert (Hfr : β `notin` ftvar_in_aenv ((b ~ abind_tvar) ++ Θ) `union` ftvar_in_pskl P
                 `union` ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞)
    by look_fresh.
  pose proof (a_lookeq_rename_tvar Hp Hbα Hβα Hfr) as Hr.
  rewrite rename_aenv_cons_tvar_eq, (@rename_aenv_fresh_eq Θ β b HbΘ),
    (@rename_aenv_fresh_eq Ξ β b (a_lookeq_binder_not_generated Hp)) in Hr.
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
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f b)) ∼[ α ]
    (open_pskl_wrt_pskl P' (pskl_var_f b)) ⤳ Ξ ⨾ 𝒞 }}a ->
  b `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P') ->
  β <> α ->
  β `notin` ftvar_in_aenv Θ
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P' (pskl_var_f b))
            `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
    (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ (subst_cstrs β b 𝒞) }}a.
Proof.
  intros Θ α P P' Ξ 𝒞 b β Hp Hb Hβα Hβ.
  destruct (β == b) as [-> | Hβb];
    [ rewrite subst_cstrs_same; exact Hp | ].
  assert (Hbα : b <> α) by (clear - Hb; fsetdec).
  assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hb; fsetdec).
  pose proof (a_lookeq_move_binder Hp Hbα HbΘ Hβα Hβb Hβ) as Hr.
  rewrite <- (subst_pskl_in_pskl_intro b P (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  rewrite <- (subst_pskl_in_pskl_intro b P' (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  exact Hr.
Qed.

Lemma a_lookeq_forall_move_l : forall Θ α P Pt Ξ 𝒞 b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f b)) ∼[ α ] Pt
    ⤳ Ξ ⨾ 𝒞 }}a ->
  b `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl Pt) ->
  β <> α ->
  β `notin` ftvar_in_aenv Θ
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
            `union` ftvar_in_pskl Pt `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ] Pt
    ⤳ Ξ ⨾ (subst_cstrs β b 𝒞) }}a.
Proof.
  intros Θ α P Pt Ξ 𝒞 b β Hp Hb Hβα Hβ.
  destruct (β == b) as [-> | Hβb];
    [ rewrite subst_cstrs_same; exact Hp | ].
  assert (Hbα : b <> α) by (clear - Hb; fsetdec).
  assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hb; fsetdec).
  pose proof (a_lookeq_move_binder Hp Hbα HbΘ Hβα Hβb Hβ) as Hr.
  rewrite (subst_pskl_in_pskl_fresh_eq Pt) in Hr by (clear - Hb; fsetdec).
  rewrite <- (subst_pskl_in_pskl_intro b P (pskl_var_f β)) in Hr
    by (clear - Hb; fsetdec).
  exact Hr.
Qed.

Lemma a_lookeq_forall_move_r : forall Θ α Ps P' Ξ 𝒞 b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ Ps ∼[ α ] (open_pskl_wrt_pskl P' (pskl_var_f b))
    ⤳ Ξ ⨾ 𝒞 }}a ->
  b `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
                     `union` ftvar_in_pskl P') ->
  β <> α ->
  β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
            `union` ftvar_in_pskl (open_pskl_wrt_pskl P' (pskl_var_f b))
            `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ Ps ∼[ α ] (open_pskl_wrt_pskl P' (pskl_var_f β))
    ⤳ Ξ ⨾ (subst_cstrs β b 𝒞) }}a.
Proof.
  intros Θ α Ps P' Ξ 𝒞 b β Hp Hb Hβα Hβ.
  destruct (β == b) as [-> | Hβb];
    [ rewrite subst_cstrs_same; exact Hp | ].
  assert (Hbα : b <> α) by (clear - Hb; fsetdec).
  assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hb; fsetdec).
  pose proof (a_lookeq_move_binder Hp Hbα HbΘ Hβα Hβb Hβ) as Hr.
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

(** A look run's ∀ binder [b] that did NOT leak (it is absent from the
    block [Ξ] and the constraints [𝒞]) can be moved to a fresh [δ] avoiding
    any given [L]: the run is the same up to the renaming of its subjects. *)
Lemma a_looksub_rename_binder : forall L {Θ α m P P' Ξ 𝒞 b},
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  b <> α -> b `notin` ftvar_in_aenv Θ ->
  b `notin` dom Ξ -> b `notin` ftvar_in_a_cstrs 𝒞 ->
  exists δ, δ <> α /\
    δ `notin` add α (add b (L `union` ftvar_in_aenv Θ `union` dom Ξ
                              `union` ftvar_in_a_cstrs 𝒞)) /\
    {{ ((δ ~ abind_tvar) ++ Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f δ) b P)
         ≼[ α , m ] (subst_pskl_in_pskl (pskl_var_f δ) b P') ⤳ Ξ ⨾ 𝒞 }}a.
Proof.
  intros * Hp Hbα HbΘ HbΞ HbC.
  pick fresh δ for (add α (add b (L `union` ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞))).
  exists δ. split; [ clear - Fr; fsetdec | split; [ clear - Fr; fsetdec | ] ].
  rewrite <- (@subst_cstrs_fresh_eq δ b 𝒞 HbC).
  apply (a_looksub_move_binder Hp Hbα HbΘ); clear - Fr; fsetdec.
Qed.

(** The same for an equality look. *)
Lemma a_lookeq_rename_binder : forall L {Θ α P P' Ξ 𝒞 b},
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  b <> α -> b `notin` ftvar_in_aenv Θ ->
  b `notin` dom Ξ -> b `notin` ftvar_in_a_cstrs 𝒞 ->
  exists δ, δ <> α /\
    δ `notin` add α (add b (L `union` ftvar_in_aenv Θ `union` dom Ξ
                              `union` ftvar_in_a_cstrs 𝒞)) /\
    {{ ((δ ~ abind_tvar) ++ Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f δ) b P)
         ∼[ α ] (subst_pskl_in_pskl (pskl_var_f δ) b P') ⤳ Ξ ⨾ 𝒞 }}a.
Proof.
  intros * Hp Hbα HbΘ HbΞ HbC.
  pick fresh δ for (add α (add b (L `union` ftvar_in_aenv Θ `union` ftvar_in_pskl P
                     `union` ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞))).
  exists δ. split; [ clear - Fr; fsetdec | split; [ clear - Fr; fsetdec | ] ].
  rewrite <- (@subst_cstrs_fresh_eq δ b 𝒞 HbC).
  apply (a_lookeq_move_binder Hp Hbα HbΘ); clear - Fr; fsetdec.
Qed.

Lemma a_looksub_lookeq_rename_var_size : forall n,
  (forall Θ α m P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') + 1 <= n ->
     {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall α', α' `notin` ftvar_in_pskl P ->
     α' `notin` dom Ξ -> α' `notin` ftvar_in_a_cstrs 𝒞 ->
     {{ Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞 }}a) /\
  (forall Θ α P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') <= n ->
     {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall α', α' `notin` ftvar_in_pskl P ->
     α' `notin` dom Ξ -> α' `notin` ftvar_in_a_cstrs 𝒞 ->
     {{ Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ∼[ α' ] P' ⤳ Ξ ⨾ 𝒞 }}a).
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
      | Θ α A B Ξ0 C0 Hgf0 Hne Hg Hg0 Hp          (* LS-Check *)
      | Θ α A B Ξ0 C0 b Hgf0 Hfr0 Hocc0 Hnv0 Hp   (* LS-ForallR *)
      | Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 Hp2 (* LS-Arrow *)
      | Θ α m Q Q' Ξ0 C0 b Hfr0 Hocc0 Hnh0 Hfr3 Hp (* LS-ForallL *)
      | Θ α m Q Q' Ξ0 C0 Hnh0 Hfr3 Hp ];          (* LS-UnivGhostL *)
      cbn in Hn, Hα'P |- *.
    - (* LS-Var *)
      destruct_if as [_ | Hne]; [ | exfalso; congruence ].
      apply a_looksub__var.
    - (* LS-Absent *)
      rewrite subst_pskl_in_pskl_fresh_eq by exact Hnf.
      apply a_looksub__absent; exact Hα'P.
    - (* LS-Vacuous *) apply a_looksub__vacuous.
      apply subst_var_neq_new; assumption.
    - (* LS-Check *)
      apply a_looksub__check;
        [ assumption
        | apply subst_var_neq_new; assumption
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
        destruct (a_looksub_rename_binder (ftvar_in_pskl A `union` ftvar_in_pskl B)
                    Hp Hbα HbΘ Hα'Ξ Hα'C) as [δ [Hδα [Hδ H1]]].
        rewrite (subst_pskl_in_pskl_fresh_eq A) in H1 by exact HbA.
        rewrite <- (subst_pskl_in_pskl_intro b B (pskl_var_f δ)) in H1
          by exact HbB.
        apply a_looksub__forall_r with (β := δ);
          [ ghost_free_auto | look_fresh
          | apply ftv_subst_var_in; exact Hocc0
          | apply subst_var_neq_new; assumption | ].
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact H1 | exact HbA | exact Hα'Ξ | exact Hα'C ].
      + (* the binder stays put *)
        apply a_looksub__forall_r with (β := b);
          [ ghost_free_auto | look_fresh
          | apply ftv_subst_var_in; exact Hocc0
          | apply subst_var_neq_new; assumption | ].
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact Hp | exact Hα'P | exact Hα'Ξ | exact Hα'C ].
    - (* LS-Arrow *)
      rewrite dom_app in Hα'Ξ. rewrite ftvar_in_a_cstrs_app in Hα'C.
      (* ⚙ the CROSS-HALF GUARD rides through: only the SUBJECT is renamed *)
      apply a_looksub__arrow;
        [ exact Hg1 | exact Hg2 | apply IHe | apply IHs ];
        solve [ lia | assumption
              | clear - Hα'P; fsetdec | clear - Hα'Ξ; fsetdec
              | clear - Hα'C; fsetdec ].
    - (* LS-ForallL — the SOURCE opens; the binder LEAKS *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + destruct (a_looksub_rename_binder (ftvar_in_pskl Q `union` ftvar_in_pskl Q')
                    Hp Hbα HbΘ Hα'Ξ Hα'C) as [δ [Hδα [Hδ H1]]].
        rewrite (subst_pskl_in_pskl_fresh_eq Q') in H1 by exact HbQ'.
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
          by exact HbQ.
        apply a_looksub__forall_l with (β := δ);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0
          | assumption | assumption | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
          by (solve [ congruence | constructor ]).
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact H1 | look_fresh | exact Hα'Ξ | exact Hα'C ].
      + apply a_looksub__forall_l with (β := b);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0
          | assumption | assumption | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α'))
          by (solve [ congruence | constructor ]).
        apply IHs;
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | exact Hp | look_fresh | exact Hα'Ξ | exact Hα'C ].
    - (* LS-UnivGhostL *)
      apply a_looksub__univ_ghost_l; [ assumption | assumption | ]; apply IHs;
        solve [ lia | assumption ]. }
  (* ==================== the [a_lookeq] half ==================== *)
  { intros Θ α P P' Ξ 𝒞 Hn Hd α' Hα'P Hα'Ξ Hα'C.
    destruct Hd as
      [ Θ α Q                                     (* LE-Var *)
      | Θ α Q Q' Hnf                              (* LE-Absent *)
      | Θ α Q                                     (* LE-Vacuous *)
      | Θ α Q b γ Hfr0 Hflx Hne Hin               (* LE-FlexR *)
      | Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 Hp2 (* LE-Arrow *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hocc0 Hp            (* LE-ForallInh *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hocc0 Hp            (* LE-ForallSyn *)
      | Θ α Q Q' Ξ0 C0 Hp                         (* LE-UnivGhost *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hocc0 Hp            (* LE-UnivGhost1 *)
      | Θ α Q Q' Ξ0 C0 Hg Hfx Hp                  (* LE-UnivGhost2 *)
      | Θ α Q Q' Ξ0 C0 Hne Hg Hp ];               (* LE-UnivGhostR *)
      cbn in Hn, Hα'P |- *.
    - (* LE-Var *)
      destruct_if as [_ | Hne]; [ | exfalso; congruence ].
      apply a_lookeq__var.
    - (* LE-Absent *)
      rewrite subst_pskl_in_pskl_fresh_eq by exact Hnf.
      apply a_lookeq__absent; exact Hα'P.
    - (* LE-Vacuous *) apply a_lookeq__vacuous.
      apply subst_var_neq_new; assumption.
    - (* LE-FlexR — the new name must dodge the GENERATED flexible, which is
         exactly what the output-freshness premise supplies *)
      cbn in Hfr0, Hα'Ξ |- *.
      apply a_lookeq__flex_r;
        [ look_fresh
        | exact Hflx
        | apply subst_var_neq_new; assumption
        | apply ftv_subst_var_in; exact Hin ].
    - (* LE-Arrow *)
      rewrite dom_app in Hα'Ξ. rewrite ftvar_in_a_cstrs_app in Hα'C.
      apply a_lookeq__arrow;
        [ exact Hg1 | exact Hg2 | apply IHe | apply IHe ];
        solve [ lia | assumption
              | clear - Hα'P; fsetdec | clear - Hα'Ξ; fsetdec
              | clear - Hα'C; fsetdec ].
    - (* LE-ForallInh — BOTH sides open *)
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      destruct (α' == b) as [-> | Hα'b].
      + destruct (a_lookeq_rename_binder (ftvar_in_pskl Q `union` ftvar_in_pskl Q')
                    Hp Hbα HbΘ Hα'Ξ Hα'C) as [δ [Hδα [Hδ H1]]].
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
          by exact HbQ.
        rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f δ)) in H1
          by exact HbQ'.
        apply a_lookeq__forall_inh with (β := δ);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
          by (solve [ congruence | constructor ]).
        apply IHe;
          [ rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia
          | exact H1 | look_fresh | exact Hα'Ξ | exact Hα'C ].
      + apply a_lookeq__forall_inh with (β := b);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
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
      + destruct (a_lookeq_rename_binder (ftvar_in_pskl Q `union` ftvar_in_pskl Q')
                    Hp Hbα HbΘ Hα'Ξ Hα'C) as [δ [Hδα [Hδ H1]]].
        rewrite (subst_pskl_in_pskl_fresh_eq (pskl_univ_ghost Q')) in H1
          by exact HbQ'.
        rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
          by exact HbQ.
        apply a_lookeq__forall_syn with (β := δ);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f b))
          by (solve [ congruence | constructor ]).
        apply IHe with (P' := pskl_univ_ghost Q');
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact H1 | look_fresh | exact Hα'Ξ | exact Hα'C ].
      + apply a_lookeq__forall_syn with (β := b);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f α'))
          by (solve [ congruence | constructor ]).
        apply IHe with (P' := pskl_univ_ghost Q');
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
      + destruct (a_lookeq_rename_binder (ftvar_in_pskl Q `union` ftvar_in_pskl Q')
                    Hp Hbα HbΘ Hα'Ξ Hα'C) as [δ [Hδα [Hδ H1]]].
        rewrite (subst_pskl_in_pskl_fresh_eq (pskl_univ_ghost Q)) in H1
          by exact HbQ.
        rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f δ)) in H1
          by exact HbQ'.
        apply a_lookeq__univ_ghost1 with (β := δ);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        apply IHe with (P := pskl_univ_ghost Q);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact H1 | cbn; exact HbQ | exact Hα'Ξ | exact Hα'C ].
      + apply a_lookeq__univ_ghost1 with (β := b);
          [ look_fresh | apply ftv_subst_var_in; exact Hocc0 | ].
        apply IHe with (P := pskl_univ_ghost Q);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hp | cbn; exact Hα'P | exact Hα'Ξ | exact Hα'C ].
    - (* LE-UnivGhost2 *)
      apply a_lookeq__univ_ghost2;
        [ exact Hg | exact Hfx | apply IHe; solve [ lia | assumption ] ].
    - (* LE-UnivGhostR *)
      apply a_lookeq__univ_ghost_r;
        [ apply subst_var_neq_new; assumption
        | apply guarded_pskl_subst_var; exact Hg
        | apply IHe; solve [ lia | assumption ] ]. }
Qed.

Lemma a_looksub_rename_var : forall Θ α m P P' Ξ 𝒞 α',
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  α' `notin` ftvar_in_pskl P ->
  α' `notin` dom Ξ -> α' `notin` ftvar_in_a_cstrs 𝒞 ->
  {{ Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞 }}a.
Proof.
  intros. eapply (proj1 (a_looksub_lookeq_rename_var_size
                           (2 * (size_pskl P + size_pskl P') + 1))); eauto.
Qed.

(* ===================================================================== *)
(*  §11. The [a_extract] FAMILY from one instance                         *)
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
  {{ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α)) ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}a ->
  α `notin` ftvar_in_pskl P ->
  exists L, forall α',
    α' `notin` (singleton α `union` ftvar_in_pskl P `union` L) ->
    {{ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α')) ⊳[ NM , α' , M ] P0 ⤳ Ξ ↪ P1 }}a.
Proof.
  intros Θ0 NM M α P P0 Ξ P1 Hex Hfr.
  (* ⭐ THREE blocks since 2026-08-04: collection [Ξl], SOLVING [Ξs],
     final guess [Ξg].  The renaming only touches the FIRST — the solve and
     the guess never see the looked-for variable — so the family is still
     the renamed look over the SAME solve and guess. *)
  inversion Hex as [ Θ0' NM' α'' m' Ps Ps' Ξl Ξs Ξg 𝒞l Q Q' Hlk Hsol Hgu
                     Hgd Hgd2 HeqΘ HeqNM Heqα Heqm HeqP HeqP0 ]; subst.
  exists (dom Ξl `union` ftvar_in_a_cstrs 𝒞l).
  intros α' Hα'.
  (* ⚙ the CROSS-LAYER guard rides through untouched: [a_looksub_rename_var]
     moves the SUBJECT and the marker and leaves [Ξl]/[𝒞l] alone. *)
  eapply a_extract__solve;
    [ | eassumption | eassumption | eassumption | eassumption ].
  assert (Hα'P : α' `notin`
                   ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                  P (pskl_var_f α)) as Hup.
    simpl in Hup. clear - Hα' Hup; fsetdec. }
  pose proof (a_looksub_rename_var Hlk Hα'P
                ltac:(clear - Hα'; solve_notin_auto) ltac:(clear - Hα'; solve_notin_auto))
    as Hlk'.
  rewrite <- (subst_pskl_in_pskl_intro α P (pskl_var_f α') Hfr) in Hlk'.
  exact Hlk'.
Qed.
