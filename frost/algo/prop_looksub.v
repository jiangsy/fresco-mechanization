(** BASICS for the constraint-collection layer
    ([a_looksub]/[a_lookeq]/[a_extract]) — docs/DESIGN-subtyping.md P2.

    The declaration-shape facts every re-attachment of a look output [Ξ] to
    a context needs: look only ever generates FLEXIBLE declarations (the
    single generative rule is LE-FlexR), and [a_extract] appends [guess]'s
    declarations ([a_guess_mono_decls]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.

Set Implicit Arguments.

Scheme a_looksub_mutind := Induction for a_looksub Sort Prop
  with a_lookeq_mutind := Induction for a_lookeq Sort Prop.

Combined Scheme a_looksub_lookeq_mutind
  from a_looksub_mutind, a_lookeq_mutind.

(* ===================================================================== *)
(*  §1  Look outputs are declaration-only contexts                        *)
(* ===================================================================== *)

Lemma a_looksub_lookeq_decls :
  (forall α m P P' Ξ C, P ≼[ α , m ] P' ⤳ Ξ ⨾ C -> a_decls Ξ) /\
  (forall α P P' Ξ C, P ∼[ α ] P' ⤳ Ξ ⨾ C -> a_decls Ξ).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun α m P P' Ξ C _ => a_decls Ξ)
           (fun α P P' Ξ C _ => a_decls Ξ));
    intros; try solve [ assumption ]; try solve [ apply a_decls__nil ];
    try solve [ apply a_decls_app; assumption ];
    try solve [ destruct (atom_fresh L) as [β0 Hβ0]; eauto ].
  (* LE-FlexR : the single generative rule *)
  econstructor; apply a_decls__nil.
Qed.

Lemma a_looksub_decls : forall α m P P' Ξ C,
  P ≼[ α , m ] P' ⤳ Ξ ⨾ C -> a_decls Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_decls); eauto. Qed.

Lemma a_lookeq_decls : forall α P P' Ξ C,
  P ∼[ α ] P' ⤳ Ξ ⨾ C -> a_decls Ξ.
Proof. intros; eapply (proj2 a_looksub_lookeq_decls); eauto. Qed.

(** [guess] generates only declarations ([SK]: none; [TY]: the fresh mono
    flexibles of [a_guess_mono]). *)
Lemma a_guess_decls : forall NM Q Ξ Q',
  a_guess NM Q Ξ Q' -> a_decls Ξ.
Proof.
  intros NM Q Ξ Q' H; destruct H;
    [ apply a_decls__nil | eapply a_guess_mono_decls; eauto ].
Qed.

Lemma a_extract_decls : forall NM α m P P' Ξ Q,
  P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q -> a_decls Ξ.
Proof.
  intros NM α m P P' Ξ Q H; destruct H.
  apply a_decls_app;
    [ eapply a_looksub_decls; eauto | eapply a_guess_decls; eauto ].
Qed.
