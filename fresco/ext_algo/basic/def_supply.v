Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Set Implicit Arguments.

Notation supply := atoms.

Lemma supply_add_grows : forall (S : supply) α, S [<=] add α S.
Proof. intros; fsetdec. Qed.

Arguments supply_add_grows : clear implicits.

Definition supply_fresh (S : supply) : atom := proj1_sig (atom_fresh S).

Lemma supply_fresh_notin : forall S, supply_fresh S `notin` S.
Proof.
  intros S. unfold supply_fresh. destruct (atom_fresh S) as [α Hα]. exact Hα.
Qed.

Arguments supply_fresh_notin : clear implicits.
