(** Frost — declarative subtyping metatheory (Phase 2.C).

    Umbrella file: [Require Export]s the split [subtyping/] modules
    ([prop_basics], [prop_consis_trans], [prop_consis_sub_trans],
    [prop_sub_sound]) so downstream files get the whole subtyping subtree
    by [Require Import src.frost.decl.prop_subtyping]. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Require Export src.frost.decl.subtyping.prop_basics.
Require Export src.frost.decl.subtyping.prop_consis_trans.
Require Export src.frost.decl.subtyping.prop_consis_sub_trans.
Require Export src.frost.decl.subtyping.prop_sub_sound.

Set Implicit Arguments.
