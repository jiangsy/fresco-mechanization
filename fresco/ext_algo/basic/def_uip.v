Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.def_ott.

#[export] Instance eqdec_atom : EqDec atom := { eq_dec := fun x y => x == y }.

Derive NoConfusion EqDec for pskl.

#[export] Instance uip_pskl : UIP pskl := eqdec_uip _.
