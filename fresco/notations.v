Require Export Metalib.Metatheory.

Require Export src.fresco.def_ott.
Require Export src.fresco.prop_ln.
Require Export src.fresco.def_shapes.

Declare Scope fresco_d_scope.
Delimit Scope fresco_d_scope with d.
Open Scope fresco_d_scope.

Declare Scope fresco_ad_scope.
Delimit Scope fresco_ad_scope with ad.
Open Scope fresco_ad_scope.

Declare Scope fresco_a_scope.
Delimit Scope fresco_a_scope with a.
Open Scope fresco_a_scope.

Declare Scope fresco_da_scope.
Delimit Scope fresco_da_scope with da.
Open Scope fresco_da_scope.

Notation inter := AtomSetImpl.inter.
Notation diff := AtomSetImpl.diff.
Notation mem := AtomSetImpl.mem.

Notation union_1 := AtomSetImpl.union_1.
Notation union_2 := AtomSetImpl.union_2.
Notation union_3 := AtomSetImpl.union_3.
Notation inter_1 := AtomSetImpl.inter_1.
Notation inter_2 := AtomSetImpl.inter_2.
Notation inter_3 := AtomSetImpl.inter_3.
Notation singleton_1 := AtomSetImpl.singleton_1.
Notation add_2 := AtomSetImpl.add_2.
Notation remove_1 := AtomSetImpl.remove_1.
Notation remove_3 := AtomSetImpl.remove_3.
Notation choose := AtomSetImpl.choose.
Notation choose_1 := AtomSetImpl.choose_1.
Notation choose_2 := AtomSetImpl.choose_2.
Notation cardinal := AtomSetImpl.cardinal.
Notation Empty := AtomSetImpl.Empty.
Notation cardinal_Empty := AtomSetProperties.cardinal_Empty.
Notation subset_cardinal_lt := AtomSetProperties.subset_cardinal_lt.
Notation empty_union_2 := AtomSetProperties.empty_union_2.

Notation "X ∪ Y" := (AtomSetImpl.union X Y)
  (at level 65, right associativity) : set_scope.

Notation "X ∩ Y" := (AtomSetImpl.inter X Y)
  (at level 63, right associativity) : set_scope.

Notation "X ∖ Y" := (AtomSetImpl.diff X Y)
  (at level 61, left associativity) : set_scope.

Notation "x ∉ L" := (x `notin` L) (at level 70, no associativity).

Notation "⌈ e ⌉" := (exp_freeze e) (at level 0, e at level 0) : type_scope.
