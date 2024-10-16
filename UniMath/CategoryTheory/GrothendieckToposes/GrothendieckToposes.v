(** * Grothendick toposes *)
(** * Definition of Grothendieck topos
    Grothendieck topos is a precategory which is equivalent to the category of sheaves on some
    Grothendieck topology. *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Subcategory.Core.

Require Import UniMath.CategoryTheory.GrothendieckToposes.GrothendieckTopologies.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sheaves.

Local Open Scope cat.

Section def_grothendiecktopos.

  Variable C : category.

  (** Here (pr1 D) is the precategory which is equivalent to the precategory of sheaves on the
      Grothendieck topology (pr2 D). *)
  Definition Grothendieck_topos : UU :=
    ∑ D' : (∑ D : category × (Grothendieck_topology C),
                  functor (pr1 D) (sheaf_cat C (pr2 D))),
           (adj_equivalence_of_cats (pr2 D')).

  (** Accessor functions *)
  Definition Grothendieck_topos_category (GT : Grothendieck_topos) : category :=
    pr1 (pr1 (pr1 GT)).
  Coercion Grothendieck_topos_category : Grothendieck_topos >-> category.

  Definition Grothendieck_topos_Grothendieck_topology (GT : Grothendieck_topos) :
    Grothendieck_topology C := pr2 (pr1 (pr1 GT)).

  Definition Grothendieck_topos_functor (GT : Grothendieck_topos) :
    functor (Grothendieck_topos_category GT)
            (sheaf_cat C (Grothendieck_topos_Grothendieck_topology GT)) :=
    pr2 (pr1 GT).

  Definition Grothendieck_topos_equivalence (GT : Grothendieck_topos) :
    adj_equivalence_of_cats (Grothendieck_topos_functor GT) := pr2 GT.

End def_grothendiecktopos.
