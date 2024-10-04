Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.yoneda.

Local Open Scope cat.

Section Sieves.

  Context {C : category}.

  (** A sieve on c is a subobject of the yoneda functor. *)
  Definition sieve (c : C) : UU :=
    Subobjectscategory (yoneda C c).


  Definition sieve_functor {c : C} (S : sieve c)
    : C^op ⟶ HSET
    := Subobject_dom S.

  Definition sieve_nat_trans {c : C} (S : sieve c) :
    sieve_functor S ⟹ yoneda_objects C c
    := Subobject_mor S.


  Definition sieve_selected_morphism {c : C} (S : sieve c)
    := ∑ (d : C), (sieve_functor S d : hSet).

  Definition sieve_selected_morphism_domain
    {c : C} {S : sieve c} (f : sieve_selected_morphism S)
    : C
    := pr1 f.

  Coercion sieve_selected_morphism_morphism
    {c : C} (S : sieve c) (f : sieve_selected_morphism S)
    : C⟦sieve_selected_morphism_domain f, c⟧
    := sieve_nat_trans S _ (pr2 f).

  Definition sieve_selected_morphism_compose
    {c : C}
    {S : sieve c}
    (f : sieve_selected_morphism S)
    {d : C}
    (g : C⟦d, sieve_selected_morphism_domain f⟧)
    : sieve_selected_morphism S
    := d ,, # (sieve_functor S) g (pr2 f).

End Sieves.
