(** * Definiton of Grothendieck topology
    The following definition is a formalization of the definition in Sheaves in Geometry and Logic,
    Saunders Mac Lane and Ieke Moerdijk, pages 109 and 110.

    Grothendieck topology is a collection J(c) of subobjects of the Yoneda functor, for every object
    of C, such that:
    - The Yoneda functor y(c) is in J(c).
    - Pullback of a subobject in J(c) along any morphism h : c' --> c is in J(c')
    - If S is a subobject of y(c) such that for all objects c' and all morphisms
      h : c' --> c in C the pullback of S along h is in J(c'), then S is in J(c).
  *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.yoneda.

Require Import UniMath.CategoryTheory.GrothendieckTopos.Sieves.

Local Open Scope cat.

Section GrothendieckTopology.

  Context {C : category}.

  Definition sieve_selection : UU := ∏ (c : C), hsubtype (sieve c).

  Section IsGrothendieckTopology.

    Context (selection : sieve_selection).

    Definition is_Grothendieck_topology_maximal_sieve : UU :=
      ∏ (c : C),
        selection c (Subobjectscategory_ob (identity (yoneda C c)) (identity_isMonic _)).

    Definition is_Grothendieck_topology_stability : UU :=
      ∏ (c c' : C) (h : c' --> c) (s : sieve c),
        selection c s →
        selection c' (PullbackSubobject Pullbacks_PreShv s (# (yoneda C) h)).

    Definition is_Grothendieck_topology_transitivity : UU :=
      ∏ (c : C) (s : sieve c),
        (∏ (c' : C) (h : c' --> c),
          selection c' (PullbackSubobject Pullbacks_PreShv s (# (yoneda C) h)))
        → selection c s.

    Definition is_Grothendieck_topology : UU :=
      is_Grothendieck_topology_maximal_sieve
      × is_Grothendieck_topology_stability
      × is_Grothendieck_topology_transitivity.

    Lemma isaprop_is_Grothendieck_topology
      : isaprop is_Grothendieck_topology.
    Proof.
      repeat apply isapropdirprod;
        repeat (apply impred_isaprop; intro);
        apply propproperty.
    Qed.

  End IsGrothendieckTopology.

  Definition Grothendieck_topology : UU :=
    ∑ selection, is_Grothendieck_topology selection.

  (** Accessor functions *)
  Definition Grothendieck_topology_sieve_selection (GT : Grothendieck_topology) : sieve_selection := pr1 GT.

  Definition Grothendieck_topology_is_Grothendieck_topology (GT : Grothendieck_topology) :
    is_Grothendieck_topology (Grothendieck_topology_sieve_selection GT) := pr2 GT.

End GrothendieckTopology.

Arguments Grothendieck_topology : clear implicits.
