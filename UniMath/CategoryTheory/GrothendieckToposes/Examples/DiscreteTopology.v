Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sieves.
Require Import UniMath.CategoryTheory.GrothendieckToposes.GrothendieckTopologies.

Section DiscreteTopology.

  Context (C : category).

  Definition discrete_topology_selection
    (c : C)
    : hsubtype (sieve c)
    := λ _, htrue.

  Lemma discrete_topology_is_topology
    : is_Grothendieck_topology discrete_topology_selection.
  Proof.
    easy.
  Qed.

  Definition discrete_topology
    : Grothendieck_topology C
    := make_Grothendieck_topology
      discrete_topology_selection
      discrete_topology_is_topology.

End DiscreteTopology.
