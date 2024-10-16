Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.GrothendieckToposes.GrothendieckTopologies.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sheaves.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Examples.EmptySieve.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.yoneda.

Local Open Scope cat.

Section DiscreteTopology.

  Context (C : category).

  Definition discrete_topology_selection
    (c : C)
    : hsubtype (Sieves.sieve c)
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

Section Sheaves.

  Context {C : category}.
  Context (F : PreShv C).
  Context (H : is_sheaf (discrete_topology C) F).

  Section Pointwise.

    Context (X : C).

    Let H' := H X
      (make_carrier (discrete_topology C X) (EmptySieve.empty_sieve X) tt)
      (InitialArrow Initial_PreShv _).

    Let FX := (F : _ ⟶ _) X : hSet.

    Definition discrete_sheaf_value
      : FX
      := yoneda_weq C X F (pr11 H').

    Lemma discrete_sheaf_value_unique
      (x : FX)
      : x = discrete_sheaf_value.
    Proof.
      pose (E := pr2 H' (invmap (yoneda_weq C X F) x ,, InitialArrowUnique Initial_PreShv _ _)).
      refine (!eqtohomot (functor_id F X) x @ _).
      exact (eqtohomot (nat_trans_eq_weq (homset_property _) _ _ (base_paths _ _ E) X) (identity X)).
    Qed.

    Definition discrete_sheaf_contractible
      : iscontr FX
      := make_iscontr discrete_sheaf_value discrete_sheaf_value_unique.

    Lemma discrete_sheaf_morphism_irrelevance
      {Y : HSET}
      (f g : HSET⟦Y, FX⟧)
      : f = g.
    Proof.
      apply funextfun.
      intro x.
      apply proofirrelevancecontr.
      apply discrete_sheaf_contractible.
    Qed.

  End Pointwise.

  Definition discrete_sheaf_terminal
    : isTerminal (PreShv C) F.
  Proof.
    intros G.
    use make_iscontr.
    - use make_nat_trans.
      + intros X g.
        exact (iscontrpr1 (discrete_sheaf_contractible X)).
      + intros X Y f.
        apply discrete_sheaf_morphism_irrelevance.
    - intro f.
      apply nat_trans_eq_alt.
      intros X.
      apply discrete_sheaf_morphism_irrelevance.
  Defined.

End Sheaves.
