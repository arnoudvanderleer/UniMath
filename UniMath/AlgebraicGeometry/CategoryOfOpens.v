(**************************************************************************************************

  The category of open subsets

  This file defines the category of open subsets of a topological space, in which the morphisms are
  inclusions. A continuous function between two topological spaces gives a functor in the other
  direction between their categories of opens. These together give an indexed category structure on
  top_cat^op.
  We can also give (opens_cat T) a Grothendieck topology, where a collection (V_i)_i is a covering
  for an object (an open subset) U, if U is contained inside the union of the V_i.

  Contents
  1. The category of opens [opens_cat_ob]
  1.1. It is univalent [is_univalent_opens_cat_ob]
  2. The functor construction [opens_cat_mor]
  3. The indexed category structure [opens_cat]
  4. The Grothendieck topology [opens_cat_Grothendieck_topology]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.PreorderCategory.Core.
Require Import UniMath.CategoryTheory.Categories.PreorderCategory.Sieves.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.GrothendieckToposes.GrothendieckTopologies.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sieves.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.OrderTheory.Preorders.
Require Import UniMath.Topology.CategoryTop.
Require Import UniMath.Topology.Topology.

Local Open Scope cat.
Local Open Scope subtype.

(** * 1. The category of opens *)

Section Ob.

  Context (X : TopologicalSpace).

  Definition open_po : po (@Open X) :=
    make_po _ (isporesrel _ _ (subtype_containment_ispreorder X)).

  Definition opens_cat_ob : category := po_category open_po.

(** ** 1.1. It is univalent *)

  Lemma is_univalent_opens_cat_ob
    : is_univalent opens_cat_ob.
  Proof.
    refine (pr2 (po_category_is_univalent_iff_is_antisymm _ _) _).
    - apply isofhlevel_hsubtype.
      apply isasethsubtype.
    - apply isantisymmresrel.
      apply subtype_containment_isantisymm.
  Defined.

End Ob.

(** * 2. The functor construction *)

Definition opens_cat_mor
  {T T' : TopologicalSpace}
  (F : continuous_function T T')
  : opens_cat_ob T' ⟶ opens_cat_ob T.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (continuous_open_preimage F).
    + intros U V HUV t.
      apply (HUV _).
  - abstract easy.
Defined.

(** * 3. The indexed category structure *)

Definition opens_cat
  : indexed_cat top_cat^op.
Proof.
  use make_indexed_cat.
  - use make_indexed_cat_data.
    + intro T.
      exact (opens_cat_ob T ,, is_univalent_opens_cat_ob T).
    + intros T T'.
      exact opens_cat_mor.
    + intro T.
      exact (nat_trans_id (functor_identity _)).
    + intros T T' T'' F F'.
      exact (nat_trans_id (opens_cat_mor (F · F'))).
  - split.
    + intros T U.
      exists (nat_trans_id (functor_identity _) U).
      abstract easy.
    + intros T T' T'' F F' U.
      exists (nat_trans_id (opens_cat_mor (F · F')) U).
      abstract easy.
  - abstract (
      repeat split;
      intros;
      apply propproperty
    ).
Defined.

(** * 4. The Grothendieck topology *)

Section GrothendieckTopology.

  Context (T : TopologicalSpace).

  Definition opens_cat_Grothendieck_topology_sieve_selection
    : sieve_selection (opens_cat T)
    := λ (U : Open) f, U ⊆ ⋃ (λ (V : carrier_subtype_weq_contained_subtype _ (po_sieve_weq_subtype f)), pr1carrier _ V).

  Definition make_opens_cat_selected_sieve
    {U : Open}
    {x : T}
    {f : sieve (U : opens_cat T)}
    (V : Open)
    (HVU : V ⊆ U)
    (HfV : (sieve_functor f V : hSet))
    (HVx : V x)
    : ∑ (i : carrier_subtype_weq_contained_subtype _ (po_sieve_weq_subtype f)), pr1carrier _ i x
    := (V ,, HVU ,, HfV) ,, HVx.

  Lemma opens_cat_Grothendieck_topology_maximal_sieve
    : Grothendieck_topology_maximal_sieve_ax opens_cat_Grothendieck_topology_sieve_selection.
  Proof.
    intros U x HUx.
    apply hinhpr.
    use make_opens_cat_selected_sieve.
    - exact U.
    - apply subtype_containment_isrefl.
    - apply subtype_containment_isrefl.
    - exact HUx.
  Qed.

  Lemma opens_cat_Grothendieck_topology_stability
    : Grothendieck_topology_stability_ax opens_cat_Grothendieck_topology_sieve_selection.
  Proof.
    intros U V HVU f HUf x HVx.
    specialize (HUf x (HVU x HVx)).
    revert HUf.
    apply hinhfun.
    intro HUf.
    use make_opens_cat_selected_sieve.
    - exact (pr1carrier _ (pr1carrier _ HUf) ∩ V)%open.
    - apply intersection_contained_r.
    - use tpair.
      + exists (intersection_contained_r _ _).
        refine (# (sieve_functor f) _ (pr22 (pr1carrier _ HUf))).
        exact (intersection_contained_l _ _).
      + apply propproperty.
    - split.
      + exact (pr2 HUf).
      + exact HVx.
  Qed.

  Arguments pr1carrier {X} {A}.

  Lemma opens_cat_Grothendieck_topology_transitivity
    : Grothendieck_topology_transitivity_ax opens_cat_Grothendieck_topology_sieve_selection.
  Proof.
    intros U f HV x HUx.
    specialize (HV U (λ x Hx, Hx) x HUx).
    revert HV.
    apply hinhfun.
    intro HV.
    use make_opens_cat_selected_sieve.
    - exact (pr1carrier (pr1carrier HV)).
    - exact (pr1carrier (pr2 (pr1carrier HV))).
    - exact (pr21 (pr22 (pr1carrier HV))).
    - exact (pr2 HV).
  Qed.

  Definition opens_cat_is_Grothendieck_topology
    : is_Grothendieck_topology opens_cat_Grothendieck_topology_sieve_selection
    := make_is_Grothendieck_topology
      opens_cat_Grothendieck_topology_maximal_sieve
      opens_cat_Grothendieck_topology_stability
      opens_cat_Grothendieck_topology_transitivity.

  Definition opens_cat_Grothendieck_topology
    : Grothendieck_topology (opens_cat T)
    := make_Grothendieck_topology
      opens_cat_Grothendieck_topology_sieve_selection
      opens_cat_is_Grothendieck_topology.

End GrothendieckTopology.
