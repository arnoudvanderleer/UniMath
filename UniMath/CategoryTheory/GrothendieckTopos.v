(** * Grothendick toposes *)
(** ** Contents
- Definition of Grothendieck topology
 - Grothendieck topologies
 - Precategory of sheaves
- Grothendieck toposes
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.yoneda.

Local Open Scope cat.

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
Section def_grothendiecktopology.

  Variable C : category.

  (** A sieve on c is a subobject of the yoneda functor. *)
  Definition sieve (c : C) : UU :=
    Subobjectscategory (yoneda C c).

  Definition sieve_functor {c : C} (S : sieve c)
    : C^op ⟶ HSET
    := Subobject_dom S.

  Definition sieve_nat_trans {c : C} (S : sieve c) :
    sieve_functor S ⟹ yoneda_objects C c
    := Subobject_mor S.

  (** ** Grothendieck topology *)

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

  (** ** Sheaves *)

  (** This is a formalization of the definition on page 122 *)
  Definition is_sheaf (P : PreShv C) (GT : Grothendieck_topology) : UU :=
    ∏ (c : C)
      (S : sieve c)
      (is_selection : Grothendieck_topology_sieve_selection GT c S)
      (τ : sieve_functor S ⟹ (P : _ ⟶ _)),
    ∃! (η : yoneda_objects _ c ⟹ (P : _ ⟶ _)),
      nat_trans_comp _ _ _ (sieve_nat_trans S) η = τ.

  Lemma isaprop_is_sheaf (GT : Grothendieck_topology) (P : PreShv C) : isaprop(is_sheaf P GT).
  Proof.
    apply impred_isaprop; intros t.
    apply impred_isaprop; intros S.
    apply impred_isaprop; intros is_selection.
    apply impred_isaprop; intros τ.
    apply isapropiscontr.
  Qed.

  (** The category of sheaves is the full subcategory of presheaves consisting of the presheaves
      which satisfy the is_sheaf proposition. *)
  Definition hsubtype_obs_is_sheaf (GT : Grothendieck_topology) :
    hsubtype (PreShv C) :=
    (λ P, make_hProp _ (isaprop_is_sheaf GT P)).

  Definition sheaf_cat (GT : Grothendieck_topology) :
    sub_precategories (PreShv C) :=
    full_sub_precategory (hsubtype_obs_is_sheaf GT).

End def_grothendiecktopology.


(** * Definition of Grothendieck topos
    Grothendieck topos is a precategory which is equivalent to the category of sheaves on some
    Grothendieck topology. *)
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
