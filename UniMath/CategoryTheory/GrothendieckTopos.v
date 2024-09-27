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
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.slicecat.
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

  Definition collection_of_sieves : UU := ∏ (c : C), hsubtype (sieve c).

  Definition isGrothendieckTopology_maximal_sieve (COS : collection_of_sieves) : UU :=
    ∏ (c : C),
      COS c (Subobjectscategory_ob (identity (yoneda C c)) (identity_isMonic _)).

  Definition isGrothendieckTopology_stability (COS : collection_of_sieves) : UU :=
    ∏ (c c' : C) (h : c' --> c) (s : sieve c),
      COS c s →
      COS c' (PullbackSubobject Pullbacks_PreShv s (# (yoneda C) h)).

  Definition isGrothendieckTopology_transitivity (COS : collection_of_sieves) : UU :=
    ∏ (c : C) (s : sieve c),
      (∏ (c' : C) (h : c' --> c),
        COS c' (PullbackSubobject Pullbacks_PreShv s (# (yoneda C) h)))
        -> COS c s.

  Definition isGrothendieckTopology (COS : collection_of_sieves) : UU :=
    (isGrothendieckTopology_maximal_sieve COS)
      × (isGrothendieckTopology_stability COS)
      × (isGrothendieckTopology_transitivity COS).

  Lemma isaprop_isGrothendieckTopology
    (COS : collection_of_sieves)
    : isaprop (isGrothendieckTopology COS).
  Proof.
    repeat apply isapropdirprod;
      repeat (apply impred_isaprop; intro);
      apply propproperty.
  Qed.

  Definition GrothendieckTopology : UU :=
    ∑ COS : collection_of_sieves, isGrothendieckTopology COS.

  (** Accessor functions *)
  Definition GrothendieckTopology_COS (GT : GrothendieckTopology) : collection_of_sieves := pr1 GT.

  Definition GrothendieckTopology_isGrothendieckTopology (GT : GrothendieckTopology) :
    isGrothendieckTopology (GrothendieckTopology_COS GT) := pr2 GT.


  (** ** Sheaves *)

  (** This is a formalization of the definition on page 122 *)
  Definition isSheaf (P : PreShv C) (GT : GrothendieckTopology) : UU :=
    ∏ (c : C)
      (S : sieve c)
      (isCOS : GrothendieckTopology_COS GT c S)
      (τ : sieve_functor S ⟹ (P : _ ⟶ _)),
    ∃! (η : yoneda_objects _ c ⟹ (P : _ ⟶ _)),
      nat_trans_comp _ _ _ (sieve_nat_trans S) η = τ.

  Lemma isaprop_isSheaf (GT : GrothendieckTopology) (P : PreShv C) : isaprop(isSheaf P GT).
  Proof.
    apply impred_isaprop; intros t.
    apply impred_isaprop; intros S.
    apply impred_isaprop; intros isCOS.
    apply impred_isaprop; intros τ.
    apply isapropiscontr.
  Qed.

  (** The category of sheaves is the full subcategory of presheaves consisting of the presheaves
      which satisfy the isSheaf proposition. *)
  Definition hsubtype_obs_isSheaf (GT : GrothendieckTopology) :
    hsubtype (PreShv C) :=
    (λ P, make_hProp _ (isaprop_isSheaf GT P)).

  Definition categoryOfSheaves (GT : GrothendieckTopology) :
    sub_precategories (PreShv C) :=
    full_sub_precategory (hsubtype_obs_isSheaf GT).

End def_grothendiecktopology.


(** * Definition of Grothendieck topos
    Grothendieck topos is a precategory which is equivalent to the category of sheaves on some
    Grothendieck topology. *)
Section def_grothendiecktopos.

  Variable C : category.

  (** Here (pr1 D) is the precategory which is equivalent to the precategory of sheaves on the
      Grothendieck topology (pr2 D). *)
  Definition GrothendieckTopos : UU :=
    ∑ D' : (∑ D : category × (GrothendieckTopology C),
                  functor (pr1 D) (categoryOfSheaves C (pr2 D))),
           (adj_equivalence_of_cats (pr2 D')).

  (** Accessor functions *)
  Definition GrothendieckTopos_category (GT : GrothendieckTopos) : category :=
    pr1 (pr1 (pr1 GT)).
  Coercion GrothendieckTopos_category : GrothendieckTopos >-> category.

  Definition GrothendieckTopos_GrothendieckTopology (GT : GrothendieckTopos) :
    GrothendieckTopology C := pr2 (pr1 (pr1 GT)).

  Definition GrothendieckTopos_functor (GT : GrothendieckTopos) :
    functor (GrothendieckTopos_category GT)
            (categoryOfSheaves C (GrothendieckTopos_GrothendieckTopology GT)) :=
    pr2 (pr1 GT).

  Definition GrothendieckTopos_equivalence (GT : GrothendieckTopos) :
    adj_equivalence_of_cats (GrothendieckTopos_functor GT) := pr2 GT.

End def_grothendiecktopos.
