(**

  The Category of Double Magmas and Related Categories

  This file defines the category of 'double magmas': sets with two binary operations.
  Using the displayed categories from magma.v, we also define the categories of
  - Rigs: the displayed product of the category of abelian monoids ('addition') and the category of
    monoids ('multiplication'), restricting to the subcategory where multiplication distributes over
    addition, and the additive identity annihilates anything under multiplication.
  - Commutative rigs: the same as rigs, but using abelian monoids twice.
  - Rings: the displayed product, but abelian groups instead of abelian monoids, and taking the
    subcategory where multiplication distributes over addition (for rings, this already implies
    annihilation).
  - Commutative rings: the same as rings, but using abelian monoids instead of monoids.

  Contents
  1. The category of double magmas [double_magma_category] [is_univalent_double_magma_category]
  2. The category of rigs [rig_category]
  3. The category of commutative rigs [commutative_rig_category]
  4. The category of rings [ring_category]
  5. The category of commutative rigs [commutative_ring_category]

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.Magma.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.Product.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

(** * 1. The category of double magmas *)

Definition double_magma_disp_cat
  : disp_cat HSET
  := dirprod_disp_cat magma_disp_cat magma_disp_cat.

Definition double_magma_category
  : category
  := total_category double_magma_disp_cat.

Definition is_univalent_double_magma_disp_cat
  : is_univalent_disp double_magma_disp_cat
  := dirprod_disp_cat_is_univalent _ _ is_univalent_magma_disp_cat is_univalent_magma_disp_cat.

(** * 2. The category of rigs *)

Definition pre_rig_disp_cat
  : disp_cat HSET.
Proof.
  use dirprod_disp_cat.
  - exact (sigma_disp_cat abelian_monoid_disp_cat).
  - exact (sigma_disp_cat monoid_disp_cat).
Defined.

Definition rig_disp_cat
  : disp_cat _
  := disp_full_sub
    (total_category pre_rig_disp_cat)
    (λ R, annihilates_ax (pr112 R) (pr122 R) (pr121 (pr212 R))
      × isdistr (pr112 R) (pr122 R)).

Definition rig_category
  : category
  := total_category (sigma_disp_cat rig_disp_cat).

(** * 3. The category of commutative rigs *)

Definition commutative_rig_disp_cat
  : disp_cat rig_category
  := disp_full_sub rig_category (λ (R : rig_category), iscomm (pr1 (pr212 R))).

Definition commutative_rig_category
  : category
  := total_category (sigma_disp_cat commutative_rig_disp_cat).

(** * 4. The category of rings *)

Definition pre_ring_disp_cat
  : disp_cat HSET.
Proof.
  use dirprod_disp_cat.
  - exact (sigma_disp_cat abelian_group_disp_cat).
  - exact (sigma_disp_cat monoid_disp_cat).
Defined.

Definition ring_disp_cat
  : disp_cat _
  := disp_full_sub (total_category pre_ring_disp_cat) (λ R, isdistr (pr112 R) (pr122 R)).

Definition ring_category
  : category
  := total_category (sigma_disp_cat ring_disp_cat).

(** * 5. The category of commutative rings *)

Definition pre_commutative_ring_disp_cat
  : disp_cat HSET.
Proof.
  use dirprod_disp_cat.
  - exact (sigma_disp_cat abelian_group_disp_cat).
  - exact (sigma_disp_cat abelian_monoid_disp_cat).
Defined.

Definition commutative_ring_disp_cat
  : disp_cat _
  := disp_full_sub (total_category pre_ring_disp_cat) (λ R, isdistr (pr112 R) (pr122 R)).

Definition commutative_ring_category
  : category
  := total_category (sigma_disp_cat commutative_ring_disp_cat).
