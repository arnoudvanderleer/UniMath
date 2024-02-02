(**************************************************************************************************

  A skeleton of finite sets

  Defines the full subcategory of SET, consisting of the sets {0, ..., n-1} and the functions
  between them.

  Contents
  1. The category [finite_set_skeleton_category]
  2. The embedding into HSET [HSET_embedding]
  3. An embedding into FinSet [FinSet_embedding]
  3.1. Lifting functors along this embedding [lift_functor_along_FinSet_embedding]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.FinSet.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.PrecompEquivalence.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Local Open Scope cat.

(** * 1. The category *)

Definition finite_set_skeleton_precat : precategory.
Proof.
  use make_precategory.
  - use make_precategory_data.
    + use make_precategory_ob_mor.
      * exact nat.
      * exact (λ m n, stn m → stn n).
    + intro.
      exact (idfun _).
    + do 3 intro.
      exact funcomp.
  - do 3 split.
Defined.

Definition finite_set_skeleton_category : category.
Proof.
  use make_category.
  - exact finite_set_skeleton_precat.
  - do 2 intro.
    apply funspace_isaset.
    apply isasetstn.
Defined.

(** * 2. The embedding into HSET *)

Definition HSET_embedding
  : finite_set_skeleton_category ⟶ HSET.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact stnset.
    + exact (λ _ _, idfun _).
  - abstract easy.
Defined.

Definition fully_faithful_HSET_embedding
  : fully_faithful HSET_embedding.
Proof.
  intros m n.
  apply idisweq.
Defined.

(** * 3. An embedding into FinSet *)

Definition FinSet_embedding
  : finite_set_skeleton_category ⟶ FinSet.
Proof.
  use make_functor.
  - use make_functor_data.
    + intro n.
      exact (stnset n ,, isfinitestn n).
    + intros m n f.
      exact (f ,, tt).
  - abstract easy.
Defined.

Lemma fully_faithful_FinSet_embedding
  : fully_faithful FinSet_embedding.
Proof.
  intros x x'.
  use isweq_iso.
  - exact pr1.
  - easy.
  - intro f.
    apply (maponpaths (tpair _ _)).
    exact (!pr2 iscontrunit _).
Qed.

Lemma essentially_surjective_FinSet_embedding
  : essentially_surjective FinSet_embedding.
Proof.
  intro x.
  induction x as [x Hx].
  revert Hx.
  refine (λ x, hinhfun _ x).
  intro Hx.
  exists (pr1 Hx).
  apply iso_in_sub_from_iso.
  apply hset_equiv_z_iso.
  exact (pr2 Hx).
Qed.

(** ** 3.1. Lifting functors along this embedding *)

Definition lift_functor_along_FinSet_embedding
  (C : univalent_category)
  (F : finite_set_skeleton_category ⟶ C)
  : FinSet ⟶ C
  := lift_functor_along _ _
    essentially_surjective_FinSet_embedding
    fully_faithful_FinSet_embedding
    F.
