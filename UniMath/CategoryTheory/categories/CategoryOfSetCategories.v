(******************************************************************************************

 The category of strict categories

 Strict categories are the categories in which the type of objects forms a set. As such,
 the type of functors between them is a set as well, and this allows us to construct a
 category whose objects are strict categories and whose morphisms are functors.

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.

Local Open Scope cat.

Definition precat_ob_mor_of_setcategory
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact setcategory.
  - exact (λ C₁ C₂, C₁ ⟶ C₂).
Defined.

Definition precat_data_of_setcategory
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact precat_ob_mor_of_setcategory.
  - exact (λ C, functor_identity _).
  - exact (λ C₁ C₂ C₃ F G, F ∙ G).
Defined.

Definition is_precategory_of_setcategory
  : is_precategory precat_data_of_setcategory.
Proof.
  use make_is_precategory_one_assoc.
  - intros C₁ C₂ F.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq ; cbn.
    + intro ; apply idpath.
    + intros x y f ; cbn.
      apply idpath.
  - intros C₁ C₂ F.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq ; cbn.
    + intro ; apply idpath.
    + intros x y f ; cbn.
      apply idpath.
  - intros C₁ C₂ C₃ C₄ F G H.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq ; cbn.
    + intro ; apply idpath.
    + intros x y f ; cbn.
      apply idpath.
Qed.

Definition precat_of_setcategory
  : precategory.
Proof.
  use make_precategory.
  - exact precat_data_of_setcategory.
  - exact is_precategory_of_setcategory.
Defined.

Definition has_homsets_cat_of_setcategory
  : has_homsets precat_of_setcategory.
Proof.
  intros C₁ C₂.
  use functor_isaset.
  - apply homset_property.
  - apply C₂.
Qed.

Definition cat_of_setcategory
  : category.
Proof.
  use make_category.
  - exact precat_of_setcategory.
  - exact has_homsets_cat_of_setcategory.
Defined.

Section IsoToEquivalence.

  Context {A B : setcategory}.
  Context (f : z_iso (C := cat_of_setcategory) A B).

  Let F : A ⟶ B
    := z_iso_mor f.
  Let G : B ⟶ A
    := inv_from_z_iso f.
  Let η : functor_identity A ⟹ F ∙ G
    := z_iso_mor (idtoiso (C := [A, A]) (!z_iso_inv_after_z_iso f)).
  Let ϵ : G ∙ F ⟹ functor_identity B
    := z_iso_mor (idtoiso (C := [B, B]) (z_iso_after_z_iso_inv f)).

  Lemma FG_form_adjunction
    : Core.form_adjunction F G η ϵ.
  Proof.
    split.
    - intro c.
      refine (maponpaths (λ x, # F (z_iso_mor x) · _) (idtoiso_functorcat_compute_pointwise _ _ _ _ _ (!z_iso_inv_after_z_iso f) _) @ _).
      refine (!maponpaths (λ x, z_iso_mor x · _) (maponpaths_idtoiso _ _ _ _ _ _) @ _).
      refine (maponpaths (λ x, _ · z_iso_mor x) (idtoiso_functorcat_compute_pointwise _ _ _ _ _ (z_iso_after_z_iso_inv f) _) @ _).
      refine (!maponpaths z_iso_mor (idtoiso_concat _ _ _ _ _ _) @ _).
      apply setcategory_refl_idtoiso.
    - intro c.
      refine (maponpaths (λ x, _ · #G (z_iso_mor x)) (idtoiso_functorcat_compute_pointwise _ _ _ _ _ (z_iso_after_z_iso_inv f) _) @ _).
      refine (!maponpaths (λ x, _ · z_iso_mor x) (maponpaths_idtoiso _ _ _ _ _ _) @ _).
      refine (maponpaths (λ x, z_iso_mor x · _) (idtoiso_functorcat_compute_pointwise _ _ _ _ _ (!z_iso_inv_after_z_iso f) _) @ _).
      refine (!maponpaths z_iso_mor (idtoiso_concat _ _ _ _ _ _) @ _).
      apply setcategory_refl_idtoiso.
  Qed.

  Lemma FG_forms_equivalence
    : forms_equivalence (F ,, G ,, η ,, ϵ).
  Proof.
    split;
      intro;
      apply (is_functor_z_iso_pointwise_if_z_iso _ _ _ _ _ _ (z_iso_is_z_isomorphism _)).
  Defined.

  Definition z_iso_to_equivalence
    : adj_equivalence_of_cats F
    := make_adj_equivalence_of_cats _ _ _ _
      FG_form_adjunction
      FG_forms_equivalence.

End IsoToEquivalence.
