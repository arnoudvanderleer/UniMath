Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedFibration.

Local Open Scope cat.

Definition fiber_hset_twosided_disp_cat
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD : discrete_twosided_disp_cat D)
           (x : C₁)
           (y : C₂)
  : hSet.
Proof.
  use make_hSet.
  - exact (D x y).
  - exact (isaset_discrete_twosided_cat_ob HD x y).
Defined.

Definition fiber_fun_hset_twosided_disp_cat
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD : discrete_twosided_disp_cat D)
           (HD' : twosided_fibration D)
           {x₁ x₂ : C₁}
           (f : x₁ --> x₂)
           {y₁ y₂ : C₂}
           (g : y₂ --> y₁)
  : fiber_hset_twosided_disp_cat HD x₂ y₂
    →
    fiber_hset_twosided_disp_cat HD x₁ y₁
  := λ xy,
     twosided_opcleaving_ob
       _
       (pr1 HD')
       (twosided_cleaving_ob
          _
          (pr12 HD')
          xy
          f)
       g.

Definition fiber_fun_hset_twosided_disp_cat_id
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD : discrete_twosided_disp_cat D)
           (HD' : twosided_fibration D)
           (x : C₁)
           (y : C₂)
  : fiber_fun_hset_twosided_disp_cat HD HD' (identity x) (identity y)
    =
    idfun _.
Proof.
  use funextsec.
  intro xy.
  cbn.
Admitted.

Definition fiber_fun_hset_twosided_disp_cat_comp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD : discrete_twosided_disp_cat D)
           (HD' : twosided_fibration D)
           {x₁ x₂ x₃ : C₁}
           (f₁ : x₃ --> x₂)
           (f₂ : x₂ --> x₁)
           {y₁ y₂ y₃ : C₂}
           (g₁ : y₁ --> y₂)
           (g₂ : y₂ --> y₃)
  : (λ xy,
     fiber_fun_hset_twosided_disp_cat
       HD HD'
       f₁ g₂
       (fiber_fun_hset_twosided_disp_cat
          HD HD'
          f₂ g₁
          xy))
    =
    fiber_fun_hset_twosided_disp_cat HD HD' (f₁ · f₂) (g₁ · g₂).
Proof.
Admitted.

Definition discrete_twosided_fibration_to_profunctor
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD : discrete_twosided_disp_cat D)
           (HD' : twosided_fibration D)
  : profunctor C₂ C₁.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (λ x, fiber_hset_twosided_disp_cat HD (pr1 x) (pr2 x)).
    + exact (λ x y f, fiber_fun_hset_twosided_disp_cat HD HD' (pr1 f) (pr2 f)).
  - admit.
Admitted.

Section FiberCat.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂)
          (x : C₁)
          (y : C₂).

  Definition fiber_twosided_disp_precat_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (D x y).
    - exact (λ xy₁ xy₂, xy₁ -->[ identity x ][ identity y ] xy₂).
  Defined.

  Definition fiber_twosided_disp_precat_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact fiber_twosided_disp_precat_ob_mor.
    - exact (λ xy, id_two_disp xy).
    - exact (λ _ _ _ f g,
             transportf
               (λ z, _ -->[ z ][ _ ] _)
               (id_left _)
               (transportf
                  (λ z, _ -->[ _ ][ z ] _)
                  (id_left _)
                  (f ;;2 g))).
  Defined.

  Definition fiber_twosided_disp_is_precategory
    : is_precategory fiber_twosided_disp_precat_data.
  Proof.
    use is_precategory_one_assoc_to_two.
    repeat split.
    - intros xy₁ xy₂ f ; cbn.
      admit.
    - intros xy₁ xy₂ f ; cbn.
      admit.
    - intros xy₁ xy₂ xy₃ xy₄ f g h ; cbn.
      admit.
  Admitted.

  Definition fiber_twosided_disp_precat
    : precategory.
  Proof.
    use make_precategory.
    - exact fiber_twosided_disp_precat_data.
    - exact fiber_twosided_disp_is_precategory.
  Defined.

  Definition fiber_twosided_disp_cat
    : category.
  Proof.
    use make_category.
    - exact fiber_twosided_disp_precat.
    - intros xy₁ xy₂ ; cbn.
      apply isaset_disp_mor.
  Defined.
End FiberCat.
