Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.

Require Import UniMath.WIP.MorphismSelections.
Require Import UniMath.WIP.ComprehensionCategory.
Require Import UniMath.WIP.DisplayMaps.
Require Import UniMath.WIP.RelativelyCartesianClosed.

Section DependentProducts.

  Context {C : category}.
  Context {D : display_maps C}.
  Context (HD : is_relatively_cartesian_closed D).

  Definition restricted_morphisms_dependent_product
    {X Y : C}
    (f : selected_morphism D X Y)
    : dependent_product (restricted_slice_cleaving  (display_maps_pullback D) (display_maps_pullback_map D)) f
    := HD X Y f.

End DependentProducts.
