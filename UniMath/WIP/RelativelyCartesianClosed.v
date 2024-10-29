Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.WIP.MorphismSelections.
Require Import UniMath.WIP.DisplayMaps.
Require Import UniMath.WIP.ComprehensionCategory.

Section DisplayMaps.

  Context {C : category}.
  Context {D : display_maps C}.

  Definition is_relatively_cartesian_closed
    : UU
    := ∏ X Y (f : selected_morphism D X Y),
      is_left_adjoint (fiber_functor_from_cleaving _ (restricted_slice_cleaving (display_maps_pullback_map D)) f).

End DisplayMaps.

Arguments is_relatively_cartesian_closed {C}.
