Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope cat.

Definition morphism_selection
  (C : category)
  : UU
  := ∏ (X Y : C), hsubtype (X --> Y).

Definition morphism_selection_to_function
  (C : category)
  (D : morphism_selection C)
  : ∏ (X Y : C), hsubtype (X --> Y)
  := D.

Coercion morphism_selection_to_function : morphism_selection >-> Funclass.

Definition is_selected
  {C : category}
  (D : morphism_selection C)
  {X Y : C}
  (f : X --> Y)
  : hProp
  := D X Y f.

Section SelectedMorphisms.

  Context {C : category}.

  Definition selected_morphism
    (D : morphism_selection C)
    (X Y : C)
    : UU
    := carrier (λ (f : X --> Y), is_selected D f).

  Definition make_selected_morphism
    {D : morphism_selection C}
    {X Y : C}
    (f : X --> Y)
    (H : is_selected D f)
    : selected_morphism D X Y
    := f ,, H.

  Coercion selected_morphism_map
    {D : morphism_selection C}
    {X Y : C}
    (f : selected_morphism D X Y)
    : X --> Y
    := pr1carrier _ f.

  Definition selected_morphism_is_selected
    {D : morphism_selection C}
    {X Y : C}
    (f : selected_morphism D X Y)
    : is_selected D f
    := pr2 f.

End SelectedMorphisms.
