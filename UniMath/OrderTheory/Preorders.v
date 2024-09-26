Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Section DownTypes.

  Definition down_type
    {X : UU}
    (P : po X)
    (x : X)
    : UU
    := ∑ y, P y x.

  Definition down_type_element
    {X : UU}
    {P : po X}
    {x : X}
    (y : down_type P x)
    : X
    := pr1 y.

  Definition down_type_is_down
    {X : UU}
    {P : po X}
    {x : X}
    (y : down_type P x)
    : P (down_type_element y) x
    := pr2 y.

End DownTypes.

Section DownwardClosedDownSubtype.

  Context {X : UU}.
  Context (P : po X).
  Context (x : X).

  Definition is_downward_closed
    (f : hsubtype (down_type P x))
    : UU
    := ∏ (y : f)
      (z : X)
      (Hzy : P z (down_type_element (pr1carrier _ y))),
      f (z ,, istrans_po P _ _ _ Hzy (down_type_is_down (pr1carrier _ y))).

  Definition downward_closed_down_subtype
    : UU
    := ∑ f, is_downward_closed f.

  Coercion downward_closed_down_subtype_to_subtype
    (f : downward_closed_down_subtype)
    : hsubtype (down_type P x)
    := pr1 f.

  Definition make_downward_closed_down_subtype
    (f : hsubtype (down_type P x))
    (H : is_downward_closed f)
    : downward_closed_down_subtype
    := f ,, H.

End DownwardClosedDownSubtype.
