Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Require Import UniMath.WIP.MorphismSelections.

Local Open Scope cat.

Section DisplayMaps.

  Context {C : category}.

  Section Axioms.

    Context (D : morphism_selection C).

    Definition selected_morphism_terminal_ax
      : UU
      := Terminal C.

    Definition selected_morphism_terminal_map_ax
      (T : Terminal C)
      : UU
      := ∏ (X : C),
        is_selected D (TerminalArrow T X).

    Definition selected_morphism_composed_map_ax
      : UU
      := ∏
        (X Y Z : C)
        (f : selected_morphism D X Y)
        (g : selected_morphism D Y Z),
        is_selected D (f · g).

    Definition selected_morphism_pullback_ax
      : UU
      := ∏
        (X Y Z : C)
        (f : C⟦Y, X⟧)
        (g : selected_morphism D Z X),
        Pullback f g.

    (* Technically, it suffices to have this only for the selected pullback. *)
    (* However, in this way it satisfies the equivalence principle. *)
    Definition selected_morphism_pullback_map_ax
      : UU
      := ∏
        (X Y Z : C)
        (f : C⟦Y, X⟧)
        (g : selected_morphism D Z X)
        (P : Pullback f g),
        is_selected D (PullbackPr1 P).

    Definition is_display_map_class
      : UU
      := (∑ (T : selected_morphism_terminal_ax),
          selected_morphism_terminal_map_ax T) ×
        selected_morphism_composed_map_ax ×
        selected_morphism_pullback_ax ×
        selected_morphism_pullback_map_ax.

    Definition make_is_display_map_class
      (T : selected_morphism_terminal_ax)
      (HT : selected_morphism_terminal_map_ax T)
      (HC : selected_morphism_composed_map_ax)
      (P : selected_morphism_pullback_ax)
      (HP : selected_morphism_pullback_map_ax)
      : is_display_map_class
      := (T ,, HT) ,, HC ,, (P ,, HP).

  End Axioms.

  Definition display_maps
    : UU
    := ∑ (D : morphism_selection C), is_display_map_class D.

  Definition make_display_maps
    (D : morphism_selection C)
    (H : is_display_map_class D)
    : display_maps
    := D ,, H.

  Coercion display_maps_to_morphism_selection
    (D : display_maps)
    : morphism_selection C
    := pr1 D.

  Section Accessors.

    Context (D : display_maps).

    Definition display_maps_terminal
      : selected_morphism_terminal_ax
      := pr112 D.

    Definition display_maps_terminal_map
      : selected_morphism_terminal_map_ax D display_maps_terminal
      := pr212 D.

    Definition display_maps_composed_map
      : selected_morphism_composed_map_ax D
      := pr122 D.

    Definition display_maps_pullback
      : selected_morphism_pullback_ax D
      := pr1 (pr222 D).

    Definition display_maps_pullback_map
      : selected_morphism_pullback_map_ax D
      := pr2 (pr222 D).

  End Accessors.

End DisplayMaps.

Arguments display_maps : clear implicits.
