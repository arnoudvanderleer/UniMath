Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
(* Require Import UniMath.CategoryTheory.Adjunctions.Core. *)
(* Require Import UniMath.CategoryTheory.Adjunctions.Examples. *)
(* Require Import UniMath.CategoryTheory.DisplayedCats.Core. *)
(* Require Import UniMath.CategoryTheory.DisplayedCats.Fiber. *)
(* Require Import UniMath.CategoryTheory.DisplayedCats.Isos. *)
(* Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses. *)
(* Require Import UniMath.CategoryTheory.Equivalences.Core. *)
(* Require Import UniMath.CategoryTheory.exponentials. *)
(* Require Import UniMath.CategoryTheory.Limits.BinCoproducts. *)
(* Require Import UniMath.CategoryTheory.Limits.BinProducts. *)
(* Require Import UniMath.CategoryTheory.Limits.DisjointBinCoproducts. *)
(* Require Import UniMath.CategoryTheory.Limits.Initial. *)
(* Require Import UniMath.CategoryTheory.Limits.Preservation. *)
(* Require Import UniMath.CategoryTheory.Limits.StrictInitial. *)
(* Require Import UniMath.CategoryTheory.whiskering. *)
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

Section DisplayMaps.

  Context {C : category}.
  Context (D : ∏ (X Y : C), hsubtype (X --> Y)).

  Definition display_map_terminal_ax
    : UU
    := ∑ (T : Terminal C),
        ∏ (X : C),
        D X T (TerminalArrow T X).

  Definition display_map_compose_ax
    : UU
    := ∏
      (X Y Z : C)
      (f : D X Y)
      (g : D Y Z),
      D X Z (pr1carrier _ f · pr1carrier _ g).

  Definition display_map_pullback_ax
    : UU
    := ∏
      (X Y Z : C)
      (f : Y --> X)
      (g : D Z X),
      ∑ (P : Pullback f (pr1carrier _ g)),
        D (PullbackObject P) Y (PullbackPr1 P).

  Definition is_display_map_class
    : UU
    := display_map_terminal_ax ×
      display_map_compose_ax ×
      display_map_pullback_ax.

End DisplayMaps.

Definition display_map_class
  (C : category)
  : UU
  := ∑ (D : ∏ (X Y : C), hsubtype (X --> Y)), is_display_map_class D.

Section Accessors.

  Context {C : category}.

  Definition is_display_map
    (D : display_map_class C)
    {X Y : C}
    (f : X --> Y)
    : hProp
    := pr1 D X Y f.

  Definition display_map
    (D : display_map_class C)
    (X Y : C)
    : UU
    := carrier (λ (f : X --> Y), is_display_map D f).

  Definition make_display_map
    {D : display_map_class C}
    {X Y : C}
    (f : X --> Y)
    (H : is_display_map D f)
    : display_map D X Y
    := f ,, H.

  Coercion display_map_map
    {D : display_map_class C}
    {X Y : C}
    (f : display_map D X Y)
    : X --> Y
    := pr1carrier _ f.

  Definition display_map_is_display_map
    {D : display_map_class C}
    {X Y : C}
    (f : display_map D X Y)
    : is_display_map D f
    := pr2 f.


  Definition terminal_display_map
    (D : display_map_class C)
    (X : C)
    : is_display_map D (TerminalArrow (pr112 D) X)
    := pr212 D X.

  Definition display_map_compose
    {D : display_map_class C}
    {X Y Z : C}
    (f : display_map D X Y)
    (g : display_map D Y Z)
    : display_map D X Z
    := make_display_map _ (pr122 D X Y Z f g).

  Definition display_map_pullback
    {D : display_map_class C}
    {X Y Z : C}
    (f : Y --> X)
    (g : display_map D Z X)
    : Pullback f g
    := pr1 (pr222 D X Y Z f g).

  Definition pullback_is_display_map
    {D : display_map_class C}
    {X Y Z : C}
    (f : Y --> X)
    (g : display_map D Z X)
    : is_display_map D (PullbackPr1 (display_map_pullback f g))
    := pr2 (pr222 D X Y Z f g).

  Definition pullback_display_map
    {D : display_map_class C}
    {X Y Z : C}
    (f : Y --> X)
    (g : display_map D Z X)
    : display_map D (display_map_pullback f g) Y
    := make_display_map _ (pullback_is_display_map f g).

End Accessors.

Section RelativeSlices.

  Context {C : category}.

  Definition relative_slice_disp
    (D : display_map_class C)
    (X : C)
    : disp_cat (slice_cat C X)
    := disp_full_sub
      (slice_cat C X)
      (λ f, is_display_map D (slicecat_ob_morphism _ _ f)).

  Definition relative_slice
    (D : display_map_class C)
    (X : C)
    : category
    := total_category (relative_slice_disp D X).

  Definition relative_slice_ob
    (D : display_map_class C)
    (X : C)
    : UU
    := relative_slice D X.

  Definition make_relative_slice_ob
    {D : display_map_class C}
    {X : C}
    (Y : C)
    (f : display_map D Y X)
    : relative_slice_ob D X
    := (Y ,, (f : C⟦_, _⟧)) ,, display_map_is_display_map f.

  Definition relative_slice_ob_domain
    {D : display_map_class C}
    {X : C}
    (f : relative_slice_ob D X)
    : C
    := pr11 f.

  Coercion relative_slice_ob_morphism
    {D : display_map_class C}
    {X : C}
    (f : relative_slice_ob D X)
    : display_map D (relative_slice_ob_domain f) X
    := make_display_map (pr21 f) (pr2 f).

  Definition relative_slice_mor
    {D : display_map_class C}
    {X : C}
    (f g : relative_slice_ob D X)
    : UU
    := relative_slice D X⟦f, g⟧.

  Definition make_relative_slice_mor
    {D : display_map_class C}
    {X : C}
    {f g : relative_slice_ob D X}
    (h : C⟦relative_slice_ob_domain f, relative_slice_ob_domain g⟧)
    (H : (f : C⟦_, _⟧) = h · g)
    : relative_slice_mor f g
    := (h ,, H) ,, tt.

  Coercion relative_slice_mor_morphism
    {D : display_map_class C}
    {X : C}
    {f g : relative_slice_ob D X}
    (h : relative_slice_mor f g)
    : C⟦relative_slice_ob_domain f, relative_slice_ob_domain g⟧
    := pr11 h.

  Definition relative_slice_mor_commutes
    {D : display_map_class C}
    {X : C}
    {f g : relative_slice_ob D X}
    (h : relative_slice_mor f g)
    : (f : C⟦_, _⟧) = (h : C⟦_, _⟧) · g
    := pr21 h.

  Lemma relative_slice_mor_eq
    {D : display_map_class C}
    {X : C}
    {f g : relative_slice_ob D X}
    {h h' : relative_slice_mor f g}
    (H : (h : C⟦_, _⟧) = h')
    : h = h'.
  Proof.
    apply subtypePath.
    {
      intro.
      apply isapropunit.
    }
    apply subtypePath.
    {
      intro.
      apply homset_property.
    }
    exact H.
  Qed.

End RelativeSlices.

Section Functors.

  Context {C : category}.
  Context {D : display_map_class C}.
  Context {X Y : C}.
  Context (f : display_map D X Y).

  (* Pullback *)

  Definition pullback_functor_ob
    (g : relative_slice_ob D Y)
    : relative_slice_ob D X
    := make_relative_slice_ob
      _
      (pullback_display_map f g).

  Definition pullback_functor_mor
    (g h : relative_slice_ob D Y)
    (i : relative_slice_mor g h)
    : relative_slice_mor (pullback_functor_ob g) (pullback_functor_ob h).
  Proof.
    use make_relative_slice_mor.
    - use PullbackArrow.
      + exact (pullback_display_map f g).
      + refine (PullbackPr2 (display_map_pullback f g) · i).
      + abstract (
          refine (PullbackSqrCommutes _ @ _);
          refine (_ @ assoc _ _ _);
          apply maponpaths;
          exact (relative_slice_mor_commutes i)
        ).
    - abstract exact (!PullbackArrow_PullbackPr1 _ _ _ _ _).
  Defined.

  Definition pullback_functor_data
    : functor_data (relative_slice D Y) (relative_slice D X)
    := make_functor_data
      pullback_functor_ob
      pullback_functor_mor.

  Lemma pullback_is_functor
    : is_functor pullback_functor_data.
  Proof.
    split.
    - intro g.
      apply relative_slice_mor_eq.
      apply (MorphismsIntoPullbackEqual (pr22 (display_map_pullback f _))).
      + refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
        exact (!id_left _).
      + refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
        refine (id_right _ @ _).
        exact (!id_left _).
    - intros g g' g'' h h'.
      apply relative_slice_mor_eq.
      apply (MorphismsIntoPullbackEqual (pr22 (display_map_pullback f _))).
      + refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ !_).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (PullbackArrow_PullbackPr1 _ _ _ _ _) @ _).
        apply PullbackArrow_PullbackPr1.
      + refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ !_).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (PullbackArrow_PullbackPr2 _ _ _ _ _) @ _).
        refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (PullbackArrow_PullbackPr2 _ _ _ _ _) @ _).
        apply assoc'.
  Qed.

  Definition pullback_functor
    : relative_slice D Y ⟶ relative_slice D X
    := make_functor
      pullback_functor_data
      pullback_is_functor.

  (* Dependent sum *)

  Definition dependent_sum_functor
    : relative_slice D X ⟶ relative_slice D Y.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro g.
        exact (make_relative_slice_ob _ (display_map_compose (g : relative_slice_ob _ _) f)).
      + intros g h i.
        use make_relative_slice_mor.
        * exact (i : relative_slice_mor _ _).
        * abstract (
            refine (_ @ assoc' _ _ _);
            apply (maponpaths (λ x, x · _));
            apply (relative_slice_mor_commutes i)
          ).
    - abstract (
        split;
        repeat intro;
        now apply relative_slice_mor_eq
      ).
  Defined.

  (* The dependent sum is a left adjoint to pullback *)

  Definition pullback_hom_weq
    (g : relative_slice_ob D X)
    (h : relative_slice_ob D Y)
    : relative_slice_mor (dependent_sum_functor g) h
    ≃ relative_slice_mor g (pullback_functor h).
  Proof.
    use weq_iso;
      intro i.
    - use make_relative_slice_mor.
      + use (PullbackArrow (display_map_pullback f h)).
        * exact g.
        * exact i.
        * exact (relative_slice_mor_commutes i).
      + abstract exact (!PullbackArrow_PullbackPr1 _ _ _ _ _).
    - use make_relative_slice_mor.
      + refine ((i : C⟦_, _⟧) · PullbackPr2 _).
      + abstract (
          refine (maponpaths (λ x, x · _) (relative_slice_mor_commutes i) @ _);
          do 2 refine (assoc' _ _ _ @ !_);
          apply maponpaths;
          apply (PullbackSqrCommutes (display_map_pullback f h))
        ).
    - abstract (
        apply relative_slice_mor_eq;
        exact (PullbackArrow_PullbackPr2 _ _ _ _ _)
      ).
    - abstract (
        apply relative_slice_mor_eq;
        apply (MorphismsIntoPullbackEqual (pr22 (display_map_pullback _ _)));
        [ refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _);
          exact (relative_slice_mor_commutes i)
        | apply PullbackArrow_PullbackPr2 ]
      ).
  Defined.

  Lemma pullback_adjoint_natural_left
    (g : relative_slice_ob D X)
    (h : relative_slice_ob D Y)
    (i : relative_slice_mor (dependent_sum_functor g) h)
    (j : relative_slice_ob D X)
    (k : relative_slice_mor j g)
    : pullback_hom_weq j h (# (dependent_sum_functor) k · i)
      = k · pullback_hom_weq g h i.
  Proof.
    apply relative_slice_mor_eq.
    apply (MorphismsIntoPullbackEqual (pr22 (display_map_pullback _ _))).
    - refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
      refine (_ @ assoc _ _ _).
      refine (_ @ !maponpaths _ (PullbackArrow_PullbackPr1 _ _ _ _ _)).
      exact (relative_slice_mor_commutes k).
    - refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
      refine (_ @ assoc _ _ _).
      exact (!maponpaths (λ x, _ · x) (PullbackArrow_PullbackPr2 _ _ _ _ _)).
  Qed.

  Lemma pullback_adjoint_natural_right
    (g : relative_slice_ob D X)
    (h : relative_slice_ob D Y)
    (i : relative_slice_mor (dependent_sum_functor g) h)
    (j : relative_slice_ob D Y)
    (k : relative_slice_mor h j)
    : pullback_hom_weq g j (i · k)
      = pullback_hom_weq g h i · # (pullback_functor) k.
  Proof.
    apply relative_slice_mor_eq.
    apply (MorphismsIntoPullbackEqual (pr22 (display_map_pullback _ _))).
    - refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
      refine (_ @ assoc _ _ _).
      refine (_ @ !maponpaths _ (PullbackArrow_PullbackPr1 _ _ _ _ _)).
      refine (!PullbackArrow_PullbackPr1 _ _ _ _ _).
    - refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
      refine (_ @ assoc _ _ _).
      refine (_ @ !maponpaths (λ x, _ · x) (PullbackArrow_PullbackPr2 _ _ _ _ _)).
      refine (_ @ assoc' _ _ _).
      exact (!maponpaths (λ x, x · _) (PullbackArrow_PullbackPr2 _ _ _ _ _)).
  Qed.

  Definition pullback_is_adjoint
    : are_adjoints dependent_sum_functor pullback_functor.
  Proof.
    use (invmap adjunction_homsetiso_weq).
    use tpair.
    - exact pullback_hom_weq.
    - split.
      + apply pullback_adjoint_natural_left.
      + apply pullback_adjoint_natural_right.
  Defined.

End Functors.
