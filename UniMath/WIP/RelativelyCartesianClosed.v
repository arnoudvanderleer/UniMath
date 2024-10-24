Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Local Open Scope mor_disp.
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

Section RestrictedSlices.

  Context {C : category}.
  Context {D : morphism_selection C}.
  Context {X : C}.

  Definition restricted_slice_disp
    : disp_cat C
    := sigma_disp_cat
        (disp_full_sub
          (total_category (disp_codomain C))
          (λ f, is_selected D (pr22 f))).

  Definition restricted_slice
    : category
    := fiber_category restricted_slice_disp X.

  (* Objects *)
  Definition restricted_slice_ob
    : UU
    := restricted_slice.

  Definition make_restricted_slice_ob
    (Y : C)
    (f : selected_morphism D Y X)
    : restricted_slice_ob
    := (Y ,, (f : C⟦_, _⟧)) ,, selected_morphism_is_selected f.

  Definition restricted_slice_ob_domain
    (f : restricted_slice_ob)
    : C
    := pr11 f.

  Coercion restricted_slice_ob_morphism
    (f : restricted_slice_ob)
    : selected_morphism D (restricted_slice_ob_domain f) X
    := make_selected_morphism (pr21 f) (pr2 f).

  Section Morphisms.

    Context {f g : restricted_slice_ob}.

    Definition restricted_slice_mor
      : UU
      := restricted_slice⟦f, g⟧.

    Definition make_restricted_slice_mor
      (h : restricted_slice_ob_domain f --> restricted_slice_ob_domain g)
      (H : h · g = f · identity X)
      : restricted_slice_mor
      := (h ,, H) ,, tt.

    Coercion restricted_slice_mor_morphism
      (h : restricted_slice_mor)
      : restricted_slice_ob_domain f --> restricted_slice_ob_domain g
      := pr11 h.

    Definition restricted_slice_mor_commutes
      (h : restricted_slice_mor)
      : (h : C⟦_, _⟧) · g = f · identity X
      := pr21 h.

    Lemma restricted_slice_mor_eq
      {h h' : restricted_slice_mor}
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

  End Morphisms.

  Lemma restricted_slice_mor_comp
    {f f' f'' : restricted_slice_ob}
    (g : restricted_slice_mor (f := f) (g := f'))
    (g' : restricted_slice_mor (f := f') (g := f''))
    : ((g · g' : restricted_slice_mor) : C⟦_, _⟧) = (g : C⟦_, _⟧) · (g' : C⟦_, _⟧).
  Proof.
    refine (maponpaths pr1 (pr1_transportf (B := mor_disp (pr1 f) (pr1 f'')) _ _) @ _).
    refine (pr1_transportf (B := λ x, pr11 f --> pr11 f'') _ _ @ _).
    apply (eqtohomot (transportf_const _ _)).
  Qed.

End RestrictedSlices.

Arguments restricted_slice_mor {C D X}.
Arguments restricted_slice_disp {C}.
Arguments restricted_slice {C}.
Arguments restricted_slice_ob {C}.

Section Axioms.

  Context {C : category}.
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

  Definition selected_morphism_pullback_map_ax
    (P : selected_morphism_pullback_ax)
    : UU
    := ∏
      (X Y Z : C)
      (f : C⟦Y, X⟧)
      (g : selected_morphism D Z X),
      is_selected D (PullbackPr1 (P X Y Z f g)).

  Definition is_display_map_class
    : UU
    := (∑ (T : selected_morphism_terminal_ax),
        selected_morphism_terminal_map_ax T) ×
      selected_morphism_composed_map_ax ×
      (∑ (P : selected_morphism_pullback_ax),
        selected_morphism_pullback_map_ax P).

End Axioms.

Section DisplayMaps.

  Context {C : category}.

  Definition display_maps
    : UU
    := ∑ (D : morphism_selection C), is_display_map_class D.

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
      : selected_morphism_pullback_map_ax D display_maps_pullback
      := pr2 (pr222 D).

  End Accessors.

End DisplayMaps.

Arguments display_maps : clear implicits.

Section Fibration.

  Context {C : category}.
  Context {D : morphism_selection C}.
  Context {P : selected_morphism_pullback_ax D}.
  Context (HP : selected_morphism_pullback_map_ax D P).

  Section CartesianLift.

    Context {X Y : C}.
    Context (f : Y --> X).
    Context (g : restricted_slice_disp D X).

    Definition restricted_slice_cleaving_object
      : restricted_slice_disp D Y
      := make_restricted_slice_ob _
        (make_selected_morphism _ (HP _ _ _ f (g : restricted_slice_ob D X))).

    Definition restricted_slice_cleaving_morphism
      : restricted_slice_cleaving_object -->[f] g.
    Proof.
      refine ((PullbackPr2 _ ,, _) ,, tt).
      abstract exact (!PullbackSqrCommutes _).
    Defined.

    Section IsCartesian.

      Context {Z : C}.
      Context {h : C⟦Z, Y⟧}.
      Context {i : restricted_slice_disp D Z}.
      Context (j : i -->[h · f] g).

      Definition restricted_slice_cleaving_is_cartesian_morphism
        : i -->[h] restricted_slice_cleaving_object.
      Proof.
        use ((_ ,, _) ,, tt).
        - use PullbackArrow.
          + exact ((i : restricted_slice_ob D Z) · h).
          + exact (pr11 j).
          + abstract (
              refine (_ @ !pr21 j);
              apply assoc'
            ).
        - abstract apply PullbackArrow_PullbackPr1.
      Defined.

      Lemma restricted_slice_cleaving_is_cartesian_commutes
        : restricted_slice_cleaving_is_cartesian_morphism ;; restricted_slice_cleaving_morphism
        = j.
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
        apply PullbackArrow_PullbackPr2.
      Qed.

      Lemma restricted_slice_cleaving_is_cartesian_unique
        (k : i -->[h] restricted_slice_cleaving_object)
        (Hk : k ;; restricted_slice_cleaving_morphism = j)
        : k = restricted_slice_cleaving_is_cartesian_morphism.
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
        apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _))).
        - refine (_ @ !PullbackArrow_PullbackPr1 _ _ _ _ _).
          exact (pr21 k).
        - refine (_ @ !PullbackArrow_PullbackPr2 _ _ _ _ _).
          exact (base_paths _ _ (base_paths _ _ Hk)).
      Qed.

    End IsCartesian.

  End CartesianLift.

  Definition restricted_slice_cleaving
    : cleaving (restricted_slice_disp D).
  Proof.
    intros X Y f g.
    simple refine (_ ,, _ ,, _).
    - exact (restricted_slice_cleaving_object f g).
    - exact (restricted_slice_cleaving_morphism f g).
    - intros Z h i j.
      use unique_exists.
      + apply (restricted_slice_cleaving_is_cartesian_morphism f g j).
      + apply restricted_slice_cleaving_is_cartesian_commutes.
      + abstract (intro; apply homsets_disp).
      + apply restricted_slice_cleaving_is_cartesian_unique.
  Defined.

End Fibration.

Section Constructions.

  Context {C : category}.
  Context {D : morphism_selection C}.

  Context (HC : selected_morphism_composed_map_ax D).
  Context {P : selected_morphism_pullback_ax D}.
  Context (HP : selected_morphism_pullback_map_ax D P).

  Section Functors.

    Context {X Y : C}.
    Context (f : selected_morphism D X Y).

    Definition postcomposition_functor_data
      : functor_data (restricted_slice D X) (restricted_slice D Y).
    Proof.
      use make_functor_data.
      - refine (λ (g : restricted_slice_ob D X), _).
        exact (make_restricted_slice_ob _ (make_selected_morphism _ (HC _ _ _ g f))).
      - refine (λ (g h : restricted_slice_ob D X) (i : restricted_slice_mor g h), _).
        use make_restricted_slice_mor.
        * exact i.
        * abstract (
            refine (assoc _ _ _ @ _);
            refine (maponpaths (λ x, x · _) (restricted_slice_mor_commutes i) @ _);
            refine (maponpaths (λ x, x · _) (id_right _) @ _);
            exact (!id_right _)
          ).
    Defined.

    Lemma postcomposition_is_functor
      : is_functor postcomposition_functor_data.
    Proof.
      split.
      - refine (λ (g : restricted_slice_ob D X), _).
        now apply restricted_slice_mor_eq.
      - repeat intro.
        apply restricted_slice_mor_eq.
        refine (restricted_slice_mor_comp (X := X) _ _ @ !_).
        now refine (restricted_slice_mor_comp (X := Y) (# postcomposition_functor_data f0) (# _ g) @ !_).
    Qed.

    Definition postcomposition_functor
      : restricted_slice D X ⟶ restricted_slice D Y
      := make_functor _ postcomposition_is_functor.

    (* Adjunction *)

    Definition pullback_hom_weq
      (g : restricted_slice_ob D X)
      (h : restricted_slice_ob D Y)
      : restricted_slice_mor (postcomposition_functor g) h
      ≃ restricted_slice_mor g (fiber_functor_from_cleaving _ (restricted_slice_cleaving HP) f h).
    Proof.
      use weq_iso;
        intro i.
      - use make_restricted_slice_mor.
        + use (PullbackArrow (P _ _ _ f h)).
          * exact g.
          * exact i.
          * abstract (
              refine (_ @ !restricted_slice_mor_commutes i);
              exact (!id_right _)
            ).
        + abstract (
            refine (_ @ !id_right _);
            exact (PullbackArrow_PullbackPr1 _ _ _ _ _)
          ).
      - use make_restricted_slice_mor.
        + refine ((i : C⟦_, _⟧) · PullbackPr2 _).
        + abstract (
            refine (_ @ !id_right _);
            refine (_ @ maponpaths (λ x, x · _) (id_right _));
            refine (!_ @ maponpaths (λ x, x · _) (restricted_slice_mor_commutes i));
            do 2 refine (assoc' _ _ _ @ !_);
            apply maponpaths;
            apply (PullbackSqrCommutes (P _ _ _ f h))
          ).
      - abstract (
          apply restricted_slice_mor_eq;
          exact (PullbackArrow_PullbackPr2 _ _ _ _ _)
        ).
      - abstract (
          apply restricted_slice_mor_eq;
          apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _)));
          [ refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ !_);
            refine (_ @ id_right _);
            exact (restricted_slice_mor_commutes i)
          | apply PullbackArrow_PullbackPr2 ]
        ).
    Defined.

    Lemma pullback_adjoint_natural_left
      (g : restricted_slice_ob D X)
      (h : restricted_slice_ob D Y)
      (i : restricted_slice_mor (postcomposition_functor g) h)
      (j : restricted_slice_ob D X)
      (k : restricted_slice_mor j g)
      : pullback_hom_weq j h (# (postcomposition_functor) k · i)
        = k · pullback_hom_weq g h i.
    Proof.
      apply restricted_slice_mor_eq.
      refine (_ @ !restricted_slice_mor_comp _ _).
      apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _))).
      - refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ !_).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (PullbackArrow_PullbackPr1 _ _ _ _ _) @ _).
        refine (_ @ id_right _).
        exact (restricted_slice_mor_commutes k).
      - refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
        refine (_ @ assoc _ _ _).
        refine (restricted_slice_mor_comp (# _ k) i @ _).
        exact (!maponpaths (λ x, _ · x) (PullbackArrow_PullbackPr2 _ _ _ _ _)).
    Qed.

    Lemma pullback_adjoint_natural_right
      (g : restricted_slice_ob D X)
      (h : restricted_slice_ob D Y)
      (i : restricted_slice_mor (postcomposition_functor g) h)
      (j : restricted_slice_ob D Y)
      (k : restricted_slice_mor h j)
      : pullback_hom_weq g j (i · k)
        = pullback_hom_weq g h i · # (fiber_functor_from_cleaving _ (restricted_slice_cleaving HP) f) k.
    Proof.
      apply restricted_slice_mor_eq.
      refine (_ @ !restricted_slice_mor_comp _ _).
      apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _))).
      - refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ !_).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (PullbackArrow_PullbackPr1 _ _ _ _ _) @ _).
        refine (assoc _ _ _ @ _).
        refine (id_right _ @ _).
        exact (PullbackArrow_PullbackPr1 _ _ _ _ _).
      - refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
        refine (restricted_slice_mor_comp i k @ !_).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths (λ x, _ · x) (PullbackArrow_PullbackPr2 _ _ _ _ _) @ _).
        refine (maponpaths (λ x, _ · pr1 x) (pr1_transportf _ _) @ _).
        refine (maponpaths _ (pr1_transportf (B := λ x, C⟦P Y X (restricted_slice_ob_domain h) f h, pr11 j⟧) _ _) @ _).
        refine (maponpaths _ (eqtohomot (transportf_const _ _) _) @ _).
        refine (assoc _ _ _ @ _).
        exact (maponpaths (λ x, x · _) (PullbackArrow_PullbackPr2 _ _ _ _ _)).
    Qed.

    Definition pullback_is_adjoint
      : are_adjoints postcomposition_functor (fiber_functor_from_cleaving _ (restricted_slice_cleaving HP) f).
    Proof.
      use (invmap adjunction_homsetiso_weq).
      use tpair.
      - exact pullback_hom_weq.
      - split.
        + apply pullback_adjoint_natural_left.
        + apply pullback_adjoint_natural_right.
    Defined.

  End Functors.

  (* Section BinProducts.

    Context {X : C}.
    Context (f1 f2 : restricted_slice_ob D X).

    Let F := pullback_functor f1.
    Let HF := pullback_is_adjoint f1.

    Definition restricted_slice_binproduct_ob
      : restricted_slice D X.
    Proof.
      exact (postcomposition_functor f1 (F f2)).
    Defined.

    Definition restricted_slice_binproduct_pr1
      : restricted_slice D X⟦restricted_slice_binproduct_ob, f1⟧.
    Proof.
      use make_restricted_slice_mor.
      - exact (F f2 : restricted_slice_ob D _).
      - reflexivity.
    Defined.

    Definition restricted_slice_binproduct_pr2
      : restricted_slice D X⟦restricted_slice_binproduct_ob, f2⟧.
    Proof.
      exact (counit_from_are_adjoints HF f2).
    Defined.

    Section IsBinProduct.

      Context (g : restricted_slice_ob D X).
      Context (h1 : restricted_slice_mor g f1).
      Context (h2 : restricted_slice_mor g f2).

      Definition restricted_slice_binproduct_arrow
        : restricted_slice D X⟦g, restricted_slice_binproduct_ob⟧.
      Proof.
        (* At this point, F no longer suffices, because it h1 is not a selected morphism *)
        use make_restricted_slice_mor.
        - use (PullbackArrow (P _ _ _ f1 f2) _ h1 h2).
          abstract (
            refine (!_ @ restricted_slice_mor_commutes h2);
            apply restricted_slice_mor_commutes
          ).
        - abstract (
            refine (_ @ assoc' _ _ _);
            refine (_ @ !maponpaths (λ x, x · _) (PullbackArrow_PullbackPr1 _ _ _ _ _));
            apply restricted_slice_mor_commutes
          ).
      Defined.

      Lemma restricted_slice_binproduct_pr1_commutes
        : restricted_slice_binproduct_arrow · restricted_slice_binproduct_pr1 = h1.
      Proof.
        use restricted_slice_mor_eq.
        apply PullbackArrow_PullbackPr1.
      Qed.

      Lemma restricted_slice_binproduct_pr2_commutes
        : restricted_slice_binproduct_arrow · restricted_slice_binproduct_pr2 = h2.
      Proof.
        use restricted_slice_mor_eq.
        refine (maponpaths _ (id_left _) @ _).
        apply PullbackArrow_PullbackPr2.
      Qed.

      Lemma isaprop_pr_commutes
        (i : restricted_slice_mor g restricted_slice_binproduct_ob)
        : isaprop
          (i · restricted_slice_binproduct_pr1 = h1
            × i · restricted_slice_binproduct_pr2 = h2).
      Proof.
        apply isapropdirprod;
        apply homset_property.
      Qed.

      Lemma restricted_slice_binproduct_arrow_unique
        (i : restricted_slice_mor g restricted_slice_binproduct_ob)
        (Hi : i · restricted_slice_binproduct_pr1 = h1
          × i · restricted_slice_binproduct_pr2 = h2)
        : i = restricted_slice_binproduct_arrow.
      Proof.
        apply restricted_slice_mor_eq.
        apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ f1 f2))).
        * refine (_ @ !PullbackArrow_PullbackPr1 _ _ _ _ _).
          exact (base_paths _ _ (base_paths _ _ (pr1 Hi))).
        * refine (_ @ !PullbackArrow_PullbackPr2 _ _ _ _ _).
          refine (!maponpaths _ (id_left _) @ _).
          exact (base_paths _ _ (base_paths _ _ (pr2 Hi))).
      Qed.

    End IsBinProduct.

    Definition restricted_slice_binproducts
      : BinProduct (restricted_slice D X) f1 f2.
    Proof.
      use make_BinProduct.
      - exact restricted_slice_binproduct_ob.
      - exact restricted_slice_binproduct_pr1.
      - exact restricted_slice_binproduct_pr2.
      - use make_isBinProduct.
        refine (λ (g : restricted_slice_ob D X) (h1 h2 : restricted_slice_mor _ _), _).
        use unique_exists.
        + exact (restricted_slice_binproduct_arrow g h1 h2).
        + split.
          * apply restricted_slice_binproduct_pr1_commutes.
          * apply restricted_slice_binproduct_pr2_commutes.
        + apply isaprop_pr_commutes.
        + apply restricted_slice_binproduct_arrow_unique.
    Defined.

  End BinProducts. *)

  (* Section ConstprodPullbackIso.

    Context {X : C}.
    Context (f : restricted_slice_ob D X).

    Lemma constprod_pullback_iso_mor_is_nat_trans
      : is_nat_trans
        (pullback_functor f ∙ postcomposition_functor f)
        (constprod_functor1 restricted_slice_binproducts f)
        (λ f, identity_z_iso _).
    Proof.
      intros g h i.
      apply restricted_slice_mor_eq.
      refine (id_right _ @ _).
      refine (_ @ !id_left _).
      apply (MorphismsIntoPullbackEqual (pr22 (P _ _ _ _ _))).
      - do 2 refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ !_).
        exact (!id_right _).
      - do 2 refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ !_).
        refine (_ @ assoc _ _ _).
        exact (!id_left _).
    Qed.

    Definition constprod_pullback_iso
      : z_iso (C := [_, _]) (pullback_functor f ∙ postcomposition_functor f) (constprod_functor1 restricted_slice_binproducts f).
    Proof.
      apply (invmap (z_iso_is_nat_z_iso _ _)).
      use make_nat_z_iso.
      - exact (make_nat_trans _ _ _ constprod_pullback_iso_mor_is_nat_trans).
      - intro.
        apply z_iso_is_z_isomorphism.
    Defined.

  End ConstprodPullbackIso. *)

End Constructions.

Section DisplayMaps.

  Context {C : category}.
  Context {D : display_maps C}.

  Section Functors.

    Context {X Y : C}.
    Context (f : selected_morphism D X Y).

    Definition display_map_postcomposition_functor
      : restricted_slice D X ⟶ restricted_slice D Y
      := postcomposition_functor (display_maps_composed_map D) f.

    Definition display_map_pullback_functor
      : restricted_slice D Y ⟶ restricted_slice D X
      := fiber_functor_from_cleaving _ (restricted_slice_cleaving (display_maps_pullback_map D)) f.

    Definition display_map_postcomposition_pullback_are_adjoints
      : are_adjoints display_map_postcomposition_functor display_map_pullback_functor
      := pullback_is_adjoint _ _ _.

  End Functors.

  Definition is_relatively_cartesian_closed
    : UU
    := ∏ X Y (f : selected_morphism D X Y),
      is_left_adjoint (display_map_pullback_functor f).

End DisplayMaps.

Arguments is_relatively_cartesian_closed {C}.

(* Section Exponentials.

  Context {C : category}.
  Context {D : display_maps C}.
  Context (H : is_relatively_cartesian_closed D).

  Context {X : C}.
  Context (f : restricted_slice_ob D X).

  Definition relatively_cartesian_closed_exponentials
    : is_exponentiable
      (restricted_slice_binproducts
        (display_maps_composed_map D)
        (display_maps_pullback_map D))
      f.
  Proof.
    refine (is_left_adjoint_closed_under_iso _ _ _ _).
    - exact (constprod_pullback_iso _ _ f).
    - refine (_ ,, are_adjoints_functor_composite _ _).
      + apply H.
      + apply display_map_postcomposition_pullback_are_adjoints.
  Defined.

End Exponentials. *)
