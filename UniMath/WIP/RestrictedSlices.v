Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.WIP.MorphismSelections.

Local Open Scope cat.

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

  (* Morphisms *)
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

Lemma restricted_slice_mor_eq
  {C : category}
  {D : morphism_selection C}
  {X Y : C}
  {f : X --> Y}
  {g : restricted_slice_disp D X}
  {g' : restricted_slice_disp D Y}
  {h h' : g -->[f] g'}
  (H : pr11 h = pr11 h')
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

Lemma make_restricted_slice_iso
  {C : category}
  {D : morphism_selection C}
  {X : C}
  {f1 f2 : restricted_slice_ob D X}
  (g : z_iso (restricted_slice_ob_domain f1) (restricted_slice_ob_domain f2))
  (H : g · f2 = f1)
  : z_iso f1 f2.
Proof.
  use make_z_iso.
  - use make_restricted_slice_mor.
    + exact g.
    + abstract (
        refine (_ @ !id_right _);
        exact H
      ).
  - use make_restricted_slice_mor.
    + exact (z_iso_inv g).
    + abstract (
        refine (_ @ !id_right _);
        apply z_iso_inv_on_right;
        exact (!H)
      ).
  - abstract (
      split;
      apply restricted_slice_mor_eq;
      refine (restricted_slice_mor_comp _ _ @ _);
      [ apply z_iso_inv_after_z_iso
      | apply z_iso_after_z_iso_inv ]
    ).
Defined.
