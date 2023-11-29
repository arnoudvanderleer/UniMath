Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section KaroubiEnvelope.

  Context (C : category).

  Definition karoubi_envelope_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
      + exact (∑ (c : C) (f : C⟦c, c⟧), f · f = f).
      + intros f f'.
        exact (∑ (g : C⟦pr1 f, pr1 f'⟧), pr12 f · g = g × g · pr12 f' = g).
    - intro f.
      repeat use tpair.
      + exact (pr12 f).
      + exact (pr22 f).
      + exact (pr22 f).
    - intros f f' f'' g g'.
      repeat use tpair.
      + exact (pr1 g · pr1 g').
      + now rewrite assoc, (pr12 g).
      + now rewrite assoc', (pr22 g').
  Defined.

  Lemma karoubi_envelope_is_precategory
    : is_precategory karoubi_envelope_data.
  Proof.
    apply make_is_precategory_one_assoc.
    - intros m n f.
      apply subtypePath.
      {
        intro.
        apply isapropdirprod;
          apply homset_property.
      }
      exact (pr12 f).
    - intros m n f.
      apply subtypePath.
      {
        intro.
        apply isapropdirprod;
          apply homset_property.
      }
      exact (pr22 f).
    - intros k l m n f g h.
      apply subtypePath.
      {
        intro.
        apply isapropdirprod;
          apply homset_property.
      }
      apply assoc.
  Qed.

  Lemma karoubi_envelope_has_homsets
    : has_homsets karoubi_envelope_data.
  Proof.
    intros m n.
    apply isaset_total2.
    - apply homset_property.
    - intro x.
      apply isasetaprop.
      apply isapropdirprod;
        apply homset_property.
  Qed.

  Definition karoubi_envelope
    : category
    := make_category
      (make_precategory
        karoubi_envelope_data
        karoubi_envelope_is_precategory)
      karoubi_envelope_has_homsets.

  Definition karoubi_envelope_inclusion
    : C ⟶ karoubi_envelope.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro c.
        repeat use tpair.
        * exact c.
        * apply identity.
        * apply id_left.
      + intros a b f.
        cbn.
        repeat use tpair.
        * exact f.
        * apply id_left.
        * apply id_right.
    - split.
      + intro a.
        apply subtypePath.
        {
          intro.
          apply isapropdirprod;
            apply homset_property.
        }
        apply idpath.
      + intros a b c f g.
        apply subtypePath.
        {
          intro.
          apply isapropdirprod;
            apply homset_property.
        }
        apply idpath.
  Defined.

  Definition karoubi_pullback
    : PreShv karoubi_envelope ⟶ PreShv C
    := pre_composition_functor
      C^op
      karoubi_envelope^op
      SET
      (functor_opp (karoubi_envelope_inclusion)).

  Definition extend_presheaf_to_karoubi
    : PreShv C → PreShv karoubi_envelope.
  Proof.
    intro P.
    use make_functor.
    - use make_functor_data.
      + intro e.
        exists (∑ x, #(P : _ ⟶ _) (pr12 e) x = x).
        abstract (
          apply isaset_total2;
          [ apply setproperty
          | intro;
            apply isasetaprop;
            apply setproperty ]
        ).
      + intros a b f x.
        use tpair.
        * exact (#(P : _ ⟶ _) (pr1 f) (pr1 x)).
        * abstract (
            refine (eqtohomot (!functor_comp P _ _) _ @ _);
            apply (maponpaths (λ x, #(P : _ ⟶ _) x _));
            exact (pr12 f)
          ).
    - split.
      + abstract (
          intro a;
          apply funextfun;
          intro x;
          apply subtypePath;
          [ intro;
            apply setproperty | ];
          exact (pr2 x)
        ).
      + abstract (
          intros a b c f g;
          apply funextfun;
          intro x;
          apply subtypePath;
          [ intro;
            apply setproperty | ];
          apply (eqtohomot (functor_comp P _ _))
        ).
  Defined.

  Definition extend_presheaf_karoubi_iso
    (a : PreShv karoubi_envelope)
    : z_iso (extend_presheaf_to_karoubi (karoubi_pullback a)) a.
  Proof.
    use make_z_iso.
    - use make_nat_trans.
      + intros c x.
        refine (#(a : _ ⟶ _) _ (pr1 x)).
        exact (pr12 c ,, pr22 c ,, id_right _).
      + abstract (
          intros c c' f;
          apply funextfun;
          intro x;
          do 2 refine (!_ @ eqtohomot (functor_comp a _ _) (pr1 x));
          apply (maponpaths (λ f, #(a : _ ⟶ _) f (pr1 x)));
          apply subtypePath;
          [ intro;
            apply isapropdirprod;
            apply homset_property | ];
          exact (pr12 f @ !pr22 f)
        ).
    - use make_nat_trans.
      + intros c x.
        use tpair.
        * refine (#(a : _ ⟶ _) _ x).
          exact (pr12 c ,, id_left _ ,, pr22 c).
        * abstract (
            refine (!eqtohomot (functor_comp a _ _) _ @ _);
            apply (maponpaths (λ f, #(a : _ ⟶ _) f x));
            apply subtypePath;
            [ intro;
              apply isapropdirprod;
              apply homset_property | ];
            exact (pr22 c)
          ).
      + abstract (
          intros c c' f;
          apply funextfun;
          intro x;
          apply subtypePath;
          [ intro;
            apply setproperty | ];
          do 2 refine (!_ @ eqtohomot (functor_comp a _ _) x);
          apply (maponpaths (λ f, #(a : _ ⟶ _) f x));
          apply subtypePath;
          [ intro;
            apply isapropdirprod;
            apply homset_property | ];
          exact (pr12 f @ !pr22 f)
        ).
    - split.
      + abstract (
          apply nat_trans_eq_alt;
          intro c;
          apply funextfun;
          intro x;
          apply subtypePath;
          [ intro;
            apply setproperty | ];
          refine (!eqtohomot (functor_comp a _ _) (pr1 x) @ _);
          refine (_ @ pr2 x);
          apply (maponpaths (λ f, # (a : _ ⟶ _) f _));
          apply subtypePath;
          [ intro;
            apply isapropdirprod;
            apply homset_property | ];
          exact (pr22 c)
        ).
      + abstract (
          apply nat_trans_eq_alt;
          intro c;
          apply funextfun;
          intro x;
          refine (!eqtohomot (functor_comp a _ _) x @ _);
          refine (_ @ eqtohomot (functor_id a _) x);
          apply (maponpaths (λ f, # (a : _ ⟶ _) f _));
          apply subtypePath;
          [ intro;
            apply isapropdirprod;
            apply homset_property | ];
          exact (pr22 c)
        ).
  Defined.

  Definition extend_presheaf_mor_to_karoubi
    {P P' : PreShv C}
    (f : (P : _ ⟶ _) ⟹ (P' : _ ⟶ _))
    : (extend_presheaf_to_karoubi P : _ ⟶ _) ⟹ (extend_presheaf_to_karoubi P' : _ ⟶ _).
  Proof.
    use make_nat_trans.
    - intros c x.
      use tpair.
      + refine (f (pr1 c) (pr1 x)).
      + abstract (
          refine (!eqtohomot (nat_trans_ax f _ _ (pr12 c)) _ @ _);
          apply (maponpaths (f _));
          exact (pr2 x)
        ).
    - abstract (
        intros c c' x;
        apply funextfun;
        intro;
        apply subtypePath;
        [ intro;
          apply setproperty | ];
        apply (eqtohomot (nat_trans_ax f _ _ (pr1 x)))
      ).
  Defined.

  Definition karoubi_pullback_equivalence
    : adj_equivalence_of_cats karoubi_pullback.
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univalent_functor_category.
      apply is_univalent_HSET.
    - intros a b.
      use isweq_iso.
      + intro f.
        exact (inv_from_z_iso (extend_presheaf_karoubi_iso a)
          · extend_presheaf_mor_to_karoubi f
          · extend_presheaf_karoubi_iso b).
      + abstract (
          intro f;
          apply nat_trans_eq_alt;
          intro c;
          apply funextfun;
          intro x;
          refine (!eqtohomot (nat_trans_ax f _ _ _) _ @ _);
          apply (maponpaths ((f : _ ⟹ _) c));
          refine (!eqtohomot (functor_comp a _ _) _ @ _);
          refine (_ @ eqtohomot (functor_id a _) _);
          apply (maponpaths (λ f, # (a : _ ⟶ _) f _));
          apply subtypePath;
          [ intro;
            apply isapropdirprod;
            apply homset_property | ];
          exact (pr22 c)
        ).
      + abstract (
          intro f;
          apply nat_trans_eq_alt;
          intro c;
          apply funextfun;
          intro x;
          refine (!eqtohomot (nat_trans_ax f _ _ _) _ @ _);
          apply (maponpaths ((f : _ ⟹ _) c));
          refine (!eqtohomot (functor_comp a _ _) _ @ _);
          refine (_ @ eqtohomot (functor_id a _) _);
          apply (maponpaths (λ f, # (a : _ ⟶ _) f _));
          apply subtypePath;
          [ intro;
            apply isapropdirprod;
            apply homset_property | ];
          apply id_left
        ).
    - intro P.
      apply hinhpr.
      exists (extend_presheaf_to_karoubi P).
      use make_z_iso.
      + use make_nat_trans.
        * intros c x.
          exact (pr1 x).
        * abstract easy.
      + use make_nat_trans.
        * intros c x.
          exists x.
          abstract apply (eqtohomot (functor_id P _)).
        * abstract (
            intros c c' f;
            apply funextfun;
            intro x;
            apply subtypePath;
            [ intro;
              apply setproperty | ];
            apply idpath
          ).
      + split.
        * abstract (
            apply nat_trans_eq_alt;
            intro c;
            apply funextfun;
            intro x;
            apply subtypePath;
            [ intro;
              apply setproperty | ];
            apply idpath
          ).
        * abstract now apply nat_trans_eq_alt.
  Qed.

End KaroubiEnvelope.
