(** * Grothendick toposes *)
(** ** Contents
- Definition of Grothendieck topology
 - Grothendieck topologies
 - Precategory of sheaves
- Grothendieck toposes
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.yoneda.

Local Open Scope cat.

(** * Definiton of Grothendieck topology
    The following definition is a formalization of the definition in Sheaves in Geometry and Logic,
    Saunders Mac Lane and Ieke Moerdijk, pages 109 and 110.

    Grothendieck topology is a collection J(c) of subobjects of the Yoneda functor, for every object
    of C, such that:
    - The Yoneda functor y(c) is in J(c).
    - Pullback of a subobject in J(c) along any morphism h : c' --> c is in J(c')
    - If S is a subobject of y(c) such that for all objects c' and all morphisms
      h : c' --> c in C the pullback of S along h is in J(c'), then S is in J(c).
  *)
Section def_grothendiecktopology.

  Variable C : category.

  (** A sieve on c is a subobject of the yoneda functor. *)
  Definition sieve (c : C) : UU :=
    Subobjectscategory (yoneda C c).

  Definition sieve_functor {c : C} (S : sieve c)
    : C^op ⟶ HSET
    := Subobject_dom S.

  Definition sieve_nat_trans {c : C} (S : sieve c) :
    sieve_functor S ⟹ yoneda_objects C c
    := Subobject_mor S.

  (** ** Grothendieck topology *)

  Definition sieve_selection : UU := ∏ (c : C), hsubtype (sieve c).

  Section IsGrothendieckTopology.

    Context (selection : sieve_selection).

    Definition is_Grothendieck_topology_maximal_sieve : UU :=
      ∏ (c : C),
        selection c (Subobjectscategory_ob (identity (yoneda C c)) (identity_isMonic _)).

    Definition is_Grothendieck_topology_stability : UU :=
      ∏ (c c' : C) (h : c' --> c) (s : sieve c),
        selection c s →
        selection c' (PullbackSubobject Pullbacks_PreShv s (# (yoneda C) h)).

    Definition is_Grothendieck_topology_transitivity : UU :=
      ∏ (c : C) (s : sieve c),
        (∏ (c' : C) (h : c' --> c),
          selection c' (PullbackSubobject Pullbacks_PreShv s (# (yoneda C) h)))
        → selection c s.

    Definition is_Grothendieck_topology : UU :=
      is_Grothendieck_topology_maximal_sieve
      × is_Grothendieck_topology_stability
      × is_Grothendieck_topology_transitivity.

    Lemma isaprop_is_Grothendieck_topology
      : isaprop is_Grothendieck_topology.
    Proof.
      repeat apply isapropdirprod;
        repeat (apply impred_isaprop; intro);
        apply propproperty.
    Qed.

  End IsGrothendieckTopology.

  Definition Grothendieck_topology : UU :=
    ∑ selection, is_Grothendieck_topology selection.

  (** Accessor functions *)
  Definition Grothendieck_topology_sieve_selection (GT : Grothendieck_topology) : sieve_selection := pr1 GT.

  Definition Grothendieck_topology_is_Grothendieck_topology (GT : Grothendieck_topology) :
    is_Grothendieck_topology (Grothendieck_topology_sieve_selection GT) := pr2 GT.

  (** ** Sheaves *)

  Section SheafProperties.

    Context (GT : Grothendieck_topology).
    Context (P : PreShv C).

    (** This is a formalization of the definition on page 122 *)
    Definition is_sheaf : UU :=
      ∏ (c : C)
        (S : Grothendieck_topology_sieve_selection GT c)
        (τ : sieve_functor (pr1carrier _ S) ⟹ (P : _ ⟶ _)),
      ∃! (η : yoneda_objects _ c ⟹ (P : _ ⟶ _)),
        nat_trans_comp _ _ _ (sieve_nat_trans (pr1carrier _ S)) η = τ.

    Lemma isaprop_is_sheaf : isaprop is_sheaf.
    Proof.
      apply impred_isaprop; intros t.
      apply impred_isaprop; intros S.
      apply impred_isaprop; intros τ.
      apply isapropiscontr.
    Qed.

    Section EqualizerSheafProperty.

      Context (c : C).
      Context (S : Grothendieck_topology_sieve_selection GT c).

      Definition is_sheaf_equalizer_domain
        : hSet.
      Proof.
        use (ProductObject _ _ (ProductsHSET _ _)).
        - exact (∑ (V : C), (sieve_functor (pr1carrier _ S) V : hSet)).
        - intro Vf.
          apply P.
          exact (pr1 Vf).
      Defined.

      Definition is_sheaf_equalizer_codomain
        : hSet.
      Proof.
        use (ProductObject _ _ (ProductsHSET _ _)).
        - exact (∑ (V W : C), (sieve_functor (pr1carrier _ S) V : hSet) × C⟦W, V⟧).
        - intro VWfg.
          apply P.
          exact (pr12 VWfg).
      Defined.

      Definition is_sheaf_equalizer_arrow1
        : is_sheaf_equalizer_domain → is_sheaf_equalizer_codomain.
      Proof.
        apply (ProductArrow _ SET).
        intro VWfg.
        refine (ProductPr _ _ _ (_ ,, _)).
        exact (# (sieve_functor _) (pr222 VWfg) (pr122 VWfg)).
      Defined.

      Definition is_sheaf_equalizer_arrow2
        : is_sheaf_equalizer_domain → is_sheaf_equalizer_codomain.
      Proof.
        apply (ProductArrow _ SET).
        intro VWfg.
        refine (ProductPr _ _ _ (pr1 VWfg ,, pr122 VWfg) · _).
        apply (# (P : _ ⟶ _)).
        exact (pr222 VWfg).
      Defined.

      Definition is_sheaf_equalizer_inducer_arrow
        : ((P : _ ⟶ _) c : hSet) → is_sheaf_equalizer_domain.
      Proof.
        apply (ProductArrow _ SET).
        intro Vf.
        apply (# (P : _ ⟶ _)).
        exact (sieve_nat_trans (pr1carrier _ S) _ (pr2 Vf)).
      Defined.

      Lemma is_sheaf_equalizer_inducer_arrow_commutes
        : (is_sheaf_equalizer_arrow1 ∘ is_sheaf_equalizer_inducer_arrow =
          is_sheaf_equalizer_arrow2 ∘ is_sheaf_equalizer_inducer_arrow)%functions.
      Proof.
        apply (ProductArrow_eq _ SET).
        intro VWfg.
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ _).
        refine (ProductPrCommutes _ _ _ _ _ _ (pr12 VWfg ,, _) @ !_).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ _).
        refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (ProductPrCommutes _ _ _ _ _ _ _) @ !_).
        refine (_ @ functor_comp _ _ _).
        apply maponpaths.
        exact (eqtohomot (nat_trans_ax (sieve_nat_trans (pr1carrier _ S)) _ _ (pr222 VWfg)) (pr122 VWfg)).
      Qed.

      Definition is_sheaf_equalizer_induced_arrow
        : SET⟦(P : _ ⟶ _) c, Equalizers_in_HSET _ _ is_sheaf_equalizer_arrow1 is_sheaf_equalizer_arrow2⟧
        := EqualizerIn (C := SET) _ _ _ is_sheaf_equalizer_inducer_arrow_commutes.

    End EqualizerSheafProperty.

    Definition is_sheaf' : UU
      := ∏ c S,
        is_z_isomorphism (is_sheaf_equalizer_induced_arrow c S).

    Lemma isaprop_is_sheaf'
      : isaprop is_sheaf'.
    Proof.
      do 2 (apply impred_isaprop; intro).
      apply isaprop_is_z_isomorphism.
    Qed.

    Definition locality
      : UU
      := ∏ (c : C)
          (S : Grothendieck_topology_sieve_selection GT c)
          (f g : ((P : _ ⟶ _) c : hSet)),
          (∏
            (d : C)
            (x : (sieve_functor (pr1carrier _ S) d : hSet)),
              # (P : _ ⟶ _) (sieve_nat_trans (pr1carrier _ S) d x) f
            = # (P : _ ⟶ _) (sieve_nat_trans (pr1carrier _ S) d x) g)
          → f = g.

    Lemma isaprop_locality
      : isaprop locality.
    Proof.
      repeat (apply impred_isaprop; intro).
      apply setproperty.
    Qed.

    Definition glueing
      : UU
      := ∏
        (c : C)
        (S : Grothendieck_topology_sieve_selection GT c)
        (x : ∏
          (d : C)
          (f : (sieve_functor (pr1carrier _ S) d : hSet)),
          ((P : _ ⟶ _) d : hSet)),
        (∏
          (V W : C)
          (f : sieve_functor (pr1carrier _ S) V : hSet)
          (g : C⟦W, V⟧),
          x _ (# (sieve_functor _) g f)
          = # (P : _ ⟶ _) g (x V f))
        → ∑ (z : (P : _ ⟶ _) c : hSet),
            ∏ d f,
              # (P : _ ⟶ _) (sieve_nat_trans (pr1carrier _ S) d f) z
              = x d f.

    Lemma isaprop_glueing
      (H : locality)
      : isaprop glueing.
    Proof.
      apply impred_isaprop.
      intro c.
      apply impred_isaprop.
      intro S.
      apply impred_isaprop.
      intro x.
      apply impred_isaprop.
      intro Hx.
      apply invproofirrelevance.
      intros z z'.
      apply subtypePath.
      {
        intro.
        repeat (apply impred_isaprop; intro).
        apply setproperty.
      }
      apply (H c S).
      intros d f.
      exact (pr2 z _ _ @ !pr2 z' _ _).
    Qed.

    Definition is_sheaf''
      : UU
      := locality × glueing.

    Lemma isaprop_is_sheaf''
      : isaprop is_sheaf''.
    Proof.
      use (isaprop_total2 (make_hProp _ _) (λ H, make_hProp _ _)).
      - exact isaprop_locality.
      - exact (isaprop_glueing H).
    Qed.

    Lemma is_sheaf_to_is_sheaf'
      : is_sheaf → is_sheaf'.
    Proof.
      intros H c S.
      specialize (H c S).
      use (make_is_z_isomorphism _ _ (make_dirprod _ _)).
      - intro VfH.
        refine (pr11 (H _) _ (identity c)).
        use make_nat_trans.
        * intros d f.
          refine (pr1 VfH (d ,, f)).
        * abstract (
            intros d d' f;
            apply funextfun;
            intro g;
            exact (eqtohomot (pr2 VfH) (_ ,, _ ,, _ ,, _))
          ).
      - apply funextfun.
        intro x.
        use (!eqtohomot (nat_trans_eq_pointwise (path_to_ctr _ _ (H _) (make_nat_trans _ _ _ _) _) _) _ @ _).
        + intros d g.
          refine (# (P : _ ⟶ _) g x).
        + intros d d' g.
          apply funextfun.
          intro g'.
          exact (eqtohomot (functor_comp (P : _ ⟶ _) g' g) x).
        + apply nat_trans_eq_alt.
          reflexivity.
        + exact (eqtohomot (functor_id P c) x).
      - apply funextfun.
        intro w.
        apply subtypePath.
        {
          intro.
          apply impred_isaset.
          intro.
          apply setproperty.
        }
        apply funextsec.
        intro Vf.
        refine (!eqtohomot (nat_trans_ax (pr11 (H _)) _ _ _) _ @ _).
        refine (_ @ eqtohomot (nat_trans_eq_pointwise (pr21 (H (make_nat_trans _ _ _ (is_sheaf_to_is_sheaf'_subproof c S w)))) (pr1 Vf)) (pr2 Vf)).
        apply (maponpaths (pr11 (H _) _)).
        apply id_right.
    Qed.

  End SheafProperties.

  (** The category of sheaves is the full subcategory of presheaves consisting of the presheaves
      which satisfy the is_sheaf proposition. *)
  Definition hsubtype_obs_is_sheaf (GT : Grothendieck_topology) :
    hsubtype (PreShv C) :=
    (λ P, make_hProp _ (isaprop_is_sheaf GT P)).

  Definition sheaf_cat (GT : Grothendieck_topology) :
    sub_precategories (PreShv C) :=
    full_sub_precategory (hsubtype_obs_is_sheaf GT).

End def_grothendiecktopology.


(** * Definition of Grothendieck topos
    Grothendieck topos is a precategory which is equivalent to the category of sheaves on some
    Grothendieck topology. *)
Section def_grothendiecktopos.

  Variable C : category.

  (** Here (pr1 D) is the precategory which is equivalent to the precategory of sheaves on the
      Grothendieck topology (pr2 D). *)
  Definition Grothendieck_topos : UU :=
    ∑ D' : (∑ D : category × (Grothendieck_topology C),
                  functor (pr1 D) (sheaf_cat C (pr2 D))),
           (adj_equivalence_of_cats (pr2 D')).

  (** Accessor functions *)
  Definition Grothendieck_topos_category (GT : Grothendieck_topos) : category :=
    pr1 (pr1 (pr1 GT)).
  Coercion Grothendieck_topos_category : Grothendieck_topos >-> category.

  Definition Grothendieck_topos_Grothendieck_topology (GT : Grothendieck_topos) :
    Grothendieck_topology C := pr2 (pr1 (pr1 GT)).

  Definition Grothendieck_topos_functor (GT : Grothendieck_topos) :
    functor (Grothendieck_topos_category GT)
            (sheaf_cat C (Grothendieck_topos_Grothendieck_topology GT)) :=
    pr2 (pr1 GT).

  Definition Grothendieck_topos_equivalence (GT : Grothendieck_topos) :
    adj_equivalence_of_cats (Grothendieck_topos_functor GT) := pr2 GT.

End def_grothendiecktopos.
