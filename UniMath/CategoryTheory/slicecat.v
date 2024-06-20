(** **********************************************************

Anders Mörtberg, Benedikt Ahrens, 2015-2016

*************************************************************)

(** **********************************************************

Contents:

- Definition of slice precategories, C/x (assumes that C has homsets)

- Isos in slice categories

- Monics in slice categories

- Epis in slice categories

- Proof that the forgetful functor [slice_cat_to_cat] : C/x → C is
  a left adjoint if C has binary products ([is_left_adjoint_slice_cat_to_cat])

- Proof that C/x is a univalent_category if C is

- Proof that any morphism C[x,y] induces a functor from C/x to C/y
  ([slice_cat_functor])

- Colimits in slice categories ([slice_precat_colims])

- Binary products in slice categories of categories with pullbacks
  ([BinProducts_slice_precat])

- Binary coproducts in slice categories of categories with binary
  coproducts ([BinCoproducts_slice_precat])

- Coproducts in slice categories of categories with coproducts
  ([Coproducts_slice_precat])

- Initial object in slice categories with initial object
  ([Initial_slice_precat])

- Terminal object in slice categories ([Terminal_slice_precat])

- Base change functor ([base_change_functor]) and proof that
  it is right adjoint to slice_cat_functor

- Pullbacks ([pullback_to_slice_pullback])

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Univalence.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monics.

Local Open Scope cat.

(** * Definition of slice categories *)
(** Given a category C and x : obj C. The slice category C/x is given by:

- obj C/x: pairs (a,f) where f : a -> x

- morphism (a,f) -> (b,g): morphism h : a -> b with
<<
           h
       a - - -> b
       |       /
       |     /
     f |   / g
       | /
       v
       x
>>
    where h · g = f

*)

Section SliceCat.

  Context (C : category) (x : C).

  Definition slice_cat_disp_ob_mor
    : disp_cat_ob_mor C.
  Proof.
    use make_disp_cat_ob_mor.
    - intro a.
      exact (a --> x).
    - intros a b f g h.
      exact (f = h · g).
  Defined.

  Lemma slice_cat_disp_id_comp
    : disp_cat_id_comp C slice_cat_disp_ob_mor.
  Proof.
    split.
    - intros a f.
      exact (!id_left _).
    - intros a1 a2 a3 h h' f1 f2 f3 Hyph Hyph'.
      refine (_ @ assoc _ _ _).
      refine (_ @ cancel_precomposition _ _ _ _ _ _ _ Hyph').
      exact Hyph.
  Qed.

  Definition slice_cat_disp_data
    : disp_cat_data C :=
    slice_cat_disp_ob_mor ,, slice_cat_disp_id_comp.

  Lemma slice_cat_disp_locally_prop
    : locally_propositional slice_cat_disp_data.
  Proof.
    do 5 intro.
    apply homset_property.
  Qed.

  Definition slice_cat_disp : disp_cat C
    := make_disp_cat_locally_prop
      slice_cat_disp_locally_prop.

  Definition slice_cat : category := total_category slice_cat_disp.

End SliceCat.

Section Accessors.

  Context {C : category} {x : C}.

  Definition slice_cat_ob_object (f : slice_cat C x) : ob C := pr1 f.
  Definition slice_cat_ob_morphism (f : slice_cat C x) : C⟦slice_cat_ob_object f, x⟧ := pr2 f.
  Definition slice_cat_mor_morphism {f g : slice_cat C x} (h : slice_cat C x⟦f, g⟧) :
    C⟦slice_cat_ob_object f, slice_cat_ob_object g⟧ := pr1 h.
  Definition slice_cat_mor_comm {f g : slice_cat C x} (h : slice_cat C x⟦f, g⟧) :
    (slice_cat_ob_morphism f) =
    (slice_cat_mor_morphism h) · (slice_cat_ob_morphism g) := pr2 h.

End Accessors.

Section SliceCatTheory.

  Context (C : category)
          (x : C).

  Local Notation "C / X" := (slice_cat C X).

  Lemma eq_mor_slice_cat (af bg : C / x) (f g : C/x⟦af,bg⟧) (H : pr1 f = pr1 g)
    : f = g.
  Proof.
    apply subtypePath.
    {
      intro.
      apply slice_cat_disp_locally_prop.
    }
    apply H.
  Qed.

  Lemma eq_mor_slice_cat_isweq (af bg : C / x) (f g : C/x⟦af,bg⟧) :
    isweq (eq_mor_slice_cat af bg f g).
  Proof.
    apply isweqimplimpl.
    - apply maponpaths.
    - apply C.
    - apply homset_property.
  Qed.

  Definition  eq_mor_slice_cat_weq (af bg : C / x) (f g : C/x⟦af,bg⟧) :
    (pr1 f = pr1 g ≃ f = g) := make_weq _ (eq_mor_slice_cat_isweq af bg f g).


  (** ** Isos in slice categories *)

  Lemma eq_z_iso_slice_cat (af bg : C / x) (f g : z_iso af bg) : pr1 f = pr1 g -> f = g.
  Proof.
    apply z_iso_eq.
  Qed.

  Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

  (** It suffices that the underlying morphism is an iso to get an iso in
      the slice category *)
  Lemma z_iso_to_slice_precat_z_iso (af bg : C / x) (h : af --> bg)
    (isoh : is_z_isomorphism (pr1 h)) : is_z_isomorphism h.
  Proof.
    apply (is_z_iso_total _ isoh).
    use tpair.
    - refine (!id_left _ @ !_).
      refine (_ @ maponpaths (λ x, x · _) (pr2 (pr2 isoh))).
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      apply slice_cat_mor_comm.
    - abstract (
        split;
        apply slice_cat_disp_locally_prop
      ).
  Defined.

  (** An iso in the slice category gives an iso in the base category *)
  Lemma slice_precat_z_iso_to_z_iso  (af bg : C / x) (h : af --> bg)
    (p : is_z_isomorphism h) : is_z_isomorphism (pr1 h).
  Proof.
    exact (is_z_iso_base_from_total p).
  Defined.

  Lemma weq_z_iso (af bg : C / x) :
    z_iso af bg ≃ ∑ h : z_iso (pr1 af) (pr1 bg), pr2 af = h · pr2 bg.
  Proof.
    apply (weqcomp (weqtotal2asstor _ _)).
    apply invweq.
    apply (weqcomp (weqtotal2asstor _ _)).
    apply weqfibtototal; intro h; simpl.
    apply (weqcomp (weqdirprodcomm _ _)).
    apply weqfibtototal; intro p.
    apply weqimplimpl.
    - intro hp; apply z_iso_to_slice_precat_z_iso; assumption.
    - intro hp; apply (slice_precat_z_iso_to_z_iso _ _ _ hp).
    - apply isaprop_is_z_isomorphism.
    - apply (isaprop_is_z_isomorphism(C:= C / x)).
  Defined.

  (** ** Monics in slice categories *)

  (** It suffices that the underlying morphism is an monic to get an monic in
      the slice category *)
  Lemma monic_to_slice_precat_monic (a b : C / x) (h : a --> b)
    (monich : isMonic (pr1 h)) : isMonic h.
  Proof.
    intros y f g eq.
    apply eq_mor_slice_cat, monich.
    exact (maponpaths pr1 eq).
  Qed.

  (** ** Epis in slice categories *)

  (** It suffices that the underlying morphism is an epic to get an epic in
      the slice category *)
  Lemma epic_to_slice_precat_epic (a b : C / x) (h : a --> b)
    (epich : isEpi (pr1 h)) : isEpi h.
  Proof.
    intros y f g eq.
    apply eq_mor_slice_cat, epich.
    apply (maponpaths pr1 eq).
  Qed.

  (** The forgetful functor from C/x to C *)
  Definition slice_cat_to_cat : (C / x) ⟶ C
    := pr1_category (slice_cat_disp C x).

  (** Right adjoint to slice_cat_to_cat *)

  Definition cat_to_slice_cat (BPC : BinProducts C)
    : C ⟶ (C / x).
  Proof.
    apply (lifted_functor (F := constprod_functor1 BPC x)).
    use tpair.
    - use tpair.
      + intro A.
        apply BinProductPr1.
      + abstract (
          intros A B f;
          refine (_ @ !BinProductOfArrowsPr1 _ _ _ _ _);
          exact (!id_right _)
        ).
    - abstract (
        split;
          intros;
          apply (homset_property C)
      ).
  Defined.

  Lemma is_left_adjoint_slice_cat_to_cat (BPC : BinProducts C) :
    is_left_adjoint slice_cat_to_cat.
  Proof.
    use left_adjoint_from_partial.
    - exact (cat_to_slice_cat BPC).
    - intro A.
      apply BinProductPr2.
    - intros A F f.
      use unique_exists.
      + exists (BinProductArrow _ _ (slice_cat_ob_morphism F) f).
        abstract exact (!BinProductPr1Commutes _ _ _ _ _ _ _).
      + abstract exact (!BinProductPr2Commutes _ _ _ _ _ _ _).
      + abstract (
          intro g;
          apply homset_property
        ).
      + abstract (
          intros g H;
          apply eq_mor_slice_cat;
          apply BinProductArrowUnique;
          [ exact (!slice_cat_mor_comm g)
          | exact (!H) ]
        ).
  Defined.

(** * Proof that C/x is a univalent_category if C is. *)
(** This is exercise 9.1 in the HoTT book *)

  Lemma is_univalent_slice_cat (HC : is_univalent C)
    : is_univalent (C / x).
  Proof.
    apply is_univalent_total_category.
    - exact HC.
    - intros A B p F G.
      induction p.
      apply isweqimplimpl.
      + intro f.
        refine (pr1 f @ _).
        apply id_left.
      + apply homset_property.
      + use (isaproptotal2).
        * intro.
          apply isaprop_is_z_iso_disp.
        * intros.
          apply homset_property.
  Qed.

End SliceCatTheory.

(** * A morphism x --> y in the base category induces a functor between C/x and C/y *)
Section SliceCatFunctor.

  Context {C : category} {x y : C} (f : C⟦x, y⟧).

  Local Notation "C / X" := (slice_cat C X).

  Definition slice_cat_functor
    : (C / x) ⟶ (C / y).
  Proof.
    apply (lifted_functor (F := pr1_category _)).
    use tpair.
    - use tpair.
      + intro F.
        exact (slice_cat_ob_morphism F · f).
      + abstract (
          intros F G g;
          refine (_ @ assoc' _ _ _);
          exact (maponpaths (λ x, x · _) (slice_cat_mor_comm g))
        ).
    - abstract (
        split;
        intros;
        apply homset_property
      ).
  Defined.

End SliceCatFunctor.

Section SliceCatFunctorTheory.

  Context (C : category).

  Local Notation "C / X" := (slice_cat C X).

  Lemma slice_cat_functor_identity (x : C) :
    slice_cat_functor (identity x) = functor_identity (C / x).
  Proof.
    apply (functor_eq _ _ (homset_property _)).
    use total2_paths_f.
    - apply funextsec; intro af.
      apply (maponpaths (tpair _ _)).
      apply id_right.
    - apply funextsec; intros [a f].
      apply funextsec; intros [b g].
      apply funextsec; intros [h hh].
      refine (transport_of_functor_map_is_pointwise _ _ _ _ _ _ _ _ _ @ _).
      unfold double_transport.
      simpl.
      rewrite transportf_total2.
      apply subtypePairEquality.
      {
        intro.
        apply C.
      }
      refine (maponpaths (λ x, _ (_ x)) (transportf_total2 _ _) @ _).
      refine (maponpaths (λ x, _ (x _) (_ (x _) _)) (toforallpaths_funextsec _) @ _).
      simpl.
      now induction (id_right f), (id_right g).
  Qed.

  (* This proof is not so nice... *)
  Lemma slice_cat_functor_comp {x y z : C} (f : C⟦x,y⟧) (g : C⟦y,z⟧) :
    slice_cat_functor (f · g) =
    functor_composite (slice_cat_functor f) (slice_cat_functor g).
  Proof.
    apply (functor_eq _ _ (homset_property _)).
    use total2_paths_f.
    - apply funextsec; intro af.
      apply (maponpaths (λ x, _ ,, x)).
      apply assoc.
    - apply funextsec; intros [a fax].
      apply funextsec; intros [b fbx].
      apply funextsec; intros [h hh].
      refine (transport_of_functor_map_is_pointwise (C / x) (C / z) _ _ _ _ _ _ _ @ _).
      unfold double_transport.
      simpl.
      rewrite transportf_total2.
      apply subtypePairEquality.
      {
        intro.
        apply C.
      }
      rewrite transportf_total2.
      rewrite toforallpaths_funextsec.
      simpl.
      now induction (assoc fax f g), (assoc fbx f g).
  Qed.

End SliceCatFunctorTheory.

(** * Colimits in slice categories *)
Section slice_cat_colimits.

Context (g : graph) (C : category) (x : C).

Local Notation "C / X" := (slice_cat C X).

Let U : functor (C / x) C := slice_cat_to_cat C x.

Lemma slice_precat_isColimCocone (d : diagram g (C / x)) (a : C / x)
  (cc : cocone d a)
  (H : isColimCocone (mapdiagram U d) (U a) (mapcocone U d cc)) :
  isColimCocone d a cc.
Proof.
set (CC := make_ColimCocone _ _ _ H).
intros y ccy.
use unique_exists.
+ use tpair; simpl.
  * apply (colimArrow CC), (mapcocone U _ ccy).
  * abstract (apply pathsinv0;
              eapply pathscomp0; [apply (postcompWithColimArrow _ CC (pr1 y) (mapcocone U d ccy))|];
              apply pathsinv0, (colimArrowUnique CC); intros u; simpl;
              eapply pathscomp0; [apply (!(pr2 (coconeIn cc u)))|];
              apply (pr2 (coconeIn ccy u))).
+ abstract (intros u; apply subtypePath; [intros xx; apply C|]; simpl;
            apply (colimArrowCommutes CC)).
+ abstract (intros f; simpl; apply impred; intro u; apply has_homsets_slice_precat).
+ abstract (intros f; simpl; intros Hf;
            apply eq_mor_slice_cat; simpl;
            apply (colimArrowUnique CC); intro u; cbn;
            rewrite <- (Hf u); apply idpath).
Defined.

Lemma slice_precat_ColimCocone (d : diagram g (C / x))
  (H : ColimCocone (mapdiagram U d)) :
  ColimCocone d.
Proof.
use make_ColimCocone.
- use tpair.
  + apply (colim H).
  + apply colimArrow.
    use make_cocone.
    * intro v; apply (pr2 (dob d v)).
    * abstract (intros u v e; apply (! pr2 (dmor d e))).
- use make_cocone.
  + intro v; simpl.
    use tpair; simpl.
    * apply (colimIn H v).
    * abstract (apply pathsinv0, (colimArrowCommutes H)).
  + abstract (intros u v e; apply eq_mor_slice_cat, (coconeInCommutes (colimCocone H))).
- intros y ccy.
  use unique_exists.
  + use tpair; simpl.
    * apply colimArrow, (mapcocone U _ ccy).
    * abstract (apply pathsinv0, colimArrowUnique; intros v; simpl; rewrite assoc;
                eapply pathscomp0;
                  [apply cancel_postcomposition,
                        (colimArrowCommutes H _ (mapcocone U _ ccy) v)|];
                induction ccy as [f Hf]; simpl; apply (! pr2 (f v))).
  + abstract (intro v; apply eq_mor_slice_cat; simpl;
              apply (colimArrowCommutes _ _ (mapcocone U d ccy))).
  + abstract (simpl; intros f; apply impred; intro v; apply has_homsets_slice_precat).
  + abstract (intros f Hf; apply eq_mor_slice_cat; simpl in *; apply colimArrowUnique;
              intros v; apply (maponpaths pr1 (Hf v))).
Defined.

End slice_cat_colimits.

Lemma slice_precat_colims_of_shape (C : category)
  {g : graph} (x : C) (CC : Colims_of_shape g C) :
  Colims_of_shape g (slice_cat C x).
Proof.
intros y; apply slice_precat_ColimCocone, CC.
Defined.

Lemma slice_precat_colims (C : category) (x : C) (CC : Colims C) :
  Colims (slice_cat C x).
Proof.
intros g d; apply slice_precat_ColimCocone, CC.
Defined.

(** * Moving between Binary products in slice categories and Pullbacks in base category *)
Section slice_cat_binproducts.

Context (C : category).

Local Notation "C / X" := (slice_cat C X).

Definition pullback_to_slice_binprod {A B Z : C} {f : A --> Z} {g : B --> Z} :
  Pullback f g -> BinProduct (C / Z) (A ,, f) (B ,, g).
Proof.
  intros P.
  use (((PullbackObject P ,, (PullbackPr1 P) · f) ,, (((PullbackPr1 P) ,, idpath _) ,, (((PullbackPr2 P) ,, (PullbackSqrCommutes P))))) ,, _).
  intros Y [j jeq] [k keq]; simpl in jeq , keq.
  use unique_exists.
  + use tpair.
    - apply (PullbackArrow P _ j k).
      abstract (rewrite <- jeq , keq; apply idpath).
    - abstract (cbn; rewrite assoc, PullbackArrow_PullbackPr1, <- jeq; apply idpath).
  + abstract (split; apply eq_mor_slice_cat; simpl;
              [ apply PullbackArrow_PullbackPr1 | apply PullbackArrow_PullbackPr2 ]).
  + abstract (intros h; apply isapropdirprod; apply has_homsets_slice_precat).
  + abstract (intros h [H1 H2]; apply eq_mor_slice_cat, PullbackArrowUnique;
             [ apply (maponpaths pr1 H1) | apply (maponpaths pr1 H2) ]).
Defined.

Definition BinProducts_slice_precat (PC : Pullbacks C) : ∏ x, BinProducts (C / x) :=
 λ x a b, pullback_to_slice_binprod (PC _ _ _ (pr2 a) (pr2 b)).

Definition slice_binprod_to_pullback {Z : C} {AZ BZ : C / Z} :
  BinProduct (C / Z) AZ BZ → Pullback (pr2 AZ) (pr2 BZ).
Proof.
  induction AZ as [A f].
  induction BZ as [B g].
  intros [[[P h] [[l leq] [r req]]] PisProd].
  use ((P ,, l ,, r) ,, (! leq @ req) ,, _).
  intros Y j k Yeq. simpl in *.
  use unique_exists.
  + exact (pr1 (pr1 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))).
  + abstract (exact (maponpaths pr1 (pr1 (pr2 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))) ,,
                                maponpaths pr1 (pr2 (pr2 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))))).
  + abstract (intros x; apply isofhleveldirprod; apply C).
  + intros t teqs.
    use (maponpaths pr1 (maponpaths pr1 (pr2 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq)) ((t ,, (maponpaths (λ x, x · f) (!(pr1 teqs)) @ !(assoc _ _ _) @ maponpaths (λ x, t · x) (!leq))) ,, _)))).
    abstract (split; apply eq_mor_slice_cat; [exact (pr1 teqs) | exact (pr2 teqs)]).
Defined.

Definition Pullbacks_from_slice_BinProducts (BP : ∏ x, BinProducts (C / x)) : Pullbacks C :=
  λ x a b f g, slice_binprod_to_pullback (BP x (a ,, f) (b ,, g)).

End slice_cat_binproducts.

(** * Binary coproducts in slice categories of categories with binary coproducts *)
Section slice_cat_bincoproducts.

Context (C : category) (BC : BinCoproducts C).

Local Notation "C / X" := (slice_cat C X).

Lemma BinCoproducts_slice_precat (x : C) : BinCoproducts (C / x).
Proof.
intros a b.
use make_BinCoproduct.
+ exists (BinCoproductObject (BC (pr1 a) (pr1 b))).
  apply (BinCoproductArrow _ (pr2 a) (pr2 b)).
+ use tpair.
  - apply BinCoproductIn1.
  - abstract (cbn; rewrite BinCoproductIn1Commutes; apply idpath).
+ use tpair.
  - apply BinCoproductIn2.
  - abstract (cbn; rewrite BinCoproductIn2Commutes; apply idpath).
+ intros c f g.
  use unique_exists.
  - exists (BinCoproductArrow _ (pr1 f) (pr1 g)).
    abstract (apply pathsinv0, BinCoproductArrowUnique;
      [ rewrite assoc, (BinCoproductIn1Commutes C _ _ (BC (pr1 a) (pr1 b))), (pr2 f); apply idpath
      | rewrite assoc, (BinCoproductIn2Commutes C _ _ (BC (pr1 a) (pr1 b))), (pr2 g)]; apply idpath).
  - abstract (split; apply eq_mor_slice_cat; simpl;
             [ apply BinCoproductIn1Commutes | apply BinCoproductIn2Commutes ]).
  - abstract (intros y; apply isapropdirprod; apply has_homsets_slice_precat).
  - abstract (intros y [<- <-]; apply eq_mor_slice_cat, BinCoproductArrowUnique; apply idpath).
Defined.

End slice_cat_bincoproducts.

(** * Coproducts in slice categories of categories with coproducts *)
Section slice_cat_coproducts.

Context (C : category) (I : UU) (BC : Coproducts I C).

Local Notation "C / X" := (slice_cat C X).

Lemma Coproducts_slice_precat (x : C) : Coproducts I (C / x).
Proof.
intros a.
use make_Coproduct.
+ exists (CoproductObject _ _ (BC (λ i, pr1 (a i)))).
  apply CoproductArrow; intro i; apply (pr2 (a i)).
+ intro i; use tpair; simpl.
  - apply (CoproductIn I C (BC (λ i, pr1 (a i))) i).
  - abstract (rewrite (CoproductInCommutes I C _ (BC (λ i, pr1 (a i)))); apply idpath).
+ intros c f.
  use unique_exists.
  - exists (CoproductArrow _ _ _ (λ i, pr1 (f i))).
    abstract (simpl; apply pathsinv0, CoproductArrowUnique; intro i;
              rewrite assoc, (CoproductInCommutes _ _ _ (BC (λ i, pr1 (a i)))), (pr2 (f i)); apply idpath).
  - abstract (intros i;
              apply eq_mor_slice_cat, (CoproductInCommutes _ _ _ (BC (λ i0 : I, pr1 (a i0))))).
  - abstract (intros y; apply impred; intro i; apply has_homsets_slice_precat).
  - abstract (simpl; intros y Hy;
              apply eq_mor_slice_cat, CoproductArrowUnique;
              intros i; apply (maponpaths pr1 (Hy i))).
Defined.

End slice_cat_coproducts.

Section slice_cat_initial.

Context (C : category) (IC : Initial C).

Local Notation "C / X" := (slice_cat C X).

Lemma Initial_slice_precat (x : C) : Initial (C / x).
Proof.
use make_Initial.
- use tpair.
  + apply (InitialObject IC).
  + apply InitialArrow.
- intros y.
  use unique_exists; simpl.
  * apply InitialArrow.
  * abstract (apply pathsinv0, InitialArrowUnique).
  * abstract (intros f; apply C).
  * abstract (intros f Hf; apply InitialArrowUnique).
Defined.

End slice_cat_initial.

Section slice_cat_terminal.

Context (C : category).

Local Notation "C / X" := (slice_cat C X).

Lemma Terminal_slice_precat (x : C) : Terminal (C / x).
Proof.
use make_Terminal.
- use tpair.
  + apply x.
  + apply (identity x).
- intros y.
  use unique_exists; simpl.
  * apply (pr2 y).
  * abstract (rewrite id_right; apply idpath).
  * abstract (intros f; apply C).
  * abstract (intros f ->; rewrite id_right; apply idpath).
Defined.

End slice_cat_terminal.

(** Base change functor: https://ncatlab.org/nlab/show/base+change *)
Section base_change.

Context (C : category) (PC : Pullbacks C).

Local Notation "C / X" := (slice_cat C X).

Definition base_change_functor_data {c c' : C} (g : C⟦c,c'⟧) : functor_data (C / c') (C / c).
Proof.
use tpair.
- intros Af'.
  exists (PullbackObject (PC _ _ _ g (pr2 Af'))).
  apply PullbackPr1.
- intros a b f.
  use tpair; simpl.
  + use PullbackArrow.
    * apply PullbackPr1.
    * apply (PullbackPr2 _ · pr1 f).
    * abstract (rewrite <- assoc, <- (pr2 f), PullbackSqrCommutes; apply idpath).
  + abstract (rewrite PullbackArrow_PullbackPr1; apply idpath).
Defined.

Lemma is_functor_base_change_functor {c c' : C} (g : C⟦c,c'⟧) :
 is_functor (base_change_functor_data g).
Proof.
split.
- intros x; apply (eq_mor_slice_cat C); simpl.
  apply pathsinv0, PullbackArrowUnique; rewrite id_left, ?id_right; apply idpath.
- intros x y z f1 f2; apply (eq_mor_slice_cat C); simpl.
  apply pathsinv0, PullbackArrowUnique.
  + rewrite <- assoc, !PullbackArrow_PullbackPr1; apply idpath.
  + rewrite <- assoc, PullbackArrow_PullbackPr2, !assoc,
            PullbackArrow_PullbackPr2; apply idpath.
Qed.

Definition base_change_functor {c c' : C} (g : C⟦c,c'⟧) : functor (C / c') (C / c) :=
  (base_change_functor_data g,,is_functor_base_change_functor g).


Local Definition eta_data {c c' : C} (g : C⟦c,c'⟧) :
  nat_trans_data (functor_identity (C / c))
            (functor_composite (slice_cat_functor g) (base_change_functor g)).
Proof.
  intros x.
  use tpair; simpl.
  + use (PullbackArrow _ _ (pr2 x) (identity _)).
    abstract (rewrite id_left; apply idpath).
  + abstract (rewrite PullbackArrow_PullbackPr1; apply idpath).
Defined.

Local Lemma is_nat_trans_eta_data {c c' : C} (g : C⟦c,c'⟧) : is_nat_trans _ _ (eta_data g).
Proof.
  intros x y f; apply eq_mor_slice_cat; simpl.
  eapply pathscomp0; [apply postCompWithPullbackArrow|].
  apply pathsinv0, PullbackArrowUnique.
  + rewrite <- assoc, !PullbackArrow_PullbackPr1, <- (pr2 f); apply idpath.
  + rewrite <- assoc, PullbackArrow_PullbackPr2, assoc,
                PullbackArrow_PullbackPr2, id_right, id_left; apply idpath.
Qed.

Local Definition eta {c c' : C} (g : C⟦c,c'⟧) :
  nat_trans (functor_identity (C / c))
            (functor_composite (slice_cat_functor g) (base_change_functor g)).
Proof.
  use make_nat_trans.
  - apply eta_data.
  - apply is_nat_trans_eta_data.
Defined.

Local Definition eps {c c' : C} (g : C⟦c,c'⟧) :
  nat_trans (functor_composite (base_change_functor g) (slice_cat_functor g))
            (functor_identity (C / c')).
Proof.
use make_nat_trans.
- intros x.
  exists (PullbackPr2 _).
  abstract (apply PullbackSqrCommutes).
- abstract ( intros x y f; apply eq_mor_slice_cat; cbn;
  rewrite PullbackArrow_PullbackPr2; apply idpath ).
Defined.

Local Lemma form_adjunction_eta_eps {c c' : C} (g : C⟦c,c'⟧) :
  form_adjunction (slice_cat_functor g) (base_change_functor g) (eta g) (eps g).
Proof.
use tpair.
- intros x; apply eq_mor_slice_cat; simpl; rewrite PullbackArrow_PullbackPr2; apply idpath.
- intros x; apply (eq_mor_slice_cat C); simpl.
  apply pathsinv0, PullbackEndo_is_identity.
  + rewrite <- assoc, !PullbackArrow_PullbackPr1; apply idpath.
  + rewrite <- assoc, PullbackArrow_PullbackPr2, assoc,
                PullbackArrow_PullbackPr2, id_left; apply idpath.
Qed.

Lemma are_adjoints_slice_cat_functor_base_change {c c' : C} (g : C⟦c,c'⟧) :
  are_adjoints (slice_cat_functor g) (base_change_functor g).
Proof.
exists (eta g,,eps g).
exact (form_adjunction_eta_eps g).
Defined.

(** If the base change functor has a right adjoint, called dependent product, then C / c has
    exponentials. The formal proof is inspired by Proposition 2.1 from:
    https://ncatlab.org/nlab/show/locally+cartesian+closed+category#in_category_theory
*)
Section dependent_product.

Context (H : ∏ (c c' : C) (g : C⟦c,c'⟧), is_left_adjoint (base_change_functor g)).

Let dependent_product_functor {c c' : C} (g : C⟦c,c'⟧) :
  functor (C / c) (C / c') := right_adjoint (H c c' g).

Let BPC c : BinProducts (C / c) := @BinProducts_slice_precat C PC c.

Lemma const_prod_functor1_slice_cat c (Af : C / c) :
  constprod_functor1 (BPC c) Af =
  functor_composite (base_change_functor (pr2 Af)) (slice_cat_functor (pr2 Af)).
Proof.
apply functor_eq; [apply has_homsets_slice_precat |].
use functor_data_eq.
- intro x; apply idpath.
- intros x y f; apply (eq_mor_slice_cat C); simpl.
  apply PullbackArrowUnique.
  + rewrite PullbackArrow_PullbackPr1, id_right; apply idpath.
  + rewrite PullbackArrow_PullbackPr2; apply idpath.
Qed.

Lemma dependent_product_to_exponentials c : Exponentials (BPC c).
Proof.
intros Af.
use tpair.
+ apply (functor_composite (base_change_functor (pr2 Af))
                           (dependent_product_functor (pr2 Af))).
+ rewrite const_prod_functor1_slice_cat.
  apply are_adjoints_functor_composite.
  - apply (pr2 (H _ _ _)).
  - apply are_adjoints_slice_cat_functor_base_change.
Defined.

End dependent_product.
End base_change.

(** ** Pullbacks *)

Section Pullbacks.
  Context {E : category} {I : ob E}.

  Local Notation "E / X" := (slice_cat E X).
  Local Notation "% A" := (slice_cat_ob_object E I A) (at level 20).
  Local Notation "$ A" := (slice_cat_ob_morphism E I A) (at level 20).
  Local Notation "$$ f" := (slice_cat_mor_morphism E I f) (at level 21).

  (** A complex lemma statement for a simpler proof later *)
  Local Lemma iscontr_cond_dirprod_weq {X : UU} {P Q R : X -> UU}
    (xx : ∃! x : X, P x × Q x) :
    (∏ x, isaprop (R x)) ->
    (∏ x, isaprop (P x)) ->
    (∏ x, isaprop (Q x)) ->
    (R (pr1 (iscontrpr1 xx))) ->
    (∃! x : X, P x × Q x × R x).
  Proof.
    intros ispropR ispropP ispropQ rxx.
    use make_iscontr.
    - exists (pr1 (iscontrpr1 xx)).
      split; [|split].
      + exact (dirprod_pr1 (pr2 (iscontrpr1 xx))).
      + exact (dirprod_pr2 (pr2 (iscontrpr1 xx))).
      + assumption.
    - intros t.
      use total2_paths_f.
      + pose (eq := proofirrelevancecontr xx (iscontrpr1 xx) (pr1 t,, make_dirprod (dirprod_pr1 (pr2 t)) (dirprod_pr1 (dirprod_pr2 (pr2 t))))).
        apply pathsinv0.
        eapply pathscomp0.
        apply (maponpaths pr1 eq).
        reflexivity.
      + apply proofirrelevance.
        do 2 (apply isapropdirprod; auto).
  Qed.

  (** Pullback diagram:
<<
      PB -- PBPr1 -> A
      |              |
    PBPr2            k
      V              V
      B ---- l ----> C
>>
  *)
  Lemma pullback_to_slice_pullback
    (A B C : ob (E / I)) (k : A --> C) (l : B --> C)
    (PB : Pullback ($$ k) ($$ l)) :
    Pullback k l.
  Proof.
    assert (eq : PullbackPr1 PB · $ A = PullbackPr2 PB · $ B).
    {
      (** Just because [k], [l] are slice category morphisms: *)
      assert (eq1 : $ A = $$ k · $ C) by (apply slice_cat_mor_comm).
      assert (eq2 : $ B = $$ l · $ C) by (apply slice_cat_mor_comm).
      rewrite eq2, eq1.
      do 2 rewrite assoc.
      apply (maponpaths (fun x => x · _)).
      apply PullbackSqrCommutes.
    }

    pose (PBtoI := PullbackPr1 PB · $ A).
    use make_Pullback.
    - use tpair.
      + exact (PullbackObject PB).
      + exact PBtoI.
    - (** The arrow [PB --> A] *)
      use tpair.
      + (** The arrow from [E] *)
        exact (PullbackPr1 PB).
      + (** The triangle commutes by definition *)
        reflexivity.
    - (** The arrow [PB --> B] *)
      use tpair.
      + exact (PullbackPr2 PB).
      + exact eq.
    - (** The square commutes *)
      apply eq_mor_slice_cat, PullbackSqrCommutes.
    - (** [isPullback] *)
      intros PB' prA' prB' commSq'.

      (** In two steps, we reduce the problem of a pullback in [E/I] to that of
          a pullback in [E] (which we already have).

          1. Simplify the equalities involved in the sigma-type.
          2. Note that what is required is simply a pullback in [E] with
             an extra commutation condition.
       *)
      use iscontrweqb;
        [exact (∑ kk : % PB' --> PullbackObject PB,
                kk · PullbackPr1 PB = ($$ prA') ×
                kk · PullbackPr2 PB = ($$ prB') ×
                slice_cat_ob_morphism _ _ PB' = kk · PBtoI)| | ].
      use weqcomp.
      + exact (∑ kk : PB' --> (PullbackObject PB,, PBtoI),
                ($$ kk) · PullbackPr1 PB = ($$ prA') ×
                ($$ kk) · PullbackPr2 PB = ($$ prB')).
      + (** Step 1 *)
        apply weqfibtototal; intro.
        apply weqdirprodf;
          (apply weqiff;
           [|apply has_homsets_slice_precat|apply homset_property];
           apply weq_to_iff).
        * eapply weqcomp; [apply invweq, eq_mor_slice_cat_weq|].
          apply idweq.
        * eapply weqcomp; [apply invweq, eq_mor_slice_cat_weq|].
          apply idweq.
      + (** Step 2 *)
        (** This is all just rearranging of direct products *)
        cbn.
        eapply weqcomp.
        * apply (@weqtotal2asstor (E⟦% PB', PB⟧) (fun f => $ PB' = f · PBtoI) _).
        * apply weqfibtototal; intro; cbn.
          eapply weqcomp.
          apply weqdirprodcomm.
          apply weqdirprodasstor.
      + apply (iscontr_cond_dirprod_weq
                 (isPullback_Pullback PB _ _ _ (maponpaths pr1 commSq'))).
        * intro; apply homset_property.
        * intro; apply homset_property.
        * intro; apply homset_property.
        * (** The unique arrow between pullbacks is also an arrow in the slice cat *)
          unfold PBtoI.
          change (pr1 (iscontrpr1
                   (isPullback_Pullback PB (pr1 PB') (pr1 prA') (pr1 prB')
                      (maponpaths pr1 commSq')))) with
            (PullbackArrow PB _ _ _ (maponpaths pr1 commSq')).
          cbn.
          rewrite assoc.
          rewrite PullbackArrow_PullbackPr1.
          apply slice_cat_mor_comm.
  Defined.
End Pullbacks.

Section SliceCategoryDirect.

  Context (C : category) (x : C).

  (* Accessor functions *)
  Definition slice_cat_direct_ob := ∑ a, C⟦a,x⟧.
  Definition slice_cat_direct_mor (f g : slice_cat_direct_ob) := ∑ h, pr2 f = h · pr2 g.

  Definition slice_cat_direct_ob_object (f : slice_cat_direct_ob) : ob C := pr1 f.

  Definition slice_cat_direct_ob_morphism (f : slice_cat_direct_ob) : C⟦slice_cat_direct_ob_object f, x⟧ := pr2 f.

  (* Accessor functions *)
  Definition slice_cat_direct_mor_morphism {f g : slice_cat_direct_ob} (h : slice_cat_direct_mor f g) :
    C⟦slice_cat_direct_ob_object f, slice_cat_direct_ob_object g⟧ := pr1 h.

  Definition slice_cat_direct_mor_comm {f g : slice_cat_direct_ob} (h : slice_cat_direct_mor f g) :
    (slice_cat_direct_ob_morphism f) = (slice_cat_direct_mor_morphism h) · (slice_cat_direct_ob_morphism g) := pr2 h.

  Definition slice_precat_direct_ob_mor : precategory_ob_mor := (slice_cat_direct_ob,,slice_cat_direct_mor).

  Definition id_slice_precat_direct (c : slice_precat_direct_ob_mor) : c --> c :=
    tpair _ _ (!(id_left (pr2 c))).

  Definition comp_slice_precat_direct_subproof {a b c : slice_precat_direct_ob_mor}
    (f : a --> b) (g : b --> c) : pr2 a = (pr1 f · pr1 g) · pr2 c.
  Proof.
    rewrite <- assoc, (!(pr2 g)).
    exact (pr2 f).
  Qed.

  Definition comp_slice_precat_direct (a b c : slice_precat_direct_ob_mor)
                              (f : a --> b) (g : b --> c) : a --> c :=
    (pr1 f · pr1 g,,comp_slice_precat_direct_subproof _ _).

  Definition slice_precat_direct_data : precategory_data :=
    make_precategory_data _ id_slice_precat_direct comp_slice_precat_direct.

  Lemma is_precategory_slice_precat_direct_data :
    is_precategory slice_precat_direct_data.
  Proof.
    repeat split; simpl.
    - intros a b f.
      induction f as [h hP].
      apply subtypePairEquality; [ intro; apply C | apply id_left ].
    - intros a b f.
      induction f as [h hP].
      apply subtypePairEquality; [ intro; apply C | apply id_right ].
    - intros a b c d f g h.
      apply subtypePairEquality; [ intro; apply C | apply assoc ].
    - intros a b c d f g h.
      apply subtypePairEquality; [ intro; apply C | apply assoc' ].
  Qed.

  Definition slice_precat_direct : precategory :=
    (_,,is_precategory_slice_precat_direct_data).

  Lemma has_homsets_slice_precat_direct : has_homsets (slice_precat_direct).
  Proof.
    intros a b.
    induction a as [a f]; induction b as [b g]; simpl.
    apply (isofhleveltotal2 2); [ apply C | intro h].
    apply isasetaprop; apply C.
  Qed.

  Definition slice_cat_direct : category := make_category _ has_homsets_slice_precat_direct.

End SliceCategoryDirect.
