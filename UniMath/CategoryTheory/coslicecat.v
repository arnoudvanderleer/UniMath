(** * Coslice categories

Author: Langston Barrett (@siddharthist), March 2018
*)

(** ** Contents:

- Definition of coslice categories, x/C

*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.

(** * Definition of coslice categories *)

(** Given a category C and x : obj C. The coslice category x/C is given by:

  - obj x/C: pairs (a,f) where f : x --> a
  - morphisms (a,f) --> (b,g): morphism h : a --> b with
<<
       x
       | \
       |  \
     f |   \  g
       v    \
       a --> b
          h
>>
    where f · h = g

*)
Section CosliceCat.

  Context (C : category) (x : C).

  Definition coslice_cat_disp_ob_mor
    : disp_cat_ob_mor C.
  Proof.
    use make_disp_cat_ob_mor.
    - intro a.
      exact (x --> a).
    - intros a b f g h.
      exact (f · h = g).
  Defined.

  Lemma coslice_cat_disp_id_comp
    : disp_cat_id_comp C coslice_cat_disp_ob_mor.
  Proof.
    split.
    - intros a f.
      apply id_right.
    - intros a1 a2 a3 h h' f1 f2 f3 Hyph Hyph'.
      refine (assoc _ _ _ @ _).
      refine (cancel_postcomposition _ _ _ Hyph @ _).
      exact Hyph'.
  Qed.

  Definition coslice_cat_disp_data
    : disp_cat_data C :=
    coslice_cat_disp_ob_mor ,, coslice_cat_disp_id_comp.

  Lemma coslice_cat_disp_locally_prop
    : locally_propositional coslice_cat_disp_data.
  Proof.
    do 5 intro.
    apply homset_property.
  Qed.

  Definition coslice_cat_disp : disp_cat C
    := make_disp_cat_locally_prop
      coslice_cat_disp_locally_prop.

  Definition coslice_cat : category := total_category coslice_cat_disp.

End CosliceCat.

Section Accessors.

  Context {C : category} {x : C}.

  Definition coslice_cat_ob_object (f : coslice_cat C x) : ob C := pr1 f.
  Definition coslice_cat_ob_morphism (f : coslice_cat C x) : C⟦x, coslice_cat_ob_object f⟧ := pr2 f.
  Definition coslice_cat_mor_morphism {f g : coslice_cat C x} (h : coslice_cat C x⟦f, g⟧) :
    C⟦coslice_cat_ob_object f, coslice_cat_ob_object g⟧ := pr1 h.
  Definition coslice_cat_mor_comm {f g : coslice_cat C x} (h : coslice_cat C x⟦f, g⟧) :
    (coslice_cat_ob_morphism f) · (coslice_cat_mor_morphism h) =
    (coslice_cat_ob_morphism g) := pr2 h.

End Accessors.

Section CosliceCatDirect.

  Context (C : category) (x : C).

  (** Accessor functions *)
  Definition coslice_cat_direct_ob := ∑ a, C⟦x,a⟧.
  Definition coslice_cat_direct_mor (f g : coslice_cat_direct_ob) := ∑ h, pr2 f · h = pr2 g.
  Definition coslice_cat_direct_ob_object (f : coslice_cat_direct_ob) : ob C := pr1 f.
  Definition coslice_cat_direct_ob_morphism (f : coslice_cat_direct_ob) : C⟦x, coslice_cat_direct_ob_object f⟧ := pr2 f.
  Definition coslice_cat_direct_mor_morphism {f g : coslice_cat_direct_ob} (h : coslice_cat_direct_mor f g) :
    C⟦coslice_cat_direct_ob_object f, coslice_cat_direct_ob_object g⟧ := pr1 h.
  Definition coslice_cat_direct_mor_comm {f g : coslice_cat_direct_ob} (h : coslice_cat_direct_mor f g) :
    (coslice_cat_direct_ob_morphism f) · (coslice_cat_direct_mor_morphism h) =
    (coslice_cat_direct_ob_morphism g) := pr2 h.

  (** Definitions *)
  Definition coslice_precat_ob_mor : precategory_ob_mor :=
    (coslice_cat_direct_ob,,coslice_cat_direct_mor).

  Definition id_coslice_precat (c : coslice_precat_ob_mor) : c --> c :=
    tpair _ _ (id_right (pr2 c)).

  Definition comp_coslice_precat {a b c : coslice_precat_ob_mor}
            (f : a --> b) (g : b --> c) : a --> c.
  Proof.
    use tpair.
    - exact (coslice_cat_direct_mor_morphism f · coslice_cat_direct_mor_morphism g).
    - abstract (refine (assoc _ _ _ @ _);
                refine (maponpaths (λ f, f · _) (coslice_cat_direct_mor_comm f) @ _);
                refine (coslice_cat_direct_mor_comm g)).
  Defined.

  Definition coslice_precat_data : precategory_data :=
    make_precategory_data _ id_coslice_precat (@comp_coslice_precat).

  Lemma is_precategory_coslice_precat_data :
    is_precategory coslice_precat_data.
  Proof.
    use make_is_precategory; intros; unfold comp_coslice_precat;
      cbn; apply subtypePairEquality.
    * intro; apply C.
    * apply id_left.
    * intro; apply C.
    * apply id_right.
    * intro; apply C.
    * apply assoc.
    * intro; apply C.
    * apply assoc'.
  Defined.

  (** that the previous Lemma is defined was done on purpose in 2018 - is it still appropriate? *)

  Definition coslice_precat : precategory :=
    (_,,is_precategory_coslice_precat_data).

  Lemma has_homsets_coslice_precat : has_homsets (coslice_precat).
  Proof.
    intros a b.
    induction a as [a f]; induction b as [b g]; simpl.
    apply (isofhleveltotal2 2); [ apply C | intro h].
    apply isasetaprop; apply C.
  Qed.

  Definition coslice_cat_direct : category := make_category _ has_homsets_coslice_precat.

End CosliceCatDirect.
