(** * Algebra I. Part D.  Rigs and rings. Vladimir Voevodsky. Aug. 2011 - . *)
(** Contents
- Standard Algebraic Structures
 - Rigs - semirings with 1, 0, and x * 0 = 0 * x = 0
  - General definitions
  - Homomorphisms of rigs (rig functions)
  - Relations similar to "greater" or "greater or equal" on rigs
  - Subobjects
  - Quotient objects
  - Direct products
  - Opposite rigs
  - Nonzero rigs
  - Group of units
*)


(** ** Preamble *)

(** Settings *)

Unset Kernel Term Sharing.

(** Imports *)

Require Import UniMath.MoreFoundations.Sets.
Require Import UniMath.MoreFoundations.Orders.
Require Import UniMath.Algebra.Groups.
Require Export UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Categories.DoubleMagma.
Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope logic.

(** *** Rigs - semirings with 1, 0 and x * 0 = 0 * x = 0 *)

(** **** General definitions *)

Definition rig : UU := rig_category.

Definition make_rig {X : setwith2binop} (is : isrigops (@op1 X) (@op2 X)) : rig.
Proof.
  exists (X : hSet).
  use tpair.
  + split.
    * exists (pr12 X).
      exact (pr111 is).
    * exists (pr22 X).
      exact (pr211 is).
  + exact (pr21 is ,, pr2 is).
Defined.

Definition pr1rig (R : rig) : setwith2binop.
Proof.
  use make_setwith2binop.
  - exact (pr1 R).
  - split.
    + exact (pr1 (pr112 R)).
    + exact (pr1 (pr212 R)).
Defined.
Coercion pr1rig : rig >-> setwith2binop.

Definition rigop1axs (X : rig) : isabmonoidop (@op1 X) := pr2 (pr112 X).

Definition rigassoc1 (X : rig) : isassoc (@op1 X) := assocax_is (rigop1axs X).

Definition rigunel1 {X : rig} : X := unel_is (rigop1axs X).

Definition riglunax1 (X : rig) : islunit op1 (@rigunel1 X) := lunax_is (rigop1axs X).

Definition rigrunax1 (X : rig) : isrunit op1 (@rigunel1 X) := runax_is (rigop1axs X).

Definition rigcomm1 (X : rig) : iscomm (@op1 X) := commax_is (rigop1axs X).

Definition rigmult0 (X : rig) : annihilates_ax (X := X) op1 op2 rigunel1 := pr122 X.

Definition rigmult0x (X : rig) : ∏ x, op2 rigunel1 x = rigunel1 := pr1 (rigmult0 X).

Definition rigmultx0 (X : rig) : ∏ x, op2 x rigunel1 = rigunel1 := pr2 (rigmult0 X).

Definition rigop2axs (X : rig) : ismonoidop (@op2 X) := pr2 (pr212 X).

Definition rigassoc2 (X : rig) : isassoc (@op2 X) := assocax_is (rigop2axs X).

Definition rigunel2 {X : rig} : X := unel_is (rigop2axs X).

Definition riglunax2 (X : rig) : islunit op2 (@rigunel2 X) := lunax_is (rigop2axs X).

Definition rigrunax2 (X : rig) : isrunit op2 (@rigunel2 X) := runax_is (rigop2axs X).

Definition rigdistraxs (X : rig) : isdistr (@op1 X) (@op2 X) := pr222 X.

Definition rigldistr (X : rig) : isldistr (@op1 X) (@op2 X) := pr1 (rigdistraxs X).

Definition rigrdistr (X : rig) : isrdistr (@op1 X) (@op2 X) := pr2 (rigdistraxs X).

Definition rigaxs (X : rig)
  : isrigops (@op1 X) (@op2 X).
Proof.
  use make_isrigops.
  - apply rigop1axs.
  - apply rigop2axs.
  - apply rigmult0x.
  - apply rigmultx0.
  - apply rigdistraxs.
Defined.

Definition make_rig'
  {X : hSet}
  (opp1 opp2 : binop X)
  (ax11 : ismonoidop opp1)
  (ax12 : iscomm opp1)
  (ax2 : ismonoidop opp2)
  (m0x : ∏ x : X, opp2 (unel_is ax11) x = unel_is ax11)
  (mx0 : ∏ x : X, opp2 x (unel_is ax11) = unel_is ax11)
  (dax : isdistr opp1 opp2)
  : rig.
Proof.
  use make_rig.
  - exact (make_setwith2binop X (make_dirprod opp1 opp2)).
  - use make_isrigops.
    + exact (make_isabmonoidop ax11 ax12).
    + exact ax2.
    + exact m0x.
    + exact mx0.
    + exact dax.
Defined.

Definition rigaddabmonoid (X : rig) : abmonoid :=
  make_abmonoid (make_setwithbinop X op1) (rigop1axs X).

Definition rigmultmonoid (X : rig) : monoid := make_monoid (make_setwithbinop X op2) (rigop2axs X).

Declare Scope rig_scope.
Notation "x + y" := (op1 x y) : rig_scope.
Notation "x * y" := (op2 x y) : rig_scope.
Notation "0" := (rigunel1) : rig_scope.
Notation "1" := (rigunel2) : rig_scope.

Delimit Scope rig_scope with rig.


(** **** Homomorphisms of rigs (rig functions) *)

Definition isrigfun {X Y : rig} (f : X → Y) : UU :=
  @ismonoidfun (rigaddabmonoid X) (rigaddabmonoid Y) f ×
  @ismonoidfun (rigmultmonoid X) (rigmultmonoid Y) f.

Definition make_isrigfun {X Y : rig} {f : X → Y}
           (H1 : @ismonoidfun (rigaddabmonoid X) (rigaddabmonoid Y) f)
           (H2 : @ismonoidfun (rigmultmonoid X) (rigmultmonoid Y) f) : isrigfun f :=
  H1 ,, H2.

Lemma isapropisrigfun {X Y : rig} (f : X → Y) : isaprop (isrigfun f).
Proof.
  use isapropdirprod.
  - use isapropismonoidfun.
  - use isapropismonoidfun.
Qed.

Definition rigfun (X Y : rig) : UU := rig_category⟦X, Y⟧%cat.

Definition isasetrigfun (X Y : rig) : isaset (rigfun X Y) := homset_property _ X Y.

Definition make_rigfun {X Y : rig} {f : X → Y} (is : isrigfun f) : rigfun X Y.
Proof.
  exists f.
  refine (_ ,, tt).
  split.
  - exists (pr11 is).
    exact (pr2 (make_abelian_monoid_morphism _ (pr1 is))).
  - exists (pr12 is).
    exact (pr2 (make_monoidfun (pr2 is))).
Defined.

Definition pr1rigfun (X Y : rig) (f : rigfun X Y) : X → Y := pr1 f.
Coercion pr1rigfun : rigfun >-> Funclass.

Definition rigfunisaddmonoidfun {X Y : rig} (f : rigfun X Y) :
  @ismonoidfun (rigaddabmonoid X) (rigaddabmonoid Y) f.
Proof.
  apply make_ismonoidfun.
  - exact (pr1 (pr112 f)).
  - exact (pr212 (pr112 f)).
Defined.

Definition rigaddfun {X Y : rig} (f : rigfun X Y) :
  monoidfun (rigaddabmonoid X) (rigaddabmonoid Y)
  := make_monoidfun (rigfunisaddmonoidfun f).

Definition rigfunismultmonoidfun {X Y : rig} (f : rigfun X Y) :
  @ismonoidfun (rigmultmonoid X) (rigmultmonoid Y) f.
Proof.
  apply make_ismonoidfun.
  - exact (pr1 (pr212 f)).
  - exact (pr22 (pr212 f)).
Defined.

Definition rigmultfun {X Y : rig} (f : rigfun X Y) :
  monoidfun (rigmultmonoid X) (rigmultmonoid Y) := make_monoidfun (rigfunismultmonoidfun f).

Definition rigfun_to_unel_rigaddmonoid {X Y : rig} (f : rigfun X Y) : f (0%rig) = 0%rig :=
  monoidfununel (rigaddfun f).

Definition rigfuncomp {X Y Z : rig} (f : rigfun X Y) (g : rigfun Y Z) : rigfun X Z.
Proof.
  use make_rigfun.
  - exact (g ∘ f).
  - use make_isrigfun.
    + exact (ismonoidfun_monoidfun (monoidfuncomp (rigaddfun f) (rigaddfun g))).
    + exact (ismonoidfun_monoidfun (monoidfuncomp (rigmultfun f) (rigmultfun g))).
Defined.

Lemma rigfun_paths {X Y : rig} (f g : rigfun X Y) (e : pr1 f = pr1 g) : f = g.
Proof.
  apply subtypePath.
  {
    intro x.
    refine (isapropdirprod _ unit _ isapropunit).
    cbn -[isaprop].
    repeat apply isapropdirprod;
      try apply isapropunit;
      repeat (apply impred_isaprop; intro);
      apply setproperty.
  }
  exact e.
Qed.

Definition rigfun_eq
  {X Y : rig}
  {f g : rigfun X Y}
  : (f = g) ≃ (∏ x, f x = g x).
Proof.
  use weqimplimpl.
  - intros e x.
    exact (maponpaths (λ (f : rigfun _ _), f x) e).
  - intro e.
    apply rigfun_paths, funextfun.
    exact e.
  - abstract apply homset_property.
  - abstract (
      apply impred_isaprop;
      intro;
      apply setproperty
    ).
Defined.

Definition rigiso (X Y : rig) : UU := ∑ (f : X ≃ Y), isrigfun f.

Definition make_rigiso {X Y : rig} (f : X ≃ Y) (is : isrigfun f) : rigiso X Y := f ,, is.

Definition pr1rigiso (X Y : rig) : rigiso X Y → X ≃ Y := @pr1 _ _.
Coercion pr1rigiso : rigiso >-> weq.

Definition rigisoisrigfun {X Y : rig} (f : rigiso X Y) : isrigfun f := pr2 f.

Definition rigaddiso {X Y : rig} (f : rigiso X Y) :
  monoidiso (rigaddabmonoid X) (rigaddabmonoid Y) :=
  @make_monoidiso (rigaddabmonoid X) (rigaddabmonoid Y) (pr1 f) (pr1 (pr2 f)).

Definition rigmultiso {X Y : rig} (f : rigiso X Y) :
  monoidiso (rigmultmonoid X) (rigmultmonoid Y) :=
  @make_monoidiso (rigmultmonoid X) (rigmultmonoid Y) (pr1 f) (pr2 (pr2 f)).

Definition rigiso_paths {X Y : rig} (f g : rigiso X Y) (e : pr1 f = pr1 g) : f = g.
Proof.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. use isapropisrigfun.
Qed.

Definition rigisotorigfun {X Y : rig} (f : rigiso X Y) : rigfun X Y := make_rigfun (pr2 f).

Lemma isrigfuninvmap {X Y : rig} (f : rigiso X Y) : isrigfun (invmap f).
Proof.
  intros. split.
  - apply (ismonoidfuninvmap (rigaddiso f)).
  - apply  (ismonoidfuninvmap (rigmultiso f)).
Defined.

Definition invrigiso {X Y : rig} (f : rigiso X Y) : rigiso Y X :=
  make_rigiso (invweq f) (isrigfuninvmap f).

Definition idrigiso (X : rig) : rigiso X X.
Proof.
  use make_rigiso.
  - exact (idweq X).
  - use make_isrigfun.
    + use make_ismonoidfun.
      * use make_isbinopfun.
        intros x x'. use idpath.
      * use idpath.
    + use make_ismonoidfun.
      * use make_isbinopfun.
        intros x x'. use idpath.
      * use idpath.
Defined.


(** **** Relations similar to "greater" or "greater or equal" on rigs *)

Definition isrigmultgt (X : rig) (R : hrel X) :=
  ∏ (a b c d : X), R a b → R c d → R (op1 (op2 a c) (op2 b d)) (op1 (op2 a d) (op2 b c)).

Definition isinvrigmultgt (X : rig) (R : hrel X) : UU :=
  (∏ (a b c d : X), R (op1 (op2 a c) (op2 b d)) (op1 (op2 a d) (op2 b c)) → R a b → R c d) ×
  (∏ (a b c d : X), R (op1 (op2 a c) (op2 b d)) (op1 (op2 a d) (op2 b c)) → R c d → R a b).


(** **** Subobjects *)

Definition issubrig {X : rig} (A : hsubtype X) : UU :=
  (@issubmonoid (rigaddabmonoid X) A) × (@issubmonoid (rigmultmonoid X) A).

Lemma isapropissubrig {X : rig} (A : hsubtype X) : isaprop (issubrig A).
Proof.
  intros. apply (isofhleveldirprod 1).
  - apply isapropissubmonoid.
  - apply isapropissubmonoid.
Defined.

Definition subrig (X : rig) : UU := ∑ ( A : hsubtype X), issubrig A.

Definition make_subrig {X : rig}
  (t : hsubtype X)
  (H : issubrig t)
  : subrig X
  := t ,, H.

Definition pr1subrig (X : rig) : @subrig X → hsubtype X :=
  @pr1 _ (λ  A : hsubtype X, issubrig A).

Definition subrigtosubsetswith2binop (X : rig) : subrig X → @subsetswith2binop X :=
  λ A, make_subsetswith2binop (pr1 A) (pr1 (pr1 (pr2 A)) ,, pr1 (pr2 (pr2 A))).
Coercion subrigtosubsetswith2binop : subrig >-> subsetswith2binop.

Definition rigaddsubmonoid {X : rig} : subrig X → @subabmonoid (rigaddabmonoid X) :=
  λ A, @make_submonoid (rigaddabmonoid X) (pr1 A) (pr1 (pr2 A)).

Definition rigmultsubmonoid {X : rig} : subrig X → @submonoid (rigmultmonoid X) :=
  λ A, @make_submonoid (rigmultmonoid X) (pr1 A) (pr2 (pr2 A)).

Lemma isrigcarrier {X : rig} (A : subrig X) : isrigops (@op1 A) (@op2 A).
Proof.
  intros. split.
  - exists (isabmonoidcarrier (rigaddsubmonoid A) ,, ismonoidcarrier (rigmultsubmonoid A)).
    + split.
      * intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
        simpl. apply rigmult0x.
      * intro a. apply (invmaponpathsincl _ (isinclpr1carrier A)).
        simpl. apply rigmultx0.
  - split.
    * intros a b c. apply (invmaponpathsincl _ (isinclpr1carrier A)).
      simpl. apply rigldistr.
    * intros a b c. apply (invmaponpathsincl _ (isinclpr1carrier A)).
      simpl. apply rigrdistr.
Defined.

Coercion carrierofasubrig (X : rig) (A : subrig X) : rig := make_rig (isrigcarrier A).

(** **** Quotient objects *)

Definition rigeqrel {X : rig} : UU := @twobinopeqrel X.
Identity Coercion id_rigeqrel : rigeqrel >-> twobinopeqrel.

Definition addabmonoideqrel {X : rig} (R : @rigeqrel X) :
  @binopeqrel (rigaddabmonoid X) := @make_binopeqrel (rigaddabmonoid X) (pr1 R) (pr1 (pr2 R)).

Definition multmonoideqrel {X : rig} (R : @rigeqrel X) :
  @binopeqrel (rigmultmonoid X) := @make_binopeqrel (rigmultmonoid X) (pr1 R) (pr2 (pr2 R)).

Lemma isrigquot {X : rig} (R : @rigeqrel X) :
  isrigops (@op1 (setwith2binopquot R)) (@op2 (setwith2binopquot R)).
Proof.
  intros. split.
  - exists (isabmonoidquot (addabmonoideqrel R) ,, ismonoidquot (multmonoideqrel R)).
    set (opp1 := @op1 (setwith2binopquot R)).
    set (opp2 := @op2 (setwith2binopquot R)).
    set (zr := setquotpr R (@rigunel1 X)).
    split.
    + refine (setquotunivprop
               R (λ x , make_hProp _ (setproperty (setwith2binopquot R) (opp2 zr x) zr)) _).
      intro x. apply (maponpaths (setquotpr R) (rigmult0x X x)).
    + refine (setquotunivprop
               R (λ x , make_hProp _ (setproperty (setwith2binopquot R) (opp2 x zr) zr)) _).
      intro x. apply (maponpaths (setquotpr R) (rigmultx0 X x)).
  - set (opp1 := @op1 (setwith2binopquot R)).
    set (opp2 := @op2 (setwith2binopquot R)).
    split.
    + unfold isldistr.
      apply (setquotuniv3prop
               R (λ x x' x'',
                    make_hProp _ (setproperty (setwith2binopquot R) (opp2  x'' (opp1 x x'))
                                             (opp1 (opp2 x'' x) (opp2 x'' x'))))).
      intros x x' x''. apply (maponpaths (setquotpr R) (rigldistr X x x' x'')).
    + unfold isrdistr.
      apply (setquotuniv3prop
               R (λ x x' x'',
                    make_hProp _ (setproperty (setwith2binopquot R) (opp2  (opp1 x x') x'')
                                             (opp1 (opp2 x x'') (opp2 x' x''))))).
      intros x x' x''. apply (maponpaths (setquotpr R) (rigrdistr X x x' x'')).
Defined.

Definition rigquot {X : rig} (R : @rigeqrel X) : rig :=
  @make_rig (setwith2binopquot R) (isrigquot R).


(** **** Direct products *)

Lemma isrigdirprod (X Y : rig) :
  isrigops (@op1 (setwith2binopdirprod X Y)) (@op2 (setwith2binopdirprod X Y)).
Proof.
  intros. split.
  - exists (isabmonoiddirprod (rigaddabmonoid X) (rigaddabmonoid Y) ,,
            ismonoiddirprod (rigmultmonoid X) (rigmultmonoid Y)).
    simpl. split.
    + intro xy. unfold setwith2binopdirprod. unfold op1. unfold op2.
      unfold ismonoiddirprod. unfold unel_is. simpl. apply pathsdirprod.
      apply (rigmult0x X). apply (rigmult0x Y).
    + intro xy. unfold setwith2binopdirprod. unfold op1. unfold op2.
      unfold ismonoiddirprod. unfold unel_is. simpl. apply pathsdirprod.
      apply (rigmultx0 X). apply (rigmultx0 Y).
  - split.
    + intros xy xy' xy''. unfold setwith2binopdirprod. unfold op1. unfold op2.
      simpl. apply pathsdirprod. apply (rigldistr X). apply (rigldistr Y).
    + intros xy xy' xy''. unfold setwith2binopdirprod. unfold op1. unfold op2.
      simpl. apply pathsdirprod. apply (rigrdistr X). apply (rigrdistr Y).
Defined.

Definition rigdirprod (X Y : rig) : rig := @make_rig (setwith2binopdirprod X Y) (isrigdirprod X Y).

(** **** Opposite rigs *)

Local Open Scope rig.

(** Following Bourbaki's Algebra, I, §8.3, Example V *)
Definition opposite_rig (X : rig) : rig.
Proof.
  use make_rig.
  - apply (make_setwith2binop X).
    split.
    + exact (λ x y, x + y).
    + exact (λ x y, y * x).
  - apply (make_isrigops (rigop1axs X)).
    (* For these proofs, we just have to switch some arguments around *)
    + apply make_ismonoidop.
      * exact (λ x y z, !rigassoc2 _ z y x).
      * refine (1,, _). (* same unit, opposite proofs *)
        exact (rigrunax2 _ ,, riglunax2 _).
    + exact (rigmultx0 _).
    + exact (rigmult0x _).
    + exact (rigrdistr _ ,, rigldistr _).
Defined.

(** In Emacs, use the function insert-char and choose SUPERSCRIPT ZERO *)
Notation "X ⁰" := (opposite_rig X) (at level 12) : rig_scope.

Definition opposite_opposite_rig (X : rig) : rigiso X ((X⁰)⁰).
Proof.
  refine ((idfun X,, idisweq X),, _).
  repeat split.
Defined.

(** **** Nonzero rigs *)

Definition isnonzerorig (X : rig) : hProp.
Proof.
  intros; use make_hProp.
  - exact ((1 : X) != 0).
  - apply isapropneg.
Defined.

Local Close Scope rig.
