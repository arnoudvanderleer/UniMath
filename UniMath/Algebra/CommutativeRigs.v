(** * Algebra I. Part D.  Rigs and rings. Vladimir Voevodsky. Aug. 2011 - . *)
(** Contents
- Standard Algebraic Structures
 - Commutative rigs
  - General definitions
  - Relations similar to "greater" on commutative rigs
  - Subobjects
  - Quotient objects
  - Direct products
  - Opposite commutative rigs
*)


(** ** Preamble *)

(** Settings *)

Unset Kernel Term Sharing.

(** Imports *)

Require Import UniMath.MoreFoundations.Sets.
Require Import UniMath.MoreFoundations.Orders.
Require Import UniMath.Algebra.Groups.
Require Export UniMath.Algebra.Monoids.
Require Export UniMath.Algebra.Rigs.
Require Export UniMath.CategoryTheory.Core.Categories.
Require Export UniMath.CategoryTheory.Categories.DoubleMagma.

Local Open Scope logic.

(** *** Commutative rigs *)

(** **** General definitions *)

Definition commrig : UU := (ob commutative_rig_category).
Definition commrig' : UU := ∑ (X : hSet)
(d : (∑ d : binop X, isabmonoidop d) × (∑ d : binop X, isabmonoidop d)),
(annihilates_ax (pr11 d) (pr12 d) (unel_is (pr21 d))) ×
isdistr (pr11 d) (pr12 d).

Coercion commrigtorig (R : commrig) : rig
  := pr1 R ,, (make_dirprod (pr112 R) (pr1 (pr212 R) ,, pr12 (pr212 R))) ,, pr22 R.

Coercion commrig'torig (R : commrig') : rig
  := pr1 R ,, (make_dirprod (pr112 R) (pr1 (pr212 R) ,, pr12 (pr212 R))) ,, pr22 R.

Time Definition test1 (R : commrig) : rig := commrigtorig R.
Time Definition test2 (R : commrig') : rig := R.
Time Definition test3 (R : commrig) : rig := R.

(*
Definition make_commrig (X : setwith2binop) (is : iscommrigops (@op1 X) (@op2 X)) : commrig.
Proof.
  exists (X : hSet).
  use tpair.
  + split.
    * exists (pr12 X).
      exact (pr1 (pr111 is)).
    * exists (pr22 X).
      refine (pr2 (pr111 is) ,, _).
      exact (pr2 is).
  + exact (pr211 is ,, pr21 is).
Defined.

Definition make_commrig'
  {X : hSet}
  (opp1 opp2 : binop X)
  (ax11 : ismonoidop opp1)
  (ax12 : iscomm opp1)
  (ax2 : ismonoidop opp2)
  (ax22 : iscomm opp2)
  (m0x : ∏ x : X, opp2 (unel_is ax11) x = unel_is ax11)
  (mx0 : ∏ x : X, opp2 x (unel_is ax11) = unel_is ax11)
  (dax : isdistr opp1 opp2) : commrig.
Proof.
  use make_commrig.
  - exact (make_setwith2binop X (make_dirprod opp1 opp2)).
  - refine (make_dirprod _ ax22).
    use make_isrigops.
    + exact (make_isabmonoidop ax11 ax12).
    + exact ax2.
    + exact m0x.
    + exact mx0.
    + exact dax.
Defined. *)

Definition rigcomm2 (X : commrig) : iscomm (@op2 (X : rig)) := pr22 (pr212 X).

Definition commrigop2axs (X : commrig) : isabmonoidop (@op2 X) := make_isabmonoidop (rigop2axs X) (rigcomm2 X).

Definition commrigmultabmonoid (X : commrig) : abmonoid :=
  make_abmonoid (make_setwithbinop X op2) (commrigop2axs X).


(** **** Relations similar to "greater" on commutative rigs *)

Lemma isinvrigmultgtif (X : commrig) (R : hrel X)
      (is2 : ∏ a b c d, R (op1 (op2 a c) (op2 b d)) (op1 (op2 a d) (op2 b c)) → R a b → R c d) :
  isinvrigmultgt X R.
Proof.
  intros. split.
  - apply is2.
  - intros a b c d r rcd.
    rewrite (rigcomm1 X (op2 a d) _) in r.
    rewrite (rigcomm2 X a c) in r.
    rewrite (rigcomm2 X b d) in r.
    rewrite (rigcomm2 X b c) in r.
    rewrite (rigcomm2 X a d) in r.
    apply (is2 _ _ _ _ r rcd).
Defined.


(** **** Subobjects *)

Lemma iscommrigcarrier {X : commrig} (A : @subrig X) : iscommrigops (@op1 A) (@op2 A).
Proof.
  intros. exists (isrigcarrier A).
  apply (pr2 (@isabmonoidcarrier (commrigmultabmonoid X) (rigmultsubmonoid A))).
Defined.

(* ??? slows down at the last [ apply ] and at [ Defined ] (oct.16.2011 - does
  not slow down anymore with two Dan's patches) *)

Definition carrierofasubcommrig {X : commrig} (A : @subrig X) : commrig :=
  make_commrig A (iscommrigcarrier A).


(** **** Quotient objects *)

Lemma iscommrigquot {X : commrig} (R : @rigeqrel X) :
  iscommrigops (@op1 (setwith2binopquot R)) (@op2 (setwith2binopquot R)).
Proof.
  intros. exists (isrigquot R).
  apply (pr2 (@isabmonoidquot  (commrigmultabmonoid X) (multmonoideqrel R))).
Defined.

Definition commrigquot {X : commrig} (R : @rigeqrel X) : commrig :=
  make_commrig (setwith2binopquot R) (iscommrigquot R).


(** **** Direct products *)

Lemma iscommrigdirprod (X Y : commrig) :
  iscommrigops (@op1 (setwith2binopdirprod X Y)) (@op2 (setwith2binopdirprod X Y)).
Proof.
  intros. exists (isrigdirprod X Y).
  apply (pr2 (isabmonoiddirprod (commrigmultabmonoid X) (commrigmultabmonoid Y))).
Defined.

Definition commrigdirprod (X Y : commrig) : commrig :=
  make_commrig (setwith2binopdirprod X Y) (iscommrigdirprod X Y).

(** **** Opposite commutative rigs *)

Local Open Scope rig.

(** We reuse much of the proof for general rigs *)
Definition opposite_commrig (X : commrig) : commrig :=
  (pr1 (X⁰),, (pr2 (X⁰) ,, λ x y, rigcomm2 X y x)).

(** Commutativity makes taking the opposite trivial *)
Definition iso_commrig_opposite (X : commrig) : rigiso X (opposite_commrig X).
Proof.
  refine ((idfun X,, idisweq X),, _).
  repeat split.
  unfold isbinopfun.
  exact (λ x y, rigcomm2 X x y).
Defined.

Local Close Scope rig.
