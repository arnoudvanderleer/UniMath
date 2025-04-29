(** * Algebra I. Part D.  Rigs and rings. Vladimir Voevodsky. Aug. 2011 - . *)
Require Import UniMath.Algebra.Groups.
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
Require Export UniMath.Algebra.Monoids.
Require Export UniMath.Algebra.Rigs.

Local Open Scope logic.

(** *** Commutative rigs *)

(** **** General definitions *)

Definition commrig : UU := ∑ (X : setwith2binop), iscommrigops (@op1 X) (@op2 X).

Definition make_commrig (X : setwith2binop) (is : iscommrigops (@op1 X) (@op2 X)) : commrig :=
  X ,, is.

Definition commrigconstr {X : hSet} (opp1 opp2 : binop X)
           (ax11 : ismonoidop opp1) (ax12 : iscomm opp1)
           (ax2 : ismonoidop opp2) (ax22 : iscomm opp2)
           (m0x : ∏ x : X, opp2 (unel_is ax11) x = unel_is ax11)
           (mx0 : ∏ x : X, opp2 x (unel_is ax11) = unel_is ax11)
           (dax : isdistr opp1 opp2) : commrig.
Proof.
  intros. exists  (make_setwith2binop X (opp1 ,, opp2)).
  split.
  - split.
    + exists ((ax11 ,, ax12) ,, ax2).
      apply (m0x ,, mx0).
    + apply dax.
  - apply ax22.
Defined.

Definition commrigtorig : commrig → rig := λ X, @make_rig (pr1 X) (pr1 (pr2 X)).
Coercion commrigtorig : commrig >-> rig.

Definition rigcomm2 (X : commrig) : iscomm (@op2 X) := pr2 (pr2 X).

Definition commrigop2axs (X : commrig) : isabmonoidop (@op2 X) :=
  rigop2axs X ,, rigcomm2 X.

Definition commrigmultabmonoid (X : commrig) : abmonoid :=
  make_abmonoid (make_setwithbinop X op2) (rigop2axs X ,, rigcomm2 X).


(** **** (X = Y) ≃ (rigiso X Y)
    We use the following composition

                          (X = Y) ≃ (make_commrig' X = make_commrig' Y)
                                  ≃ ((pr1 (make_commrig' X)) = (pr1 (make_commrig' Y)))
                                  ≃ (rigiso X Y)

    where the third weak equivalence uses univalence for rigs, [rig_univalence]. We define
    [commrig'] to be able to apply it.
 *)

Local Definition commrig' : UU :=
  ∑ D : (∑ X : setwith2binop, isrigops (@op1 X) (@op2 X)), iscomm (@op2 (pr1 D)).

Local Definition make_commrig' (CR : commrig) : commrig' :=
  (pr1 CR ,, dirprod_pr1 (pr2 CR)) ,, (dirprod_pr2 (pr2 CR)).

Definition commrig_univalence_weq1 : commrig ≃ commrig' :=
  weqtotal2asstol
    (λ X : setwith2binop, isrigops (@op1 X) (@op2 X))
    (λ y : (∑ (X : setwith2binop), isrigops (@op1 X) (@op2 X)), iscomm (@op2 (pr1 y))).

Definition commrig_univalence_weq1' (X Y : commrig) : (X = Y) ≃ (make_commrig' X = make_commrig' Y) :=
  make_weq _ (@isweqmaponpaths commrig commrig' commrig_univalence_weq1 X Y).

Definition commrig_univalence_weq2 (X Y : commrig) :
  ((make_commrig' X) = (make_commrig' Y)) ≃ ((pr1 (make_commrig' X)) = (pr1 (make_commrig' Y))).
Proof.
  use subtypeInjectivity.
  intros w. use isapropiscomm.
Defined.
Opaque commrig_univalence_weq2.

Definition commrig_univalence_weq3 (X Y : commrig) :
  ((pr1 (make_commrig' X)) = (pr1 (make_commrig' Y))) ≃ (rigiso X Y) :=
  rig_univalence (pr1 (make_commrig' X)) (pr1 (make_commrig' Y)).

Definition commrig_univalence_map (X Y : commrig) : (X = Y) → (rigiso X Y).
Proof.
  intros e. induction e. exact (idrigiso X).
Defined.

Lemma commrig_univalence_isweq (X Y : commrig) : isweq (commrig_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (commrig_univalence_weq1' X Y)
                   (weqcomp (commrig_univalence_weq2 X Y) (commrig_univalence_weq3 X Y))).
  - intros e. induction e.
    refine (weqcomp_to_funcomp_app @ _).
    exact weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque commrig_univalence_isweq.

Definition commrig_univalence (X Y : commrig) : (X = Y) ≃ (rigiso X Y)
  := make_weq
  (commrig_univalence_map X Y)
  (commrig_univalence_isweq X Y).


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
