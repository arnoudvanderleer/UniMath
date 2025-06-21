Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.
(* Require Export UniMath.Combinatorics.FiniteSets. *)

(** ** Vectors *)

(** A [Vector] of length n with values in X is an ordered n-tuple of elements of X,
    encoded here as a function ⟦n⟧ → X. *)
Definition Vector (X : UU) (n : nat) : UU := stn n -> X.

(** hlevel of vectors *)
Lemma vector_hlevel (X : UU) (n : nat) {m : nat} (ism : isofhlevel m X) :
  isofhlevel m (Vector X n).
Proof.
  apply impred; auto.
Defined.

(** Constant vector *)
Definition const_vec {X : UU} {n : nat} (x : X) : Vector X n := λ _, x.

(** The unique empty vector *)
Definition iscontr_vector_0 X : iscontr (Vector X 0).
Proof.
  intros. apply (@iscontrweqb _ (empty -> X)).
  - apply invweq. apply weqbfun. apply weqstn0toempty.
  - apply iscontrfunfromempty.
Defined.

Definition empty_vec {X : UU} : Vector X 0 := iscontrpr1 (iscontr_vector_0 X).

(** Every type is equivalent to vectors of length 1 on that type. *)
Lemma weq_vector_1 {X : UU} : X ≃ Vector X 1.
  intermediate_weq (unit → X).
  - apply invweq, weqfunfromunit.
  - apply weqbfun.
    exact weqstn1tounit.
Defined.

Section Append.

  Context {X : UU} {n : nat} (vec : Vector X n) (x : X).

  Definition append_vec : Vector X (S n).
  Proof.
    intro i.
    induction (natlehchoice i n (stnlt i)) as [Hi | Hi].
    - refine (vec (make_stn _ _ Hi)).
    - exact x.
  Defined.

  Definition append_vec_compute_1 i : append_vec (dni lastelement i) = vec i.
  Proof.
    refine (maponpaths (coprod_rect _ _ _) (natlehchoice_lt _ (transportb (λ x, x < n) (di_eq1 (stnlt i)) (stnlt i))) @ _).
    apply (maponpaths vec).
    apply stn_eq.
    exact (di_eq1 (stnlt i)).
  Qed.

  Definition append_vec_compute_2 : append_vec lastelement = x.
  Proof.
    exact (maponpaths (coprod_rect _ _ _) (natlehchoice_eq _ (idpath n))).
  Qed.

  Definition stn_sn_ind
    {A : stn (S n) → UU}
    (Hx : ∏ i, A (dni lastelement i))
    (Hlast : A lastelement)
    : ∏ i, A i.
  Proof.
    intro i.
    induction (natlehchoice i n (stnlt i)) as [Hi | Hi].
    - refine (transportf A _ (Hx (make_stn _ _ Hi))).
      apply stn_eq.
      exact (di_eq1 Hi).
    - refine (transportf A _ Hlast).
      apply stn_eq.
      exact (!Hi).
  Defined.

  Lemma stn_sn_ind_dni
    {A : stn (S n) → UU}
    (Hx : ∏ i, A (dni lastelement i))
    (Hlast : A lastelement)
    (i : stn n)
    : stn_sn_ind Hx Hlast (dni lastelement i) = Hx i.
  Proof.
    refine (maponpaths (coprod_rect _ _ _) (natlehchoice_lt _ (transportb (λ x, x < n) (di_eq1 (stnlt i)) (stnlt i))) @ _).
    simple refine (
      maponpaths (λ e, transportf _ e _) _ @
      !functtransportf (dni lastelement) _ _ _ @
      transport_section Hx _).
    - apply isasetstn.
    - apply stn_eq.
      exact (di_eq1 (stnlt i)).
  Qed.

  Lemma stn_sn_ind_last
    {A : stn (S n) → UU}
    (Hx : ∏ i, A (dni lastelement i))
    (Hlast : A lastelement)
    : stn_sn_ind Hx Hlast lastelement = Hlast.
  Proof.
    refine (maponpaths (coprod_rect _ _ _) (natlehchoice_eq _ (idpath n)) @ _).
    refine (maponpaths (λ e, transportf _ e _) (_ : _ = idpath _)).
    apply isasetstn.
  Qed.

  Lemma append_vec_eq
    {g : stn (S n) → X}
    (Hf : ∏ i, g (dni lastelement i) = vec i)
    (Hlast : g lastelement = x)
    : g = append_vec.
  Proof.
    apply funextfun.
    refine (stn_sn_ind _ _).
    - intro i.
      refine (_ @ !append_vec_compute_1 _).
      apply Hf.
    - refine (_ @ !append_vec_compute_2).
      apply Hlast.
  Qed.

  Definition append_vec_dep
    {A : X → UU}
    (af : ∏ i, A (vec i))
    (alast : A x)
    : ∏ (i : stn (S n)), A (append_vec i).
  Proof.
    intro i.
    unfold append_vec.
    induction (natlehchoice i n (stnlt i)).
    - apply af.
    - apply alast.
  Defined.

End Append.

Arguments append_vec_eq {X n vec x g} Hf Hlast.
Arguments append_vec_dep {X n vec x A} af alast.

Lemma drop_and_append_vec {X n} (x : Vector X (S n)) :
  append_vec (x ∘ dni lastelement) (x lastelement) = x.
Proof.
  intros.
  apply funextfun.
  refine (stn_sn_ind _ _).
  + exact (append_vec_compute_1 _ _).
  + exact (append_vec_compute_2 _ _).
Defined.

Lemma append_and_drop_vec {X n} (xs : Vector X n) (x : X) :
  append_vec xs x ∘ dni lastelement = xs.
Proof.
  intros.
  apply funextsec.
  exact (append_vec_compute_1 _ _).
Qed.

(** An induction principle for vectors: If a statement is true for the empty
    vector, and if it is true for vectors of length n it is also true for those
    of length S n, then it is true for all vectors.
 *)
Definition Vector_rect' {X : UU} {P : ∏ n, Vector X n -> UU}
  (p0 : P 0 empty_vec)
  (ind : ∏ (n : nat) (vec : Vector X (S n)),
        P n (vec ∘ dni lastelement) -> P (S n) vec)
  {n : nat} (vec : Vector X n) : P n vec.
Proof.
  intros.
  induction n as [|n IH].
  - refine (transportf (P 0) _ p0).
    apply proofirrelevancecontr, iscontr_vector_0.
  - apply ind.
    apply IH.
Defined.

Lemma Vector_rect_empty' {X : UU} {P : ∏ n, Vector X n -> UU}
  (p0 : P 0 empty_vec)
  (ind : ∏ (n : nat) (vec : Vector X (S n)),
        P n (vec ∘ dni lastelement) -> P (S n) vec)
  : Vector_rect' p0 ind empty_vec = p0.
Proof.
  refine (maponpaths (λ e, transportf (P 0) e p0) (_ : _ = idpath _)).
  do 2 apply isapropifcontr.
  apply iscontr_vector_0.
Qed.

Lemma Vector_rect_append' {X : UU} {P : ∏ n, Vector X n -> UU}
  (p0 : P 0 empty_vec)
  (ind : ∏ (n : nat) (vec : Vector X (S n)),
        P n (vec ∘ dni lastelement) -> P (S n) vec)
  (x : X) {n : nat} (l : Vector X n)
  : Vector_rect' p0 ind (append_vec l x) = ind n (append_vec l x) (Vector_rect' p0 ind (append_vec l x ∘ dni lastelement)).
Proof.
  reflexivity.
Qed.

Definition Vector_rect {X : UU} {P : ∏ n, Vector X n -> UU}
  (p0 : P 0 empty_vec)
  (ind : ∏ (n : nat) (vec : Vector X n) (x : X),
        P n vec -> P (S n) (append_vec vec x))
  {n : nat} (vec : Vector X n) : P n vec.
Proof.
  refine (Vector_rect' p0 _ vec).
  clear n vec.
  intros n vec Hn.
  exact (transportf (P _) (drop_and_append_vec vec) (ind n (vec ∘ dni lastelement) (vec lastelement) Hn)).
Defined.

Lemma Vector_rect_empty {X : UU} {P : ∏ n, Vector X n -> UU}
  (p0 : P 0 empty_vec)
  (ind : ∏ (n : nat) (vec : Vector X n) (x : X),
        P n vec -> P (S n) (append_vec vec x))
  : Vector_rect p0 ind empty_vec = p0.
Proof.
  apply Vector_rect_empty'.
Qed.

(* The current proof needs X to be an hSet, because it uses the fact that Vector X n is a set *)
Lemma Vector_rect_append {X : UU} (HX : isaset X) {P : ∏ n, Vector X n -> UU}
  (p0 : P 0 empty_vec)
  (ind : ∏ (n : nat) (vec : Vector X n) (x : X),
        P n vec -> P (S n) (append_vec vec x))
  (x : X) {n : nat} (l : Vector X n)
  : Vector_rect p0 ind (append_vec l x) = ind n l x (Vector_rect p0 ind l).
Proof.
  refine (_ @ transport_section (λ (l : Vector X n), ind n l x (Vector_rect p0 ind l)) (append_and_drop_vec l x)).
  refine (_ @ !functtransportf (λ l, append_vec l x) _ _ _).
  apply transportf_transpose_right.
  refine (_ @ transport_section (λ (a : X), ind n (append_vec l x ∘ dni lastelement) a (Vector_rect p0 ind (append_vec l x ∘ dni lastelement))) (append_vec_compute_2 l x)).
  refine (_ @ !functtransportf (λ x, append_vec _ x) _ _ _).
  refine (transport_f_f _ _ _ _ @ _).
  refine (maponpaths (λ x, transportf _ x _) _).
  refine (proofirrelevance _ ((_ : isaset _) _ _) _ _).
  apply funspace_isaset.
  exact HX.
Qed.

Section Lemmas.

  Context {X : UU} {n : nat}.

  Definition vectorEquality {m : nat} (f : Vector X n) (g : Vector X m) (p : n = m) :
    (∏ i, f i = g (transportf stn p i))
    -> transportf (Vector X) p f = g.
  Proof.
    intro.
    induction p.
    apply funextfun.
    assumption.
  Defined.

  Definition tail (vecsn : Vector X (S n)) : Vector X n :=
    vecsn ∘ dni (0,, natgthsn0 n).

  (** It doesn't matter what the proofs are in the stn inputs. *)
  Definition vector_stn_proofirrelevance {vec : Vector X n}
            {i j : stn n} : (stntonat _ i = stntonat _ j) -> vec i = vec j.
  Proof.
    intro.
    apply maponpaths, isinjstntonat; assumption.
  Defined.
End Lemmas.
