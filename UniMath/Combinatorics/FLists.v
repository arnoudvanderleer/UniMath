(** * Finite sequences

Vectors and matrices defined in March 2018 by Langston Barrett (@siddharthist).
 *)

(** ** Contents

  - Vectors
  - Matrices
  - Lists
    - Definitions
    - Lemmas

 *)

Require Export UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.FVectors.

Require Import UniMath.MoreFoundations.All.

Local Open Scope transport.


(** ** Lists *)

(** *** Definitions *)

(** A [list] is a [vector] of any length. *)
Definition list (X : UU) : UU := ∑ n, vector X n.

Definition length {X : UU} (xs : list X) : nat := pr1 xs.

Definition list_to_function {X : UU} (xs : list X) : stn (length xs) → X := pr2 xs.

Coercion list_to_function : list >-> Funclass.

Definition make_list {X : UU} {n : nat} (f : stn n → X) : list X := (n ,, f).

Lemma list_hlevel (X : UU) {m : nat} (ism : isofhlevel (S (S m)) X)
  : isofhlevel (S (S m)) (list X).
Proof.
  apply isofhleveltotal2.
  - clear ism.
    induction m.
    + exact isasetnat.
    + apply hlevelntosn.
      exact IHm.
  - intro n.
    exact (vector_hlevel _ _ ism).
Qed.


Definition nonempty_list (X : UU) : UU := ∑ n, vector X (S n).

Definition length' {X : UU} (x : nonempty_list X) : nat := S (pr1 x).

Definition nonempty_list_to_function {X : UU} (x : nonempty_list X) : stn (length' x) → X := pr2 x.

Coercion nonempty_list_to_function : nonempty_list >-> Funclass.

Coercion nonempty_list_to_list {X : UU} (x : nonempty_list X) : list X := make_list x.

Definition make_nonempty_list {X : UU} {n : nat} (xs : vector X (S n)) : nonempty_list X := (n ,, xs).

Definition nonempty_list'
  (X : UU)
  : UU
  := ∑ (xs : list X), length xs != 0.

Definition make_nonempty_list'
  {X : UU}
  (xs : list X)
  (H : length xs != 0)
  : nonempty_list' X
  := xs ,, H.

Definition nonempty_list'_eq
  {X : UU}
  (xs ys : nonempty_list' X)
  (H : pr1 xs = pr1 ys)
  : xs = ys
  := subtypePath (λ _, isapropneg _) H.

Definition nonempty_list_weq
  (X : UU)
  : nonempty_list' X ≃ nonempty_list X.
Proof.
  use weq_iso.
  - intro xs.
    induction xs as [xs Hxs].
    induction xs as [n xs].
    induction n as [| n IHn].
    + exact (fromempty (Hxs (idpath 0))).
    + exact (make_nonempty_list xs).
  - intro xs.
    exact (make_nonempty_list' xs (negpathssx0 _)).
  - abstract (
      intro xs;
      induction xs as [xs Hxs];
      induction xs as [n xs];
      apply nonempty_list'_eq;
      induction n as [|n IHn];
      [ exact (fromempty (Hxs (idpath 0)))
      | reflexivity ]
    ).
  - reflexivity.
Defined.


Definition unordered_list (X : UU) : UU := ∑ (I : FiniteSet), I → X.

Definition unordered_list_to_function {X : UU} (x : unordered_list X) : pr1 (pr1 x) → X := pr2 x.

Coercion unordered_list_to_function : unordered_list >-> Funclass.

Definition list_to_unordered_list {X : UU} (x : list X) : unordered_list X.
Proof.
  exists (standardFiniteSet (length x)).
  exact x.
Defined.

Coercion list_to_unordered_list : list >-> unordered_list.

Definition make_unordered_list {X : UU} {I : FiniteSet} (f : I → X) : unordered_list X := (I ,, f).


Section Accessors.

  Context {X : UU}.
  Context (xs : list X).
  Context (Hxs : length xs != 0).

  Let xs' : nonempty_list X := nonempty_list_weq X (xs ,, Hxs).

  Definition last : X := last xs'.
  Definition init : list X := make_list (init xs').

  Definition head : X := head xs'.
  Definition tail : list X := make_list (tail xs').

End Accessors.

Definition const_list {X : UU} (n : nat) (x : X) : list X := make_list (const_vec (n := n) x).

Section NilSnoc.

  Context {X : UU}.

  Definition nil : list X := make_list nil.

  Definition nil_length (x : list X) : length x = 0 <-> x = nil.
  Proof.
    split.
    - intro e.
      induction x as [n x].
      induction (!e : 0 = n).
      apply pair_path_in2.
      apply uniqueness.
    - intro h.
      exact (maponpaths _ h).
  Defined.

  Definition snoc (xs : list X) (x : X) : list X := make_list (snoc xs x).

  Lemma length_snoc (xs : list X) (x : X)
    : length (snoc xs x) = S (length xs).
  Proof.
    reflexivity.
  Defined.

  Lemma init_snoc (xs : list X) (x : X)
    : init (snoc xs x) (negpathssx0 _) = xs.
  Proof.
    apply pair_path_in2, init_snoc.
  Qed.

  Lemma last_snoc (xs : list X) (x : X)
    : last (snoc xs x) (negpathssx0 _) = x.
  Proof.
    apply last_snoc.
  Qed.

  Lemma snoc_init_last (xs : list X) (Hxs : length xs != 0)
    : snoc (init xs Hxs) (last xs Hxs) = xs.
  Proof.
    refine (_ @ base_paths _ _ (homotinvweqweq (nonempty_list_weq X) (make_nonempty_list' _ Hxs))).
    apply pair_path_in2, snoc_init_last.
  Qed.

End NilSnoc.

Local Notation "s □ x" := (snoc s x) (at level 64, left associativity).

Section Recursion.

  Context {X : UU}.
  Context {P : UU}.
  Context (p_nil : P).
  Context (p_snoc : P → X → P).

  Definition list_rect
    (xs : list X)
    : P
    := vector_rect (P := λ n, P) p_nil (λ n Hx x, p_snoc Hx x) _ xs.

  Definition list_rect_nil
    : list_rect nil = p_nil
    := vector_rect_nil _ _.

  Definition list_rect_snoc
    (xs : list X)
    (x : X)
    : list_rect (snoc xs x) = p_snoc (list_rect xs) x
    := vector_rect_snoc p_nil (λ n, p_snoc) x xs.

End Recursion.

Section Induction.

  Context {X : UU}.
  Context {P : list X →UU}.
  Context (p_nil : P nil).
  Context (p_snoc : ∏ (xs : list X), P xs → ∏ (x : X), P (snoc xs x)).

  Definition list_ind
    (xs : list X)
    : P xs
    := vector_ind (P := λ n xs, P (make_list xs)) p_nil (λ n xs Hx x, p_snoc (make_list xs) Hx x) _ xs.

  Definition list_ind_nil
    : list_ind nil = p_nil
    := vector_ind_nil _ _.

  Definition list_ind_snoc
    (HX : isaset X)
    (xs : list X)
    (x : X)
    : list_ind (snoc xs x) = p_snoc xs (list_ind xs) x
    := vector_ind_snoc _ _ HX x xs.

End Induction.

(** *** Lemmas *)

Section Equality.

  Context {X : UU}.
  Context {xs ys : list X}.
  Context (e_len : length xs = length ys).

  Definition list_eq
    (e_el : ∏ i, xs i = ys (transportf stn e_len i))
    : xs = ys
    := total2_paths_f e_len (vector_eq e_len e_el).

  Definition list_eq'
    (e_el : ∏ i ltxs ltys, xs (make_stn _ i ltxs) = ys (make_stn _ i ltys))
    : xs = ys
    := total2_paths_f e_len (vector_eq' e_len e_el).

  Definition list_eq''
    (e_el : ∏ i, ∑ ltxs ltys, xs (make_stn _ i ltxs) = ys (make_stn _ i ltys))
    : xs = ys
    := total2_paths_f e_len (vector_eq'' e_len e_el).

End Equality.

Section ListAssembly.

  Context {X : UU}.

  Definition disassemble_list : list X → unit ⨿ (list X × X).
  Proof.
    intros xs.
    induction xs as [n xs].
    induction n as [| n].
    - exact (ii1 tt).
    - exact (ii2 (make_list (FVectors.init xs) ,, FVectors.last xs)).
  Defined.

  Definition assemble_list : unit ⨿ (list X × X) → list X.
  Proof.
    intros co.
    induction co as [t | p].
    - exact nil.
    - exact (snoc (pr1 p) (pr2 p)).
  Defined.

  Theorem list_assembly : list X ≃ unit ⨿ (list X × X).
  Proof.
    apply (weq_iso disassemble_list assemble_list).
    - abstract (
        intro xs;
        induction xs as [n xs];
        induction n as [| n];
        [ apply pair_path_in2;
          exact (!uniqueness _ _)
        | exact (snoc_init_last (make_list xs) (negpathssx0 n)) ]
      ).
    - abstract (
        intro co;
        induction co as [t | p];
        [ now induction t
        | induction p as [int lst];
          apply (maponpaths ii2);
          apply pathsdirprod;
          [ apply init_snoc
          | apply last_snoc ] ]
      ).
  Defined.

End ListAssembly.

Section Concatenate.

  Context {X : UU}.

  Definition concatenate (xs ys : list X) : list X
    := make_list (concatenate xs ys).

  Lemma concatenate_length
    (xs ys : list X)
    : length (concatenate xs ys) = length xs + length ys.
  Proof.
    reflexivity.
  Qed.

  Lemma concatenate_0r
    (xs ys : list X)
    (H : length ys = 0)
    : concatenate xs ys = xs.
  Proof.
    induction (!pr1 (nil_length _) H).
    refine (list_eq (natplusr0 _ : length (concatenate xs nil) = _) _).
    intro i.
    apply concatenate_0r'.
  Qed.

  Lemma concatenate_0l
    (xs ys : list X)
    (H : length xs = 0)
    : concatenate xs ys = ys.
  Proof.
    induction (!pr1 (nil_length _) H).
    apply (list_eq (idpath _ : length (concatenate nil ys) = length ys)).
    apply concatenate_0l'.
  Qed.

  Lemma concatenate_snoc
    (xs ys : list X)
    (y : X)
    : concatenate xs (snoc ys y) = snoc (concatenate xs ys) y.
  Proof.
    use total2_paths_b.
    - apply natplusnsm.
    - apply concatenate_snoc.
  Qed.

  Lemma concatenate_is_foldl
    (xs ys : list X)
    : concatenate xs ys = foldl snoc xs ys.
  Proof.
    revert ys.
    refine (list_ind _ _).
    - now apply concatenate_0r.
    - intros ys Hys y.
      refine (concatenate_snoc _ _ _ @ _).
      refine (_ @ !foldl_snoc _ _ _ _).
      now apply maponpaths_2.
  Qed.

  Lemma nonempty_list_weq_concatenate
    (xs ys : list X)
    (Hys : length ys != 0)
    : nonempty_list_weq X (make_nonempty_list' (concatenate xs ys) (Hys ∘ plusmn0n0 _ _))
      = make_nonempty_list (transportf (vector X) (natplusnsm _ _)
          (FVectors.concatenate xs (nonempty_list_weq X (make_nonempty_list' ys Hys)))).
  Proof.
    pose (ys' := invmap (nonempty_list_weq _) (nonempty_list_weq _ (make_nonempty_list' ys Hys))).
    refine (maponpaths (nonempty_list_weq X)
        (_ : _ = make_nonempty_list' (concatenate xs (pr1 ys')) (pr2 ys' ∘ plusmn0n0 _ _)) @ _).
    - apply nonempty_list'_eq.
      apply (maponpaths (concatenate xs)).
      exact (base_paths (make_nonempty_list' ys Hys) _ (!homotinvweqweq _ _)).
    - apply pathsweq1'.
      apply nonempty_list'_eq.
      now refine (total2_paths_f _ _).
  Qed.

  Lemma init_concatenate
    (xs ys : list X)
    (Hys : length ys != 0)
    : init (concatenate xs ys) (Hys ∘ plusmn0n0 _ _) = concatenate xs (init ys Hys).
  Proof.
    refine (maponpaths (λ (x : nonempty_list _), make_list (FVectors.init x))
        (nonempty_list_weq_concatenate _ _ _) @ _).
    apply (maponpaths make_list).
    apply init_concatenate.
  Qed.

  Lemma last_concatenate
    (xs ys : list X)
    (Hys : length ys != 0)
    : last (concatenate xs ys) (Hys ∘ plusmn0n0 _ _) = last ys Hys.
  Proof.
    refine (maponpaths (λ (x : nonempty_list _), FVectors.last x)
        (nonempty_list_weq_concatenate _ _ _) @ _).
    apply last_concatenate.
  Qed.

  Definition concatenate_step
    (xs ys : list X)
    (Hy : length ys != 0)
    : concatenate xs ys = snoc (concatenate xs (init ys Hy)) (last ys Hy).
  Proof.
    refine (!maponpaths (λ t, concatenate xs (pr1 t)) (homotinvweqweq (nonempty_list_weq X) (ys ,, Hy)) @ _).
    use total2_paths_b.
    - apply natplusnsm.
    - apply concatenate_step.
  Defined.

  Definition isassoc_concatenate
    (xs ys zs : list X)
    : concatenate (concatenate xs ys) zs = concatenate xs (concatenate ys zs).
  Proof.
    use total2_paths_b.
    - apply natplusassoc.
    - apply isassoc_concatenate.
  Qed.

End Concatenate.

Definition map {X Y : UU} (f : X → Y) (xs : list X) : list Y := make_list (map f xs).

Definition map_unordered_list {X Y : UU} (f : X → Y) (xs : unordered_list X) : unordered_list Y
  := make_unordered_list (f ∘ xs).

Definition reindex {X : UU} (xs : list X) (f : list (stn (length xs))) : list X
  := make_list (reindex xs f).

Definition flatten {X : UU} (x : list (list X))
  : list X
  := make_list (flatten (list_to_function ∘ x)).

Definition flatten_unordered_list
  {X : UU}
  (xs : unordered_list (unordered_list X))
  : unordered_list X.
Proof.
  use tpair.
  - exact ((∑ i, pr1 (xs i))%finset).
  - exact (uncurry (unordered_list_to_function xs)).
Defined.

Definition flatten_step
  {X : UU}
  (xs : nonempty_list (list X))
  : flatten xs
    = concatenate (flatten (reindex xs (make_list (dni lastelement)))) (last xs (negpathssx0 _)).
Proof.
  intros.
  apply pair_path_in2.
  exact (flatten_step _ (λ i j, xs i j)).
Defined.

(* partitions *)

Definition partition
  {X : UU}
  (f : list nat)
  (x : vector X (stnsum f))
  : list (list X).
Proof.
  refine (make_list _).
  intro i.
  refine (make_list _).
  exact (partition f x i).
Defined.

Definition flatten_partition
  {X : UU}
  (f : list nat)
  (x : vector X (stnsum f))
  : flatten (partition f x) = make_list x.
Proof.
  apply pair_path_in2.
  apply funextfun.
  exact (flatten_partition f x).
Defined.

(* Work from here *)

(** Reverse *)

Definition reverse
  {X : UU}
  (xs : list X)
  : list X
  := make_list (reverse xs).

Lemma reverse_reverse
  {X : UU}
  (x : list X)
  : reverse (reverse x) = x.
Proof.
  apply pair_path_in2.
  apply reverse_reverse.
Qed.
