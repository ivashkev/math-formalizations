(* 

 AN EXAMPLE FORMAL VERIFICATION OF SORT FUNCTION

 Evgeny V Ivashkevich
 
 E-mail: ivashkev@yandex.ru

 January 29, 2019

 Abstract: In this file we give a simple example of a verified programming 
           style. We first give an example of unsecure programming, and then 
           demonstrate the Coq tools to validate the specifications of 
           the programs.
 
*)

Require Import Arith.
Notation " x << y " := (le_lt_dec x y) (at level 60).
Notation " x == y " := (eq_nat_dec x y) (at level 60).

Require Import List.
Import ListNotations.

Module Unsafe.

(* Example of unsafe programming *)

Fixpoint Insert (n : nat) (x : list nat) : list nat :=
  match x with
    | [] => [n]
    | h :: t => if (n << h) 
                     then (h :: n :: t) 
                     else (h :: Insert n t)
  end. 

Fixpoint Sort (x : list nat) : list nat :=
  match x with
    | [] => []
    | h :: t => Insert h (Sort t)
  end. 

Compute (Sort [ 10; 9; 8; 7; 6; 5; 4; 3; 2; 1; 0 ]).
(*     = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10] *)
Compute (Sort [ 1; 0; 6; 4; 9; 2; 10; 7; 5; 3; 8 ]).
(* oops! somthing goes wrong! *)
(*     = [8; 1; 0; 6; 4; 2; 7; 5; 3; 10; 9] *)
Compute (Sort [ 4; 7; 3; 9; 8; 5; 0; 10; 1; 6; 2 ]).
(*     = [2; 0; 1; 6; 4; 3; 5; 10; 7; 9; 8] *)

End Unsafe.

(** To proceed further to safe programming we need to create macro-language
 to program our specifications. In this example the macro-language will
 include just two new terms - "Ordered" and "Permutation". *)

(* Definition of Ordered list *)

Inductive Ordered : list nat -> Prop :=
  | Ord0 : Ordered []
  | Ord1 (n : nat) : Ordered [n]
  | Ord2 (n m : nat) (x : list nat) : 
      n <= m -> Ordered (m :: x) -> Ordered (n :: m :: x).

Lemma OrderedTail :
  forall (n : nat) (x : list nat), 
  Ordered (n :: x) -> Ordered x.
Proof.
 intros n x H.
 destruct x as [ | h t ].
 - apply Ord0.
 - inversion H; subst; assumption.
Qed.

(* Count function  and its properties*)

Fixpoint Count (n : nat) (x : list nat) : nat :=
  match x with
  | [ ] => 0
  | m :: y => if (n == m) 
                     then S (Count n y)
                     else Count n y
  end.

Lemma Count_cons_eq (n : nat) (x : list nat) :
  Count n (n :: x)  = S (Count n x).
Proof.
  simpl. 
  destruct (eq_nat_dec n n).
  - reflexivity.
  - now elim n0.
Qed.

Lemma Count_cons_neq (n m : nat) (x : list nat)  :
  n <> m -> Count n (m :: x)  = Count n x.
Proof.
  intros H. simpl.
  destruct (eq_nat_dec n m); subst.
  - now elim H.
  - reflexivity.
  Qed.

Theorem Count_inv_nil (x : list nat) :
  (forall n : nat, Count n x = 0) <-> x = [].
Proof.
  split.
  destruct x as [ | h t ]; trivial.
  { intros H. specialize (H h). simpl in H.
    destruct (h == h) as [ H1 | H2 ].
    - discriminate.
    - now elim H2.
  }
  { now intros ->. }
Qed.

Theorem Ord_count :
  forall (n h : nat) (t : list nat),
  Ordered (h :: t)
    -> n < h
    -> Count n t = 0. 
Proof.
  intros n h t oht nh.
  induction t as [ | m t ]; simpl; auto.
  { destruct ( n == m ) as [ H1 | H2 ]; subst; simpl. 
    { destruct ( m == m ) as [ H3 | H4 ]; subst; simpl.
      { inversion oht; subst.
        apply (le_lt_trans h m h H1) in nh. 
        apply lt_irrefl in nh. contradiction.
      }
      { now elim H4. }
    }
    { destruct ( n == m ) as [ H3 | H4 ]; subst; simpl. 
      { now elim H2. }
      { apply IHt. clear dependent n.
        destruct t as [ | k t ].
        { apply Ord1. }
        { inversion oht; subst.
          inversion H3; subst.  
          apply Ord2; try assumption.
          apply (le_trans h m k); assumption.
        }
      }
    }
  }
Qed.

(* Definition of Permutation equivalence *)

Definition Permutation (x y : list nat) : Prop 
  := forall n : nat, Count n x = Count n y.
  Notation " x ~ y " := (Permutation x y) (at level 60).

Lemma Perm_refl : forall x : list nat, x ~ x.
Proof.
  unfold Permutation; trivial.
Qed.
Lemma Perm_sym : forall x y : list nat, x ~ y -> y ~ x.
Proof.
  unfold Permutation. 
  intros; symmetry; apply (H n).
Qed.
Lemma Perm_trans :
 forall x y z : list nat, x ~ y -> y ~ z -> x ~ z.
Proof.
  unfold Permutation.
  intros x y z H H0 n. 
  rewrite (H n). apply (H0 n).
Qed.
Add Parametric Relation : (list nat) Permutation
  reflexivity proved by Perm_refl
  symmetry proved by Perm_sym
  transitivity proved by Perm_trans 
as ListPermutSetoid.

Lemma Perm_skip :
  forall (n : nat) (x y : list nat), 
  x ~ y <-> (n :: x) ~ (n :: y).
Proof.
  unfold Permutation.
  split.
  { intros H m. 
    case (eq_nat_dec m n).
    { intros; subst. 
      rewrite Count_cons_eq. 
      rewrite Count_cons_eq.
      rewrite (H n); reflexivity.
    } 
    { intros mn.
      rewrite Count_cons_neq; try assumption.
      rewrite Count_cons_neq; try assumption.
      rewrite (H m); reflexivity.
    } 
  }
  { intros H m. 
    case (eq_nat_dec m n). 
    { intros; subst. 
      specialize (H n).
      rewrite Count_cons_eq in H. 
      rewrite Count_cons_eq in H. 
      inversion H. reflexivity.
    }
    { intros mn.
     specialize (H m).
     rewrite Count_cons_neq in H; try assumption. 
     rewrite Count_cons_neq in H; try assumption. 
   }
 }
Qed.

Lemma Perm_swap :
  forall (n m : nat) (x : list nat),
  (n :: m :: x) ~ (m :: n :: x).
Proof.
  intros n m x k.
  case (eq_nat_dec k n); case (eq_nat_dec k m); 
  intros H1 H2; repeat subst; try reflexivity. 
  { rewrite Count_cons_eq.
    rewrite Count_cons_neq; try assumption.
    rewrite Count_cons_neq; try assumption. 
    rewrite Count_cons_eq; reflexivity.
  } 
  { rewrite Count_cons_neq; try assumption. 
    rewrite Count_cons_eq.
    rewrite Count_cons_eq.
    rewrite Count_cons_neq; try assumption. 
    reflexivity.
  }
  { rewrite Count_cons_neq; try assumption. 
    rewrite Count_cons_neq; try assumption.
    rewrite Count_cons_neq; try assumption. 
    rewrite Count_cons_neq; try assumption.
    reflexivity.
  }
Qed.

Theorem Perm_ord_eq :
  forall (x y : list nat),
  x ~ y 
    -> Ordered x 
    -> Ordered y 
    -> x = y.
Proof.
  intros x.
  induction x as [| hx tx ].
  { intros y epy oe oy.
    symmetry. unfold Permutation in epy. 
    apply -> Count_inv_nil. intros k. specialize (epy k). 
    rewrite <- epy. symmetry; auto.
  } 
  { intros y xy oax oy. 
    destruct y as [ | hy ty ]. apply -> Count_inv_nil. auto.
    specialize (IHtx ty).
    destruct (lt_eq_lt_dec hx hy) as [ [ H1 | H2 ] | H3 ].
    { specialize (xy hx).
      assert (H5 : Count hx ty = 0). { apply (Ord_count hx hy ty); auto. }
      assert (H6 : Count hx (hy :: ty) = 0). 
      { unfold Count.
        destruct ( hx == hy ) as [ H3 | H4 ]; subst; auto.
        { apply lt_irrefl in H1. contradiction. }
      }
      rewrite H6 in xy. simpl in xy.
      destruct ( hx == hx ) as [ H3 | H4 ]; subst.
      { discriminate. }
      { now elim H4. }
    }
    { subst.
      apply Perm_skip in xy.
      apply IHtx in xy; subst; auto. 
      apply (OrderedTail hy tx oax).
      apply (OrderedTail hy ty oy).
    }
    { specialize (xy hy).
      assert (H5 : Count hy tx = 0). { apply (Ord_count hy hx tx); auto. }
      assert (H6 : Count hy (hx :: tx) = 0).
      { unfold Count.
        destruct ( hy == hx ) as [ H1 | H2 ]; subst. 
        apply lt_irrefl in H3. contradiction. assumption.
      }
      rewrite H6 in xy. simpl in xy.
      destruct ( hy == hy ) as [ H1 | H2 ]; subst.
      { discriminate. }
      { now elim H2. }
    }
  }
Qed.

(* Safe Programming *)

Module FuncSpec.

(* Version 1 - we first write function and then prove its properies. *)

Fixpoint Insert (n : nat) (x : list nat) : list nat :=
  match x with
    | [] => [n]
    | h :: t => if (n << h) 
                     then (n :: h :: t) 
                     else (h :: Insert n t)
  end. 

Lemma Perm_insert : 
  forall (x : list nat) (n : nat), 
  (n :: x) ~ (Insert n x).
Proof.
 induction x as [|n y H]; simpl.
 { intro; reflexivity. } 
 { intros m; case (le_lt_dec m n); simpl.
   { intro; reflexivity. } 
   { intro; apply Perm_trans with (n :: m :: y). apply Perm_swap. 
     specialize (H m). apply Perm_skip; assumption.
   }
 }
Qed.

Lemma Ord_insert :
  forall (x : list nat) (n : nat), 
  Ordered x -> Ordered (Insert n x).
Proof.
  intros x n H. 
  elim H; simpl. 
  { apply Ord1. }
  { intro m.
    case (le_lt_dec n m); simpl. 
    { intro nm. apply Ord2; try assumption. apply Ord1. }
    { intro mn. apply Ord2; try assumption. firstorder. apply Ord1. }
  }
  { intros n1 n2 y.
    case (le_lt_dec n n2); simpl; intros; case (le_lt_dec n n1); simpl. 
    { intro nn1. apply Ord2; try assumption. apply Ord2; try assumption. }
    { intro nn1. apply Ord2; try assumption. firstorder. }
    { intro nn1. apply Ord2; try assumption. apply Ord2; try assumption. }
    { intro nn1. apply Ord2; try assumption. }
  }
Qed.

Fixpoint Sort (x : list nat) : list nat :=
  match x with
    | [] => []
    | h :: t => Insert h (Sort t)
  end. 

Lemma PermutationSort : 
  forall (x : list nat), 
  x ~ Sort x.
Proof.
  intros x.
  induction x as [ | n y H ]; simpl; try reflexivity. 
  assert ( H1 : Insert n (Sort y) ~ Insert n y). 
  { rewrite <- (Perm_insert y n). 
    rewrite <- (Perm_insert (Sort y) n).
    apply Perm_skip. symmetry; auto.
  }
  rewrite H1. apply Perm_insert.
Qed.

Lemma OrderedSort :
  forall (x : list nat), 
  Ordered (Sort x).
Proof.
  intros x. 
  induction x as [ | n x H ]; simpl. 
  - apply Ord0.
  - apply Ord_insert; auto. 
Qed.

End FuncSpec.

Require Import Program.

Module ProgSpec.

(* Version 2 - we first declare function specifications 
and then prove all the obligations. *)

Program Fixpoint Insert (n : nat) (x : list nat) : 
  { y : list nat | y ~ (n :: x) /\ (Ordered x -> Ordered y) } :=
  match x with
    | [] => [n]
    | h :: t => if (n << h) 
                     then (n :: h :: t) 
                     else (h :: Insert n t)
  end. 

Obligation 1 of Insert.
Proof. 
 split; try reflexivity. 
 intros H. apply Ord1.
Qed.

Obligation 2 of Insert.
Proof.
  split; try reflexivity. 
  intros oht. apply Ord2; assumption.
Qed.

Obligation 3 of Insert.
Proof.
  destruct x0 as [ | m x ].
  { specialize (p n). simpl in p. 
    destruct ( n == n ) as [ H1 | H2 ].
    - discriminate.
    - now elim H2.
  }
  split.
  { symmetry. rewrite Perm_swap. apply Perm_skip. symmetry. assumption. }
  { intros ht. 
    assert ( ot : Ordered t). { apply (OrderedTail h t ht). }
    specialize (o ot).
    apply Ord2; try assumption. 
    destruct (le_lt_dec n m). 
    { apply (le_trans h n m); try assumption; auto with arith. }
    { destruct (le_lt_dec h m); try assumption. 
      assert (cmt : Count m t = 0). { apply (Ord_count m h t); assumption. }
      assert (cmnt : Count m (n :: t) = 0).
      { unfold Count.
        destruct ( m == n ) as [ H3 | H4 ]; subst; auto.
        { apply lt_irrefl in l. contradiction. }
      }
      specialize (p m). rewrite cmnt in p. simpl in p.
      destruct ( m == m ) as [ H3 | H4 ]; subst. 
      - discriminate. 
      - now elim H4.
    }
  } 
Defined.

Lemma Perm_insert : 
  forall (x : list nat) (n : nat), 
  (n :: x) ~ proj1_sig (Insert n x).
Proof.
 induction x as [|n y H]; simpl.
 { intro; reflexivity. } 
 { intros m; 
   case (le_lt_dec m n); simpl. 
   { intro; reflexivity. } 
   { intro; apply Perm_trans with (n :: m :: y). apply Perm_swap.
     specialize (H m). apply Perm_skip; assumption.
   }
 }
Qed.

Lemma Ord_insert :
  forall (x : list nat) (n : nat), 
  Ordered x -> Ordered (proj1_sig (Insert n x)).
Proof.
  intros x n H. 
  elim H; simpl. 
  { apply Ord1. }
  { intro m.
    case (le_lt_dec n m); simpl. 
    { intro nm. apply Ord2; try assumption. apply Ord1. }
    { intro mn. apply Ord2; try assumption. firstorder. apply Ord1. }
  }
  { intros n1 n2 y.
    case (le_lt_dec n n1); simpl.
    { case (le_lt_dec n n2); simpl.
      { intros. apply Ord2; try assumption. apply Ord2; try assumption. }
      { intros. apply Ord2; try assumption. apply Ord2; try assumption. }
    }
    { case (le_lt_dec n n2); simpl.
      { intros. apply Ord2; try assumption. firstorder. }
      { intros. apply Ord2; try assumption. }
    }
  } 
Qed.

Program Fixpoint Sort (x : list nat) { measure (length x) } : 
  { y : list nat | Permutation x y /\ Ordered y }:=
  match x with
  | [] => []
  | h :: t => Insert h (Sort t)
  end. 

Obligation 1 of Sort.
Proof. 
  split. firstorder. 
  apply Ord0. 
Qed.

Obligation 3 of Sort.
Proof. 
  program_simpl.
  destruct (Sort t ) as [ H1 [ H2 H3 ] ].
  split. 
  - rewrite <- Perm_insert; apply Perm_skip; auto.
  - apply Ord_insert; auto.
Qed.

End ProgSpec. 

(* Function extraction and calculations. *)

(* proof style *)
Example sort_2357 : Ordered [ 2; 3; 5; 7 ]. 
Proof. repeat apply Ord2; try apply Ord1; auto. Qed.
Example sort_14578 : Ordered [ 1; 4; 5; 7; 8 ]. 
Proof. repeat apply Ord2; try apply Ord1; auto. Qed.
Example sort_8_12_18_21 : Ordered [ 8; 12; 18; 21 ]. 
Proof. repeat apply Ord2; try apply Ord1; auto with arith. Qed.

(* computation style *)
Compute (FuncSpec.Sort [ 1; 0; 6; 4; 9; 2; 7; 5; 3; 8 ]).
Compute (FuncSpec.Sort [ 4; 7; 3; 9; 8; 5; 0; 1; 6; 2 ]).
Compute (proj1_sig (ProgSpec.Sort [ 7; 12; 4; 5; 8; 5; 6; 9; 0; 3; 6; 2 ])).

(*
Extraction Language Haskell.
Extraction "insert" FuncSpec.Sort.
*)