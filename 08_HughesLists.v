(* 

 HUGHES LISTS

 Evgeny V Ivashkevich
 
 E-mail: ivashkev@yandex.ru

 March 2, 2019

 Abstract: In this file, we formalize the short paper by R. John Muir Hughes,
           "A novel repesentation of lists and its application to the function 
           reverse". Information Pocessing Letters 22 (1986) 141-144,
           where fast algorithm for lists reverse function was proposed.
*)

Require Import FunctionalExtensionality.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Module ArrowType.

Section Hughes.

Variable T : Type.

Definition A := list T.

Definition R := A -> A.

Definition rep (x : A) : R := app x.

Check rep.

Definition abs (f : R) : A := f [].

Check abs.

Print abs.

Theorem abs_rep :
  forall a : A,
  abs (rep a) = a.
Proof.
  unfold abs, rep.
  intros a.
  rewrite app_nil_r.
  reflexivity.
Qed.

Parameter find_rep : forall f : R, { F : A | f = rep F }.

Theorem rep_abs :
  forall f : R,
  rep (abs f) = f.
Proof.
  intros f.
  destruct (find_rep f) as [ F Hf ].
  rewrite Hf.
  rewrite abs_rep.
  reflexivity.
Qed.

Definition appendR (f g : R) : R := fun x => f (g x).

Check appendR.

Theorem appendR_rep :
  forall (a b : A),
  appendR (rep a) (rep b) = rep (a ++ b).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold appendR, rep; simpl.
  apply app_assoc.
Qed.

Theorem abs_appendR :
  forall (f g : R),
  abs (appendR f g) = (abs f) ++ (abs g).
Proof.
  intros.
  destruct (find_rep f) as [ F Hf ].
  destruct (find_rep g) as [ G Hg ].
  rewrite Hf. rewrite Hg. rewrite appendR_rep.
  unfold abs, rep; simpl.
  repeat rewrite app_nil_r.
  reflexivity.
Qed.

Fixpoint rev (x : A) : R :=
  match x with
  | nil => id
  | a :: y => fun (t : A) => (rev y) (a :: t)
  end.

Definition reverse (x : A) := (rev x) [].

Theorem rev_app :
  forall (x y : A),
  rev x y = rev x [] ++ y.
Proof.
  intros. 
  induction y as [| h t ].
  { simpl. rewrite app_nil_r. reflexivity. }
  { assert (H1 : rev x [] = abs (rev x)). reflexivity.
    assert (H2 : h :: t = abs (app (h :: t))). 
    { unfold abs. rewrite app_nil_r. reflexivity. }
    rewrite H1. rewrite H2 at 2.
    rewrite <- abs_appendR.
    unfold appendR, abs, rep; simpl.
    rewrite app_nil_r. reflexivity.
  }
Qed.

Theorem rev_app_distr:
  forall (x y : A),
  reverse (x ++ y) = reverse y ++ reverse x.
Proof.
  intros.
  unfold reverse.
  induction x as [| h t ].
  { simpl. rewrite app_nil_r. reflexivity. }
  { simpl.
    rewrite (rev_app t [h]).
    rewrite rev_app.
    rewrite IHt.
    rewrite app_assoc.
    reflexivity.
  }
Qed.

Theorem app_length :
  forall x y : A,
  length (x ++ y) = length x + length y.
Proof.
  intros x y. 
  induction x as [| h t ].
  { reflexivity. }
  { simpl. rewrite -> IHt. reflexivity. }
Qed.

Theorem reverse_length :
  forall x : A,
  length (reverse x) = length x.
Proof.
  intros x.
  unfold reverse.
  induction x as [| h t ].
  { reflexivity. }
  { assert (H : rev (h :: t) [] = rev t [] ++ [h]). 
    { simpl. rewrite rev_app. reflexivity. }
    rewrite H. 
    rewrite app_length.
    rewrite IHt.
    rewrite PeanoNat.Nat.add_comm.
    simpl. reflexivity.
  }
Qed.

Theorem reverse_involutive :
  forall x : A,
  reverse (reverse x) = x.
Proof.
  induction x. 
  { reflexivity. }
  { simpl.
    replace (a :: x) with ([a] ++ x).
    { repeat rewrite rev_app_distr. 
      rewrite IHx. reflexivity. 
    }
    { reflexivity. }
  }
Qed.

Theorem rev_injective :
  forall (x y : A),
  reverse x = reverse y -> x = y.
Proof.
  intros x y reveq.
  rewrite <- reverse_involutive. 
  rewrite <- reveq.
  rewrite -> reverse_involutive.
  reflexivity.
Qed.

End Hughes.

Compute reverse [2;3;6;3;6;9].

Compute reverse [true;true;true;false;false;false].


End ArrowType.

(* In the next module we change representation type from 
   functional (R := A -> A) to inductive type with additional condition 
   that we consider only those functions on lists that can be generated
   with the help of the function append.
*)

Module InductiveType.

Section Hughes.

Variable T : Type.

Definition A := list T.

Record R : Type 
  := build { func : A -> A ; prop : exists x : A, func = app x }.

Definition rep (x : A) : R.
Proof.
  apply build with (app x).
  exists x; reflexivity.
Defined.

Check rep.

Print rep.

Definition abs (F : R) : A.
Proof.
  destruct F as [ f _ ].
  apply (f []).
Defined.

Check abs.

Print abs.

Theorem abs_rep :
  forall a : A,
  abs (rep a) = a.
Proof.
  unfold abs, rep.
  intros a.
  rewrite app_nil_r.
  reflexivity.
Qed.

Definition find_rep :
  forall F : R, 
  { x : A | F = rep x }.
Proof.
  intros [ f Hf ].
  exists (f []).
  destruct Hf as [ x H ].
  subst f. unfold rep.
  rewrite app_nil_r.
  reflexivity.
Defined.

Theorem rep_abs :
  forall F : R,
  rep (abs F) = F.
Proof.
  intros F.
  destruct (find_rep F) as [ x H ].
  subst F. rewrite abs_rep.
  reflexivity.
Qed.

Theorem func_unique :
  forall F G : R,
  func F = func G -> F = G.
Proof.
  intros.
  rewrite <- (rep_abs F).
  rewrite <- (rep_abs G).
  destruct F as [ f [ x Hf ]].
  destruct G as [ g [ y Hg ]].
  simpl in *. rewrite H.
  reflexivity.
Qed.

Definition appendR (F G : R) : R.
Proof.
  destruct F as [ f Hf ].
  destruct G as [ g Hg ].
  exists (fun y => f (g y)).
  destruct Hf as [ F Hf ].
  destruct Hg as [ G Hg ].
  subst f. subst g.
  exists (app F G).
  apply functional_extensionality.
  intros x.
  rewrite app_assoc.
  reflexivity.
Defined.

Check appendR.

Print appendR.

Theorem appendR_rep :
  forall (a b : A),
  appendR (rep a) (rep b) = rep (a ++ b).
Proof.
  intros. 
  apply func_unique. simpl. 
  apply functional_extensionality. 
  intros t. rewrite app_assoc. reflexivity.
Qed.

Theorem abs_appendR :
  forall (f g : R),
  abs (appendR f g) = (abs f) ++ (abs g).
Proof.
  intros.
  destruct (find_rep f) as [ F Hf ].
  destruct (find_rep g) as [ G Hg ].
  rewrite Hf. rewrite Hg. rewrite appendR_rep.
  unfold abs, rep; simpl.
  repeat rewrite app_nil_r.
  reflexivity.
Qed.

Definition rev (x : A) : R.
Proof.
  set (f := (fix rev (x : A) : A -> A :=
    match x with
    | [] => id
    | a :: y => fun (t : A) => rev y (a :: t)
    end)).
  exists (f x).
  exists ((f x) []).
  induction x.
  { simpl. reflexivity. }
  { simpl. rewrite IHx.
    apply functional_extensionality.
    intros t; simpl. rewrite <- app_assoc. reflexivity.
  }
Defined.

Definition reverse (x : A) := func (rev x) [].

Theorem rev_app :
  forall (x y : A),
  func (rev x) y = func (rev x) [] ++ y.
Proof.
  intros. 
  induction y as [| h t ].
  { rewrite app_nil_r. reflexivity. }
  { assert (H1 : func (rev x) [] = abs (rev x)). reflexivity.
    assert (H2 : h :: t = abs (rep (h :: t))). 
    { unfold abs, rep. rewrite app_nil_r. reflexivity. }
    rewrite H1. rewrite H2 at 2.
    rewrite <- abs_appendR.
    unfold appendR, abs, rep; simpl.
    rewrite app_nil_r. reflexivity.
  }
Qed.

Theorem rev_app_distr:
  forall (x y : A),
  reverse (x ++ y) = reverse y ++ reverse x.
Proof.
  intros.
  unfold reverse.
  induction x as [| h t ].
  { simpl. rewrite app_nil_r. reflexivity. }
  { replace (func (rev ((h :: t) ++ y)) []) with (func (rev (t ++ y)) [h]).
    replace (func (rev (h :: t)) []) with (func (rev t) [h]).
    rewrite (rev_app t [h]).
    rewrite rev_app.
    rewrite IHt.
    rewrite app_assoc.
    reflexivity.
    reflexivity.
    reflexivity.
  }
Qed.

Theorem app_length :
  forall x y : A,
  length (x ++ y) = length x + length y.
Proof.
  intros x y. 
  induction x as [| h t ].
  { reflexivity. }
  { simpl. rewrite -> IHt. reflexivity. }
Qed.

Theorem reverse_length :
  forall x : A,
  length (reverse x) = length x.
Proof.
  intros x.
  unfold reverse.
  induction x as [| h t ].
  { reflexivity. }
  { assert (H : func (rev (h :: t)) [] = func (rev t) [] ++ [h]). 
    { replace (func (rev (h :: t)) []) with (func (rev t) [h]).
      rewrite rev_app. reflexivity.
      reflexivity.
    }
    rewrite H. 
    rewrite app_length.
    rewrite IHt.
    rewrite PeanoNat.Nat.add_comm.
    simpl. reflexivity.
  }
Qed.

Theorem reverse_involutive :
  forall x : A,
  reverse (reverse x) = x.
Proof.
  induction x. 
  { reflexivity. }
  { simpl.
    replace (a :: x) with ([a] ++ x).
    { repeat rewrite rev_app_distr. 
      rewrite IHx. reflexivity. 
    }
    { reflexivity. }
  }
Qed.

Theorem rev_injective :
  forall (x y : A),
  reverse x = reverse y -> x = y.
Proof.
  intros x y reveq.
  rewrite <- reverse_involutive. 
  rewrite <- reveq.
  rewrite -> reverse_involutive.
  reflexivity.
Qed.

End Hughes.

Compute reverse [2;3;6;3;6;9].

Compute reverse [true;true;true;false;false;false].

End InductiveType.