(* 

  FORMALIZATION OF UNTYPED LAMBDA CALCULUS

  Evgeny V Ivashkevich
 
  E-mail: ivashkev@yandex.ru

  January 29, 2019

  Abstract: In this file we formalize untyped lambda calculus.
            We borrowed a lot from Gerard Huet's formalization in 
            Coq's repository "https://github.com/coq-contribs/lambda".
 
*)

Require Import Arith Omega List.
Import ListNotations.

(********************************************************************)
(*                          Definitions                             *)
(********************************************************************)

Definition symbol
  := nat.
Definition word : Set
  := list symbol.
Notation "'a'" := (1 : symbol) (at level 0).
Notation "'b'" := (2 : symbol) (at level 0).
Notation "'c'" := (3 : symbol) (at level 0).
Notation "'d'" := (4 : symbol) (at level 0).

Definition nds : word -> word
  := nodup eq_nat_dec.

Fixpoint insert (w : word)(x : symbol) : word
  := match w with
     | [] => [x]
     | h :: t => if le_lt_dec x h
                 then x :: h :: t
                 else h :: insert t x
     end.

Fixpoint sort (w : word) : word
  := match w with
     | [] => []
     | h :: t => insert (sort t) h
     end.

Fixpoint getSymbol (w : word)(x : symbol) : symbol
  := match w with
     | [] => x
     | h :: t => if eq_nat_dec h x
                 then getSymbol t (S x)
                 else if le_gt_dec h x
                      then getSymbol t x
                      else x
     end.

Definition newSymbol (w : word)
  := getSymbol (sort w) 1.

(********************************************************************)
(*                          Terms                             *)
(********************************************************************)

Inductive Term : Set
  := | Var : symbol -> Term
     | Lam : symbol -> Term -> Term
     | App : Term -> Term -> Term
     .
Notation "n `"
  := (Var n)
     (at level 1).
Notation "x @ y"
  := (App x y)
     (at level 15, left associativity).
Notation "'\' n '->' x"
  := (Lam n x)
     (at level 25, n at level 0, left associativity).
Notation "'\' n m '->' x"
  := (\n -> (\m -> x))
     (at level 25, n at level 0, m at level 0, left associativity).
Notation "'\' n m p '->' x"
  := (\n -> (\m -> (\p -> x)))
     (at level 25, n at level 0, m at level 0, p at level 0, left associativity).
Notation "'\' n m p q '->' x"
  := (\n -> (\m -> (\p -> (\q -> x))))
     (at level 25, n at level 0, m at level 0, p at level 0, q at level 0, left associativity).

Fixpoint freeVariables (T : Term) : word
  := match T with
     | Var k => [k]
     | Lam n t => remove eq_nat_dec n (freeVariables t)
     | App u v  => nds ((freeVariables u) ++ (freeVariables v))
     end.

(********************************************************************)
(*                          de Brujin Numbering                     *)
(********************************************************************)

Fixpoint Pth (w : word)(x : symbol) : nat
  := match w with
     | [] => O
     | h :: t => if eq_nat_dec x h
                 then S O
                 else S (Pth t x)
     end.

Fixpoint Nth (w : word)(n : nat) : symbol
  := match w with
     | [] => O
     | h :: t => match n with
                 | O => O
                 | S O => h
                 | S m => Nth t m
                 end
     end.

Inductive term : Set
  := | var : nat -> term
     | lam : term -> term
     | app : term -> term -> term
     .

Fixpoint removeSymbols (w : word)(T : Term) : term
  := match T with
     | Var k => var (Pth w k)
     | Lam n t => lam (removeSymbols (n :: w) t)
     | App u v  => app (removeSymbols w u)(removeSymbols w v)
     end.

Fixpoint restoreSymbols (w : word)(t : term) : Term
  := match t with
     | var k => Var (Nth w k)
     | lam t => Lam (newSymbol w)(restoreSymbols ((newSymbol w) :: w) t)
     | app u v  => App (restoreSymbols w u)(restoreSymbols w v)
     end.

(********************************************************************)
(*                          Substitution                            *)
(********************************************************************)

Reserved Notation " t ! n ^ m "
  (at level 5, n at level 0, left associativity).
Fixpoint termShift (t : term)(n m : nat) 
  := match t with
     | var k => if le_gt_dec k m then var k else var (k + n - 1)
     | app u v  => app (u ! n ^ m)(v ! n ^ m)
     | lam s => lam (s ! n ^ (S m))
     end
  where "t ! n ^ m"
  := (termShift t n m).
Notation " t ! n "
  := (termShift t n 0)
     (at level 5, n at level 0, left associativity).

Reserved Notation " t [ n <- s ] "
  (at level 8, n at level 10, left associativity).
Fixpoint termSubst (t s : term)(n : nat)
  := match t with
     | var k => match (lt_eq_lt_dec k n) with
                | inleft (left _) => var k
                | inleft (right _) => s ! k
                | inright _ => var (k - 1)
                end
     | app u v => app (u [ n <- s ])( v [ n <- s ])
     | lam t => lam (t [ S n <- s ])
     end
  where "t [ n <- s ]"
  := (termSubst t s n).
Notation "t [ <- s ]"
  := (termSubst t s 1)
     (at level 5).

(********************************************************************)
(*                          Shift Theorems                          *)
(********************************************************************)

Lemma shift_0 (t : term)(n : nat) :
  t ! 1 ^ n = t.
Proof.
  generalize dependent n.
  induction t; intros; simpl.
  { destruct (le_gt_dec n n0);
    replace (n + 1 - 1) with n by omega; 
    reflexivity.
  }
  { rewrite IHt; reflexivity. }
  { rewrite IHt1; rewrite IHt2; reflexivity. }
Qed.

Lemma shift_1 (t : term)(n m i j : nat) :
  m <= j
    -> j < n + m
    -> (t ! n ^ m) ! i ^ j = t ! (n + i - 1) ^ m.
Proof.
  generalize dependent n.
  generalize dependent m.
  generalize dependent j.
  induction t; 
  intros; simpl.
  { destruct (le_gt_dec n m); simpl.
    { destruct (le_gt_dec n j); auto; omega. }
    { destruct (le_gt_dec (n + n0 - 1) j); try omega; 
      replace (n + (n0 + i - 1) - 1) with (n + n0 - 1 + i - 1) by omega;
      reflexivity.
    }
  }
  { rewrite IHt; try omega; reflexivity. }
  { rewrite IHt1; auto; rewrite IHt2; auto. }
Qed.

Lemma shift_2 (t : term)(n m i j : nat) :
  i > 0
    -> n > 0
    -> m + n <= j + 1
    -> (t ! n ^ m) ! i ^ j = (t ! i ^ (j + 1 - n)) ! n ^ m.
Proof.
  generalize dependent n.
  generalize dependent m.
  generalize dependent j.
  induction t; 
  intros; simpl.
  { destruct (le_gt_dec n m); destruct (le_gt_dec n (j + 1 - n0)); simpl.
    { destruct (le_gt_dec n j); destruct (le_gt_dec n m); intuition. }
    { omega. }
    { destruct (le_gt_dec (n + n0 - 1) j);
      destruct (le_gt_dec n m); intuition.
    }
    { destruct (le_gt_dec (n + n0 - 1) j);
      destruct (le_gt_dec (n + i - 1) m); intuition.
    }
  }
  { rewrite IHt; intuition;
    replace (S (j + 1 - n)) with (S j + 1 - n) by omega; reflexivity.
  }
  { rewrite IHt1; intuition;  rewrite IHt2; intuition;  reflexivity. }
Qed.

Lemma shift_shift (t : term)(n m : nat) :
  m > 0
    -> (t ! m) ! n  = t ! (m + n - 1).
Proof.
  intros; apply shift_1; omega.
Qed.

Lemma subst_1 (t s : term)(i k n : nat) :
  k < n
    -> n <= k + i
    -> t ! i ^ k = (t ! (S i) ^ k) [ n <- s ].
Proof.
  generalize dependent n.
  generalize dependent k.
  induction t; 
  intros; simpl.
  { destruct (le_gt_dec n k); simpl.
    { destruct (lt_eq_lt_dec n n0) as [ [ | ] | ];
      [ reflexivity | subst; omega | omega ].
    }
    { destruct ( lt_eq_lt_dec (n + S i - 1) n0) as [ [ | ] | ];
      [ omega | omega | 
      replace (n + S i - 1 - 1) with (n + i - 1) by omega; reflexivity ].
    }
  }
  { rewrite <- IHt; [ reflexivity | omega | omega ]. }
  { rewrite <- IHt1; intuition;  rewrite <- 1IHt2; intuition;  reflexivity. }
Qed.

Lemma subst_2 (t s : term)(i k n : nat) :
  i > 0
    -> k + i <= n
    -> (t ! i ^ k) [ n <- s ] = (t [ n - i + 1 <- s ] ) ! i ^ k.
Proof.
  generalize dependent n.
  generalize dependent k.
  induction t; 
  intros; simpl.
  { destruct (le_gt_dec n k); simpl.
    { destruct (lt_eq_lt_dec n n0) as [ [ | ] | ];
      destruct (lt_eq_lt_dec n (n0 - i + 1)) as [ [ | ] | ]; simpl; try omega;
      destruct (le_gt_dec n k); [ reflexivity | omega ].
    }
    { destruct (lt_eq_lt_dec (n + i - 1) n0) as [ [ | ] | ];
      destruct (lt_eq_lt_dec n (n0 - i + 1)) as [ [ | ] | ]; simpl; try omega.
      { destruct (le_gt_dec n k); [ omega | reflexivity ]. }
      { rewrite shift_1; try reflexivity; omega. }
      { destruct (le_gt_dec (n - 1) k); try omega;
        replace (n + i - 1 - 1) with (n - 1 + i - 1) by omega; reflexivity.
      }
    }
  }
  { rewrite IHt; auto; try omega.
    replace (S (n - i + 1)) with (S n - i + 1) by omega; reflexivity.
  }
  { rewrite <- IHt1; intuition;  rewrite <- 1IHt2; intuition;  reflexivity. }
Qed.

Lemma subst_3 (t s : term)(i k n : nat) :
  i > 0
    -> n > 0
    -> n <= k + 1
    -> (t [ n <- s ]) ! i ^ k = (t ! i ^ (k + 1)) [ n <- s ! i ^ (k + 1 - n) ].
Proof.
  generalize dependent n.
  generalize dependent k.
  induction t; 
  intros; simpl.
  { destruct (le_gt_dec n (k + 1)); simpl.
    { destruct (lt_eq_lt_dec n n0) as [ [ | ] | ]; simpl.
      { destruct (le_gt_dec n k); auto; omega. }
      { subst; rewrite shift_2; auto. }
      { destruct (le_gt_dec (n - 1) k) as [ H2 | H4 ]; auto; omega. }
    }
    { destruct (lt_eq_lt_dec n n0) as [ [ | ] | ];
      destruct (lt_eq_lt_dec (n + i - 1) n0) as [ [ | ] | ];simpl; try omega.
      destruct (le_gt_dec (n-1) k); try omega.
      replace (n - 1 + i - 1) with (n + i - 1 - 1) by omega; reflexivity.
    }
  }
  { rewrite IHt; auto; try omega. }
  { replace (S k + 1 - S n) with (k + 1 - n) by omega.
    rewrite <- IHt1; intuition;  rewrite <- 1IHt2; intuition;  reflexivity.
  }
Qed.

Lemma subst_4 (t s r : term)(i n : nat) :
  i > 0
    -> n >= i
    -> t [ i <- s ] [ n <- r ] = t [ n + 1 <- r ] [ i <- s [ n - i + 1 <- r ] ].
Proof.
  generalize dependent n.
  generalize dependent i.
  induction t; 
  intros; simpl.
  { destruct (lt_eq_lt_dec n i) as [ [ | ] | ];
    destruct (lt_eq_lt_dec n (n0 + 1)) as [ [ | ] | ]; simpl; auto; try omega.
    { destruct (lt_eq_lt_dec n n0) as [ [ | ] | ];
      destruct (lt_eq_lt_dec n i) as [ [ | ] | ]; simpl; auto; try omega.
    }
    { subst; destruct (lt_eq_lt_dec i i) as [ [ | ] | ]; simpl; try omega; 
      rewrite subst_2; auto.
    }
    { destruct (lt_eq_lt_dec (n - 1) n0) as [ [ H1 | H2 ] | H7 ];
      destruct (lt_eq_lt_dec n i) as [ [ H8 | H5 ] | H6 ]; 
      simpl; auto; try omega.
    }
    { destruct (lt_eq_lt_dec (n - 1) n0) as [ [ H7 | H4 ] | H6 ]; 
      simpl; auto; try omega.
      subst n0; replace (n - 1 - i + 1) with (n - i) by omega.
      rewrite (subst_1 r (s [n - i <- r])(n-1) 0 i); try omega.
      replace (S (n - 1)) with n by omega; auto.
    }
    { destruct (lt_eq_lt_dec (n - 1) n0) as [ [ | ] | ];
      destruct (lt_eq_lt_dec (n - 1) i) as [ [ | ] | ]; simpl; auto; try omega.
    }
  }
  { rewrite IHt; try omega;
    replace (S n + 1) with (S (n + 1)) by omega; 
    replace (S n - S i + 1) with (n - i + 1) by omega; auto.
  }
  { rewrite IHt1; intuition; rewrite <- 1IHt2; intuition; auto. }
Qed.

Lemma subst_travers (t s r : term)(n : nat) :
  n > 0
    -> t [ <- s ] [ n <- r ] = t [ n + 1 <- r ] [ <- s [ n <- r ] ].
Proof.
  intros; rewrite (subst_4 t s r 1 n); auto; try omega.
  replace (n - 1 + 1) with n by omega; auto.
Qed.

(********************************************************************)
(*                          Beta reduction                          *)
(********************************************************************)

Reserved Notation " t --> s " (at level 15, left associativity).
Inductive betaStep : term -> term -> Prop
  := | beta_red (t s : term) :
         app (lam t) s --> t [ <- s ]
     | beta_lam (t s : term) :
         t --> s
           -> lam t --> lam s
     | beta_app_left (t t' s : term) :
         t --> s
           -> app t t' --> app s t'
     | beta_app_right (t t' s : term) :
         t --> s
           -> app t' t --> app t' s
  where "t --> s"
  := (betaStep t s).

Reserved Notation "t -->> s" (at level 15, left associativity).
Inductive betaReduction : term -> term -> Prop
  := | beta_step (t s : term) :
         t --> s
           -> t -->> s
     | beta_refl (t : term) :
         t -->> t
     | beta_trans (t s r : term) :
         t -->> s
           -> s -->> r
           -> t -->> r
  where "t -->> s"
  := (betaReduction t s).

Lemma betaReduction_lam (t s : term) :
  t -->> s
    -> lam t -->> lam s.
Proof.
  induction 1; intros.
  { apply beta_step; apply beta_lam; trivial. }
  { apply beta_refl. }
  { apply beta_trans with (lam s); trivial. }
Qed.

Lemma betaReduction_app_left (t t' s : term) :
  t -->> s
    -> app t t' -->> app s t'.
Proof.
  induction 1; intros.
  { apply beta_step; apply beta_app_left; trivial. }
  { apply beta_refl. }
  { apply beta_trans with (app s t'); trivial. }
Qed.

Lemma betaReduction_app_right (t t' s : term) :
  t -->> s
    -> app t' t -->> app t' s.
Proof.
  induction 1; intros.
  { apply beta_step; apply beta_app_right; trivial. }
  { apply beta_refl. }
  { apply beta_trans with (app t' s); trivial. }
Qed.

Lemma betaReduction_app (t t' s s' : term) :
  t -->> t'
    -> s -->> s'
    -> app t s -->> app t' s'.
Proof.
  intros; apply beta_trans with (app t' s).
  { apply betaReduction_app_left; trivial. }
  { apply betaReduction_app_right; trivial. }
Qed.

Lemma betaReduction_redex (t t' s s' : term) :
  t -->> t'
    -> s -->> s'
    -> app (lam t) s -->> t' [ <- s' ].
Proof.
  intros; apply beta_trans with (app (lam t') s').
  { apply betaReduction_app; trivial.
    apply betaReduction_lam; trivial.
  }
  { apply beta_step; apply beta_red. }
Qed.

(********************************************************************)
(*                          Parallel Beta-reduction                 *)
(********************************************************************)

Reserved Notation "t ==> s" (at level 15, left associativity).
Inductive parallelStep : term -> term -> Prop
  := | par_var (n : nat) :
         var n ==> var n
     | par_lam (t t' : term) :
         t ==> t'
           -> lam t ==> lam t'
     | par_red (t s t' s': term) :
         t ==> t'
           -> s ==> s'
           -> app (lam t) s ==> t' [ <- s' ]
     | par_app (t s t' s': term) :
         t ==> t'
           -> s ==> s'
           -> app t s ==> app t' s'
  where "t ==> s"
  := (parallelStep t s).
Hint Resolve par_red par_var par_lam par_app.

Reserved Notation "t ==>> s" (at level 15, left associativity).
Inductive parallelReduction : term -> term -> Prop
  := | par_refl (t s : term) :
         t ==> s
           -> t ==>> s
     | par_trans (t s r : term) :
         t ==>> s
           -> s ==>> r
           -> t ==>> r
  where "t ==>> s"
  := (parallelReduction t s).

Lemma parallelStep_refl (t : term) :
  t ==> t.
Proof.
  induction t; auto.
Qed.

Lemma parallelReduction_refl (t : term) :
  t ==>> t.
Proof.
  apply par_refl.
  apply parallelStep_refl.
Qed.
Hint Resolve parallelStep_refl parallelReduction_refl.

Lemma parallelShift (n m : nat)(t s : term) :
  t ==> s
    -> t ! (S n) ^ m ==> s ! (S n) ^ m.
Proof.
  intros Pts.
  generalize dependent n.
  generalize dependent m.
  induction Pts; subst; auto.
  { intros; simpl; apply par_lam; apply IHPts. }
  { intros; rewrite (subst_3 t' s' (S n) m 1); simpl; try omega.
    { apply par_red; try omega; auto.
      { replace (m+1) with (S m); try omega; apply IHPts1. }
      { replace (m + 1 - 1) with m; try omega; apply IHPts2. }
    }
  }
  { intros; simpl.
    apply par_app.
    { apply IHPts1. }
    { apply IHPts2. }
  }
Qed.

Lemma parallelSubstitute (n : nat)(t t' s s' : term) :
  t ==> t'
    -> s ==> s'
    -> t [ S n <- s ] ==> t' [ S n <- s' ].
Proof.
  intros Pts Puv. 
  generalize dependent n.
  induction Pts; subst; auto.
  { intros; simpl.
    destruct (lt_eq_lt_dec n (S n0)) as [ [ H1 | H2 ] | H3 ].
    { apply parallelStep_refl. }
    { subst n. apply (parallelShift n0 0 s s'); auto. }
    { apply parallelStep_refl. }
  }
  { intros; simpl.
    apply par_lam. apply IHPts.
  }
  { intros; simpl. 
    rewrite (subst_travers); simpl; try omega.
    { apply par_red.
      { replace (S (n + 1)) with (S(S n)); try omega.
        apply (IHPts1 (S n)).
      }
      { apply (IHPts2 n); omega. }
    }
  }
  { intros; simpl. apply par_app.
    { apply IHPts1. }
    { apply IHPts2. }
  }
Qed.

(********************************************************************)
(*        Equivalence between reduction and parallel reduction      *)
(********************************************************************)

Lemma betaStep_parallelStep (t s : term) :
  t --> s
    -> t ==> s.
Proof.
  simple induction 1; auto.
Qed.

Lemma betaReduction_parallelReduction (t s : term) :
  t -->> s
    -> t ==>> s.
Proof.
  induction 1; intros.
  { apply par_refl; induction H; auto. }
  { apply par_refl; auto. }
  { apply par_trans with s; trivial. }
Qed.

Lemma parallelReduction_betaReduction (t s : term) :
  t ==>> s
    -> t -->> s.
Proof.
  induction 1.
  { induction H.
    { intros; apply beta_refl; trivial. }
    { intros; apply betaReduction_lam; trivial. }
    { intros; apply betaReduction_redex; trivial. }
    { intros; apply betaReduction_app; trivial. }
  }
  { intros; apply beta_trans with s; trivial. }
Qed.

(*******************************************************************)
(*             Maximal Parallel Beta-reduction                     *)
(*******************************************************************)

Reserved Notation "t **" (at level 1, left associativity).
Fixpoint maximumStep (t : term) : term
  := match t with
     | var n => var n
     | lam t => lam t**
     | app (lam s) v => s** [ <- v** ]
     | app u v => app u** v**
     end
  where "t **"
  := (maximumStep t).

Lemma maximumStep_parallelStep (t : term) :
  t ==> t**.
Proof.
  induction t; simpl.
  { apply par_var; auto. }
  { apply par_lam; auto. }
  induction t1; simpl; auto.
  { apply par_red; simpl; auto.
    inversion IHt1; subst; auto.
  }
Qed.

Lemma parallelStep_maximumStep (t s : term) :
  t ==> s
    -> s ==> t**.
Proof.
  generalize dependent s.
  induction t.
  { intros; inversion H; subst; auto. }
  { intros; inversion H; subst; simpl.
    inversion H; subst. apply par_lam. apply IHt; auto.
  }
  { induction t1; intros.
    { inversion H; subst. 
      inversion H2; subst; simpl.
      apply par_app. 
      { apply par_var. }
      { inversion H; subst. apply IHt2; auto. }
    }
    { inversion H; subst; simpl; auto.
      { apply parallelSubstitute; auto.
        assert (au : lam t' ==> (lam t1)**). { apply IHt1; auto. }
        inversion au; subst; auto.
      }
      { inversion H2; subst; simpl; auto. 
        apply par_red; auto.
        assert (au : lam t'0 ==> (lam t1)**). { apply IHt1; auto. }
        inversion au; subst; auto.
      }
    }
    { inversion H; subst; simpl.
      apply par_app.
      { inversion H; subst. apply IHt1; auto. }
      { inversion H; subst. apply IHt2; auto. }
    }
  }
Qed.

(********************************************************************)
(*                       Diamond Properties                         *)
(********************************************************************)

Lemma parallelStep_diamond (t s r : term) :
  t ==> s
    -> t ==> r
    -> { u : term |  s ==> u /\ r ==> u }.
Proof.
  intros Pts Ptr.
  exists t**.
  split;
    [ apply (parallelStep_maximumStep t s)
    | apply (parallelStep_maximumStep t r) ]; auto;
      apply maximumStep_maximumStep; auto.
Qed.

Lemma parallelReduction_strip (t s r : term) :
  t ==> s
    -> t ==>> r
    -> exists u : term,  s ==>> u /\ r ==> u.
Proof.
  intros Pts Rtr.
  generalize dependent s.
  induction Rtr; subst.
  { intros.
    destruct (parallelStep_diamond t s0 s) as [ u [ H1 H2 ] ]; auto.
    exists u. split; auto; apply par_refl; auto.
  }
  { intros.
    destruct (IHRtr1 s0 Pts) as [ u [ H1 H2 ] ].
    destruct (IHRtr2 u H2) as [ v [ G1 G2 ] ].
    exists v. split; auto.
    apply (par_trans s0 u v); auto.
  }
Qed.

Theorem parallelReduction_diamond (t s r : term) :
  t ==>> s
    -> t ==>> r
    -> exists u : term,  s ==>> u /\ r ==>> u.
Proof.
  intros Rts Rtr.
  generalize dependent r.
  induction Rts.
  { intros. 
    destruct (parallelReduction_strip t s r) as [ u [ H1 H2 ] ]; auto.
    exists u. split; auto; apply par_refl; auto.
  }
  { intros.
    destruct (IHRts1 r0 Rtr) as [ u [ H1 H2 ] ].
    destruct (IHRts2 u H1) as [ v [ H3 H4 ] ].
    exists v. split; auto. apply (par_trans r0 u v); auto.
  }
Qed.

Theorem Church_Rosser (t s r : term) :
  t -->> s
    -> t -->> r
    -> exists u : term,  s -->> u /\ r -->> u.
Proof.
  intros Rts Rtr.
  apply betaReduction_parallelReduction in Rts.
  apply betaReduction_parallelReduction in Rtr.
  destruct (parallelReduction_diamond t s r Rts Rtr ) as [ u [ Rsu Rry ] ].
  exists u; split; apply parallelReduction_betaReduction; auto.
Qed.

(********************************************************************)
(*                          Applications                            *)
(********************************************************************)

Fixpoint len (T : Term) : nat
  := match T with
     | Var k => 1
     | Lam n t => S (len t)
     | App u v  => (len u) + (len v)
     end.

Fixpoint step (n : nat)(t : term)
  := match n with
     | O => t
     | S m => step m (maximumStep t)
     end.

Definition beta (n : nat)(T : Term)
  := let fV := (freeVariables T)
     in restoreSymbols fV (step n (removeSymbols fV T)).

(********************************************************************)
(*                               Examples                           *)
(********************************************************************)

Definition max := 120.
Definition reduce := beta max.

(*  Boolean constants *)

Definition tru  := \a b -> a`.
Definition fls  := \a b -> b`.

Definition ifte := \a b c -> a` @ b` @ c`.
Definition and  := \a b -> a` @ b` @ fls.
Definition or   := \a b -> a` @ tru @ b`.
Definition not  := \a -> a` @ fls @ tru.

Compute reduce (ifte @ tru @ a` @ b`).
Compute reduce (ifte @ fls @ a` @ b`).

Compute reduce (and @ tru @ tru).
Compute reduce (and @ tru @ fls).
Compute reduce (and @ fls @ tru).
Compute reduce (and @ fls @ fls).

Compute reduce (or @ tru @ tru).
Compute reduce (or @ tru @ fls).
Compute reduce (or @ fls @ tru).
Compute reduce (or @ fls @ fls).

Compute reduce (not @ tru).
Compute reduce (not @ fls).

(*  Pairs *)

Definition pair := \a b c -> c` @ a` @ b`.
Definition fst  := \a -> a` @ tru.
Definition snd  := \a -> a` @ fls.

Compute reduce (fst @ (pair @ a` @ b`)).
Compute reduce (snd @ (pair @ a` @ b`)).

(*  Numerals *)

Definition o := \a b -> b`.
Definition s := \a b c -> b` @ (a` @ b` @ c`).

Fixpoint numeral (n : nat) : Term
  := match n with
      | O   => o
      | S p => s @ numeral p
      end.
Notation "# n" := (beta (3 * n) (numeral n)) (at level 0).

Definition value (t : Term) : nat
  := (len t) - 3.
Notation "$ t" := (value (reduce t)) (at level 0).

Definition plus   := \a b c d -> a` @ c` @ (b` @ c` @ d`).

Definition iszero := \a -> a` @ (\b -> fls) @ tru.

Definition zz     := pair @ #0 @ #0.
Definition ss     := \a -> pair @ (snd @ a`) @ (plus @ #1 @ (snd @ a`)).
Definition pred   := \a -> fst @ (a` @ ss @ zz).

Definition minus  := \a b -> b` @ pred @ a`.

Definition mult   := \a b c -> a` @ (b` @ c`).
Definition power  := \a b -> b` @ a`.

Definition equal  := \a b -> and @ (iszero @ (a` @ pred @ b`)) @ (iszero @ (b` @ pred @ a`)).

Compute $(s @ #0).
Compute $(s @ #1).
Compute $(s @ #2).
Compute $(s @ #3).
Compute $(s @ #4).

Compute $(pred @ #0).
Compute $(pred @ #1).
Compute $(pred @ #2).
Compute $(pred @ #3).
Compute $(pred @ #4).
Compute $(pred @ #5).

Compute $(plus @ #2 @ #3).
Compute $(plus @ #3 @ #5).

Compute $(minus @ #4 @ #2).
Compute $(minus @ #8 @ #3).
Compute $(minus @ #12 @ #8).

Compute $(mult @ #2 @ #3).
Compute $(mult @ #3 @ #5).
Compute $(mult @ #5 @ #4).

Compute $(power @ #2 @ #10).
Compute $(power @ #3 @ #3).
Compute $(power @ #6 @ #3).

Compute reduce (iszero @ #0).
Compute reduce (iszero @ #1).
Compute reduce (iszero @ #2).
Compute reduce (iszero @ #3).
Compute reduce (iszero @ #4).

Compute reduce (equal @ #5 @ #5).
Compute reduce (equal @ #5 @ #6).

(*  Recursion *)

Definition omega := (\a -> a` @ a` ) @ (\a -> a` @ a` ).

Definition fixpoint := \a -> ((\b -> a` @ (\c -> b` @ b` @ c` )) @ (\b -> a` @ (\c -> b` @ b` @ c` ))).
Definition ff := \a b -> ifte @ (iszero @ b`) @ (\c -> #1) @ (\c -> (mult @ b` @ (a` @ (pred @ b`)))) @ #0.
Definition factorial := fixpoint @ ff.

Compute reduce (omega @ omega).

Compute $(factorial @ #0).
Compute $(factorial @ #1).
Compute $(factorial @ #2).
Compute $(factorial @ #3).
Compute $(factorial @ #4).

(*  Tests *)

Definition t1 := a` @ (\b c -> a`).
Definition G1 := sort (freeVariables t1).
Definition s1 := removeSymbols G1 t1.
Compute G1.
Compute s1.
Compute (restoreSymbols G1 s1).

Definition t2 := a` @ (\b -> a`) @ (\b -> a` @ (\c -> a`)).
Definition G2 := sort (freeVariables t2).
Definition s2 := removeSymbols G2 t2.
Compute G2.
Compute s2.
Compute (restoreSymbols G2 s2).

Definition t3 := \a -> (\b -> b` @ (\c -> c`)) @ (\b -> a` @ b`).
Definition G3 := sort (freeVariables t3).
Definition s3 := removeSymbols G3 t3.
Compute G3.
Compute s3.
Compute (restoreSymbols G3 s3).

Definition t4 := \a b c -> a` @ c` @ (b` @ c`).
Definition G4 := sort (freeVariables t4).
Definition s4 := removeSymbols G4 t4.
Compute G4.
Compute s4.
Compute (restoreSymbols G4 s4).

Definition t5 := (\a b -> (c` @ a` @ b`)) @ (\a -> b` @ a`).
Definition G5 := sort (freeVariables t5).
Definition s5 := removeSymbols G5 t5.
Compute G5.
Compute s5.
Compute (restoreSymbols G5 s5).

Definition t6 := \a -> b` @ (\c -> d` @ c`) @ a`.
Definition G6 := sort(freeVariables t6).
Definition s6 := removeSymbols G6 t6.
Compute G6.
Compute s6.
Compute (restoreSymbols G6 s6).