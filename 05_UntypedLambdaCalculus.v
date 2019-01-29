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

Definition Symbol := nat.
Definition nextSymbol := S.
Definition Context : Set := list Symbol.

Inductive Term : Set:=
  | Var : Symbol -> Term
  | Lam : Symbol -> Term -> Term
  | App : Term -> Term -> Term.
Notation " # n " := (Var n)(at level 1).
Notation " x ''' y " := (App x y)(at level 15, left associativity).
Notation " '\' n '->' x " := (Lam n x)
  (at level 25, n at level 0,  left associativity).
Notation " '\' n m '->' x " := (\n -> (\m -> x))
  (at level 25, n at level 0, m at level 0, left associativity).
Notation " '\' n m p '->' x " := (\n -> (\m -> (\p -> x)))
  (at level 25, n at level 0, m at level 0, p at level 0, left associativity).
Notation " '\' n m p q '->' x " := (\n -> (\m -> (\p -> (\q -> x))))
  (at level 25, n at level 0, m at level 0, p at level 0, q at level 0, left associativity).

Fixpoint Nth (n : nat)(G : Context) : Symbol :=
  match G with
  | [] => 0
  | h :: t => match n with
                   | 0 => 0
                   | S 0 => h
                   | S m => Nth m t
                   end
  end.

Fixpoint In (x : Symbol)(G : Context) : bool :=
  match G with
  | [] => false
  | h :: t => if eq_nat_dec x h
                   then true
                   else In x t
  end.

Fixpoint Pth (x : Symbol)(G : Context) : nat :=
  match G with
  | [] => 0
  | h :: t => if eq_nat_dec x h
                   then (S O)
                   else S (Pth x t)
  end.

Fixpoint remove (x : Symbol)(G : Context) : Context :=
  match G with
  | [] => []
  | h :: t => if eq_nat_dec x h
                   then remove x t
                   else h :: (remove x t)
  end.

Fixpoint nodups (G : Context) : Context :=
  match G with
  | [] => []
  | h :: t => if in_dec eq_nat_dec h t
                   then nodups t
                   else h :: (nodups t)
  end.

Fixpoint freeVariables (T : Term) : Context :=
  match T with
  | Var k => [k]
  | Lam n t => remove n (freeVariables t)
  | App u v  => nodups ((freeVariables u) ++ (freeVariables v))
  end.

Fixpoint termLength (T : Term) : nat :=
  match T with
  | Var k => 1
  | Lam n t => S (termLength t)
  | App u v  => (termLength u) + (termLength v)
  end.

Fixpoint insert (x : Symbol)(G : Context) : Context :=
  match G with
  | [] => [x]
  | h :: t => if le_lt_dec x h
                   then x :: h :: t
                   else h :: insert x t
  end.

Fixpoint sort (G : Context) : Context :=
  match G with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Fixpoint getSymbol (G : Context)(x : Symbol) : Symbol :=
  match G with
  | [] => x
  | h :: t => if eq_nat_dec h x
                   then getSymbol t (nextSymbol x)
                   else if le_gt_dec h x
                           then getSymbol t x
                           else x
  end.

Definition newSymbol (G : Context) := getSymbol (sort G) 1.

(********************************************************************)
(*                          de Brujin Numbering                     *)
(********************************************************************)

Inductive term : Set:=
  | var : nat -> term
  | lam : term -> term
  | app : term -> term -> term.

Fixpoint removeSymbols (t : Term)(G : Context) : term :=
  match t with
  | Var k => var (Pth k G)
  | Lam n t => lam (removeSymbols t (n :: G))
  | App u v  => app (removeSymbols u G)(removeSymbols v G)
  end.

Fixpoint restoreSymbols (t : term)(G : Context) : Term :=
  match t with
  | var k => Var (Nth k G)
  | lam t => Lam (newSymbol G)(restoreSymbols t ((newSymbol G) :: G))
  | app u v  => App (restoreSymbols u G)(restoreSymbols v G)
  end.

(********************************************************************)
(*                          Substitution                            *)
(********************************************************************)

Reserved Notation " t ! n ^ m " (at level 5, n at level 0, left associativity).
Fixpoint termShift (t : term)(n m : nat) :=
  match t with
  | var k => if le_gt_dec k m then var k else var (k + n - 1)
  | app u v  => app (u ! n ^ m)(v ! n ^ m)
  | lam b => lam (b ! n ^ (S m))
  end
  where "t ! n ^ m" := (termShift t n m).
Notation " t ! n " := (termShift t n 0)
  (at level 5, n at level 0, left associativity).

Reserved Notation " t [ n <- s ] "
  (at level 8, n at level 10, left associativity).
Fixpoint termSubst (t s : term)(n : nat) :=
  match t with
  | var k => match (lt_eq_lt_dec k n) with
               | inleft (left _) => var k
               | inleft (right _) => s ! k
               | inright _ => var (k - 1)
               end
  | app u v => app (u [ n <- s ])( v [ n <- s ])
  | lam t => lam (t [ S n <- s ])
  end
  where " t [ n <- s ] " := (termSubst t s n).
Notation " t [ <- s ] " := (termSubst t s 1)(at level 5).

(********************************************************************)
(*                          Shift Theorems                          *)
(********************************************************************)

Lemma shift_0 :
  forall (t : term)(m : nat),
  t ! 1 ^ m = t.
Proof.
  induction t; intros; simpl.
    destruct (le_gt_dec n m);
      replace (n + 1 - 1) with n by omega; reflexivity.
    rewrite IHt; reflexivity.
    rewrite IHt1; rewrite IHt2; reflexivity.
Qed.

Lemma shift_1 :
  forall (t : term)(n m i j : nat),
  m <= j
    -> j < n + m
    -> (t ! n ^ m) ! i ^ j = t ! (n + i - 1) ^ m.
Proof.
  intro t; induction t; intros; simpl.
    destruct (le_gt_dec n m); simpl.
      destruct (le_gt_dec n j); auto; omega.
      destruct (le_gt_dec (n + n0 - 1) j); simpl.
        omega.
        replace (n + (n0 + i - 1) - 1) with (n + n0 - 1 + i - 1) by omega;
          reflexivity.
    rewrite IHt; try omega; reflexivity.
    rewrite IHt1; auto; rewrite IHt2; auto.
Qed.

Lemma shift_2:
  forall t n m i j,
  i > 0
    -> n > 0
    -> m + n <= j + 1
    -> (t ! n ^ m) ! i ^ j = (t ! i ^ (j + 1 - n)) ! n ^ m.
Proof.
  intro t; induction t; intros; simpl.
    destruct (le_gt_dec n m); destruct (le_gt_dec n (j + 1 - n0)); simpl.
      destruct (le_gt_dec n j); destruct (le_gt_dec n m); intuition. omega.
      destruct (le_gt_dec (n + n0 - 1) j); destruct (le_gt_dec n m); intuition.
      destruct (le_gt_dec (n + n0 - 1) j);
      destruct (le_gt_dec (n + i - 1) m); intuition.
    rewrite IHt; intuition;
    replace (S (j + 1 - n)) with (S j + 1 - n) by omega; reflexivity.
    rewrite IHt1; intuition;  rewrite IHt2; intuition;  reflexivity.
Qed.

Lemma shift_shift :
  forall t n m,
  m > 0
    -> (t ! m) ! n  = t ! (m + n - 1).
Proof.
  intros; apply shift_1; omega.
Qed.

Lemma subst_1:
  forall a b i k n,
  k < n
    -> n <= k + i
    -> a ! i ^ k = (a ! (S i) ^ k) [ n <- b ].
Proof.
  intros t; induction t; intros; simpl.
    destruct (le_gt_dec n k); simpl.
      destruct (lt_eq_lt_dec n n0) as [ [ | ] | ];
        [ reflexivity | subst; omega | omega ].
      destruct ( lt_eq_lt_dec (n + S i - 1) n0) as [ [ | ] | ];
        [ omega
        | omega
        | replace (n + S i - 1 - 1) with (n + i - 1) by omega; reflexivity ].
    rewrite <- IHt; [ reflexivity | omega | omega ].
    rewrite <- IHt1; intuition;  rewrite <- 1IHt2; intuition;  reflexivity.
Qed.

Lemma subst_2:
  forall a b i k n,
  i > 0
    -> k + i <= n
    -> (a ! i ^ k) [ n <- b ] = (a [ n - i + 1 <- b ] ) ! i ^ k.
Proof.
  intros t; induction t; intros; simpl.
    destruct (le_gt_dec n k); simpl.
      destruct (lt_eq_lt_dec n n0) as [ [ | ] | ];
        destruct (lt_eq_lt_dec n (n0 - i + 1)) as [ [ | ] | ]; simpl; try omega;
          destruct (le_gt_dec n k); [ reflexivity | omega ].
      destruct (lt_eq_lt_dec (n + i - 1) n0) as [ [ | ] | ];
        destruct (lt_eq_lt_dec n (n0 - i + 1)) as [ [ | ] | ]; simpl; try omega.
          destruct (le_gt_dec n k); [ omega | reflexivity ].
            rewrite shift_1; try reflexivity; omega.
          destruct (le_gt_dec (n - 1) k).
            omega.
            replace (n + i - 1 - 1) with (n - 1 + i - 1) by omega; reflexivity.
    rewrite IHt; auto.
      replace (S (n - i + 1)) with (S n - i + 1) by omega; reflexivity.
      omega.
    rewrite <- IHt1; intuition;  rewrite <- 1IHt2; intuition;  reflexivity.
Qed.

Lemma subst_3:
  forall a b i k n,
  i > 0
    -> n > 0
    -> n <= k + 1
    -> (a [ n <- b ]) ! i ^ k = (a ! i ^ (k + 1)) [ n <- b ! i ^ (k + 1 - n) ].
Proof.
  intros t; induction t; intros; simpl.
    destruct (le_gt_dec n (k + 1)); simpl.
      destruct (lt_eq_lt_dec n n0) as [ [ | ] | ]; simpl.
        destruct (le_gt_dec n k); auto; omega.
        subst; rewrite shift_2; auto.
        destruct (le_gt_dec (n - 1) k) as [ H2 | H4 ]; auto; omega.
      destruct (lt_eq_lt_dec n n0) as [ [ | ] | ];
        destruct (lt_eq_lt_dec (n + i - 1) n0) as [ [ | ] | ];simpl; try omega.
          destruct (le_gt_dec (n-1) k).
            omega.
            replace (n - 1 + i - 1) with (n + i - 1 - 1) by omega; reflexivity.
      rewrite IHt; auto.
        replace (S k + 1 - S n) with (k + 1 - n) by omega.
        omega.
      rewrite <- IHt1; intuition;  rewrite <- 1IHt2; intuition;  reflexivity.
Qed.

Lemma subst_4:
  forall a b c i n,
  i > 0
    -> n >= i
    -> a [ i <- b ] [ n <- c ] = a [ n + 1 <- c ] [ i <- b [ n - i + 1 <- c ] ].
Proof.
  intros t; induction t; intros; simpl.
    destruct (lt_eq_lt_dec n i) as [ [ | ] | ];
      destruct (lt_eq_lt_dec n (n0 + 1)) as [ [ | ] | ]; simpl; auto; try omega.
        destruct (lt_eq_lt_dec n n0) as [ [ | ] | ];
          destruct (lt_eq_lt_dec n i) as [ [ | ] | ]; simpl; auto; try omega.
        subst; destruct (lt_eq_lt_dec i i) as [ [ | ] | ]; simpl; try omega; rewrite subst_2; auto.
        destruct (lt_eq_lt_dec (n - 1) n0) as [ [ H1 | H2 ] | H7 ];
          destruct (lt_eq_lt_dec n i) as [ [ H8 | H5 ] | H6 ]; simpl; auto; try omega.
        destruct (lt_eq_lt_dec (n - 1) n0) as [ [ H7 | H4 ] | H6 ]; simpl; auto; try omega.
          subst n0; replace (n - 1 - i + 1) with (n - i) by omega.
            rewrite (subst_1 c (b [n - i <- c])(n-1) 0 i); try omega.
              replace (S (n - 1)) with n by omega; auto.
        destruct (lt_eq_lt_dec (n - 1) n0) as [ [ | ] | ];
          destruct (lt_eq_lt_dec (n - 1) i) as [ [ | ] | ]; simpl; auto; try omega.
    rewrite IHt; try omega.
      replace (S n + 1) with (S (n + 1)) by omega; replace (S n - S i + 1) with (n - i + 1) by omega; auto.
    rewrite IHt1; intuition; rewrite <- 1IHt2; intuition; auto.
Qed.

Lemma subst_travers :
  forall  a b c n,
  n > 0
    -> a [ <- b ] [ n <- c ] = a [ n + 1 <- c ] [ <- b [ n <- c ] ].
Proof.
  intros; rewrite (subst_4 a b c 1 n); auto; try omega.
  replace (n - 1 + 1) with n by omega; auto.
Qed.

(********************************************************************)
(*                          Beta reduction                          *)
(********************************************************************)

Reserved Notation " t --> s " (at level 15, left associativity).
Inductive betaStep : term -> term -> Prop :=
  | beta_red :
      forall M N : term,
      app (lam M) N --> M [ <- N ]
  | beta_lam :
      forall M N : term,
      M --> N
        -> lam M --> lam N
  | beta_app_left :
      forall M1 M2 N1 : term,
      M1 --> N1
        -> app M1 M2 --> app N1 M2
  | beta_app_right :
      forall M1 M2 N2 : term,
      M2 --> N2
        -> app M1 M2 --> app M1 N2
  where " t --> s " := (betaStep t s).

Reserved Notation " t -->> s " (at level 15, left associativity).
Inductive betaReduction : term -> term -> Prop :=
  | beta_step :
      forall M N : term,
      M --> N
        -> M -->> N
  | beta_refl :
      forall M : term,
      M -->> M
  | beta_trans :
      forall M N P : term,
      M -->> N
          -> N -->> P
          -> M -->> P
  where " t -->> s " := (betaReduction t s).

Lemma betaReduction_lam :
  forall M M' : term,
  M -->> M'
    -> lam M -->> lam M'.
Proof.
  simple induction 1; intros.
  apply beta_step; apply beta_lam; trivial.
  apply beta_refl.
  apply beta_trans with (lam N); trivial.
Qed.

Lemma betaReduction_app_left :
  forall M M' N : term,
  M -->> M'
    -> app M N -->> app M' N.
Proof.
  simple induction 1; intros.
  apply beta_step; apply beta_app_left; trivial.
  apply beta_refl.
  apply beta_trans with (app N0 N); trivial.
Qed.

Lemma betaReduction_app_right :
  forall M M' N : term,
  M -->> M'
    -> app N M -->> app N M'.
Proof.
  simple induction 1; intros.
  apply beta_step; apply beta_app_right; trivial.
  apply beta_refl.
  apply beta_trans with (app N N0); trivial.
Qed.

Lemma betaReduction_app :
  forall M M' N N' : term,
  M -->> M'
    -> N -->> N'
    -> app M N -->> app M' N'.
Proof.
  intros; apply beta_trans with (app M' N).
  apply betaReduction_app_left; trivial.
  apply betaReduction_app_right; trivial.
Qed.

Lemma betaReduction_redex :
  forall M M' N N' : term,
  M -->> M'
    -> N -->> N'
    -> app (lam M) N -->> M' [ <- N' ].
Proof.
  intros; apply beta_trans with (app (lam M') N').
  apply betaReduction_app; trivial.
  apply betaReduction_lam; trivial.
  apply beta_step; apply beta_red.
Qed.

(********************************************************************)
(*                          Parallel Beta-reduction                 *)
(********************************************************************)

Reserved Notation " t ==> s " (at level 15, left associativity).
Inductive parallelStep : term -> term -> Prop :=
  | par_var :
      forall n : nat,
      var n ==> var n
  | par_lam :
      forall M M' : term,
      M ==> M'
        -> lam M ==> lam M'
  | par_red :
      forall M N M' N': term,
      M ==> M'
        -> N ==> N'
        -> app (lam M) N ==> M' [ <- N' ]
  | par_app :
      forall M N M' N': term,
      M ==> M'
        -> N ==> N'
        -> app M N ==> app M' N'
  where " t ==> s " := (parallelStep t s).
Hint Resolve par_red par_var par_lam par_app.

Reserved Notation " t ==>> s " (at level 15, left associativity).
Inductive parallelReduction : term -> term -> Prop :=
  | par_refl :
      forall M N : term,
      M ==> N
        -> M ==>> N
  | par_trans :
      forall M N P : term,
      M ==>> N
        -> N ==>> P
        -> M ==>> P
  where " t ==>> s " := (parallelReduction t s).

Lemma parallelStep_refl :
  forall (t : term),
  t ==> t.
Proof.
  intros t; induction t; auto.
Qed.

Lemma parallelReduction_refl :
  forall (t : term),
  t ==>> t.
Proof.
  intros t.
  apply par_refl.
  apply parallelStep_refl.
Qed.
Hint Resolve parallelStep_refl parallelReduction_refl.

Lemma parallelShift :
  forall (n m : nat)(t s : term),
  t ==> s
    -> t ! (S n) ^ m ==> s ! (S n) ^ m.
Proof.
  intros n m t s Pts. generalize n m. clear n m.
  induction Pts; subst; auto.
    intros; simpl; apply par_lam; apply IHPts.
    intros; rewrite (subst_3 M' N' (S n) m 1); simpl.
      apply par_red.
        replace (m+1) with (S m).
          apply IHPts1.
          omega.
        replace (m + 1 - 1) with m.
          apply IHPts2.
          omega.
      omega.
      auto.
      omega.
    intros. simpl. apply par_app.
      apply IHPts1.
      apply IHPts2.
Qed.

Lemma parallelSubstitute :
  forall (n : nat)(t s u v : term),
  t ==> s
    -> u ==> v
    -> t [ S n <- u ] ==> s [ S n <- v ].
Proof.
  intros n t s u v Pts Puv. generalize n. clear n.
  induction Pts; subst; auto.
    intros. simpl.
    destruct (lt_eq_lt_dec n (S n0)) as [ [ H1 | H2 ] | H3 ].
      apply parallelStep_refl. subst n.
      apply (parallelShift n0 0 u v); auto.
      apply parallelStep_refl.
    intros. simpl. apply par_lam.  apply IHPts.
    intros. simpl. rewrite (subst_travers M' N' v (S n)). simpl. apply par_red.
    replace (S (n + 1)) with (S(S n)). apply (IHPts1 (S n)). omega.
    apply (IHPts2 n). omega.
    intros. simpl. apply par_app. apply IHPts1. apply IHPts2.
  Qed.

(********************************************************************)
(*        Equivalence between reduction and parallel reduction      *)
(********************************************************************)

Lemma betaStep_parallelStep :
  forall M N : term,
  M --> N
    -> M ==> N.
Proof.
  simple induction 1; auto.
Qed.

Lemma betaReduction_parallelReduction :
  forall M N : term,
  M -->> N
    -> M ==>> N.
Proof.
  simple induction 1; intros.
  apply par_refl; induction H0; auto.
  apply par_refl; auto.
  apply par_trans with N0; trivial.
Qed.

Lemma parallelReduction_betaReduction :
  forall M N : term,
  M ==>> N
    -> M -->> N.
Proof.
  simple induction 1.
  2: intros; apply beta_trans with N0; trivial.
  simple induction 1.
  intros; apply beta_refl; trivial.
  intros; apply betaReduction_lam; trivial.
  intros; apply betaReduction_redex; trivial.
  intros; apply betaReduction_app; trivial.
Qed.

(*******************************************************************)
(*             Maximal Parallel Beta-reduction                     *)
(*******************************************************************)

Reserved Notation " t * " (at level 1, left associativity).
Fixpoint maximumStep (t : term) : term :=
  match t with
  | var n => var n
  | lam t => lam t*
  | app (lam s) v => s* [ <- v* ]
  | app u v => app u* v*
  end
  where " t * " := (maximumStep t)  .

Lemma maximumStep_parallelStep :
  forall (t : term),
  t ==> t*.
Proof.
  intros t.
  induction t; simpl.
    apply par_var; auto.
    apply par_lam; auto.
    induction t1; simpl; auto.
      apply par_red; simpl; auto.
      inversion IHt1; subst; auto.
Qed.

Lemma parallelStep_maximumStep :
  forall (t s : term),
  t ==> s
    -> s ==> t*.
Proof.
  induction t.
    intros; inversion H; subst; auto.
    intros. inversion H; subst.
      simpl. inversion H; subst. apply par_lam. apply IHt; auto.
    intros; induction t1. inversion H; subst. inversion H2; subst.
        simpl. apply par_app. apply par_var. inversion H; subst. apply IHt2; auto.
      inversion H; subst; auto.
        simpl. apply parallelSubstitute; auto.
        assert (au : lam M' ==> (lam t1)*). apply IHt1; auto. inversion au; subst. auto.
        inversion H2; subst; auto. simpl. apply par_red; auto.
        assert (au : lam M'0 ==> (lam t1)*). apply IHt1; auto. inversion au; subst. auto.
      inversion H; subst. simpl. apply par_app. inversion H. subst. apply IHt1; auto.
        inversion H. subst. apply IHt2; auto.
Qed.

(********************************************************************)
(*                       Diamond Properties                         *)
(********************************************************************)

Lemma parallelStep_diamond :
  forall (t s r : term),
  t ==> s
    -> t ==> r
    -> { u : term |  s ==> u /\ r ==> u }.
Proof.
  intros t s r Pts Ptr.
  exists t*.
  split;
    [ apply (parallelStep_maximumStep t s)
    | apply (parallelStep_maximumStep t r) ]; auto;
      apply maximumStep_maximumStep; auto.
Qed.

Lemma parallelReduction_strip :
  forall (t s r : term),
  t ==> s
    -> t ==>> r
    -> exists u : term,  s ==>> u /\ r ==> u.
Proof.
  intros t s r Pts Rtr. generalize s Pts. clear s Pts.
  induction Rtr; subst.
  intros. destruct (parallelStep_diamond M s N) as [ u [ H1 H2 ] ]; auto.
  exists u. split; auto; apply par_refl; auto.
  intros.
    destruct (IHRtr1 s Pts) as [ u [ H1 H2 ] ].
    destruct (IHRtr2 u H2) as [ v [ G1 G2 ] ].
  exists v. split; auto.
  apply (par_trans s u v); auto.
Qed.

Theorem parallelReduction_diamond :
  forall (t s r : term),
  t ==>> s
    -> t ==>> r
    -> exists u : term,  s ==>> u /\ r ==>> u.
Proof.
  intros t s r Rts Rtr. generalize r Rtr. clear r Rtr.
  induction Rts.
    intros. destruct (parallelReduction_strip M N r) as [ u [ H1 H2 ] ]; auto.
    exists u. split; auto; apply par_refl; auto.
    intros.
      destruct (IHRts1 r Rtr) as [ u [ H1 H2 ] ].
      destruct (IHRts2 u H1) as [ v [ H3 H4 ] ].
      exists v. split; auto. apply (par_trans r u v); auto.
Qed.

Theorem Church_Rosser :
  forall (t s r : term),
  t -->> s
    -> t -->> r
    -> exists u : term,  s -->> u /\ r -->> u.
Proof.
  intros t s r Rts Rtr.
  apply betaReduction_parallelReduction in Rts.
  apply betaReduction_parallelReduction in Rtr.
  destruct (parallelReduction_diamond t s r Rts Rtr ) as [ u [ Rsu Rry ] ].
  exists u; split; apply parallelReduction_betaReduction; auto.
Qed.

(********************************************************************)
(*                          Applications                            *)
(********************************************************************)

Fixpoint multiStep (n : nat)(t : term) :=
  match n with
  | O => t
  | S m => multiStep m (maximumStep t)
  end.

Definition BetaReduction (n : nat)(t : Term) :=
  (restoreSymbols (multiStep n (removeSymbols t (freeVariables t))))(freeVariables t).

(********************************************************************)
(*                               Examples                           *)
(********************************************************************)

(*  Boolean constants *)

Definition tru := \1 2 -> #1.
Definition fls := \1 2 -> #2.

Definition ifte := \1 2 3 -> #1 ' #2 ' #3.
Definition and :=  \1 2 -> #1 ' #2 ' fls.
Definition or :=  \1 2 -> #1 ' tru ' #2.
Definition not :=  \1 -> #1 ' fls ' tru.

Compute (BetaReduction 3 (ifte ' tru ' #1 ' #2)).
Compute (BetaReduction 3 (ifte ' fls ' #1 ' #2)).

Compute (BetaReduction 3 (and ' tru ' tru)).
Compute (BetaReduction 3 (and ' tru ' fls)).
Compute (BetaReduction 3 (and ' fls ' tru)).
Compute (BetaReduction 3 (and ' fls ' fls)).

Compute (BetaReduction 3 (or ' tru ' tru)).
Compute (BetaReduction 3 (or ' tru ' fls)).
Compute (BetaReduction 3 (or ' fls ' tru)).
Compute (BetaReduction 3 (or ' fls ' fls)).

Compute (BetaReduction 3 (not ' tru)).
Compute (BetaReduction 3 (not ' fls)).

(*  Pairs *)

Definition pair := \1 2 3 -> #3 ' #1 ' #2.
Definition fst := \1 -> #1 ' tru.
Definition snd := \1 -> #1 ' fls.

Compute (BetaReduction 5 (fst ' (pair ' #1 ' #2))).
Compute (BetaReduction 5 (snd ' (pair ' #1 ' #2))).

(*  Numerals *)

Definition c0  := \1 2 -> #2.
Definition c1  := \1 2 -> #1 ' #2.
Definition c2  := \1 2 -> #1 ' (#1 ' #2).
Definition c3  := \1 2 -> #1 ' (#1 ' (#1 ' #2)).
Definition c4  := \1 2 -> #1 ' (#1 ' (#1 ' (#1 ' #2))).
Definition c5  := \1 2 -> #1 ' (#1 ' (#1 ' (#1 ' (#1 ' #2)))).
Definition c6  := \1 2 -> #1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' #2))))).
Definition c7  := \1 2 -> #1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' #2)))))).
Definition c8  := \1 2 -> #1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' #2))))))).
Definition c9  := \1 2 -> #1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' #2)))))))).
Definition c10 := \1 2 -> #1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' #2))))))))).
Definition c11 := \1 2 -> #1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' #2)))))))))).
Definition c12 := \1 2 -> #1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' (#1 ' #2))))))))))).

Definition numeral (t : Term) : nat := (termLength t) - 3.

Compute (numeral c0).
Compute (numeral c1).
Compute (numeral c2).
Compute (numeral c3).
Compute (numeral c4).
Compute (numeral c5).
Compute (numeral c6).
Compute (numeral c7).
Compute (numeral c8).
Compute (numeral c9).

Definition iszero := \1 -> #1 ' (\2 -> fls) ' tru.

Definition succ := \3 1 2 -> #1 ' (#3 ' #1 ' #2).
Definition plus :=\4 3 1 2 -> #4 ' #1 ' (#3 ' #1 ' #2).

Definition zz := pair ' c0 ' c0.
Definition ss := \1 -> pair ' (snd ' #1) ' (plus ' c1 ' (snd ' #1)).
Definition pred := \1 -> fst ' (#1 ' ss ' zz).
Definition minus :=\1 2 -> #2 ' pred ' #1.

Definition mult :=  \1 2 3 -> #1 ' (#2 ' #3).
Definition power :=  \1 2 -> #2 ' #1.

Definition equal :=  \1 2 -> and ' (iszero ' (#1 ' pred ' #2)) ' (iszero ' (#2 ' pred ' #1)).

Compute (numeral (BetaReduction 3 (succ ' c0))).
Compute (numeral (BetaReduction 3 (succ ' c1))).
Compute (numeral (BetaReduction 3 (succ ' c2))).
Compute (numeral (BetaReduction 3 (succ ' c3))).
Compute (numeral (BetaReduction 3 (succ ' c4))).

Compute (numeral (BetaReduction 6 (pred ' c0))).
Compute (numeral (BetaReduction 6 (pred ' c1))).
Compute (numeral (BetaReduction 8 (pred ' c2))).
Compute (numeral (BetaReduction 8 (pred ' c3))).
Compute (numeral (BetaReduction 8 (pred ' c4))).
Compute (numeral (BetaReduction 8 (pred ' c5))).

Compute (numeral (BetaReduction 4 (plus ' c2 ' c3))).
Compute (numeral (BetaReduction 4 (plus ' c3 ' c5))).

Compute (numeral (BetaReduction 16 (minus ' c4 ' c2))).
Compute (numeral (BetaReduction 21 (minus ' c8 ' c3))).
Compute (numeral (BetaReduction 46 (minus ' c12 ' c8))).

Compute (numeral (BetaReduction 4 (mult ' c2 ' c3))).
Compute (numeral (BetaReduction 4 (mult ' c3 ' c5))).
Compute (numeral (BetaReduction 4 (mult ' c5 ' c4))).

Compute (numeral (BetaReduction 52 (power ' c2 ' c10))).
Compute (numeral (BetaReduction 52 (power ' c3 ' c3))).
Compute (numeral (BetaReduction 52 (power ' c6 ' c3))).

Compute (BetaReduction 3 (iszero ' c0)).
Compute (BetaReduction 3 (iszero ' c1)).
Compute (BetaReduction 3 (iszero ' c2)).
Compute (BetaReduction 3 (iszero ' c3)).
Compute (BetaReduction 3 (iszero ' c4)).

Compute (BetaReduction 32 (equal ' c5 ' c5)).
Compute (BetaReduction 32 (equal ' c5 ' c6)).

(*  Recursion *)

Definition omega := (\1 -> #1 ' #1 ) ' (\1 -> #1 ' #1 ).

Definition fixpoint := \1 -> ((\2 -> #1 ' (\3 -> #2 ' #2 ' #3 )) ' (\2 -> #1 ' (\3 -> #2 ' #2 ' #3 ))).
Definition ff := \1 2 -> ifte ' (iszero ' #2) ' (\3 -> c1) ' (\3 -> (mult ' #2 ' (#1 ' (pred ' #2)))) ' c0.
Definition factorial :=  fixpoint ' ff.

Compute (BetaReduction 4 (omega ' omega)).

Compute (numeral (BetaReduction 8 (factorial ' c0))).
Compute (numeral (BetaReduction 15 (factorial ' c1))).
Compute (numeral (BetaReduction 20 (factorial ' c2))).
Compute (numeral (BetaReduction 25 (factorial ' c3))).
Compute (numeral (BetaReduction 30 (factorial ' c4))).

(*  Tests *)

Definition t1 := #1 ' (\2 3 -> #1).
Definition G1 :=  (sort (freeVariables t1)).
Definition s1 := removeSymbols t1 G1.
Compute s1.
Compute (restoreSymbols s1 G1).

Definition t2 := #1 ' (\2 -> #1) ' (\2 -> #1 ' (\3 -> #1)).
Definition G2 :=  (sort (freeVariables t2)).
Definition s2 := removeSymbols t2 G2.
Compute s2.
Compute (restoreSymbols s2 G2).

Definition t3 := \1 -> (\2 -> #2 ' (\3 -> #3)) ' (\2 -> #1 ' #2).
Definition G3 :=  (sort (freeVariables t3)).
Definition s3 := removeSymbols t3 G3.
Compute (restoreSymbols s3 G3).

Definition t4 := \ 1 2 3 -> #1 ' #3 ' (#2 ' #3).
Definition G4 :=  (sort (freeVariables t4)).
Definition s4 := removeSymbols t4 G4.
Compute (restoreSymbols s4 G4).

Definition t5 := (\1 2 -> (#3 ' #1 ' #2)) ' (\1 -> #2 ' #1).
Definition G5 :=  (sort (freeVariables t5)).
Definition s5 := removeSymbols t5 G5.
Compute (restoreSymbols s5 G5).

Definition t6 := \4 -> #3 ' (\1 -> #2 ' #1) ' #4.
Definition G6 := sort(freeVariables t6).
Definition s6 := removeSymbols t6 G6.
Compute (restoreSymbols s6 G6).

Compute s5.
Definition s5x := (lam (app (app (var 4)(var 2))(var 1))).
Definition s5y := lam (app (var 2)(var 1)).
Compute (s5x [ <- s5y ]).

Compute (multiStep  1 s5).