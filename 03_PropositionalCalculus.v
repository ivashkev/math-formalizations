(* 

 PROPOSITIONAL LOGIC

 Evgeny V Ivashkevich
 
 E-mail: ivashkev@yandex.ru

 January 29, 2019

 Abstract: In this file, we formalize algebra and calculus of propositions 
           in Coq and give relatively simple proofs of the theorems of 
           soundness and completeness. Finally, we prove the equivalence of 
           the calculus of propositions and the rules of natural deduction.
 
*)

Require Import Coq.Program.Equality.
Require Import List.
Import ListNotations.
Notation "x :- L" := (In x L)(at level 20).

Definition eq_nat_dec :
  forall x y : nat, { x = y } + { x <> y }.
Proof.
  induction x; destruct y.
  - now left.
  - now right.
  - now right.
  - destruct (IHx y); [left|right]; auto.
Defined.

(* ALPHABET *)

(* propositional symbols: P1, P2, P3 ... *)
Definition symbol := nat.

Definition word : Set
  := list symbol.
Definition nds : word -> word
  := nodup eq_nat_dec.

(* LANGUAGE *)

Inductive formula : Set :=
         | falsehood : formula
         | variable  : symbol -> formula
         | implies   : formula -> formula -> formula
         .

(* language is decidable *)
Definition eq_formula_dec :
  forall (P Q : formula), { P = Q } + { P <> Q }.
Proof.
  induction P; destruct Q;
  try (left; reflexivity);
  try (right; discriminate).
  { destruct (eq_nat_dec s s0).
    { left; subst; reflexivity. }
    { right; contradict n; inversion n; subst; reflexivity. }
  }
  { destruct (IHP1 Q1);
    [destruct (IHP2 Q2);
    [left; f_equal;assumption |]|];
    right; injection; intros; contradiction.
  }
Defined.

(* context *)
Definition context : Set
  := list formula.

Definition ndf : context -> context
  := nodup eq_formula_dec.

(* LOGICAL FUNCTIONS *)

Definition truth : formula
  := implies falsehood falsehood.

Notation "_|_"
  := (falsehood)
  (at level 1).
Notation "# x"
  := (variable x)
  (at level 1).
Notation "P --> Q"
  := (implies P Q)
  (at level 16, right associativity).

Definition Not (P : formula) : formula
  := (P --> _|_).
Notation "^ P"
  := (Not P)
  (at level 0).
Definition And (P Q : formula) : formula
  := ^ (P --> ^ Q).
Notation "P 'and' Q"
  := (And P Q)
  (at level 15, right associativity).
Definition Or (P Q : formula) : formula
  := (^ P --> Q).
Notation "P 'or' Q"
  := (Or P Q)
  (at level 15, right associativity).
Definition Iff (P Q : formula)
  := (P --> Q) and (Q --> P).
Notation "P <--> Q"
  := (Iff P Q)
  (at level 15, right associativity).

(* VALUE OF SYMBOLS AND FORMULAE *)

Record evaluation : Type := eval { symbolValue : symbol -> bool }.

Fixpoint formulaValue (E : evaluation)(P : formula) : bool :=
  match P with
  | falsehood   => false
  | variable x  => symbolValue E x
  | implies A B => if (formulaValue E A)
                   then (formulaValue E B)
                   else true
  end.

Definition Compatible (E : evaluation)(G : context) : Prop
  := forall (P : formula), P :- G -> formulaValue E P = true.

Definition Eq (G : context)(P Q : formula) : Prop
  := forall (E : evaluation),
     Compatible E G -> formulaValue E P = formulaValue E Q.
Notation "G |== [ P ] == [ Q ]"
  := (Eq G P Q)
  (at level 80, right associativity).
Notation "G |== P"
  := (G |== [ P ] == [ truth ])
  (at level 80).
Notation "|== P"
  := ([] |== P)
  (at level 80).

Lemma Compatible_empty (E : evaluation) :
  Compatible E [].
Proof.
  intros P H2.
  simpl in H2.
  contradiction.
Qed.

Lemma ValidProposition (P : formula) :
  |== P
    <-> forall (E : evaluation), formulaValue E P = true.
Proof.
  unfold Eq.
  split; intros; apply H; auto; apply Compatible_empty.
Qed.

Lemma Compatible_ext_hyp (E : evaluation)(G : context)(P : formula) :
  Compatible E (P :: G)
    <-> Compatible E G /\ formulaValue E P = true.
Proof.
  intros; split; intros *.
  { split.
    { intros Q Hq. apply H. right; auto. }
    { apply H. left; auto. }
  }
  { intros [ H1 H2 ] Q Hq.
    destruct (eq_formula_dec P Q) as [ PeqQ | nPeqQ ].
    { subst; auto. }
    { apply H1. unfold In in Hq. destruct Hq.
      {contradiction. }
      { auto. }
    }
  }
Qed.

Lemma Compatible_sum_ctx (E : evaluation)(G1 G2 : context) :
  Compatible E (G1 ++ G2)
    <-> Compatible E G1 /\ Compatible E G2.
Proof.
  intros.
  induction G1.
  { split; intros; try split; simpl in *; auto.
    { apply Compatible_empty; auto. }
    { destruct H; auto. }
  }
  { split; intros; try split.
    { unfold Compatible in *. intros P H1. apply H.
      apply in_app_iff; left; auto.
    }
    { unfold Compatible in *. intros P H1. apply H.
      apply in_app_iff; right; auto.
    }
    { destruct H as [ H1 H2 ]; unfold Compatible in *.
      intros P H0.
      destruct (in_app_or (a :: G1) G2 P); auto.
    }
  }
Qed.

Lemma Compatible_nodup_ctx (E : evaluation)(G : context) :
  Compatible E (ndf G)
    <-> Compatible E G.
Proof.
  intros.
  induction G.
  { split; intros; try split; simpl in *; auto. }
  { split; intros.
    { apply Compatible_ext_hyp. unfold Compatible in *.
      split.
      { apply IHG. intros P H1. apply H.
        apply nodup_In. apply (nodup_In eq_formula_dec G P) in H1.
        right; auto.
     }
      { apply H. apply nodup_In. left; auto. }
    }
    { unfold Compatible in *. intros P H1. apply H.
      apply (nodup_In eq_formula_dec (a :: G) P) in H1; auto.
    }
  }
Qed.

(* PROPOSITIONAL ALGEBRA *)

Lemma pa_as (G : context)(P : formula) :
  P :- G
    -> G |== P.
Proof.
  unfold Eq, Compatible.
  intros.
  apply H0; auto.
Qed.

Lemma pa_ap (G : context)(P Q : formula) :
  G |== P --> Q
    -> G |== P
    -> G |== Q.
Proof with eauto.
  unfold Eq.
  intros.
  simpl in *.
  assert (implb (formulaValue E P)(formulaValue E Q) = true).
  { apply (H E)... }
  assert (formulaValue E P = true). { apply (H0 E)... }
  rewrite H3 in *.
  destruct (formulaValue E Q);
  simpl; try reflexivity; simpl in *; assumption.
Qed.

Lemma pa_K (G : context)(P Q : formula) :
  G |== P --> (Q --> P).
Proof.
  unfold Eq.
  intros.
  simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q); simpl;
  try reflexivity; simpl in *; firstorder.
Qed.

Lemma pa_S (G : context)(P Q R : formula) :
  G |== (P --> Q --> R) --> (P --> Q) --> (P --> R).
Proof.
  unfold Eq.
  intros.
  simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  destruct (formulaValue E R);
  simpl; try reflexivity;
  simpl in *; firstorder.
Qed.

Lemma pa_C (G : context)(P : formula) :
  G |== ^ ^ P --> P.
Proof.
  unfold Eq.
  intros.
  simpl.
  destruct (formulaValue E P); simpl;
  try reflexivity; simpl in *; firstorder.
Qed.

Lemma pa_impl_refl (G : context)(P : formula) :
  G |== P --> P.
Proof.
  apply (pa_ap G (P --> P --> P)).
  { apply (pa_ap G (P --> (P --> P) --> P)).
    { apply (pa_S G P (P --> P)). }
    { apply pa_K. }
  }
  { apply pa_K. }
Qed.

Lemma pa_True (G : context) :
  G |== truth.
Proof.
  apply pa_impl_refl.
Qed.

Lemma pa_ext (G : context)(P Q : formula) :
  G |== P
    -> G |== Q --> P.
Proof.
  intros H.
  apply (pa_ap G P); try assumption.
  apply pa_K.
Qed.

Lemma pa_ext_hyps (G : context)(P Q : formula) :
  G |== P
    -> Q :: G |== P.
Proof.
  intros H.
  unfold Eq in *.
  intros f CfG.
  apply Compatible_ext_hyp in CfG.
  destruct CfG as [ CfG VfQ ].
  apply H; auto.
Qed.

Lemma pa_ctx_ext (G1 G2 : context)(P : formula) :
  G1 |== P
    -> G2 ++ G1 |== P.
Proof.
  intros H.
  unfold Eq in *.
  intros f CfG.
  apply Compatible_sum_ctx in CfG.
  destruct CfG as [ CfG1 CfG2 ].
  apply H; auto.
Qed.

(** Deduction rule *)

Lemma pa_in (G : context)(P Q : formula) :
  P :: G |== Q
    -> G |== P --> Q.
Proof with eauto.
  unfold Eq; simpl; intros.
  assert (Compatible E (P :: G) -> formulaValue E Q = true)...
  clear H.
  destruct (formulaValue E Q); simpl;
  try reflexivity; simpl in *; firstorder.
  { destruct (formulaValue E P); simpl... }
  { rewrite Compatible_ext_hyp in H1.
    destruct (formulaValue E P); simpl...
  }
Qed.

Lemma pa_mp (G : context)(P Q : formula) :
  G |== P --> Q
    -> P :: G |== Q.
Proof.
  intros H.
  apply (pa_ap (P :: G) P Q).
  { apply pa_ext_hyps; assumption. }
  apply pa_as; left; reflexivity.
Qed.

Lemma pa_mp_hyp (G : context)(P Q : formula) :
  P :: (P --> Q) :: G |== Q.
Proof.
  apply pa_mp.
  apply pa_as; auto; left; reflexivity.
Qed.

Lemma pa_mp_var (G : context)(P Q : formula) :
  G |== P
    -> G |== (P --> Q) --> Q.
Proof.
  intros H.
  apply pa_in.
  apply (pa_ext_hyps G P (P --> Q)) in H.
  apply (pa_ap (P --> Q :: G) P); auto.
  apply pa_as; auto; left; reflexivity.
Qed.

Lemma pa_excl (G : context)(P Q : formula) :
  G |== P
    -> P :: G |== Q
    -> G |== Q.
Proof.
  intros H1 H2.
  apply (pa_ap G P Q); auto.
  apply pa_in; assumption.
Qed.

(** Context Theorems *)

Lemma pa_hyp_elim (G : context)(P Q : formula) :
  P :: P :: G |== Q
    -> P :: G |== Q.
Proof.
  intros H.
  unfold Eq in *.
  intros f CfG.
  apply H; auto.
  apply Compatible_ext_hyp; split; auto.
  apply Compatible_ext_hyp in CfG.
  destruct CfG; auto.
Qed.

Lemma pa_swap_hyps (G : context)(P Q R : formula) :
  P :: Q :: G |== R
    -> Q :: P :: G |== R.
Proof.
  intros H.
  unfold Eq in *.
  intros f CfG.
  apply H; auto.
  apply Compatible_ext_hyp in CfG.
  destruct CfG as [ CfG VfQ ].
  apply Compatible_ext_hyp in CfG.
  destruct CfG as [ CfG VfP ].
  apply Compatible_ext_hyp; split; auto.
  apply Compatible_ext_hyp; split; auto.
Qed.

Lemma pa_ctx_sym (G1 G2 : context)(P : formula) :
  G1 ++ G2 |== P
    -> G2 ++ G1 |== P.
Proof.
  intros H.
  unfold Eq in *.
  intros f CfG.
  apply H; auto.
  apply Compatible_sum_ctx in CfG.
  destruct CfG as [ CfG1 CfG2 ].
  apply Compatible_sum_ctx; split; auto.
Qed.

Lemma pa_swap_ctx (G1 G2 : context)(P Q R: formula) :
  G1 ++ [ P ; Q ] ++ G2 |== R
    -> G1 ++ [ Q ; P ] ++ G2 |== R.
Proof.
  intros H.
  apply pa_ctx_sym in H.
  rewrite <- app_assoc in H.
  apply pa_ctx_sym.
  rewrite <- app_assoc.
  apply pa_swap_hyps; auto.
Qed.

Lemma pa_first_hyp_last (G : context)(P Q : formula) :
  [ P ] ++ G |== Q
    -> G ++ [ P ] |== Q.
Proof.
  intros H.
  unfold Eq in *.
  intros f CfG.
  apply H; auto.
  apply Compatible_sum_ctx in CfG.
  destruct CfG as [ CfG VfQ ].
  apply Compatible_sum_ctx. split; auto.
Qed.

Lemma pa_ctx_split_sym (G1 G2 G3 : context)(P : formula) :
  G1 ++ G2 ++ G3 |== P
    -> G2 ++ G1 ++ G3 |== P.
Proof.
  intros H.
  unfold Eq in *.
  intros f CfG.
  apply H; auto.
  apply Compatible_sum_ctx in CfG.
  destruct CfG as [ CfG2 CfG1 ].
  apply Compatible_sum_ctx in CfG1.
  destruct CfG1 as [ CfG1 CfG3 ].
  apply Compatible_sum_ctx; split; auto.
  apply Compatible_sum_ctx; split; auto.
Qed.

Lemma pa_ctx_nodup (G : context)(P : formula) :
  G |== P <-> ndf G |== P.
Proof.
  split; intros * H; unfold Eq in *;
  intros f CfG; apply H; apply Compatible_nodup_ctx; auto.
Qed.

(** Transitivity Theorems *)

Lemma pa_asoc (G : context)(P Q R : formula) :
  G |== P --> Q
    -> G |== Q --> R
    -> G |== P --> R.
Proof.
  intros H1 H2.
  apply pa_in.
  apply (pa_ap (P :: G) Q R).
  { apply pa_ext_hyps; assumption. }
  { apply pa_mp; assumption. }
Qed.

Lemma pa_asoc_pc (G : context)(P Q R : formula) :
  P :: G |== Q
    -> Q :: G |== R
    -> P :: G |== R.
Proof.
  intros H1 H2.
  apply pa_mp.
  apply (pa_asoc G P Q R).
  { apply pa_in; assumption. }
  { apply pa_in; assumption. }
Qed.

(** Contraposition Theorems *)

Lemma pa_not_intro (G : context)(P : formula) :
  G |== P
    -> G |== ^ ^ P.
Proof.
  intros H.
  apply pa_mp_var.
  assumption.
Qed.

Lemma pa_not_elim (G : context)(P : formula) :
  G |== ^ ^ P
    -> G |== P.
Proof.
  intros H.
  apply (pa_ap G (^ ^ P)).
  { apply pa_C. }
  { assumption. }
Qed.

Lemma pa_contr_pc (G : context)(P Q : formula) :
  G |== P --> Q
    -> G |== ^ Q --> ^ P.
Proof.
  intros H.
  apply pa_in. apply pa_in.
  apply pa_swap_hyps.
  apply pa_mp in H.
  apply pa_mp.
  apply pa_not_intro.
  assumption.
Qed.

Lemma pa_contr (G : context)(P Q : formula) :
  G |== ^ Q --> ^ P
    -> G |== P --> Q.
Proof.
  intros H.
  apply pa_mp in H.
  apply pa_mp in H.
  apply pa_swap_hyps in H.
  apply pa_in in H.
  apply pa_in.
  apply pa_not_elim.
  assumption.
Qed.

Lemma pa_contr_hyp (G : context)(P Q : formula) :
  ^ Q :: G |== ^ P
    -> P :: G |== Q.
Proof.
  intros H.
  apply pa_in in H.
  apply pa_mp.
  apply pa_contr; assumption.
Qed.

Lemma pa_contr_hyp_pc (G : context)(P Q : formula) :
  P :: G |== Q
    -> ^ Q :: G |== ^ P.
Proof.
  intros H.
  apply pa_in in H.
  apply pa_mp.
  apply pa_contr_pc; assumption.
Qed.

Lemma pa_contr_var (G : context)(P Q : formula) :
  G |== (^ Q --> ^ P) --> P --> Q.
Proof.
  apply pa_in.
  apply pa_contr.
  apply pa_as; auto; left; reflexivity.
Qed.

Lemma pa_contradiction (G : context)(P : formula) :
  P :: ^ P :: G |== _|_.
Proof.
  apply pa_mp.
  apply pa_as; auto; left; reflexivity.
Qed.

Lemma pa_exfalso (G : context)(P : formula) :
  G |== _|_
    -> G |== P.
Proof.
  intros H.
  apply pa_not_elim.
  apply pa_in.
  apply pa_ext_hyps; assumption.
Qed.

Lemma pa_and_imp (G : context)(P Q : formula) :
  G |== P
    -> G |== ^ Q
    -> G |== ^ (P --> Q).
Proof.
  intros.
  intros E CfG. unfold Eq in *; simpl in *.
  assert (formulaValue E P = true). apply (H E CfG).
  assert (implb (formulaValue E Q) false = true).
  apply (H0 E CfG).
  destruct (formulaValue E P); 
  destruct (formulaValue E Q); simpl; auto.
Qed.

Lemma DoubleNegationLaw (G : context)(P : formula) :
  G |== [ ^ ^ P ] == [ P ].
Proof.
  unfold Eq.
  intros; simpl.
  destruct (formulaValue E P); simpl; reflexivity.
Qed.

(** Equivalencies of Logical Functions *)

Lemma ExcludedMiddleLaw (G : context)(P : formula) :
  G |== P or ^ P.
Proof.
  unfold Eq, Or. 
  intros; simpl.
  destruct (formulaValue E P);
  simpl; reflexivity.
Qed.

Lemma iffEq (G : context)(P Q : formula) :
  G |== [ P ] == [ Q ]
    <->  G |== P <--> Q.
Proof.
  unfold Eq.
  intros; simpl. split.
  intros; simpl. intros.
  assert (formulaValue E P = formulaValue E Q).
  apply (H E). simpl; auto.
  simpl;
    destruct (formulaValue E P);
    destruct (formulaValue E Q); simpl; try reflexivity; auto.
  intros.
  assert (formulaValue E ((P --> Q) and (Q --> P)) = true).
  apply (H E); auto.
  simpl in *.
  destruct (formulaValue E P);
    destruct (formulaValue E Q); simpl; 
    try reflexivity; simpl in *; firstorder.
Qed.

Lemma LawOfContradiction (G : context)(P : formula) :
  G |== [ P and ^ P ] == [ _|_ ].
Proof.
  unfold Eq, And.
  intros; simpl.
  destruct (formulaValue E P);
  simpl; reflexivity.
Qed.

Lemma And_sym (G : context)(P Q : formula) :
  G |== [ P and Q ] == [ Q and P ].
Proof.
  unfold Eq, And.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  simpl; reflexivity.
Qed.

Lemma Or_sym (G : context)(P Q : formula) :
  G |== [ P or Q ] == [ Q or P ].
Proof.
  unfold Eq, Or.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  simpl; reflexivity.
Qed.

Lemma And_assoc (G : context)(P Q R : formula) :
  G |== [ P and (Q and R) ] == [ (P and Q) and R ].
Proof.
  unfold Eq, And.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  destruct (formulaValue E R);
  simpl; reflexivity.
Qed.

Lemma Or_assoc (G : context)(P Q R : formula):
  G |== [ P or (Q or R) ] == [ (P or Q) or R ].
Proof.
  unfold Eq, Or.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  destruct (formulaValue E R);
  simpl; reflexivity.
Qed.

Lemma And_distib (G : context)(P Q R : formula) :
  G |== [ (P or Q) and R ] == [ (P and R) or (Q and R) ].
Proof.
  unfold Eq, And, Or.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  destruct (formulaValue E R);
  simpl; reflexivity.
Qed.

Lemma Or_distib (G : context)(P Q R : formula) :
  G |== [ (P and Q) or R ] == [ (P or R) and (Q or R) ].
Proof.
  unfold Eq, And, Or.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  destruct (formulaValue E R);
  simpl; reflexivity.
Qed.

Lemma Impl_equiv (G : context)(P Q : formula) :
  G |== [ P --> Q ] == [ ^ P or Q ].
Proof.
  unfold Eq, And, Or.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  simpl; reflexivity.
Qed.

Lemma DeMorgan_And (G : context)(P Q : formula) :
  G |== [ ^ (P and Q) ] == [ ^ P or ^ Q ].
Proof.
  unfold Eq, And, Or.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  simpl; reflexivity.
Qed.

Lemma DeMorgan_Or (G : context)(P Q : formula) :
  G |== [ ^ (P or Q) ] == [ ^ P and ^ Q ].
Proof.
  unfold Eq, And, Or.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  simpl; reflexivity.
Qed.

Lemma Absorbtion_And (G : context)(P Q : formula) :
  G |== [ (P and Q) or P ] == [ P ].
Proof.
  unfold Eq, And, Or.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  simpl; reflexivity.
Qed.

Lemma Absorbtion_Or (G : context)(P Q : formula) :
  G |== [ P or (Q and P) ] == [ P ].
Proof.
  unfold Eq, And, Or.
  intros; simpl.
  destruct (formulaValue E P);
  destruct (formulaValue E Q);
  simpl; reflexivity.
Qed.

(* PROPOSITIONAL CALCULUS *)

Reserved Notation "G |-- F" (at level 70).
Inductive PC : context -> formula -> Prop :=
         | pc_as (G : context)(P : formula) :
             P :- G
               -> G |-- P
         | pc_ap (G : context)(P Q : formula) :
             G |-- P --> Q
               -> G |-- P
               -> G |-- Q
         | pc_K (G : context)(P Q : formula) :
             G |-- P --> (Q --> P)
         | pc_S (G : context)(P Q R: formula) :
             G |-- (P --> Q --> R) --> (P --> Q) --> (P --> R)
         | pc_C (G : context)(P : formula) :
             G |-- ^ ^ P --> P
    where "G |-- F" := (PC G F).

Notation "|-- P"
  := ([] |-- P)
  (at level 80).

Lemma pc_impl_refl (G : context)(P : formula) :
  G |-- P --> P.
Proof.
  apply (pc_ap G (P --> P --> P)).
  { apply (pc_ap G (P --> (P --> P) --> P)).
    { apply (pc_S G P (P --> P)). }
    apply pc_K.
  }
  apply pc_K.
Qed.

Lemma pc_True (G : context) :
  G |-- truth.
Proof.
  apply pc_impl_refl.
Qed.

Lemma pc_ext (G : context)(P Q : formula) :
  G |-- P
    -> G |-- Q --> P.
Proof.
  intros H.
  apply (pc_ap G P). { apply pc_K. }
  assumption.
Qed.

Lemma pc_ext_hyps (G : context)(P Q : formula) :
  G |-- P
    -> Q :: G |-- P.
Proof.
  intros H.
  induction H.
  { apply pc_as; right; assumption. }
  { apply (pc_ap (Q :: G) P).
    { apply IHPC1. }
    assumption.
  }
  { apply pc_K. }
  { apply pc_S. }
  { apply pc_C. }
Qed.

Lemma pc_ctx_ext (G1 G2 : context)(P : formula) :
  G1 |-- P
    -> G2 ++ G1 |-- P.
Proof.
  intros H.
  induction G2.
  { assumption. }
  assert(H0 : (a :: G2) ++ G1 = a :: (G2 ++ G1)).
  { reflexivity. }
  rewrite H0.
  apply pc_ext_hyps; assumption.
Qed.

(** Deduction theorem *)

Lemma pc_in (G : context)(P Q : formula) :
  P :: G |-- Q
    -> G |-- P --> Q.
Proof.
  intros H.
  dependent induction H.
  { destruct H.
    { subst P0; apply pc_impl_refl. }
    { apply pc_ext; apply pc_as; assumption. }
  }
  { specialize (IHPC1 G P (JMeq_refl (P :: G))).
    specialize (IHPC2 G P (JMeq_refl (P :: G))).
    apply (pc_ap G (P --> P0)).
    { apply (pc_ap G (P --> P0 --> Q)).
      { apply pc_S. }
      apply IHPC1.
    }
    apply IHPC2.
  }
  { apply pc_ext; apply pc_K. }
  { apply pc_ext; apply pc_S. }
  { apply pc_ext; apply pc_C. }
Qed.

Lemma pc_mp (G : context)(P Q : formula) :
  G |-- P --> Q
    -> P :: G |-- Q.
Proof.
  intros H.
  apply (pc_ap (P :: G) P Q).
  { apply pc_ext_hyps; assumption. }
  apply pc_as; left; reflexivity.
Qed.

Lemma pc_mp_hyp (G : context)(P Q : formula) :
  P :: P --> Q :: G |-- Q.
Proof.
  apply pc_mp.
  apply pc_as; left; reflexivity.
Qed.

Lemma pc_mp_var (G : context)(P Q : formula) :
  G |-- P
    -> G |-- (P --> Q) --> Q.
Proof.
  intros H.
  apply pc_in.
  apply (pc_ext_hyps G P (P --> Q)) in H.
  apply (pc_ap (P --> Q :: G) P).
  { apply pc_as; left; reflexivity. }
  assumption.
Qed.

Lemma pc_excl (G : context)(P Q : formula) :
  G |-- P
    -> P :: G |-- Q
    -> G |-- Q.
Proof.
  intros H1 H2.
  apply (pc_ap G P Q).
  { apply pc_in; assumption. }
  assumption.
Qed.

(** context theorems *)

Lemma pc_hyp_elim (G : context)(P Q : formula) :
  P :: P :: G |-- Q
    -> P :: G |-- Q.
Proof.
  intros H.
  dependent induction H.
  { apply pc_as; firstorder. }
  { apply (pc_ap (P :: G) P0).
    { apply IHPC1; reflexivity. }
    { apply IHPC2; reflexivity. }
  }
  { apply pc_K. }
  { apply pc_S. }
  { apply pc_C. }
Qed.

Lemma pc_in_hyp_elim (G : context)(P Q : formula) :
  P :- G
    -> P :: G |-- Q
    -> G |-- Q.
Proof.
  intros PinG H.
  dependent induction H.
  { apply in_inv in H.
    destruct H; subst; apply pc_as; firstorder.
  }
  { apply (pc_ap G P0 Q);
    apply (pc_excl G P); auto;
    apply pc_as; auto.
  }
  { apply pc_K. }
  { apply pc_S. }
  { apply pc_C. }
Qed.

Lemma pc_swap_hyps (G : context)(P Q R : formula) :
 P :: Q :: G |-- R
  -> Q :: P :: G |-- R.
Proof.
  intros H.
  dependent induction H.
  { apply pc_as; firstorder. }
  { apply (pc_ap (Q :: P :: G) P0).
    { apply IHPC1; reflexivity. }
    { apply IHPC2; reflexivity. }
  }
  { apply pc_K. }
  { apply pc_S. }
  { apply pc_C. }
Qed.

Lemma pc_ctx_sym (G1 G2 : context)(P : formula) :
  G1 ++ G2 |-- P
    -> G2 ++ G1 |-- P.
Proof.
  intros H.
  dependent induction H.
  { apply pc_as; firstorder.
    apply in_app_or in H.
    destruct H; apply in_or_app; [right|left]; assumption.
  }
  { apply (pc_ap (G2 ++ G1) P).
    { apply IHPC1; reflexivity. }
    { apply IHPC2; reflexivity. }
  }
  { apply pc_K. }
  { apply pc_S. }
  { apply pc_C. }
Qed.

Lemma pc_swap_ctx (G1 G2 : context)(P Q R: formula) :
  G1 ++ [ P ; Q ] ++ G2 |-- R
    -> G1 ++ [ Q ; P ] ++ G2 |-- R.
Proof.
  intros H.
  dependent induction H.
  { apply pc_as; firstorder.
    destruct (in_app_or (G1)([P; Q] ++ G2) P0).
    { assumption. }
    { apply (in_or_app (G1)([Q; P] ++ G2) P0).
      left; assumption.
    }
    apply (in_or_app (G1)([Q; P] ++ G2) P0); right.
    destruct (in_app_or ([P; Q])(G2) P0).
    { assumption. }
    { apply (in_or_app ([Q; P])(G2) P0).
      left; firstorder.
    }
    { apply (in_or_app ([Q; P])(G2) P0).
      right; firstorder.
    }
  }
  { apply (pc_ap (G1 ++ [Q; P] ++ G2) P0).
    { apply IHPC1; reflexivity. }
    { apply IHPC2; reflexivity. }
  }
  { apply pc_K. }
  { apply pc_S. }
  { apply pc_C. }
Qed.

Lemma pc_first_hyp_last (G : context)(P Q : formula) :
  [ P ] ++ G |-- Q
    -> G ++ [ P ] |-- Q.
Proof.
  intros H.
  dependent induction H.
  { apply pc_as; firstorder.
    subst; firstorder.
  }
  { apply (pc_ap (G ++ [P]) P0).
    { apply IHPC1; reflexivity. }
    { apply IHPC2; reflexivity. }
  }
  { apply pc_K. }
  { apply pc_S. }
  { apply pc_C. }
Qed.

Lemma pc_ctx_split_sym (G1 G2 G3 : context)(P : formula) :
  G1 ++ G2 ++ G3 |-- P
    -> G2 ++ G1 ++ G3 |-- P.
Proof.
  intros H.
  dependent induction H.
  { apply pc_as; firstorder.
    apply in_app_or in H.
    destruct H; apply in_or_app.
    { right. apply in_or_app.
      left. assumption.
    }
    { apply in_app_or in H.
      destruct H.
      { left. assumption. }
      { right. apply in_or_app.
        right. assumption.
      }
    }
  }
  { apply (pc_ap (G2 ++ G1 ++ G3) P).
    { apply IHPC1; reflexivity. }
    { apply IHPC2; reflexivity. }
  }
  { apply pc_K. }
  { apply pc_S. }
  { apply pc_C. }
Qed.

Lemma length_nodup {A : Type}
        (decA : forall x y : A, { x = y } + { x <> y })(L : list A) :
  length (nodup decA L) <= length L.
Proof with eauto.
  induction L.
  { reflexivity. }
  { destruct (in_dec decA a L).
    { assert (nodup decA (a :: L) = nodup decA L).
      { unfold nodup at 1.
        destruct (in_dec decA a L); simpl...
        contradiction.
      }
      { rewrite H. eauto with arith. }
    }
    { assert (nodup decA (a :: L) = a :: nodup decA L).
      { unfold nodup at 1.
        destruct (in_dec decA a L); simpl...
        contradiction.
      }
      { rewrite H.
        assert (length (a :: nodup decA L) = S(length (nodup decA L)))...
        assert (length (a :: L) = S(length L))...
        rewrite H0. rewrite H1. eauto with arith.
      }
    }
  }
Qed.

Lemma length_sum_nodup {A : Type}
        (decA : forall x y : A, { x = y } + { x <> y })(L1 L2 : list A) :
  length (nodup decA L2) <= length (nodup decA (L1 ++ L2)).
Proof.
  induction L1; auto.
  destruct (in_dec decA a (L1 ++ L2)).
  { assert (nodup decA (a :: (L1 ++ L2)) = nodup decA (L1 ++ L2)).
    { unfold nodup at 1.
      destruct (in_dec decA a (L1 ++ L2)); simpl; auto.
      contradiction.
    }
    { rewrite <- app_comm_cons. rewrite H. apply IHL1. }
  }
  { assert (nodup decA (a :: (L1 ++ L2)) = a :: nodup decA (L1 ++ L2)).
    { unfold nodup at 1.
      destruct (in_dec decA a (L1 ++ L2)); simpl; auto. contradiction.
    }
    { rewrite <- app_comm_cons. rewrite H. eauto with arith. }
  }
Qed.

Lemma nodup_nodup {A : Type}
        (decA : forall x y : A, { x = y } + { x <> y })(L : list A) :
  nodup decA L = nodup decA (nodup decA L).
Proof.
  induction L; auto.
  destruct (in_dec decA a L).
  { assert (nodup decA (a :: L) = nodup decA L).
    { unfold nodup at 1.
      destruct (in_dec decA a L); simpl; auto.
      contradiction.
    }
    { rewrite H. apply IHL. }
  }
  { assert (nodup decA (a :: L) = a :: nodup decA L).
    { unfold nodup at 1.
      destruct (in_dec decA a L); simpl; auto.
      contradiction.
    }
    { rewrite H.
      assert (~ a :- nodup decA L).
      { contradict n. apply nodup_In in n; auto. }
      assert (nodup decA (a :: nodup decA L)
        = a :: nodup decA (nodup decA L)).
      { unfold nodup at 1.
        destruct (in_dec decA a (nodup decA L)); simpl; auto.
        contradiction.
      }
      rewrite H1. rewrite <- IHL; auto.
    }
  }
Qed.

Lemma nodup_sum_nodup {A : Type}
        (decA : forall x y : A, { x = y } + { x <> y })(x1 x2 : list A) :
  nodup decA (x1 ++ x2) = nodup decA (nodup decA x1 ++ nodup decA x2).
Proof.
  intros.
  induction x1 as [| a ].
  { apply nodup_nodup. }
  { destruct (in_dec decA a x1).
    { assert (nodup decA (a :: x1) = nodup decA x1).
      { unfold nodup at 1.
        destruct (in_dec decA a x1); simpl; auto.
        contradiction.
      }
      { rewrite H. rewrite <- IHx1.
        assert ((a :: x1) ++ x2 = a :: (x1 ++ x2)).
        { apply app_comm_cons. }
        rewrite H0. unfold nodup at 1.
        destruct (in_dec decA a (x1 ++ x2)); simpl; auto.
        contradict n.
        apply in_app_iff.
        left; auto.
      }
    }
    { rewrite <- app_comm_cons.
      assert (nodup decA (a :: x1) = a :: nodup decA x1).
      { unfold nodup at 1.
        destruct (in_dec decA a x1); simpl; auto.
        contradiction.
      }
      { rewrite H. rewrite <- app_comm_cons.
        destruct (in_dec decA a x2).
        { assert (nodup decA (a :: x1 ++ x2) = nodup decA (x1 ++ x2)).
          { unfold nodup at 1.
            destruct (in_dec decA a (x1 ++ x2)); simpl; auto.
            contradict n0.
            apply in_app_iff; auto.
          }
          rewrite H0. rewrite IHx1; auto. symmetry. simpl.
          destruct (in_dec decA a (nodup decA x1 ++ nodup decA x2)); auto.
          contradict n0. apply in_app_iff; right; apply nodup_In; auto.
        }
        { assert (nodup decA (a :: x1 ++ x2) = a :: nodup decA (x1 ++ x2)).
          { unfold nodup at 1.
            destruct (in_dec decA a (x1 ++ x2)); simpl; auto.
            contradict n0.
            apply in_app_iff in i; auto.
            destruct i; try contradiction; auto.
          }
          rewrite H0.
          assert (nodup decA (a :: nodup decA x1 ++ nodup decA x2)
            = a :: nodup decA (nodup decA x1 ++ nodup decA x2)).
          { unfold nodup at 1.
            destruct (in_dec decA a (nodup decA x1 ++ nodup decA x2));
            simpl; auto.
            apply in_app_iff in i; auto.
            destruct i.
            contradict n.
            { apply nodup_In in H1; auto. }
            { contradict n0. apply nodup_In in H1; auto. }
          }
          rewrite H1. rewrite IHx1; auto.
        }
      }
    }
  }
Qed.

Lemma pc_ctx_ndf (G : context)(P : formula) :
  G |-- P
    <-> ndf G |-- P.
Proof.
  split; intros * H.
  { dependent induction H.
    { assert (P :- ndf G). apply nodup_In; auto.
      apply pc_as; firstorder.
    }
    { apply (pc_ap (ndf G) P Q); auto. }
    { apply pc_K. }
    { apply pc_S. }
    { apply pc_C. }
  }
  { dependent induction H.
    { assert (P :- G).
      { unfold ndf in *. apply nodup_In in H; auto. }
      apply pc_as; firstorder.
    }
    { assert (G |-- P --> Q). {apply IHPC1; auto. }
      assert (G |-- P). { apply IHPC2; auto. }
      apply (pc_ap G P Q); auto.
    }
    { apply pc_K. }
    { apply pc_S. }
    { apply pc_C. }
  }
Qed.

Lemma pc_sum_ctx_ndf (G1 G2 : context)(P : formula) :
  G1 ++ G2 |-- P
    <-> ndf G1 ++ ndf G2 |-- P.
Proof.
  split; intros * H.
  { apply pc_ctx_ndf. apply pc_ctx_ndf in H.
    unfold ndf. rewrite <- nodup_sum_nodup; auto.
  }
  { apply pc_ctx_ndf. apply pc_ctx_ndf in H.
    unfold ndf. rewrite nodup_sum_nodup; auto.
  }
Qed.

(** Transitivity theorems *)

Lemma pc_asoc (G : context)(P Q R : formula) :
  G |-- P --> Q
    -> G |-- Q --> R
    -> G |-- P --> R.
Proof.
  intros H1 H2.
  apply pc_in.
  apply (pc_ap (P :: G) Q R).
  { apply pc_ext_hyps; assumption. }
  { apply pc_mp; assumption. }
Qed.

Lemma pc_asoc_pc (G : context)(P Q R : formula) :
  P :: G |-- Q
    -> Q :: G |-- R
    -> P :: G |-- R.
Proof.
  intros H1 H2.
  apply pc_mp.
  apply (pc_asoc G P Q R).
  { apply pc_in; assumption. }
  { apply pc_in; assumption. }
Qed.

(** Contraposition theorems *)

Lemma pc_not_intro (G : context)(P : formula) :
  G |-- P
    -> G |-- ^ ^ P.
Proof.
  intros H.
  apply pc_mp_var.
  assumption.
Qed.

Lemma pc_not_elim (G : context)(P : formula) :
  G |-- ^ ^ P
    -> G |-- P.
Proof.
  intros H.
  apply (pc_ap G (^ ^ P)).
  { apply pc_C. }
  { assumption. }
Qed.

Lemma pc_contr_pc (G : context)(P Q : formula) :
  G |-- P --> Q
    -> G |-- ^ Q --> ^ P.
Proof.
  intros H.
  apply pc_in. apply pc_in.
  apply pc_swap_hyps.
  apply pc_mp in H.
  apply pc_mp.
  apply pc_not_intro.
  assumption.
Qed.

Lemma pc_contr (G : context)(P Q : formula) :
  G |-- ^ Q --> ^ P
    -> G |-- P --> Q.
Proof.
  intros H.
  apply pc_mp in H.
  apply pc_mp in H.
  apply pc_swap_hyps in H.
  apply pc_in in H.
  apply pc_in.
  apply pc_not_elim.
  assumption.
Qed.

Lemma pc_contr_hyp (G : context)(P Q : formula) :
  ^ Q :: G |-- ^ P
    -> P :: G |-- Q.
Proof.
  intros H.
  apply pc_in in H.
  apply pc_mp.
  apply pc_contr; assumption.
Qed.

Lemma pc_contr_hyp_pc (G : context)(P Q : formula) :
  P :: G |-- Q
    -> ^ Q :: G |-- ^ P.
Proof.
  intros H.
  apply pc_in in H.
  apply pc_mp.
  apply pc_contr_pc; assumption.
Qed.

Lemma pc_contr_var (G : context)(P Q : formula) :
  G |-- (^ Q --> ^ P) --> P --> Q.
Proof.
  apply pc_in.
  apply pc_contr.
  apply pc_as; left; reflexivity.
Qed.

Lemma pc_contradiction (G : context)(P : formula) :
  P :: ^ P :: G |-- _|_.
Proof.
  apply pc_mp.
  apply pc_as; left; reflexivity.
Qed.

Lemma pc_exfalso (G : context)(P : formula) :
  G |-- _|_
    -> G |-- P.
Proof.
  intros H.
  apply pc_not_elim.
  apply pc_in.
  apply pc_ext_hyps; assumption.
Qed.

Lemma pc_and_imp (G : context)(P Q : formula) :
  G |-- P
    -> G |-- ^ Q
    -> G |-- ^ (P --> Q).
Proof.
  intros.
  apply pc_in.
  assert (H1 : P --> Q :: G |-- Q).
  { apply (pc_mp_var G P Q) in H.
    apply pc_mp in H; auto.
  }
  apply (pc_ext_hyps G ^ Q (P --> Q)) in H0.
  apply (pc_ap (P --> Q :: G) Q _|_); auto.
Qed.

(** Equivalencies of logical functions *)

Lemma pc_and_left (G : context)(P Q : formula) :
  G |-- P and Q
    -> G |-- P.
Proof.
  intros H.
  apply pc_not_elim.
  cut (^ P :: G |-- P --> ^ Q).
  { intros H1.
    apply pc_in. apply pc_mp in H.
    apply (pc_asoc_pc G (^ P)(P --> ^ Q)); assumption.
  }
  apply pc_in.
  apply pc_swap_hyps.
  apply pc_contr_hyp_pc.
  apply pc_swap_hyps.
  apply pc_as.
  left; reflexivity.
Qed.

Lemma pc_and_right (G : context)(P Q : formula) :
  G |-- P and Q
    -> G |-- Q.
Proof.
  intros H.
  apply pc_not_elim.
  cut (^ Q :: G |-- P --> ^ Q).
  { intros H1.
    apply pc_in.
    apply pc_mp in H.
    apply (pc_asoc_pc G (^ Q)(P --> ^ Q)); assumption.
  }
  apply pc_in.
  apply pc_swap_hyps.
  apply pc_as.
  left; reflexivity.
Qed.

Lemma pc_and_hyp (G : context)(P Q : formula) :
  P :: Q :: G |-- P and Q.
Proof.
  apply pc_swap_hyps.
  apply pc_contr_hyp.
  apply pc_not_elim.
  apply pc_contr_hyp_pc.
  apply pc_contr_hyp_pc.
  apply pc_swap_hyps.
  apply pc_mp_hyp.
Qed.

Lemma pc_and (G : context)(P Q : formula) :
  G |-- P
    -> G |-- Q
    -> G |-- P and Q.
Proof.
  intros Hp Hq.
  apply (pc_excl G Q); try assumption.
  apply (pc_excl (Q :: G) P); try assumption.
  apply pc_ext_hyps; assumption.
  apply pc_and_hyp.
Qed.

Lemma pc_or_left (G : context)(P Q : formula) :
  G |-- P
    -> G |-- P or Q.
Proof.
  intros H. unfold Or in *.
  apply pc_in.
  apply pc_exfalso.
  apply (pc_excl (^ P :: G) P).
  apply pc_ext_hyps; assumption.
  apply pc_contradiction.
Qed.

Lemma pc_or_right (G : context)(P Q : formula) :
  G |-- Q
    -> G |-- P or Q.
Proof.
  intros H.
  apply pc_ext; assumption.
Qed.

Lemma pc_or_case (G : context)(P Q R : formula) :
  P :: G |-- R
    -> Q :: G |-- R
    -> P or Q :: G |-- R.
Proof.
  intros Hp Hq.
  assert (H0 : ^ R :: G |-- ^ P and ^ Q).
  { apply pc_contr_hyp_pc in Hp.
    apply pc_contr_hyp_pc in Hq.
    apply pc_and; assumption.
  }
  apply pc_contr_hyp.
  assert (H1 : ^ ((^ P) --> ^ ^ Q) :: G |-- ^ ((^ P) --> Q)).
  { apply pc_contr_hyp_pc.
    apply pc_in.
    apply pc_not_intro.
    apply pc_mp.
    apply pc_as.
    left; reflexivity.
  }
  apply pc_in in H1.
  apply
    (pc_ext_hyps G ((^ ((^ P) --> ^ ^ Q)) --> ^ ((^ P) --> Q))(^ R))
    in H1.
  apply (pc_ap (^ R :: G)(^ ((^ P) --> ^ ^ Q))); assumption.
Qed.

Lemma pc_or_case_ctx (G1 G2 : context)(P Q R : formula) :
  P :: G1 |-- R
    -> Q :: G2 |-- R
    -> (P or Q) :: (G1 ++ G2) |-- R.
Proof.
  intros Hp Hq.
  apply (pc_ctx_ext (P :: G1) G2) in Hp.
  apply (pc_ctx_ext (Q :: G2) G1) in Hq.
  apply pc_ctx_sym in Hp. simpl in *.
  assert (H1 : G1 ++ Q :: G2 = G1 ++ [Q] ++ G2).
  { simpl. reflexivity. }
  rewrite H1 in Hq.
  apply pc_ctx_split_sym in Hq. simpl in *.
  apply pc_or_case; assumption.
Qed.

Lemma pc_tertium_non_datur (G : context)(P Q : formula) :
  P or ^ P :: G |-- Q
    -> G |-- Q.
Proof.
  intros H.
  apply pc_in in H.
  eapply pc_ap. apply H.
  apply pc_impl_refl.
Qed.

(** Soundness *)

Theorem Soundness_general (G : context)(P : formula) :
  G |-- P
    -> G |== P.
Proof.
  intros H.
  induction H.
  { apply (pa_as G P); auto. }
  { apply (pa_ap G P Q); auto. }
  { apply (pa_K G P Q); auto. }
  { apply (pa_S G P Q R); auto. }
  { apply (pa_C G P); auto. }
Qed.

(** Completeness *)

Fixpoint VarList (P : formula) : word :=
  match P with
  | _|_ => []
  | # Q => [Q]
  | Q --> R => VarList Q ++ VarList R
  end.

Definition Literals (P : formula) : word
  := nds (VarList P).

Definition Bar (E : evaluation)(x : symbol) : formula
  := if (symbolValue E x) then # x else ^ # x.

Lemma map_nodup (E : evaluation)(W : word) :
  map (Bar E)(nds W) = ndf (map (Bar E) W).
Proof.
  induction W.
  { simpl; auto. }
  { assert (H1 : map (Bar E)(a :: W) = Bar E a :: map (Bar E) W).
    { unfold map at 1; simpl; auto. }
    rewrite H1.
    destruct (in_dec eq_nat_dec a W).
    { assert (nds (a :: W) = nds W).
      { unfold nds at 1. unfold nodup at 1.
        destruct (in_dec eq_nat_dec a W); simpl; auto.
        contradiction.
      }
      rewrite H.
      assert (H2 : ndf (Bar E a :: map (Bar E) W) = ndf (map (Bar E) W)).
     { unfold ndf at 1. unfold nodup at 1.
       destruct (in_dec eq_formula_dec (Bar E a)(map (Bar E) W)); simpl; auto.
       contradict n. apply in_map; auto.
     }
     rewrite H2; auto.
    }
    { assert (nds (a :: W) = a :: nds W).
      { unfold nds at 1. unfold nodup at 1.
        destruct (in_dec eq_nat_dec a W); simpl; auto.
        contradiction.
      }
      rewrite H.
      assert (H2 : map (Bar E)(a :: nds W)
        = Bar E a :: map (Bar E)(nds W)).
      { unfold map at 1; simpl; auto. }
      rewrite H2. rewrite IHW. symmetry.
      unfold ndf at 1. unfold nodup at 1.
      destruct (in_dec eq_formula_dec (Bar E a)(map (Bar E) W)); simpl; auto.
      apply in_map_iff in i. destruct i as [ b [ H3 H4 ] ].
      unfold Bar in H3.
      destruct (symbolValue E b); destruct (symbolValue E a); inversion H3;
      subst; auto; contradiction.
    }
  }
Qed.

Lemma map_impl_sum (E : evaluation)(P1 P2 : formula) :
  map (Bar E)(Literals (P1 --> P2))
    = ndf (map (Bar E)(Literals P1) ++ map (Bar E)(Literals P2)).
Proof.
  unfold Literals; simpl.
  rewrite map_nodup.
  rewrite map_app.
  repeat rewrite map_nodup.
  unfold ndf.
  rewrite nodup_sum_nodup; auto.
Qed.

Lemma incl_nodup {A : Type}
        (decA : forall x y : A, { x = y } + { x <> y })(L1 L2 : list A) :
  incl L1 L2
    -> incl (nodup decA L1)(nodup decA L2).
Proof.
  induction L1 as [| b ]; simpl in *; unfold incl; intros * H1 a H2.
  { contradiction. }
  { destruct (in_dec decA b L1); auto.
    { apply IHL1; unfold incl; auto.
      intros c Hc. apply (H1 c). apply in_cons; auto.
    }
    { destruct H2 as [ H2 | H2 ]; auto; subst.
      apply nodup_In; apply H1; left; auto.
      apply IHL1; auto.
      unfold incl; intros c Hc. apply (H1 c). apply in_cons; auto.
    }
  }
Qed.

Lemma length_nodup_sum_sym {A : Type}
        (decA : forall x y : A, { x = y } + { x <> y })(L1 L2 : list A) :
  length (nodup decA (L1 ++ L2)) = length (nodup decA (L2 ++ L1)).
Proof.
  intros.
  assert (H1 : length (nodup decA (L1 ++ L2))
    <= length (nodup decA (L2 ++ L1))).
  { apply NoDup_incl_length.
    apply NoDup_nodup; auto.
    apply incl_nodup. unfold incl.
    intros a Ha.
    apply in_app_iff in Ha. apply in_app_iff.
    destruct Ha as [ H1 | H2 ]; [right|left]; auto.
  }
  assert (H2 : length (nodup decA (L2 ++ L1))
    <= length (nodup decA (L1 ++ L2))).
  { apply NoDup_incl_length.
    apply NoDup_nodup; auto.
    apply incl_nodup. unfold incl.
    intros a Ha.
    apply in_app_iff in Ha. apply in_app_iff.
    destruct Ha as [ H2 | H3 ]; [right|left]; auto.
  }
  firstorder.
Qed.

Theorem le_n_0_eq (n : nat) :
  n <= 0 -> 0 = n.
Proof.
  induction n; auto with arith.
Qed.

Theorem le_lt_trans (n m p : nat) :
  n <= m -> m < p -> n < p.
Proof.
  induction 2; auto with arith.
Qed.

Lemma LiteralsToformula (E : evaluation)(P : formula) :
  map (Bar E)(Literals P) |-- if formulaValue E P then P else ^ P.
Proof.
  intros.
  assert (Hn : exists n, length (Literals P) < n).
    exists (S(length (Literals P))); auto. destruct Hn as [ n H0 ].
  generalize P E H0. clear dependent P. clear E.
  induction n; intros P E H.
  apply le_n_0_eq in H. discriminate.
  induction P;  simpl in *.
  { apply pc_in. apply pc_as; firstorder. }
  { unfold Bar; destruct (symbolValue E s); apply pc_as;
    try apply _|_; simpl; left; auto.
  }
  { rewrite map_impl_sum.
    unfold Literals. apply -> pc_ctx_ndf.
    assert (HP1 : exists vp1 : bool, formulaValue E P1 = vp1).
     exists (formulaValue E P1); auto.
     destruct HP1 as [ vp1 HP1 ]. rewrite HP1 in *.
    assert (HP2 : exists vp2 : bool, formulaValue E P2 = vp2).
     exists (formulaValue E P2); auto.
     destruct HP2 as [ vp2 HP2 ]. rewrite HP2 in *.
    destruct (vp1). destruct (vp2); simpl.
    { cut (map (Bar E)(nds (VarList P2)) |-- P2).
      intros xHP2.
      apply (pc_ctx_ext (map (Bar E)(nds (VarList P2)))
        (map (Bar E)(nds (VarList P1))) P2) in xHP2.
      apply pc_ext; auto. apply IHP2.
      unfold Literals, nds in *; simpl in *.
      rewrite nodup_sum_nodup in H.
      repeat fold nds in *. clear IHP1 IHP2 IHn.
      eapply le_lt_trans.
      apply length_sum_nodup. unfold nds in H.
      rewrite <- nodup_sum_nodup in H. apply H.
    }
    { cut (map (Bar E)(Literals P1) |-- P1). intros xHP1.
      apply (pc_ctx_ext (map (Bar E)(Literals P1))
        (map (Bar E)(Literals P2)) P1) in xHP1.
      apply pc_ctx_sym in xHP1.
      cut (map (Bar E)(Literals P2) |-- ^ P2). intros xHP2.
      apply (pc_ctx_ext (map (Bar E)(Literals P2))
        (map (Bar E)(Literals P1)) ^ P2) in xHP2.
      apply pc_and_imp; auto. apply IHP2.
      unfold Literals, nds in *; simpl in *.
      rewrite nodup_sum_nodup in H.
      repeat fold nds in *. clear IHP1 IHP2 IHn. eapply le_lt_trans.
      apply length_sum_nodup. unfold nds in H.
      rewrite <- nodup_sum_nodup in H. apply H.
      apply IHP1.
      unfold Literals, nds in *; simpl in *.
      rewrite nodup_sum_nodup in H.
      repeat fold nds in *. clear IHP1 IHP2 IHn. eapply le_lt_trans.
      apply length_sum_nodup. unfold nds in H.
      rewrite <- nodup_sum_nodup in H.
      rewrite length_nodup_sum_sym. apply H.
    }
    { simpl.
      cut (map (Bar E)(Literals P1) |-- ^ P1).
        intros xHP1. simpl in *.
      apply pc_contr. apply pc_ext.
      apply (pc_ctx_ext (map (Bar E)(Literals P1))
        (map (Bar E)(Literals P2)) ^ P1) in xHP1.
      apply pc_ctx_sym in xHP1.
      assumption. apply IHP1. unfold Literals in *. simpl in *.
      unfold nds in *. rewrite nodup_sum_nodup in H.
      repeat fold nds in *.
      eapply le_lt_trans. apply length_sum_nodup. unfold nds in H.
      rewrite length_nodup_sum_sym in H. repeat fold nds in *.
      unfold nds in *. rewrite nodup_sum_nodup. apply H.
    }
  }
Qed.

Definition pro (E : evaluation)(x : symbol)(b : bool) : evaluation :=
  {| symbolValue := fun y : symbol => if eq_nat_dec x y
                                      then b
                                      else symbolValue E y
  |}.

Lemma pro_eq_fun (E : evaluation)(x : symbol)(b : bool)(w : word) :
  ~ x :- w
    -> map (Bar E) w = map (Bar (pro E x b)) w.
Proof.
  intros * H. generalize b E x H; clear b E x H.
  induction w as [| c ].
  intros. simpl. reflexivity.
  intros b E x H.
  assert (map (Bar E)(c :: w) = Bar E c :: map (Bar  E)w).
    unfold map at 1; auto. rewrite H0. clear H0.
  assert (forall s, s <> x -> symbolValue (pro E x b) s = symbolValue E s).
    intros s naeqs. unfold pro; simpl. destruct (eq_nat_dec x s); auto.
    contradict naeqs; auto.
  assert (Hg : exists g, g = pro E x b). exists (pro E x b); auto.
    destruct Hg as [ g Hg ].
  assert (map (Bar g)(c :: w) = Bar g c :: map (Bar g) w).
    unfold map at 1; auto. rewrite <- Hg. rewrite H1.
  assert (forall s, x <> s -> Bar E s = Bar g s).
    rewrite Hg. unfold Bar, pro.
    intros s naeqs; simpl.
    destruct (eq_nat_dec x s); auto. subst; auto. contradict naeqs; auto.
  assert (forall t, ~ x :- t -> map (Bar E) t = map (Bar g) t).
    intros t naint. induction t. simpl; auto.
    unfold map. rewrite H2. unfold map in IHt. rewrite IHt; auto.
    contradict naint. right; auto. contradict naint. subst. left; auto.
  rewrite (H2 c). rewrite (H3 w); auto. contradict H. right; auto.
  contradict H. left; auto.
Qed.

Lemma skipn_first {A : Type}(n : nat)(x : list A) :
  skipn (S n) x = tl (skipn n x).
Proof.
  generalize n; clear n.
  induction x; simpl; auto. induction n; auto.
  intros n. destruct n. induction x; simpl; auto.
    rewrite IHx. simpl. reflexivity.
Qed.

Lemma skipn_nodup {A : Type}(n : nat)(x : list A) :
  NoDup x
    -> NoDup (skipn n x).
Proof.
  intros.
  induction n. simpl; auto.
  rewrite skipn_first.
  destruct (skipn n x). simpl in *; auto.
  simpl. apply NoDup_cons_iff in IHn.
  destruct IHn;  auto.
Qed.

Lemma list_rev_ind {A : Type}(P : list A -> Prop)(x : list A) :
  P x
    -> (forall n, P (skipn n x) -> P (skipn (S n) x))
    -> P [].
Proof.
  intros.
  induction x; auto. apply IHx.
  apply (H0 O); simpl; auto.
  intros n Pn. apply (H0 (S n)).
  induction n; simpl; auto.
Qed.

Theorem Completeness_empty (P : formula) :
  |== P
    -> |-- P.
Proof.
  intros H.
  unfold Eq in *. simpl in *.
  assert (VfP : forall E, formulaValue E P = true).
  { intros E. apply H. apply Compatible_empty. }
  clear H.
  assert (H : forall E, map (Bar E)(Literals P) |-- P).
  { intros E.
    cut (map (Bar E)(Literals P) |-- (if formulaValue E P then P else (^ P))).
    intros. rewrite (VfP E) in H; auto. apply LiteralsToformula.
  }
  unfold Literals in *.
  assert (Hn : forall n,
    (forall E, map (Bar E)(skipn n (nds (VarList P))) |-- P)
      -> (forall E, map (Bar E)(skipn (S n)(nds (VarList P))) |-- P)).
  { intros n Hn E. rewrite skipn_first.
    assert (H0 : exists x, x = skipn n (nds (VarList P))).
    { exists (skipn n (nds (VarList P))); auto. }
    destruct H0 as [ x Hx ].
    rewrite <- Hx.
    generalize VfP Hn E. clear VfP Hn E.
    induction x.
    { rewrite <- Hx in *. simpl in *; auto. }
    { intros VfP Hn. simpl. rewrite <- Hx in Hn.
      { assert (H1 : forall E, Bar E a :: map (Bar  E)x |-- P). { apply Hn. }
        assert (Ha : forall E, # a :: map (Bar  E)x |-- P).
        { intros E.
          rewrite (pro_eq_fun E a true).
          { replace (# a) with (Bar (pro E a true) a).
            { apply (H1 (pro E a true)). }
            unfold Bar, pro; simpl.
            destruct (eq_nat_dec a a); try reflexivity.
            contradict n0; auto.
          }
          eapply NoDup_cons_iff.
          cut (NoDup (skipn n (nds (VarList P)))).
          { intros G. rewrite <- Hx in G. auto. }
          apply skipn_nodup. unfold nds. apply NoDup_nodup.
        }
        assert (nHa : forall E, (^ # a) :: map (Bar E) x |-- P).
        { intros E.
          rewrite (pro_eq_fun E a false).
          { replace (^ # a) with (Bar (pro E a false) a).
            { apply (H1 (pro E a false)). }
            unfold Bar, pro; simpl.
            destruct (eq_nat_dec a a); try reflexivity.
            contradict n0; auto.
          }
          eapply NoDup_cons_iff.
          cut (NoDup (skipn n (nds (VarList P)))).
          { intros G. rewrite <- Hx in G. auto. }
          apply skipn_nodup. unfold nds. apply NoDup_nodup.
        }
        assert (Hor : forall E, (# a or (^ # a)) :: map (Bar E) x |-- P).
        { intros f. apply pc_or_case; auto. }
        intros f. eapply pc_tertium_non_datur. apply Hor.
      }
    }
  }
  assert (forall E, map (Bar E) [] |-- P).
  { eapply list_rev_ind. apply H. intros n H0 f. apply Hn. apply H0. }
  simpl in H0. apply H0.
  split. apply (fun b => true).
Qed.

Theorem Completeness_general (G : context)(P : formula) :
  G |== P
    -> G |-- P.
Proof.
  intros H.
  generalize P H. clear P H.
  induction G as [| Q ].
  { apply Completeness_empty; auto. }
  { intros P H. apply pc_mp. apply pa_in in H.
    apply IHG; auto.
  }
Qed.

Theorem prov_equiv_models (G : context)(P : formula) :
  G |-- P
    <-> G |== P.
Proof.
 split.
 { apply Soundness_general. }
 { apply Completeness_general. }
Qed.

(* NATURAL DEDUCTION *)

Reserved Notation " G |--- F " (at level 70).
Inductive ND : context -> formula -> Prop :=
         | nd_as (G : context)(P : formula) :
             P :- G
               -> G |--- P
         | nd_ap (G : context)(P Q : formula) :
             G |--- P --> Q
               -> G |--- P
               -> G |--- Q
         | nd_in (G : context)(P Q : formula) :
             P :: G |--- Q
               -> G |--- P --> Q
         | nd_nn (G : context)(P : formula) :
             G |--- ^ ^ P
               -> G |--- P
    where " G |--- F " := (ND G F).
Notation "|--- P"
  := ([] |--- P)
  (at level 80).

Lemma nd_K (G : context)(P Q : formula) :
  G |--- P --> Q --> P.
Proof.
  apply nd_in.
  apply nd_in.
  apply nd_as.
  right; left; reflexivity.
Qed.

Lemma nd_S (G : context)(P Q R : formula) :
  G |--- (P --> Q --> R) --> (P --> Q) --> P --> R.
Proof.
  apply nd_in.
  apply nd_in.
  apply nd_in.
  apply (nd_ap (P :: P --> Q :: P --> Q --> R :: G) Q).
    apply (nd_ap (P :: P --> Q :: P --> Q --> R :: G) P).
      apply nd_as.
      right; right; left; reflexivity.
      apply nd_as.
        left; reflexivity.
    apply (nd_ap (P :: P --> Q :: P --> Q --> R :: G) P).
      apply nd_as.
        right; left; reflexivity.
      apply nd_as.
        left; reflexivity.
Qed.

Lemma nd_C (G : context)(P : formula) :
  G |--- ^ ^ P --> P.
Proof.
  apply nd_in.
  apply nd_nn.
  apply nd_as; left; reflexivity.
Qed.

Lemma nd_contr (G : context)(P Q : formula) :
  G |--- (^ Q --> ^ P) --> (P --> Q).
Proof.
  apply nd_in.
  apply nd_in.
  apply nd_nn.
  apply nd_in.
  apply (nd_ap ((^ Q) :: P :: (^ Q) --> (^ P) :: G) P).
    apply (nd_ap ((^ Q) :: P :: (^ Q) --> (^ P) :: G)(^ Q)).
     apply nd_as.
       right; right; left; reflexivity.
     apply nd_as.
       left; reflexivity.
     apply nd_as.
       right; left; reflexivity.
Qed.

(* Equivalence of natural deduction and formulaositionalal calculus. *)

Lemma pc_nd (G : context)(P : formula) :
  G |-- P
    -> G |--- P.
Proof.
  intros H.
  induction H.
    apply nd_as; assumption.
    apply (nd_ap G P).
      apply IHPC1.
      apply IHPC2.
    apply nd_K.
    apply nd_S.
    apply nd_C.
Qed.

Lemma nd_pc (G : context)(P : formula) :
  G |--- P
    -> G |-- P.
Proof.
  intros H.
  dependent induction H.
    apply pc_as; assumption.
  apply (pc_ap G P).
    apply IHND1.
  exact IHND2.
    apply pc_in.
    exact IHND.
    apply pc_not_elim.
    assumption.
Qed.

Theorem nd_eq_pc (G : context)(P : formula) :
  G |--- P
    <-> G |-- P.
Proof.
  split.
    apply nd_pc.
    apply pc_nd.
Qed.

(* Theorems of natural deduction. *)

Lemma nd_True (G : context) :
  G |--- truth.
Proof.
  apply nd_in.
  apply nd_as.
  left; reflexivity.
Qed.

Lemma nd_id (G : context)(P : formula) :
  G |--- P --> P.
Proof.
  apply nd_in.
  apply nd_as.
  left; reflexivity.
Qed.

Lemma nd_ext (G : context)(P Q : formula) :
  G |--- P
    -> Q :: G |--- P.
Proof.
  intros H.
  apply nd_eq_pc in H.
  apply nd_eq_pc.
  apply pc_ext_hyps.
  assumption.
Qed.

Lemma nd_swap_hyps (G : context)(P Q R : formula) :
  P :: Q :: G |--- R
    -> Q :: P :: G |--- R.
Proof.
  intros H.
  apply nd_eq_pc in H.
  apply nd_eq_pc.
  apply pc_swap_hyps.
  assumption.
Qed.