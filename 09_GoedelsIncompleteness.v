(* 

 GOEDEL'S INCOMPLETENESS THEOREM

 Evgeny V Ivashkevich
 
 E-mail: ivashkev@yandex.ru

 April 13, 2019

 Abstract: In this file, we formalize the first chapter from 
           Raymond Smullyan’s book “Goedel's Incompleteness Theorems”, 
           where a simplified example of incompleteness is given. 
           The entire text of the comments below is taken from the book.
*)


(* 
   Let us consider a computing machine that prove and print 
   out various expressions composed of the following 
   symbols:
*)

Inductive symbol : Set :=
         | P   : symbol
         | PF  : symbol
         | NP  : symbol
         | NPF : symbol
         .

(* 
   By an "expression", we mean any finite non-empty string 
   of these symbols.
*)
Inductive expression : Set :=
         | one : symbol -> expression
         | app : expression -> expression -> expression
         .
Notation "# s" := (one s)(at level 60).
Notation "X [ Y ]" := (app X Y)(at level 60).

(* 
   By the "norm" of an expression X, we shall mean the 
   expression X [ X ] - e.g. the norm of PF is PF [ PF ]. 
*)
Definition norm (X : expression) : expression := X [ X ].

(* 
   By "sentence" we mean any expression of one of the 
   follwing four forms (X is any expression):
   (1) P [ X ] 
   (2) PF [ X ]
   (3) NP [ X ] 
   (4) NPF [ X ] 
*)
Definition is_sentence (X : expression) : Prop
  := match X with
     | (# _) [ _ ] => True
     | _ => False
     end.

(* 
   Any sentence has its head and tail. 
*)
Fixpoint head (X : expression) : symbol
  := match X with
     | # s     => s
     | h [ t ] => head h
     end.

Definition tailSig (X : expression) :
  is_sentence X -> { Y : expression | X = #(head X) [ Y ] }.
Proof.
  intros H. 
  destruct X as [ X0 | [ X1 | X2 ]]; simpl in *; try destruct H.
  exists X2. reflexivity.
Defined.

Definition tail (X : expression) (H : is_sentence X)
  := proj1_sig (tailSig X H).

(* 
   An expression X is called "provable" if the machine can 
   prove and print it. We assume the machine programmed so 
   that any expression that the machine can prove will be 
   printed sooner or later.
*)
Parameter provable : expression -> Prop.

(* 
   Informally, P stands for "provable"; F stands for 
   "the norm of" and N stands for "not". And so we define 
   P [ X ] to be "true" if (and only if) X provable. 
   We define PF [ X ] to be true if the "norm" of X is 
   provable. We call NP [ X ] true iff X is not provable, 
   and NPF [ X ] is defined to be true iff the norm of X 
   is not provable. [This last sentence we read as 
   "The norm of X is not provable".]
*)
Inductive true (X : expression) : Prop :=
         | tP (H : is_sentence X) : 
             head X = P -> provable (tail X H) -> true X
         | tPF (H : is_sentence X) :
             head X = PF -> provable (norm (tail X H)) -> true X
         | tNP (H : is_sentence X) :
             head X = NP -> ~ provable (tail X H) -> true X
         | tNPF (H : is_sentence X) :
             head X = NPF -> ~ provable (norm (tail X H)) -> true X
         .
(*
   We have now given a perfectly precise definition of what 
   it means for a sentence to be true, and we have here an 
   interesting case of self-reference. The machine is 
   printing out various sentences about what the machine 
   can and cannot print, and so it is describing its own
   behavior!
*)

(*
   We are given that the machine is completely accurate 
   in that all sentences proved and printed by the machine 
   are true. And so, for example, if the machine ever 
   prints P [ X ], then X really is provable (X will be 
   printed by the machine sooner or later). Also, if 
   PF [ X ] is provable, so is X [ X ] (the norm of X). 
*)
Axiom provable_true : 
  forall (X : expression),
  is_sentence X -> provable X -> true X.

(*
   Now, suppose X is provable. Does it follow that P [ X ] 
   is provable? Not necessarily. If X is provable, then 
   P [ X ] is certainly "true", but we are not given that 
   the machine is capable of provin and printing all true 
   sentences but only that the machine never prints any 
   false ones.
*)
Lemma true_P : 
  forall (X : expression), 
  provable X
    <-> true ((# P) [ X ]).
Proof.
  split; intros.
  { assert (H0 : is_sentence ((# P) [X])). { simpl; auto. }
    eapply (tP ((# P) [X]) H0); simpl; auto.
    unfold tail, tailSig; simpl. destruct H0; simpl; auto.
  }
  { inversion H; try discriminate H1.
    assert (H3 : (tail ((# P) [X]) H0) = X).
    { unfold tail, tailSig; simpl; auto. destruct H0; simpl; auto. }
    rewrite H3 in H2; auto.
  }
Qed.
Lemma true_PF : 
  forall (X : expression), 
  provable (norm X)
    <-> true ((# PF) [ X ]).
Proof.
  split; intros.
  { assert (H0 : is_sentence ((# PF) [X])). { simpl; auto. }
    eapply (tPF ((# PF) [X]) H0); simpl; auto.
    unfold tail, tailSig; simpl. destruct H0; simpl; auto.
  }
  { inversion H; try discriminate H1.
    assert (H3 : (tail ((# PF) [X]) H0) = X).
    { unfold tail, tailSig; simpl; auto. destruct H0; simpl; auto. }
    rewrite H3 in H2; auto.
  }
Qed.
Lemma true_NP : 
  forall (X : expression), 
  ~ provable X
    <-> true ((# NP) [ X ]).
Proof.
  split; intros.
  { assert (H0 : is_sentence ((# P) [X])). { simpl; auto. }
    eapply (tNP ((# NP) [X]) H0); simpl; auto.
    unfold tail, tailSig; simpl. destruct H0; simpl; auto.
  }
  { inversion H; try discriminate H1.
    contradict H2.
    assert (H3 : (tail ((# NP) [X]) H0) = X).
    { unfold tail, tailSig; simpl; auto. destruct H0; simpl; auto. }
    rewrite H3; auto.
  }
Qed.
Lemma true_NPF : 
  forall (X : expression), 
  ~ provable (norm X)
    <-> true ((# NPF) [ X ]).
Proof.
  split; intros.
  { assert (H0 : is_sentence ((# NPF) [X])). { simpl; auto. }
    eapply (tNPF ((# NPF) [X]) H0); simpl; auto.
    unfold tail, tailSig; simpl. destruct H0; simpl; auto.
  }
  { inversion H; try discriminate H1.
    contradict H2.
    assert (H3 : (tail ((# NPF) [X]) H0) = X).
    { unfold tail, tailSig; simpl; auto. destruct H0; simpl; auto. }
    rewrite H3; auto.
  }
Qed.

(*
   Is it possible that the machine "can" prove and print 
   all the true sentences? The answer is "no" and the 
   problem is: Find a true sentence that the machine cannot 
   prove and print.
*)
Definition Goedel := (# NPF) [ # NPF ].

(*
   The sentence is NPF [ NPF ]. By definition of "true", 
   this sentence is true if and only if the norm of NPF 
   is not provable and not printable. But the norm of NPF
   is the very sentence NPF [ NPF ]. And so the sentence 
   is true if and only if it is not provable. This means 
   that either the sentence is true and not provable, or 
   it is provable and not true. The latter alternative 
   violates the given hypothesis that the machine never 
   prints sentences that are not true. Hence the sentence 
   must be true, but the machine cannot print it.
*)
Lemma true_non_provable_Goedel : 
  true Goedel <-> ~ provable Goedel.
Proof.
  unfold Goedel.
  split; intros; apply true_NPF; auto.
Qed.

Lemma provable_non_true_Goedel : 
  provable Goedel -> ~ true Goedel.
Proof.
  unfold Goedel.
  intros. contradict H. apply true_NPF; auto.
Qed.

Theorem non_provable_Goedel : 
  ~ provable Goedel.
Proof.
  intros H.
  assert (H0 : ~ true Goedel).
  { apply provable_non_true_Goedel; auto. }
  contradict H0. 
  apply provable_true; auto.
  unfold Goedel. simpl; auto.
Qed.

Theorem true_Goedel : 
  true Goedel.
Proof.
  apply true_non_provable_Goedel.
  apply non_provable_Goedel.
Qed.
