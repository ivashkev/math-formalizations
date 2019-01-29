(*
 
 CONSTRUCTIVE AXIOMATICS FOR PLANE EUCLIDEAN GEOMETRY

 Evgeny V. Ivashkevich
 
 E-mail: ivashkev@yandex.ru

 January 29, 2019

 Introduction

 1. The logic of Euclid

 Euclidean geometry [1] studies not only the properties of geometric figures,
 but also the rules of their construction. Propositions, that we encounter
 in Euclid's Elements, can be divided onto two types: problems and theorems.
 To solve a problem one needs to find a sequence of elementary actions
 (postulates) that leads to the construction of a figure with the required
 properties. The set of allowed elementary actions is completely determined
 by chosen geometric tools (a pencil, a ruler and a collapsing compass) and
 provides us with the instructions on how to handle these instruments.
 Pencil helps us to draw some points on a plane. Ruler helps us to draw a
 straight lines passing through two distinct points. Compass helps us to
 draw a circle through a given point and center of the circle.
 To prove a theorem one needs to find a sequence of elementary inferences
 (axioms) that confirms the presence of a certain property in a given figure.
 The set of allowed elementary inferences describes some basic properties of
 figures (points, lines, circles and triangles) that were constructed using
 the geometric tools that we have chosen.
 A distinctive feature of Euclid's logic, is that it is not purely
 deductive [2-3]. Postulates and problems represent an important constructive
 part of Euclid's logic which cannot be completely separated from the
 deductive one. Indeed, proofs of Euclid's theorems often require auxiliary
 constructions, while problem solutions often require intermediate proofs
 to ensure applicability of postulates or previously solved problems.
 So, the inherent logic of Euclid's Elements can be considered as
 constructive-deductive.
 Later interpreters of Euclid, however, sought to reduce his theory to purely
 predicate logic, reformulating all its problems into existential theorems.
 In other words, they treated all objects of the theory as idealized and
 pre-existing and considered every problem not as instruction on how to
 construct the object with the required properties, but simply as propositional
 proof of object's existence.
 This forced reduction of constructive-deductive logic of Euclid to purely
 propositional logic was not without its difficulties. Indeed, in the logic of
 Euclid, every object under consideration must first be constructed. While in
 purely propositional logic the mere existence of an object with the required
 properties can be proved indirectly. One first assumes that such an object
 does not exist, and then prove that this assumption leads to a contradiction.
 Such an indirect proof by contradiction relies upon so-called "the law of
 the excluded middle" first formulated by Aristotle. This law states that
 either an assertion or its negation must be true.
 Intuitionistic logic [4-6] was proposed to prohibit all indirect proofs of
 existence. The main idea of the method was to reduce further not only the
 constructive-deductive logic of Euclid, but also the classical propositional
 logic. Namely, intuitionists suggested to exclude "the law of the excluded
 middle" from the inference rules of propositional logic. As a results,
 from the existential proofs of the intuitionistic logic one do can reproduce
 original Euclid's constructions and vice versa.
 Despite of the apparent success, this reduction of classical logic cannot
 be considered satisfactory. Indeed, let us recall that Euclid builds his
 theory using a limited set of geometric tools (a pencil, a ruler and a
 collapsing compass). This means, that translating postulates and problems
 into existential axioms and theorems, and then limiting ourselves by the
 rules of intuitionistic logic, we shall be able to prove existence of only
 those geometric figures that can be constructed with this limited set of
 geometric tools. However, it is well known that not all geometric figures
 can be constructed by these simple tools. For example, it is impossible to
 do an angle trisection. Obviously, this does not mean that the rays
 that divide an angle onto three equal parts do not exist. To get around
 this new difficulty, intuitionists would have to change the original
 Euclidean postulates, thereby introducing some new idealized tools that
 would give them the ability to construct more complex geometric figures.

 2. Hilbert's system of axioms

 The standards of mathematical rigor have changed dramatically since Euclid
 wrote his Elements. Subsequently, many mathematicians added missing but
 implicitly used statements to the original list of Euclid's postulates and
 axioms. The culmination of this development was a small book by german
 mathematician David Hilbert "Foundations of geometry" [6].
 Although the overall approach of Hilbert is fairly close in spirit to
 that of Euclid, yet in some respects it deviates substantially from it.
 Let us discuss these differences.
 a) First of all, we have to note that Hilbert does not adhere to the
 constructive-deductive logic of Euclid. In fact, Hilbert was one of the main
 proponents of the existential approach and hence reduced all the postulates
 and problems of Euclid's Elements to purely existential statements within
 classical logic.
 b) Another striking feature of the Hilbert's axioms is the complete absence of
 circles. Instead of circles, Hilbert focuses all his attention on the
 properties of angles. Moreover, instead of Euclid's tools (a pencil, a ruler
 and a collapsing compass), Hilbert introduces more complicated instruments to
 transfer both segments and angles. Surprisingly, those same authors who
 criticized Euclid for his method of superposition (which is nothing more than
 an auxiliary tool for existential triangle transfer) seem to accept
 Hilbert's tool for angle transfer without any questions.
 Since without compass it is not possible to reproduce many propositions from
 Euclid's Elements, Hilbert followers [8,9] have to introduce some additional
 "principles": such as line-circle intersection and circle-circle
 intersection. These "principles" are nothing but additional postulates that
 describe simple constructions by ruler and compass. However, those authors
 do not add these "principles" to the list of Hilbert's axioms. Instead,
 they treat them as being derived from the Hilbert continuity axiom. Needless
 to say, that if such a derivation is actually provided by those authors,
 it goes far beyond Euclid's original approach.
 c) As for the treatment of angles on which Hilbert seems to focus instead of
 circles, it cannot be considered completely satisfactory either. The thing
 is that, Hilbert defines only convex angles (greater than null angle and
 less than straight angle). As a result of this truncated definition, it is
 impossible to universally define the addition of two arbitrary convex
 angles. Indeed, the sum of the two convex angles in Hilbert's theory is
 defined only iff the resulting angle is also convex. 
 d) In the last edition of his book, to define area of an arbitrary polygon
 Hilbert introduces the idea of triangle orientation. However, Hilbert did
 not provide the reader with any clear definition of the triangle orientation
 and has not studied the properties of the concept within his system of axioms.
 e) Hilbert introduces a number of separate congruence axioms for segments and
 angles. In Euclid's approach, on the contrary, the lengths of segments,
 angular measures and areas were all considered as "quantities" that obey the
 same universal axioms: "two quantities equal to the third are equal to each 
 other", etc. In other words, for Euclid, "quantities" are more general 
 concepts than segments and angles themselves. As such, Euclid considers 
 "quantities" as classes o congruence.

 3. Motivation and results

 In this work, we return to Euclid's original constructive-deductive logic.
 This means that we are going to use classical logic for propositions and
 intuitionistic logic for constructions. In other words, we shall clearly
 distinguish between existential statements and real constructions.
 The same applies to disjunction. We shall consider both propositional
 disjunctions which is a logical assertion that one of the two alternatives
 is true without specifying which one, and constructive disjunction, which is
 a practical algorithm that for every configuration of objects on the plane
 decides which one of the two alternatives actually takes place.
 We will show that the "Calculus of Constructions" (CoC), as it was
 implemented in the Coq Proof Assistant, suits ideally for the
 constructive-deductive logic of Euclid. In the CoC we have two sorts:
 "Prop" and "Set". The first one is inhabited by propositions and their
 proofs, while the second by constructed objects and their specifications
 (required properties). Without contradiction we may accept classical
 logic for proofs in the "Prop" sort, and at the same time limit ourselves
 to intuitionistic logic for constructions in the "Set" sort. As a result,
 our constructions will be limited to only those that can be performed with
 our simple tools (a pencil, a ruler and a collapsing compass), while we
 shall be able to prove propositional existence of more complex geometric
 figures.
 We abandon Hilbert's postulates for segment and angle transfer and replace
 them with simple versions of Euclid's postulates for collapsing compass
 whose legs fold up when the compass is lifted off the paper. Moreover,
 constructive-deductive logic of Euclid also gives us the opportunity to
 formalize Euclid's "method of superposition". To prove triangle congruence
 theorems, Euclid conjectured that every triangle could be moved and placed
 over another triangle so that their respective sides and angles could be
 compared. In this interpretation, the method of superposition seems to be
 quite a strong postulate, which makes it possible to move, rotate and flip
 triangles on the plane. That is why it is not very popular nowadays, and
 it was questioned even in the times of Euclid. In our interpretation the
 method of superposition turns into an axiom about the existence of an equal
 triangle anywhere on the plane. The actual construction of equal triangle
 can be done later by our standard tools (a pencil, a ruler and a collapsing
 compass).
 We define angles as a pairs of rays originating from the same point and prove
 that addition of angles can be defined uniformly for all angles (modulo the
 full angle). Then we define the orientation of angles on the plane and use
 this concept to define a subclass of convex angles, thus returning to
 the Hilbert's definition of angle. As a results, all Hilbert axioms can
 be derived form our formalization of Euclid's constructive-deductive method.
 Finally, we replaced congruence axioms for segments and angles by
 their classes of congruences and consider the classes as definitions of
 Euclid's "quantities". Such an approach simplifies our formalization
 of Euclid's constructive-deductive method in the Coq Proof Assistant.

 BIBLIOGRAPHY

 [1] Euclid, "Elements",
       Book I, Alexandria, (300 BC)
 [2] Andrei Rodin, "On Constructive Axiomatic Method",
       Logique et Analyse, Vol 61, No 242 (2018)
 [3] Andrei Rodin, "Euclid's Mathematics in Context of Plato's and
       Aristotle's Philosophy", Moscow, Nauka, (2003)
 [4] Arend Heyting, "Axiomatic Projective Geometry",
       Elsevier Science (2008)
 [5] Jan Von Plato, "The Axioms of Constructive Geometry",
       Annals of Pure and Applied Logic 76, 169-200 (1995)
 [6] Michael Beeson, "A Constructive Version of Tarski's Geometry",
       Annals of Pure and Applied Logic 166 (11) 1199-1273 (2015)
 [7] David Hilbert, "Grundlagen der Geometrie",
       7th ed., (1930)
 [8] Marvin Jay Greenberg, "Euclidean and non-Euclidean geometries",
       W. H. Freeman, New York, 2008.
 [9] Robin Hartshorne, "Geometry: Euclid and beyond",
       Springer, 2000
[10] Julien Narboux and others, "GeoCoq Project".

*)

Require Import Classical Setoid Morphisms.

(*****************************************************************************)
(** DEFINITIONS *)
(*****************************************************************************)

Record Duo { U : Set } : Set
  := BuildDuo { d1 : U; d2 : U }.
Notation " {{ A , B }} "
  := ({| d1 := A; d2 := B |})(at level 60).

Record Trio { U : Set } : Set
  := BuildTrio { t1 : U; t2 : U; t3 : U }.
Notation " {{ A , B , C }} "
  := ({| t1 := A; t2 := B; t3 := C |})(at level 60).

Record Duple { U : Set } { P : U -> U -> Prop } : Set
  := BuildDuple { da : U; db : U; dp : P da db }.
Notation " {{ A # B | AB }} "
  := ({| da := A; db := B; dp := AB |})(at level 60).

Record Triple { U : Set } { P : U -> U -> U -> Prop } : Set
  := BuildTriple { ta : U; tb : U; tc : U; tp : P ta tb tc }.
Notation " {{ A # B # C | ABC }} "
  := ({| ta := A; tb := B; tc := C; tp := ABC |})(at level 60).

Class Declarations :=
{
  Point : Set;
  Line : Set;

  Incident : Point -> Line -> Prop;
  Between : Point -> Point -> Point -> Prop;
}.
Notation " [ A @ x ] "
  := (Incident A x)
  (at level 60).
Notation " [ A , B @ x ] "
  := ([ A @ x ] /\ [ B @ x ])
  (at level 60).
Notation " [ A @ x , y ] "
  := ([ A @ x ] /\ [ A @ y ])
  (at level 60).
Notation " [ A , B , C @ x ] "
  := ([ A @ x ] /\ [ B @ x ] /\ [ C @ x ])
  (at level 60).
Notation " [ A , B @ x , y ] "
  := ([ A, B @ x ] /\ [ A, B @ y ])
  (at level 60).
Notation " [ A @ x , y , z ] "
  := ([ A @ x ] /\ [ A @ y ] /\ [ A @ z ])
  (at level 60).
Notation " [ A , B , C , D @ x ] "
  := ([ A @ x ] /\ [ B @ x ] /\ [ C @ x ] /\ [ D @ x ])
  (at level 60).
Notation " [ A , B , C , D , E @ x ] "
  := ([ A @ x ] /\ [ B @ x ] /\ [ C @ x ] /\ [ D @ x ] /\ [ E @ x ])
  (at level 60).
Notation " [ A , B , C , D , E , F @ x ] "
  := ([ A @ x ] /\ [ B @ x ] /\ [ C @ x ]
   /\ [ D @ x ] /\ [ E @ x ] /\ [ F @ x ])
  (at level 60).
Notation " [ A , B , C @ x , y ] "
  := ([ A , B , C @ x ] /\ [ A , B , C @ y ])
  (at level 60).
Notation " [ A , B @ x , y , z ] "
  := ([ A @ x , y , z ] /\ [ B @ x , y , z ])
  (at level 60).
Notation " [ A @ x , y , z , t ] "
  := ([ A @ x ] /\ [ A @ y ] /\ [ A @ z ] /\ [ A @ t ])
  (at level 60).
Notation " [ A , B ] "
  := (exists x : Line, [ A , B @ x ])
  (at level 60).
Notation " [ A , B , C ] "
  := (exists x : Line, [ A , B , C @ x ])
  (at level 60).
Notation " [ A , B , C , D ] "
  := (exists x : Line, [ A , B , C , D @ x ])
  (at level 60).
Notation " [ A , B , C , D , E ] "
  := (exists x : Line, [ A , B , C , D , E @ x ])
  (at level 60).
Notation " [ A , B , C , D , E , F ] "
  := (exists x : Line, [ A , B , C , D , E , F @ x ])
  (at level 60).
Notation " [ A # B # C ] " (* Hilbert's between relation *)
  := (Between A B C)
  (at level 60).
Notation " [ A ; B # C ] "
  := ([ A # B # C ] \/ (A = B /\ B <> C))
  (at level 60).
Notation " [ A # B ; C ] "
  := ([ A # B # C ] \/ (A <> B /\ B = C))
  (at level 60).
Notation " [ A ; B ; C ] " (* Tarski's between relation *)
  := ([ A # B # C ] \/ A = B \/ B = C)
  (at level 60).
Notation " [ A # B # C # D ] "
  := ([ A # B # C ] /\
      [ A # B # D ] /\
      [ A # C # D ] /\
      [ B # C # D ])
  (at level 60).
Notation " [ A # B # C # D # E ] "
  := ([ A # B # C # D ] /\
      [ A # B # C # E ] /\
      [ A # B # D # E ] /\
      [ A # C # D # E ] /\
      [ B # C # D # E ])
  (at level 60).

Class Definitions `(dc : Declarations) :=
{
  Convergent (x y : Line) : Prop
    := (x <> y) /\ (exists A : Point, [ A @ x, y ]);
  Parallel (x y : Line) : Prop
    := (~ Convergent x y);
  SameRay (O : Point)(A B : Point) : Prop
    := O <> A /\ O <> B /\ [ A, O, B ] /\ ~ [ A # O # B ];
  OppositeSide (x : Line)(A B : Point) : Prop
    := ~ [ A @ x ] /\ ~ [ B @ x ] /\ (exists O, [ O @ x ] /\ [ A # O # B ]);
  SameSide (x : Line)(A B : Point) : Prop
    := ~ [ A @ x ] /\ ~ [ B @ x ] /\ ~ (exists O, [ O @ x ] /\ [ A # O # B ]);
  SameHalfplane (O A B C : Point) : Prop
    := O <> A /\ exists x : Line, [ O @ x ] /\ [ A @ x ] /\ SameSide x B C;
  OppositeHalfplane (O A B C : Point) : Prop
    := O <> A /\ exists x : Line, [ O @ x ] /\ [ A @ x ] /\ OppositeSide x B C;

  Segment
    := @Duo Point;
  BuildSegment
    := @BuildDuo Point;

  Triangle
    := @Triple Point (fun A B C => ~ [ A, B, C ]);
  BuildTriangle
    := @BuildTriple Point (fun A B C => ~ [ A, B, C ]);

  Ray
    := @Duple Point (fun A B => A <> B);
  BuildRay
    := @BuildDuple Point (fun A B => A <> B);

  EqRays (a b : Ray) : Prop
    := (da a = da b) /\ SameRay (da a)(db a)(db b);
  OpRays (a b : Ray) : Prop
    := (da a = da b) /\ [ db a # da a # db b ];

  Sector
    := @Duple Ray (fun a b => da a = da b);
  BuildSector
    := @BuildDuple Ray (fun a b => da a = da b);

  nColRs (a b : Ray) : Prop
    := da a = da b /\ ~ [ (db a), (da a), (db b) ];

  Flag
    := @Duple Ray (fun a b => nColRs a b);
  BuildFlag
    := @BuildDuple Ray (fun a b => nColRs a b);
}.
Notation " ![ a , b ] "
  := ([ da a, db a, da b, db b ])
  (at level 60).
Notation " ![ a , b , c ] "
  := ([ da a, db a, da b, db b, da c, db c ])
  (at level 60).
Notation " ![ a # b ] "
  := (nColRs a b)
  (at level 60).
Notation " x >< y "
  := (Convergent x y)
  (at level 60).
Notation " [ O # A , B ] "
  := (SameRay O A B)
  (at level 60).
Notation " [ O ; A , B ] "
  := ([ O # A , B ] \/ O = A \/ O = B)
  (at level 60).
Notation " [ A | x | B ] "
  := (OppositeSide x A B)
  (at level 60).
Notation " [ x | A , B ] "
  := (SameSide x A B)
  (at level 60).
Notation " [ O # A | B , C ] "
  := (SameHalfplane O A B C)
  (at level 60).
Notation " [ B | O # A | C ] "
  := (OppositeHalfplane O A B C)
  (at level 60).
Notation " [ O | A ; B ; C ] "
  := ([ O # A | B, C ] /\ [ O # C | B, A ])
  (at level 60).
Notation " a == b "
  := (EqRays a b)
  (at level 60).
Notation " a =/= b "
  := (~ EqRays a b)
  (at level 60).
Notation " a <==> b "
  := (OpRays a b)
  (at level 60).
Notation " a <=/=> b "
  := (~ OpRays a b)
  (at level 60).
Notation " x || y "
  := (Parallel x y).

Class Quantities `(df : Definitions) :=
{(* This Class substitutes congruence axioms of Hilbert. We consider
 Hilbert's "congruence classes" as "quanitites" in Euclud's Elements.
 Thus, we consider this Class as the definition of those quantities.
 Since in our subsequent geometric axioms we do not construct Length and
 Angle 'per se', we do not assume that DrawSegment and DrawSector functions
 do construct some new points and rays on the plane. Rather, they refer to
 earlier constructed points and rays.
*)
  Length : Set;
  Ruler : Segment -> Length;
  DrawSegment : forall d : Length, { s : Segment | Ruler s = d };

  Angle : Set;
  Protractor : Sector -> Angle;
  DrawSector : forall a : Angle, { s : Sector | Protractor s = a };
}.
Notation " [| A , B |] "
  := (Ruler ({{ A, B }}))
  (at level 60).
Notation " [| a , b | ab |] "
  := (Protractor ({{ a # b | ab }}))
  (at level 60).
Notation " [| A , O , B | OA , OB |] "
  := ([| {{ O # A | OA }} , {{ O # B | OB }} | eq_refl O |])
  (at level 60).
Notation " [ A -- O -- B ] "
  := ([ A # O # B ] /\ [| O, A |] = [| O, B |])
  (at level 60).

Class Orientations `(qs : Quantities) :=
{(* This class does not contain any additional postulates or axioms.
 It will be instantiated later based on the postulates and axioms of
 poins, lines and circles. This class is placed here for a
 technical reasons. It helps us to define the convex angles right here,
 at the very beginning of the file. Otherwise we woud have to postpone
 the definition of the convex angles together with angle axioms
 untill we study all the properties of triangle orientations on the plane.
*)
  ConvexFlag : Flag -> bool;
  ConvexAngleRs (a b : Ray)(diab : ![ a # b ]) : Angle
    := match ConvexFlag ({{ a # b | diab }}) with
       | true => [| a, b | proj1 diab |]
       | false => [| b, a | eq_sym (proj1 diab) |]
       end;
  nColPs_DiPs : forall (A O B : Point),
    ~ [ A, O, B ] -> O <> A /\ O <> B /\ A <> B;
  ConvexAnglePs (A O B : Point)(nColAOB : ~ [A, O, B]) : Angle
    := match nColPs_DiPs A O B nColAOB with
       | conj nOeqA (conj nOeqB _) =>
         let a := {{ O # A | nOeqA }} in
         let b := {{ O # B | nOeqB }} in
         ConvexAngleRs a b (conj eq_refl nColAOB)
       end;
  nCol_a : forall (A B C : Point),
    ~ [ A, B, C ] -> ~ [ B, C, A ];
  nCol_b : forall (A B C : Point),
    ~ [ A, B, C ] -> ~ [ C, A, B ];
  EqTriangle (A B : Triangle)
    := [| ta A, tb A |] = [| ta B, tb B |]
    /\ [| tb A, tc A |] = [| tb B, tc B |]
    /\ [| tc A, ta A |] = [| tc B, ta B |]
    /\ ConvexAnglePs (ta A)(tb A)(tc A)(tp A)
     = ConvexAnglePs (ta B)(tb B)(tc B)(tp B)
    /\ ConvexAnglePs (tb A)(tc A)(ta A)(nCol_a (ta A)(tb A)(tc A)(tp A))
     = ConvexAnglePs (tb B)(tc B)(ta B)(nCol_a (ta B)(tb B)(tc B)(tp B))
    /\ ConvexAnglePs (tc A)(ta A)(tb A)(nCol_b (ta A)(tb A)(tc A)(tp A))
     = ConvexAnglePs (tc B)(ta B)(tb B)(nCol_b (ta B)(tb B)(tc B)(tp B));
}.
Notation " % F "
  := (ConvexFlag F)
  (at level 70).
Notation " [| a # b | diab |] "
  := (ConvexAngleRs a b diab)
  (at level 60).
Notation " [| A # O # B | nColAOB |] "
  := (ConvexAnglePs A O B nColAOB)
  (at level 60).
Notation " A :=: B "
  := (EqTriangle A B)
  (at level 60).

(*****************************************************************************)
(** AXIOMS AND POSTULATES *)
(*****************************************************************************)

Class Points `(df : Definitions) :=
{
  (** P1 *)
  DrawPoint :
    { A : Point | A = A };
  (** P2 *)
  DrawDistinctPoint : forall (A : Point),
    { B : Point | A <> B };
  (** P3, Arend Heyting *)
  DecidePointsDistinction : forall (A B C : Point),
    A <> C
      -> { A <> B } + { B <> C };
}.

Class Lines `(pt : Points) :=
{
  (** P4 *)
  DrawPointOnLine : forall (x : Line),
    { A : Point | [ A @ x ] };
  (** P5 *)
  DrawDistinctPointOnLine : forall (A : Point)(x : Line),
    [ A @ x ]
      -> { B : Point | A <> B /\ [ B @ x ] };
  (** P6 *)
  DrawPointApartLine : forall (x : Line),
    { A : Point | ~ [ A @ x ] };
  (** P7, Point-Point Extension *)
  DrawExtensionLinePP : forall (A B : Point),
    A <> B
      -> { x : Line | [ A, B @ x ] };
  (** P8, Jan Von Plato *)
  DecideLineApartTwoPoints : forall (A B : Point)(x y : Line),
    A <> B
      -> [ A, B @ x ]
      -> x <> y
      -> { ~ [ A @ y ] } + { ~ [ B @ y ] };
  (** P9, Line-Line Intersection *)
  DrawIntersectionPointLL : forall (x y : Line),
    x >< y
      -> { A : Point | [ A @ x, y ] };
}.

Class Circles `(ln : Lines)(qs : Quantities df) :=
{(* Note that we formalize here collapsing compas of Euclid.
 So, the circle is defined by any two poins - circle's center and arbitrary
 point on the circle. Circles with null radius are also permitted.
*)
  (** A1a *)
  BetPs_DiPs : forall (A B C : Point),
    [ A # B # C ]
      -> A <> C;
  (** A1b *)
  BetPs_ColPs : forall (A B C : Point),
    [ A # B # C ]
      -> [ A, B, C ];
  (** A1c *)
  BetPs_sym : forall (A B C : Point),
    [ A # B # C ]
      -> [ C # B # A ];
  (** A1d *)
  BetPs_nBetPerPs :
  forall (A B C : Point),
  [ A # B # C ]
    -> ~ [ B # A # C ];
  (** P10, Morits Pasch *)
  DecideTwoSides : forall (A B C : Point)(x : Line),
    ~ [ B @ x ]
      -> [ A | x | C ]
      -> { [ A | x | B ] } + { [ B | x | C ] };
  (** A2 *)
  SegPs_sym : forall (A B : Point),
    [| A, B |] = [| B, A |];
  (** A3 : *)
  EqSgs_EqPs : forall (A B C : Point),
    [| A, B |] = [| C, C |]
      <-> A = B;
  (** P11, Line-Circle Intersection *)
  DrawIntersectionPointLC : forall (O A B : Point),
    O <> A
      -> { C : Point | [ A # O ; C ] /\ [| O, C |] = [| O, B |] };
}.

Class Angles `(on : Orientations) :=
{(* Axiom 6 States that if two angles are equal, their explementary angles 
 will also be equal.

 Since we defined angles as quantities (congruence classes), we need
 the last Axiom 8, which ensures that the orientations we defined
 earlier for pairs of rays originating from the same point, can also be
 assigned to their respective angles. So, with this axiom we can lift
 definition of orientation up from a particular geometric figures
 (pair of rays) to angles (congruence class).
*)
  (** A4 *)
  EqRs_EqRs_EqAs : forall (a b c d : Ray)
    (orab : da a = da b)(orcd : da c = da d),
    a == b
      -> c == d
      -> [| a, b | orab |] = [| c, d | orcd |];
  (** A5 *)
  OpRs_OpRs_EqAs : forall (a b c d : Ray)
    (orab : da a = da b)(orcd : da c = da d),
    a <==> b
      -> c <==> d
      -> [| a, b | orab |] = [| c, d | orcd |];
  (** A6 *)
  EqAs_EqExpAs : forall (a b c d : Ray)
    (orab : da a = da b)(orcd : da c = da d),
    [| a, b | orab |] = [| c, d | orcd |]
      -> [| b, a | eq_sym orab |] = [| d, c | eq_sym orcd |];
  (** A7 *)
  EqAs_EqRs :
    forall (a b c : Ray)(roab : da a = da b)(roac : da a = da c),
    [| a, b | roab |] = [| a, c | roac |]
      <-> b == c;
  (** A8 *)
  EqAs_EqTs : forall (a b c d : Ray)
    (orab : da a = da b)(orcd : da c = da d)
    (diab : ![ a # b ])(dicd : ![ c # d]),
    [| a, b | orab |] = [| c, d | orcd |]
      -> % {{ a # b | diab }} = % {{ c # d | dicd }};
}.

Class Concentricals `(cr : Circles) :=
{
  (** A9 *)
  ConcentricCircles : forall (O A B A' B' : Point),
    [ O # A # B ]
      -> [ O # A', B' ]
      -> [| O, A |] = [| O, A' |]
      -> [| O, B |] = [| O, B' |]
      -> [ O # A' # B' ] /\ [| A, B |] = [| A', B' |];
  (** P12, Circle-Circle Intersection*)
  DrawIntersectionPointCC : forall (A O B A' O' B' P: Point),
    ~ [ O, O', P ]
      -> [ A -- O -- B ]
      -> [ A' -- O' -- B' ]
      -> [ A # A' # B # B' ]
      -> { Q : Point | [ O # O' | P, Q ] /\ [| O, Q |] = [| O, A |]
                     /\ [| O', Q |] = [| O', A' |] };
}.

(* We shall prove that the next two statements are actually equivalent to
 each other. So, it suffices to accept only one of them as a new axiom.
 The first statement formalizes the so-called Euclid's method of
 superposition, while the second is actually a combination of
 Euclid's SAS and SSS triangle congruence theorems.
*)
Class Superpositions `(on : Orientations) :=
{
  (** A10 *)
  SuperpositionPrinciple : forall (A B C D E F : Point)
    (nABC : ~ [ A, B, C ])(nDEF : ~ [ D, E, F ]),
    [| A, B |] = [| D, E |]
      -> exists (F' : Point)(nDEF' : ~ [ D, E, F' ]), [ D # E | F, F' ] /\
         {{ A # B # C | nABC }} :=: {{ D # E # F' | nDEF' }};
}.
Class Congruences `(on : Orientations) :=
{
  (** A10' *)
  TriangleCongruence : forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
    [| A, B |] = [| D, E |]
      -> [| B, C |] = [| E, F |]
      -> [| C, A |] = [| F, D |]
      <-> [| A # B # C | nColABC |] = [| D # E # F | nColDEF |];
}.

Class Parallels (dc : Declarations)(df : Definitions dc) :=
{
  (** A11, John Playfair, 1748-1819 *)
  (* No more than one line parallel to the given passes through
   an arbitrary point on the plane. *)
  ParallelAxiom :
  forall (A : Point)(x y z : Line),
  x || z
    -> y || z
    -> [ A @ x, y ]
    -> x = y;
}.

(*****************************************************************************)
(* 1 *) Section INCIDENCE.
Context `{ ls : Lines }.
(*****************************************************************************)

Lemma nIncPt_DiPs :
  forall (A B : Point)(x : Line),
  [ A @ x ]
    -> ~ [ B @ x ]
    -> A <> B.
Proof with eauto.
  intros * Aox nBox AeqB; subst; auto.
Qed.
Lemma nIncPt_DiLs :
  forall (A : Point)(x y : Line),
  [ A @ x ]
    -> ~ [ A @ y ]
    -> x <> y.
Proof with eauto.
  intros * Aox nAoy xeqy; subst...
Qed.

(** Theorem #1. *)
(* a) For any two distinct points, there is at most one line containing
  both these points. *)
Theorem DiPs_EqLs :
  forall (A B : Point)(x y : Line),
  A <> B
    -> [ A, B @ x, y ]
    -> x = y.
Proof with eauto.
  intros * nAeqB [[ Aox Box ][ Aoy Boy ]].
  apply NNPP; intros nxeqy.
  destruct (DecideLineApartTwoPoints A B x y)...
Qed.
(* b) For any two distinct lines, there is at most one point on
  both these lines. *)
Theorem DiLs_EqPs :
  forall (A B : Point)(x y : Line),
  x <> y
    -> [ A, B @ x, y ]
    -> A = B.
Proof with eauto.
  intros * nxeqy [[ Aox Box ][ Aoy Boy ]].
  apply NNPP; contradict nxeqy.
  apply (DiPs_EqLs A B x y)...
Qed.

(** Problem #1 *)
(* Given an arbitrary point. Draw a line that pass through it. *)
Definition DrawLineThroughPoint :
  forall (A : Point),
  { x : Line | [ A @ x ] }.
Proof with eauto.
  intros.
  destruct (DrawDistinctPoint A) as [ B nAeqB ];
  destruct (DrawExtensionLinePP A B nAeqB) as [ x [ Aox Box ]];
  exists x...
Defined.

(** Problem #2 *)
(* Draw an arbitrary line on plane. *)
Definition DrawLine :
  { x : Line | x = x }.
Proof with eauto.
  destruct DrawPoint as [ A _ ].
  destruct (DrawLineThroughPoint A) as [ x Aox ].
  exists x...
Defined.

(** Problem #3 *)
(* Given an arbitrary point. Draw a line that does not pass through it. *)
Definition DrawLineApartPoint :
  forall (A : Point),
  { x : Line | ~ [ A @ x ] }.
Proof with eauto.
  intros.
  destruct (DrawDistinctPoint A) as [ B nBeqA ].
  destruct (DrawExtensionLinePP B A) as [ t [ Bot Aot ]]...
  destruct (DrawPointApartLine t) as [ C nCot ].
  assert (nBeqC : B <> C). { contradict nCot; subst... }
  destruct (DrawExtensionLinePP B C ) as [ x [ Box Cox ]]...
  exists x. intros Aox.
  assert (xeqt : x = t). { eapply (DiPs_EqLs A B)... }
  subst...
Defined.

(** Problem #4 *)
(* Given two distinct points. Draw a line that passes through one of these
 points and does not pass through another. *)
Definition DrawLineSeparatingTwoPoints :
  forall (A B : Point),
  A <> B
    -> { x : Line | [ A @ x ] /\ ~ [ B @ x ] }.
Proof with eauto.
  intros * nAeqB.
  destruct (DrawExtensionLinePP A B) as [ t [ Bot Aot ]]...
  destruct (DrawPointApartLine t) as [ C nCot ].
  assert (nAeqC : A <> C). { contradict nCot; subst... }
  destruct (DrawExtensionLinePP A C ) as [ x [ Aox Cox ]]...
  exists x; split...
  intros Box.
  assert (xeqt : x = t). { eapply (DiPs_EqLs A B)... }
  subst...
Defined.

(** Problem #5 *)
(* Given two distinct lines. Draw a point that lies on one of these lines
 and does not lie on the other. *)
Definition DrawPointSeparatingTwoLines :
  forall (x y : Line),
  x <> y
    -> { A : Point | [ A @ x ] /\ ~ [ A @ y ] }.
Proof with eauto.
  intros x y nxeqy.
  destruct (DrawPointOnLine x) as [ A Aox ].
  destruct (DrawDistinctPointOnLine A x Aox) as [ B [ nAeqB Box ]]...
  destruct (DecideLineApartTwoPoints A B x y)...
Defined.

(** Problem #6 *)
(* Given two distinct points, through one of which pass two distinct lines.
 Decide which of these two lines does not pass through another point. *)
Definition DecidePointApartTwoLines :
  forall (O A : Point)(x y : Line),
  A <> O
    -> [ O @ x, y ]
    -> x <> y
    -> { ~ [ A @ x ] } + { ~ [ A @ y ] }.
Proof with eauto.
  intros * nAeqO [ Oox Ooy ] nxeqy.
  destruct (DrawDistinctPointOnLine O x Oox) as [ B [ nBeqO Box ]].
  destruct (DrawDistinctPointOnLine O y Ooy) as [ C [ nCeqO Coy ]].
  assert (nBeqC : B <> C).
  { contradict nxeqy; subst. eapply (DiPs_EqLs O C)... }
  destruct (DrawExtensionLinePP B C nBeqC) as [ z [ Boz Coz ]].
  destruct (DrawExtensionLinePP A O nAeqO) as [ t [ Aot Oot ]].
  assert (nteqz : t <> z).
  { contradict nxeqy; subst...
    assert (y = z). { eapply (DiPs_EqLs O C)... }
    subst...
    eapply (DiPs_EqLs O B)...
  }
 destruct (DecideLineApartTwoPoints B C z t nBeqC)
   as [ H1 | H2 ]; try split...
 { left. contradict H1.
   assert (x = t). { eapply (DiPs_EqLs A O)... }
   subst...
 }
 { right. contradict H2.
   assert (y = t). { eapply (DiPs_EqLs A O)... }
   subst...
 }
Defined.

Example DrawThirdDistinctPoint :
  forall (A B : Point),
  { C : Point | C <> A /\ C <> B }.
Proof with eauto.
  intros.
  destruct (DrawDistinctPoint A) as [ P nPeqA ].
  destruct (DecidePointsDistinction A B P nPeqA) as [ nAeqB | nBeqP ].
  { destruct (DrawExtensionLinePP A B nAeqB) as [ x [ Aox Box ]].
    destruct (DrawPointApartLine x) as [ C nCox ].
    exists C; split; contradict nCox; subst...
  }
  { exists P; split... }
Defined.

Lemma ConvLs_irrefl :
  forall (x : Line),
  ~ x >< x.
Proof.
  intros x [ H _ ].
  contradict H; auto.
Qed.
Lemma ConvLs_sym :
  forall (x y : Line),
  x >< y
    -> y >< x.
Proof.
  unfold Convergent.
  intros x y [ nyeqx [ A [ Aoy Aox ]]].
  split; eauto.
Qed.

Lemma nIncPt_ConvLs_1 :
  forall (A B : Point)(x y : Line),
  A <> B
    -> [ A @ x ]
    -> [ A @ y ]
    -> [ B @ x ]
    -> ~ [ B @ y ]
    -> x >< y.
Proof with eauto.
  intros * nAeqB Aox Aoy Box nBoy.
  split.
  { contradict nBoy; subst... }
  { exists A; split... }
Qed.
Lemma nIncPt_ConvLs_2 :
  forall (A B : Point)(x y : Line),
  A <> B
    -> [ A @ x ]
    -> [ A @ y ]
    -> [ B @ y ]
    -> ~ [ B @ x ]
    -> x >< y.
Proof with eauto.
  intros * nAeqB Aox Aoy Boy nBox.
  split.
  { contradict nBox; subst... }
  { exists A; split... }
Qed.

Lemma ParLs_InsPs_EqLs :
  forall (A : Point)(x y : Line),
  x || y
    -> [ A @ x, y ]
    -> x = y.
Proof.
  intros * xpary [ Aox Aoy ].
  unfold Parallel, Convergent in *.
  apply NNPP; intros nxeqy.
  contradict xpary; split; try exists A; auto.
Qed.

End INCIDENCE.

Hint Resolve
  not_eq_sym nIncPt_DiPs
  : DiPs.
Hint Resolve
  DiLs_EqPs
  : EqPs.
Hint Resolve
  not_eq_sym nIncPt_DiLs
  : DiLs.
Hint Resolve
  DiPs_EqLs
  ParLs_InsPs_EqLs
  : EqLs.

Tactic Notation "dips"
  := try solve
  [ congruence
  | eauto with DiPs
  | intuition eauto with DiPs ].
Tactic Notation "dips" integer(n)
  := try solve
  [ congruence
  | eauto n with DiPs
  | intuition (auto n with DiPs) ].
Tactic Notation "eqps"
  := try solve
  [ congruence
  | eauto with EqPs
  | intuition eauto with EqPs ].
Tactic Notation "eqps" integer(n)
  := try solve
  [ congruence
  | eauto n with EqPs
  | intuition (auto n with EqPs) ].
Tactic Notation "dils"
  := try solve
  [ congruence
  | eauto with DiLs
  | intuition eauto with DiLs].
Tactic Notation "dils" integer(n)
  := try solve
  [ congruence
  | eauto n with DiLs
  | intuition (auto n with DiLs) ].
Tactic Notation "eqls"
  := try solve
  [ congruence
  | eauto with EqLs
  | intuition eauto with EqLs].
Tactic Notation "eqls" integer(n)
  := try solve
  [ congruence
  | eauto n with EqLs
  | intuition (auto n with EqLs) ].

(*****************************************************************************)
(* 2 *) Section COLLINEARITY.
Context `{ lns : Lines }.
(*****************************************************************************)

Lemma ColPs_IncPt :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A, B @ x ]
    -> [ A, B, C ] \/
       [ A, C, B ] \/
       [ B, A, C ] \/
       [ B, C, A ] \/
       [ C, A, B ] \/
       [ C, B, A ]
    -> [ C @ x ].
Proof.
  intros * nAeqB [ Aox Box ] H;
  repeat destruct H as [ H | H ];
  destruct H as [ t [ Aot [ Bot Cot ]]];
  rewrite (DiPs_EqLs A B x t nAeqB); firstorder.
Qed.
Lemma ColPs_IncPt_1 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ A, B, C ]
    -> [ C @ x ].
Proof with eauto.
  intros; apply (ColPs_IncPt A B)...
Qed.
Lemma ColPs_IncPt_2 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ B, C, A ]
    -> [ C @ x ].
Proof with eauto.
  intros; apply (ColPs_IncPt A B)...
Qed.
Lemma ColPs_IncPt_3 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ C, A, B ]
    -> [ C @ x ].
Proof with auto 6.
  intros; apply (ColPs_IncPt A B)...
Qed.
Lemma ColPs_IncPt_4 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ B, A, C ]
    -> [ C @ x ].
Proof with eauto.
  intros; apply (ColPs_IncPt A B)...
Qed.
Lemma ColPs_IncPt_5 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ A, C, B ]
    -> [ C @ x ].
Proof with eauto.
  intros; apply (ColPs_IncPt A B)...
Qed.
Lemma ColPs_IncPt_6 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ C, B, A ]
    -> [ C @ x ].
Proof with auto 6.
  intros; apply (ColPs_IncPt A B)...
Qed.

Lemma nColPs_nIncPt :
  forall (A B C : Point)(x : Line),
  ~ [ A, B, C ] \/
  ~ [ A, C, B ] \/
  ~ [ B, A, C ] \/
  ~ [ B, C, A ] \/
  ~ [ C, A, B ] \/
  ~ [ C, B, A ]
    -> [ A, B @ x ]
    -> ~ [ C @ x ].
Proof.
  intros; firstorder.
Qed.
Lemma nColPs_nIncPt_1 :
  forall (A B C : Point)(x : Line),
  [ A @ x ]
    -> [ B @ x ]
    -> ~ [ A, B, C ]
    -> ~ [ C @ x ].
Proof.
  intros; firstorder.
Qed.
Lemma nColPs_nIncPt_2 :
  forall (A B C : Point)(x : Line),
  [ A @ x ]
    -> [ B @ x ]
    -> ~ [ B, C, A ]
    -> ~ [ C @ x ].
Proof.
  intros; firstorder.
Qed.
Lemma nColPs_nIncPt_3 :
  forall (A B C : Point)(x : Line),
  [ A @ x ]
    -> [ B @ x ]
    -> ~ [ C, A, B ]
    -> ~ [ C @ x ].
Proof.
  intros; firstorder.
Qed.
Lemma nColPs_nIncPt_4 :
  forall (A B C : Point)(x : Line),
  [ A @ x ]
    -> [ B @ x ]
    -> ~ [ B, A, C ]
    -> ~ [ C @ x ].
Proof.
  intros; firstorder.
Qed.
Lemma nColPs_nIncPt_5 :
  forall (A B C : Point)(x : Line),
  [ A @ x ]
    -> [ B @ x ]
    -> ~ [ A, C, B ]
    -> ~ [ C @ x ].
Proof.
  intros; firstorder.
Qed.
Lemma nColPs_nIncPt_6 :
  forall (A B C : Point)(x : Line),
  [ A @ x ]
    -> [ B @ x ]
    -> ~ [ C, B, A ]
    -> ~ [ C @ x ].
Proof.
  intros; firstorder.
Qed.

Lemma nIncPt_nColPs_1 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> ~ [ C @ x ]
    -> ~ [ A, B, C ].
Proof with eauto.
  intros * nAeqB Aox Box nCox.
  contradict nCox. eapply ColPs_IncPt_1...
Qed.
Lemma nIncPt_nColPs_2 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> ~ [ C @ x ]
    -> ~ [ B, C, A ].
Proof with eauto.
  intros * nAeqB Aox Box nCox.
  contradict nCox. eapply ColPs_IncPt_2...
Qed.
Lemma nIncPt_nColPs_3 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> ~ [ C @ x ]
    -> ~ [ C, A, B ].
Proof with eauto.
  intros * nAeqB Aox Box nCox.
  contradict nCox. eapply ColPs_IncPt_3...
Qed.
Lemma nIncPt_nColPs_4 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> ~ [ C @ x ]
    -> ~ [B, A, C].
Proof with eauto.
  intros * nAeqB Aox Box nCox.
  contradict nCox. eapply ColPs_IncPt_4...
Qed.
Lemma nIncPt_nColPs_5 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> ~ [ C @ x ]
    -> ~ [ A, C, B ].
Proof with eauto.
  intros * nAeqB Aox Box nCox.
  contradict nCox. eapply ColPs_IncPt_5...
Qed.
Lemma nIncPt_nColPs_6 :
  forall (A B C : Point)(x : Line),
  A <> B
    -> [ A @ x ]
    -> [ B @ x ]
    -> ~ [ C @ x ]
    -> ~ [C, B, A].
Proof with eauto.
  intros * nAeqB Aox Box nCox.
  contradict nCox. eapply ColPs_IncPt_6...
Qed.

Lemma ColPs_ColPerPs :
  forall (A B C : Point),
  [ A, C, B ] \/
  [ B, A, C ] \/
  [ B, C, A ] \/
  [ C, A, B ] \/
  [ C, B, A ]
    -> [ A, B, C ].
Proof with eauto.
  intros * H;
  repeat destruct H as [ H | H ];
  destruct H as [ x [ Aox [ Box Cox ]]];
  exists x...
Qed.

Lemma ColPerPs_1 :
  forall (A B C : Point),
  [ A, B, C ]
    -> [ B, C, A ].
Proof.
  intros; firstorder.
Qed.
Lemma ColPerPs_2 :
  forall (A B C : Point),
  [ A, B, C ]
    -> [ C, A, B ].
Proof.
  intros; firstorder.
Qed.
Lemma ColPerPs_3 :
  forall (A B C : Point),
  [ A, B, C ]
    -> [ B, A, C ].
Proof.
  intros; firstorder.
Qed.
Lemma ColPerPs_4 :
  forall (A B C : Point),
  [ A, B, C ]
    -> [ A, C, B ].
Proof.
  intros; firstorder.
Qed.
Lemma ColPerPs_5 :
  forall (A B C : Point),
  [ A, B, C ]
    -> [ C, B, A ].
Proof.
  intros; firstorder.
Qed.

Lemma nColPs_nColPerPs :
  forall (A B C : Point),
  ~ [ A, C, B ] \/
  ~ [ B, A, C ] \/
  ~ [ B, C, A ] \/
  ~ [ C, A, B ] \/
  ~ [ C, B, A ]
    -> ~ [ A, B, C ].
Proof with eauto.
  intros * H;
  repeat destruct H as [ H | H ]; contradict H;
  destruct H as [ x [ Aox [ Box Cox ]]];
  exists x...
Qed.
Lemma nColPerPs_1 :
  forall (A B C : Point),
  ~ [ A, B, C ]
    -> ~ [ B, C, A ].
Proof with eauto.
  intros; apply nColPs_nColPerPs...
Qed.
Lemma nColPerPs_2 :
  forall (A B C : Point),
  ~ [ A, B, C ]
    -> ~ [ C, A, B ].
Proof with eauto.
  intros; apply nColPs_nColPerPs...
Qed.
Lemma nColPerPs_3 :
  forall (A B C : Point),
  ~ [ A, B, C ]
    -> ~ [ B, A, C ].
Proof.
  intros.
  apply nColPs_nColPerPs.
  auto.
Qed.
Lemma nColPerPs_4 :
  forall (A B C : Point),
  ~ [ A, B, C ]
    -> ~ [ A, C, B ].
Proof with eauto.
  intros; apply nColPs_nColPerPs...
Qed.
Lemma nColPerPs_5 :
  forall (A B C : Point),
  ~ [ A, B, C ]
    -> ~ [ C, B, A ].
Proof with eauto.
  intros; apply nColPs_nColPerPs...
Qed.

(** Theorem #2. *)
(* Whatever are two points, there exists a line passing through
 both of them. *)
Theorem ExistLineThroughTwoPoints :
  forall (A B : Point),
  [ A, B ].
Proof with eauto.
  intros *.
  destruct (classic (A = B)) as [ AeqB | nAeqB ]; subst;
  [destruct (DrawDistinctPoint B) as [ A nAeqB ]| idtac ];
   destruct (DrawExtensionLinePP A B) as [ x [ Pox Aox ]
  ]...
Qed.

Lemma ColPs_12 :
  forall (A B : Point),
  [ A, A, B ].
Proof.
  intros *.
  destruct (ExistLineThroughTwoPoints A B); exists x; firstorder.
Qed.
Lemma ColPs_23 :
  forall (A B : Point),
  [ A, B, B ].
Proof.
  intros *.
  destruct (ExistLineThroughTwoPoints A B); exists x; firstorder.
Qed.
Lemma ColPs_13 :
  forall (A B : Point),
  [ A, B, A ].
Proof.
  intros *.
  destruct (ExistLineThroughTwoPoints A B); exists x; firstorder.
Qed.

(** Theorem #3. *)
(* If three points are not collinear, they are all distinct. *)
Theorem nColPs_3DiPs :
  forall (A O B : Point),
  ~ [ A, O, B ]
    -> O <> A /\ O <> B /\ A <> B.
Proof.
  intros * nColABC.
  repeat split; contradict nColABC; subst.
  { destruct (ExistLineThroughTwoPoints A B); exists x; firstorder. }
  { destruct (ExistLineThroughTwoPoints A B); exists x; firstorder. }
  { destruct (ExistLineThroughTwoPoints B O); exists x; firstorder. }
Qed.

Lemma nColPs_DiPs_12 :
  forall (A B C : Point),
  ~ [ A, B, C ]
    -> A <> B.
Proof with eauto.
  intros * nColABC.
  contradict nColABC; subst.
  destruct (ExistLineThroughTwoPoints B C); exists x; firstorder.
Qed.
Lemma nColPs_DiPs_23 :
  forall (A B C : Point),
  ~ [ A, B, C ]
    -> B <> C.
Proof.
  intros * nColABC.
  contradict nColABC; subst.
  destruct (ExistLineThroughTwoPoints A C); exists x; firstorder.
Qed.
Lemma nColPs_DiPs_13 :
  forall (A B C : Point),
  ~ [ A, B, C ]
    -> A <> C.
Proof.
  intros * nColABC.
  contradict nColABC; subst.
  destruct (ExistLineThroughTwoPoints B C); exists x; firstorder.
Qed.

Lemma nColPs_DiLs_1 :
  forall (A B C : Point)(x y : Line),
  ~ [ A, B, C ]
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ C @ y ]
    -> x <> y.
Proof.
  intros * nColABC Aox Box Coy xeqy.
  subst; contradict nColABC; exists y; auto.
Qed.
Lemma nColPs_DiLs_2 :
  forall (A B C : Point)(x y : Line),
  ~ [ A, B, C ]
    -> [ A @ x ]
    -> [ B @ y ]
    -> [ C @ x ]
    -> x <> y.
Proof.
  intros * nColABC Aox Box Coy xeqy.
  subst; contradict nColABC; exists y; auto.
Qed.
Lemma nColPs_DiLs_3 :
  forall (A B C : Point)(x y : Line),
  ~ [ A, B, C ]
    -> [ A @ y ]
    -> [ B @ x ]
    -> [ C @ x ]
    -> x <> y.
Proof.
  intros * nColABC Aox Box Coy xeqy.
  subst; contradict nColABC; exists y; auto.
Qed.

Example DrawNonCollinearPoint :
  forall (A B : Point),
  A <> B
    -> { C : Point | ~ [ A, B, C ] }.
Proof with eauto.
  intros * nAeqB.
  destruct (DrawExtensionLinePP A B) as [ x [ Aox Box ]]...
  destruct (DrawPointApartLine x) as [ C nCox ]...
  exists C; contradict nCox.
  apply (ColPs_IncPt A B C)...
Defined.

Lemma ColPs_weak_trans :
  forall (A B C D : Point),
  [ A, B, D ]
    -> [ B, C, D ]
    -> [ A, C, D ]
    -> [ A, B, C ].
Proof with subst; eauto.
  intros * ColABD ColBCD ColACD.
  destruct ColABD as [ x [ Aox [ Box Dox ]]].
  destruct ColBCD as [ y [ Aoy [ Coy Doy ]]].
  destruct ColACD as [ z [ Aoz [ Boz Doz ]]].
  destruct (classic (A = B)) as [ AeqB | nAeqB ].
  { subst... }
  { destruct (classic (B = C)) as [ BeqC | nBeqC ].
    { subst... }
    { destruct (classic (A = C)) as [ AeqC | nAeqC ].
      { subst... }
      { destruct (classic (B = D)) as [ BeqD | nBeqD ].
        { subst; exists z... }
        { destruct (classic (A = D)) as [ AeqD | nAeqD ].
          { subst; exists y... }
          { destruct (classic (C = D)) as [ CeqD | nCeqD ].
            { subst; exists x... }
            { assert (xeqy : x = y). { apply (DiPs_EqLs B D x y)... }
              assert (yeqz : y = z). { apply (DiPs_EqLs C D y z)... }
              exists z...
            }
          }
        }
      }
    }
  }
Qed.

Lemma ColPs_5_trans :
  forall (A B X Y Z : Point),
  A <> B
    -> [ X, A, B ]
    -> [ A, Y, B ]
    -> [ A, B, Z ]
    -> [ X, Y, Z ].
Proof with eauto.
  intros * nAeqB ColABC ColABD ColABE.
  destruct ColABC as [ x [ Aox [ Box Cox ]]];
  destruct ColABD as [ y [ Aoy [ Boy Doy ]]];
  destruct ColABE as [ z [ Aoz [ Boz Eoz ]]].
  assert (yeqz : y = z). { try apply (DiPs_EqLs A B y z nAeqB)... }
  assert (xeqy : x = y). { try apply (DiPs_EqLs A B x y nAeqB)... }
  subst. exists z...
Qed.
Lemma ColPs_trans :
  forall (O A B C : Point),
  B <> O
    -> [ A, O, B ]
    -> [ B, O, C ]
    -> [ A, O, C ].
Proof with eauto.
  intros A B C D nAeqB Col1 Col2.
  apply (ColPs_5_trans A C B A D)...
  { apply ColPs_12... }
  { apply ColPerPs_3... }
Qed.

Example nColPs_trans :
  forall (O A B C : Point),
  B <> O
    -> ~ [ A, O, C ]
    -> { ~ [ A, O, B ] } + { ~ [ B, O, C ] }.
Proof with eauto.
  intros * nBeqO nColAOC.
  destruct (DrawExtensionLinePP B O nBeqO) as [ x [ Box Oox ]].
  assert (nAeqC : A <> C). { eapply nColPs_DiPs_13... }
  destruct (DrawExtensionLinePP A C nAeqC) as [ y [ Aoy Coy ]].
  assert (nxeqy : x <> y). { contradict nColAOC; subst... }
  destruct (DecideLineApartTwoPoints A C y x nAeqC) as [ H1 | H2 ]...
  { left; contradict H1; eapply (ColPs_IncPt O B A x); dips. }
  { right; contradict H2; eapply (ColPs_IncPt O B C x)... }
Defined.

Example nColPs_5_trans :
  forall (A B X Y Z : Point),
  A <> B
    -> ~ [ X, Y, Z ]
    -> { ~ [ X, A, B ] } + { ~ [ A, Y, B ] } + { ~ [ A, B, Z ] }.
Proof with eauto.
  intros * nAeqB nColXYZ.
  destruct (nColPs_3DiPs X Y Z nColXYZ) as [ nXeqY [ nYeqZ nXeqZ ]].
  destruct (DecidePointsDistinction A X B nAeqB) as [ nAeqX | nXeqB ].
  { destruct (nColPs_trans X Y A Z) as [ nColACD | nColACE ]...
    { eapply nColPs_nColPerPs... }
    { destruct (nColPs_trans A X B Y) as [ nColBAC | nColBAD ]...
      { eapply nColPs_nColPerPs... }
      { left; right. eapply nColPs_nColPerPs... }
    }
    { destruct (nColPs_trans A X B Z) as [ nColBAC | nColBAE ]...
      { eapply nColPs_nColPerPs... }
      { right. eapply nColPs_nColPerPs... }
    }
  }
  { destruct (nColPs_trans X Y B Z) as [ nColBCD | nColBCE ]...
    { eapply nColPs_nColPerPs... }
    { destruct (nColPs_trans B X A Y) as [ nColABC | nColABD ]...
      { eapply nColPs_nColPerPs... }
      { left; left. eapply nColPs_nColPerPs... }
      { left; right. eapply nColPs_nColPerPs... }
    }
    { destruct (nColPs_trans B X A Z) as [ nColABC | nColABE ]...
      { eapply nColPs_nColPerPs... }
      { left; left. eapply nColPs_nColPerPs... }
    }
  }
Defined.

(** Problem #7 *)
(* Given three non-collinear points and an arbitrary line.
 Decide wich of the three points does not lie on the line. *)
Definition nColPs_ApartPt :
  forall (A B C : Point)(x : Line),
  ~ [ A, B, C ]
    -> { ~ [ A @ x ] } + { ~ [ B @ x ] } + { ~ [ C @ x ] }.
Proof with eauto.
  intros.
  destruct (DrawPointOnLine x) as [ P Pox ].
  destruct (DrawDistinctPointOnLine P x Pox) as [ Q [ nPeqQ Qox ]].
  destruct (nColPs_5_trans P Q A B C) as [[ G | G ]| G ]...
   { left; left. contradict G. exists x; repeat split... }
   { left; right. contradict G. exists x; repeat split... }
   { right. contradict G. exists x; repeat split... }
Defined.

(** Problem #8 *)
(* Given three non-collinear points and an arbitrary point.
 Decide wich of the three points are not collinear with each other. *)
Definition nColPs_weak_trans :
  forall (A B C D : Point),
  ~ [ A, B, C ]
    -> { ~ [ A, B, D ] } + { ~ [ B, C, D ] } + { ~ [ A, C, D ] }.
Proof with dips.
  intros * nColABC.
  destruct (DecidePointsDistinction A D B) as [ nAeqD | nBeqD ]...
  { contradict nColABC; subst; eapply ColPs_12. }
  { destruct (nColPs_trans A B D C)...
    { eapply nColPs_nColPerPs... }
    { left; left. eapply nColPs_nColPerPs... }
    { right. eapply nColPs_nColPerPs... }
  }
  { destruct (nColPs_trans B A D C)...
    left; right. eapply nColPs_nColPerPs...
  }
Defined.

End COLLINEARITY.

Hint Resolve
 nColPs_DiPs_12 nColPs_DiPs_23 nColPs_DiPs_13
 : DiPs.

Hint Resolve
  nColPs_DiLs_1 nColPs_DiLs_2 nColPs_DiLs_3
  : DiLs.

Hint Resolve
  ColPs_IncPt_1 ColPs_IncPt_2 ColPs_IncPt_3
  ColPs_IncPt_4 ColPs_IncPt_5 ColPs_IncPt_6
  : IncPt.

Hint Resolve
  nColPs_nIncPt_1 nColPs_nIncPt_2 nColPs_nIncPt_3
  nColPs_nIncPt_4 nColPs_nIncPt_5 nColPs_nIncPt_6
  : nIncPt.

Hint Resolve
  ColPs_12 ColPs_23 ColPs_13
  : ColPs.

Hint Resolve
  nIncPt_nColPs_1 nIncPt_nColPs_2 nIncPt_nColPs_3
  nIncPt_nColPs_4 nIncPt_nColPs_5 nIncPt_nColPs_6
  : nColPs.

Hint Resolve
  ColPerPs_1 ColPerPs_2 ColPerPs_3 ColPerPs_4 ColPerPs_5
  ColPs_trans ColPs_5_trans ColPs_weak_trans
  : ColPerPs.

Hint Resolve
  nColPerPs_1 nColPerPs_2 nColPerPs_3 nColPerPs_4 nColPerPs_5
  : nColPerPs.

Hint Immediate eq_sym.

Tactic Notation "incpt"
  := try solve
  [ eauto with IncPt
  | intuition eauto with IncPt ].
Tactic Notation "incpt" integer(n)
  := try solve
  [ eauto n with IncPt
  | intuition (auto n with IncPt) ].
Tactic Notation "nincpt"
  := try solve
  [ eauto with nIncPt
  | intuition eauto with nIncPt ].
Tactic Notation "nincpt" integer(n)
  := try solve
  [ eauto n with nIncPt
  | intuition (auto n with nIncPt) ].
Tactic Notation "inc"
  := try solve
  [ congruence
  | eauto with DiPs DiLs EqPs EqLs IncPt nIncPt
  | intuition eauto with DiPs DiLs EqPs EqLs IncPt nIncPt ].
Tactic Notation "inc" integer(n)
  := try solve
  [ congruence
  | eauto n with DiPs DiLs EqPs EqLs IncPt nIncPt
  | intuition (auto n with DiPs DiLs EqPs EqLs IncPt nIncPt) ].
Tactic Notation "colps"
  := try solve
  [ eauto with ColPs
  | intuition eauto with ColPs ].
Tactic Notation "colps" integer(n)
  := try solve
  [ eauto n with ColPs
  | intuition (auto n with ColPs) ].
Tactic Notation "ncolps"
  := try solve
  [ eauto with nColPs
  | intuition eauto with nColPs ].
Tactic Notation "ncolps" integer(n)
  := try solve
  [ eauto n with nColPs
  | intuition (auto n with nColPs) ].
Tactic Notation "colperps"
  := try solve
  [ eauto with ColPs ColPerPs
  | intuition eauto with ColPs ColPerPs ].
Tactic Notation "colperps" integer(n)
  := try solve
  [ eauto n with ColPs ColPerPs
  | intuition (auto n with ColPs ColPs ColPerPs) ].
Tactic Notation "ncolperps"
  := try solve
  [ eauto with nColPerPs
  | intuition eauto with nColPs nColPerPs ].
Tactic Notation "ncolperps" integer(n)
  := try solve
  [ eauto n with nColPerPs
  | intuition (auto n with nColPs nColPerPs) ].
Tactic Notation "col"
  := try solve
  [ eauto with IncPt nIncPt ColPs nColPs
  | intuition eauto with IncPt nIncPt ColPs nColPs ].
Tactic Notation "col" integer(n)
  := try solve
  [ eauto n with IncPt nIncPt ColPs nColPs
  | intuition (auto n with IncPt nIncPt ColPs nColPs) ].
Tactic Notation "colper"
  := try solve
  [ eauto with IncPt nIncPt ColPs nColPs ColPerPs nColPerPs
  | intuition eauto with IncPt nIncPt ColPs nColPs ColPerPs nColPerPs ].
Tactic Notation "colper" integer(n)
  := try solve
  [ eauto n with IncPt nIncPt ColPs nColPs ColPerPs nColPerPs
  | intuition (auto n with IncPt nIncPt ColPs nColPs ColPerPs nColPerPs)].
Tactic Notation "colinc"
  := try solve
  [ eauto with DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs
  | intuition eauto with DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs ].
Tactic Notation "colinc" integer(n)
  := try solve
  [ eauto n with DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs
  | intuition (auto n with DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs) ].
Tactic Notation "colperinc"
  := try solve
  [ eauto with
    DiPs DiLs EqPs EqLs IncPt ColPerPs nColPerPs nIncPt ColPs nColPs
  | intuition eauto with ColPerPs nColPerPs nIncPt ColPs nColPs ].
Tactic Notation "colperinc" integer(n)
  := try solve
  [ eauto n with
    DiPs DiLs EqPs EqLs IncPt ColPerPs nColPerPs nIncPt ColPs nColPs
  | intuition (auto n with
    DiPs DiLs EqPs EqLs IncPt ColPerPs nColPerPs nIncPt ColPs nColPs) ].

(*****************************************************************************)
(* 3 *) Section BETWEEN.
Context `{ cr : Circles }.
(*****************************************************************************)

Lemma BetPs_nBetPerPs_1 :
  forall (A B C : Point),
  [ A # B # C ]
    -> ~ [ B # C # A ].
Proof.
  intros * BetABC BetACB.
  apply BetPs_sym in BetABC.
  apply BetPs_nBetPerPs in BetABC; contradiction.
Qed.
Lemma BetPs_nBetPerPs_2 :
  forall (A B C : Point),
  [ A # B # C ]
    -> ~ [ A # C # B ].
Proof.
  intros * BetABC BetACB;
  apply BetPs_sym in BetABC; apply BetPs_sym in BetACB;
  apply BetPs_nBetPerPs in BetABC; contradiction.
Qed.
Lemma BetPs_nBetPerPs_3 :
  forall (A B C : Point),
  [ A # B # C ]
    -> ~ [ C # A # B ].
Proof.
  intros * BetABC BetBAC.
  apply BetPs_nBetPerPs in BetABC.
  apply BetPs_sym in BetBAC.
  contradiction.
Qed.

Lemma BetPs_3DiPs :
  forall (A B C : Point),
  [ A # B # C ]
    -> A <> B /\ B <> C /\ A <> C.
Proof with eauto.
  intros * BetABC.
  assert (BetCBA : [C # B # A]). { apply (BetPs_sym A B C)... }
  assert(nBetBCA : ~ [B # C # A]). { apply (BetPs_nBetPerPs C B A)... }
  assert(nBetBAC : ~ [B # A # C]). { apply (BetPs_nBetPerPs A B C)... }
  repeat split; intro; subst...
  apply BetPs_DiPs in BetABC...
Qed.

Lemma BetPerPs_DiPs :
  forall (A B C : Point),
  [ A # B # C ] \/
  [ A # C # B ] \/
  [ B # A # C ] \/
  [ B # C # A ] \/
  [ C # A # B ] \/
  [ C # B # A ]
    -> A <> B.
Proof.
  intros * H;
  repeat destruct H;
  [ apply (BetPs_3DiPs A B C)
  | apply (BetPs_3DiPs A C B)
  | apply not_eq_sym; apply (BetPs_3DiPs B A C)
  | apply not_eq_sym; apply (BetPs_3DiPs B C A)
  | apply (BetPs_3DiPs C A B)
  | apply not_eq_sym; apply (BetPs_3DiPs C B A) ]; auto.
Qed.
Lemma BetPs_DiPs_1 :
  forall (A B C : Point),
  [ A # B # C ]
    -> (A <> B).
Proof.
  intros; eapply BetPerPs_DiPs; eauto.
Qed.
Lemma BetPs_DiPs_2 :
  forall (A B C : Point),
  [ B # C # A ]
    -> A <> B.
Proof.
  intros; eapply BetPerPs_DiPs; eauto.
Qed.
Lemma BetPs_DiPs_3 :
  forall (A B C : Point),
  [ C # A # B ]
    -> A <> B.
Proof.
  intros; eapply BetPerPs_DiPs; eauto 6.
Qed.
Lemma BetPs_DiPs_4 :
  forall (A B C : Point),
  [ B # A # C ]
    -> A <> B.
Proof.
  intros; eapply BetPerPs_DiPs; eauto.
Qed.
Lemma BetPs_DiPs_5 :
  forall (A B C : Point),
  [ A # C # B ]
    -> A <> B.
Proof.
  intros; eapply BetPerPs_DiPs; eauto.
Qed.
Lemma BetPs_DiPs_6 :
  forall (A B C : Point),
  [ C # B # A ]
    -> A <> B.
Proof.
  intros; eapply BetPerPs_DiPs; eauto 6.
Qed.

Example DrawLineThroughOrderedPoints :
  forall (A B C : Point),
  [ A # B # C ]
    -> { x : Line | [ A, B, C @ x ] }.
Proof with eauto.
  intros * BetABC.
  assert (nAeqC : A <> C). { eapply BetPs_DiPs_5... }
  destruct (DrawExtensionLinePP A C) as [ x [ Aox Cox ]]...
  exists x; repeat split; auto.
  eapply (ColPs_IncPt A C B)...
  apply BetPs_ColPs in BetABC...
Defined.

Lemma BetPs_IncPt :
  forall (A B C : Point)(x : Line),
  [ A # B # C ] \/
  [ A # C # B ] \/
  [ B # A # C ] \/
  [ B # C # A ] \/
  [ C # A # B ] \/
  [ C # B # A ]
    -> [ A, B @ x ]
    -> [ C @ x ].
Proof with inc.
  intros * H [ Aox Box ].
  assert (nAeqB : A <> B). { eapply BetPerPs_DiPs... }
  assert (ColABC : [ A, B, C ]).
  { repeat destruct H as [ H | H ];
    eapply BetPs_ColPs in H...
  }
  eapply ColPs_IncPt...
Qed.
Lemma BetPs_IncPt_1 :
  forall (A B C : Point)(x : Line),
  [ A # B # C ]
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ C @ x ].
Proof.
  intros; eapply BetPs_IncPt; eauto.
Qed.
Lemma BetPs_IncPt_2 :
  forall (A B C : Point)(x : Line),
  [ B # C # A ]
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ C @ x ].
Proof.
  intros; eapply BetPs_IncPt; eauto.
Qed.
Lemma BetPs_IncPt_3 :
  forall (A B C : Point)(x : Line),
  [ C # A # B ]
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ C @ x ].
Proof.
  intros; eapply BetPs_IncPt; eauto 6.
Qed.
Lemma BetPs_IncPt_4 :
  forall (A B C : Point)(x : Line),
  [ B # A # C ]
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ C @ x ].
Proof.
  intros; eapply BetPs_IncPt; eauto.
Qed.
Lemma BetPs_IncPt_5 :
  forall (A B C : Point)(x : Line),
  [ A # C # B ]
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ C @ x ].
Proof.
  intros; eapply BetPs_IncPt; eauto.
Qed.
Lemma BetPs_IncPt_6 :
  forall (A B C : Point)(x : Line),
  [ C # B # A ]
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ C @ x ].
Proof.
  intros; eapply BetPs_IncPt; eauto 6.
Qed.

Lemma BetPs_ColPs_1 :
  forall (A B C : Point),
  [ A # C # B ]
    -> [ A, B, C ].
Proof.
  intros * H.
  apply BetPs_ColPs in H; colperps.
Qed.
Lemma BetPs_ColPs_2 :
  forall (A B C : Point),
  [ B # A # C ]
    -> [ A, B, C ].
Proof.
  intros * H.
  apply BetPs_ColPs in H; colperps.
Qed.
Lemma BetPs_ColPs_3 :
  forall (A B C : Point),
  [ B # C # A ]
    -> [ A, B, C ].
Proof.
  intros * H.
  apply BetPs_ColPs in H; colperps.
Qed.
Lemma BetPs_ColPs_4 :
  forall (A B C : Point),
  [ C # A # B ]
    -> [ A, B, C ].
Proof.
  intros * H.
  apply BetPs_ColPs in H; colperps.
Qed.
Lemma BetPs_ColPs_5 :
  forall (A B C : Point),
  [ C # B # A ]
    -> [ A, B, C ].
Proof.
  intros * H.
  apply BetPs_ColPs in H; colperps.
Qed.

(** Theorem #4 *)
(* The relation SameSide is equivalence relation, i.e. it is
 reflexive, symmetric and transitive. *)
Theorem SS_refl :
  forall (A : Point)(x : Line),
  ~ [ A @ x ]
    -> [ x | A, A ].
Proof.
  intros * nAox; repeat split; auto; intros [ B [ Box BetABA ]].
  destruct (BetPs_3DiPs A B A BetABA) as [ _ [ _ nAeqA ]]; auto.
Qed.
Theorem SS_sym :
  forall (A B : Point)(x : Line),
  [ x | A, B ]
    -> [ x | B, A ].
Proof.
  intros * [ nAox [ nBox SSxAB ]];
  repeat split; auto; contradict SSxAB;
  destruct SSxAB as [ C [ Cox BetBCA ]];
  apply (BetPs_sym B C A) in BetBCA;
  exists C; auto.
Qed.
Theorem SS_trans :
  forall (A B C : Point)(x : Line),
  [ x | A, B ]
    -> [ x | B, C ]
    -> [ x | A, C ].
Proof with eauto.
  intros * [ nAox [ nBox SSxAB ]][ _ [ nCox SSxBC ]]; repeat split...
  intros nSSxAC.
  destruct (DecideTwoSides A B C x) as [[ _ [ _ H ]]|[ _ [ _ H ]]];
  repeat split...
Qed.

Lemma SH_DiPs_1 :
  forall O A B C : Point,
  [ O # A | B, C ]
    -> O <> A.
Proof with eauto.
  intros * [ nOeqA [ x [ Oox [ Aox SSxBC ]]]]...
Qed.
Lemma SH_DiPs_2 :
  forall O A B C : Point,
  [ O # A | B, C ]
    -> O <> B.
Proof with eauto.
  intros * [ nOeqA [ x [ Oox [ Aox [ H1 SSxBC ]]]]] OeqB.
  subst. contradiction.
Qed.
Lemma SH_DiPs_3 :
  forall O A B C : Point,
  [ O # A | B, C ]
    -> O <> C.
Proof with eauto.
  intros * [ nOeqA [ x [ Oox [ Aox [ H1 [ H2 SSxBC ]]]]]] OeqB.
  subst. contradiction.
Qed.
Lemma SH_DiPs_4 :
  forall O A B C : Point,
  [ O # A | B, C ]
    -> A <> B.
Proof with eauto.
  intros * [ nOeqA [ x [ Oox [ Aox [ H1 [ H2 SSxBC ]]]]]] OeqB.
  subst. contradiction.
Qed.
Lemma SH_DiPs_5 :
  forall O A B C : Point,
  [ O # A | B, C ]
    -> A <> C.
Proof with eauto.
  intros * [ nOeqA [ x [ Oox [ Aox [ H1 [ H2 SSxBC ]]]]]] OeqB.
  subst. contradiction.
Qed.

Lemma SH_nColPs :
  forall A B C D : Point,
  [ A # B | C, D ]
    -> ~ [ A, B, C ].
Proof.
  intros * [ nBeqA [ x [ Aox [ Box [ nCox _ ]]]]]; ncolps.
Qed.

Lemma SH_refl :
  forall O A B : Point,
  ~ [ A, O, B ]
    -> [ O # A | B, B ].
Proof with dips.
  intros * nColAOB.
  assert (nOeqA : O <> A). { apply not_eq_sym... }
  destruct (DrawExtensionLinePP O A) as [ x [ Oox Aox ]]...
  split; auto.
  exists x. split; try split; auto. apply SS_refl.
  contradict nColAOB. exists x...
Qed.
Lemma SHa_sym :
  forall O A B C : Point,
  [ O # A | B, C ]
    -> [ A # O | B, C ].
Proof.
  intros * [ nOeqA [ x [ Oox [ Aox SSxBC ]]]]; split; dips.
Qed.
Lemma SHb_sym :
  forall O A B C : Point,
  [ O # A | B, C ]
    -> [ O # A | C, B ].
Proof.
  intros * [ nOeqA [ x [ Oox [ Aox SSxBC ]]]].
  apply (SS_sym B C x) in SSxBC; split; dips.
Qed.
Lemma SH_trans :
  forall O A B C D : Point,
  [ O # A | B, C ]
    -> [ O # A | C, D ]
    -> [ O # A | B, D ].
Proof with inc.
  intros * [ nOeqA [ x [ Oox [ Aox SSxBC ]]]].
  intros [ _ [ y [ Oou [ Aoy SSxCD ]]]].
  assert (xeqy : x = y)...
  subst y.
  split; eauto.
  exists x; split; try split; auto.
  eapply SS_trans...
Qed.

(** Theorem #5 *)
(* The relation OppositeSide is irreflexive and symmetric. *)
Theorem OS_irrefl :
  forall (A B : Point)(x : Line),
  [ A | x | B ]
    -> A <> B.
Proof.
  intros * OSxAB.
  destruct OSxAB as [ nAox [ nBox [ C [ Cox BetACB ]]]].
  apply (BetPs_DiPs A C B BetACB).
Qed.
Theorem OS_sym :
  forall (A B : Point)(x : Line),
  [ A | x | B ]
    -> [ B | x | A ].
Proof.
  intros * [ nAox [ nBox [ C [ Cox BetACB ]]]];
  repeat split; auto;
  apply (BetPs_sym A C B) in BetACB; exists C; auto.
Qed.

Lemma OH_DiPs_1 :
  forall A B C D : Point,
  [ C | A # B | D ]
    -> A <> B.
  intros * [ nCeqB [ x [ Aox [ Box [ nCox [ nDox [ O [ Oox COD ]]]]]]]] AeqB.
  subst. contradiction.
Qed.
Lemma OH_DiPs_2 :
  forall A B C D : Point,
  [ C | A # B | D ]
    -> C <> D.
Proof with eauto.
  intros * [ nCeqB [ x [ Aox [ Box [ nCox [ nDox [ O [ Oox COD ]]]]]]]] AeqB.
  subst. apply BetPs_DiPs in COD. contradiction.
Qed.
Lemma OH_DiPs_3 :
  forall A B C D : Point,
  [ C | A # B | D ]
    -> A <> C.
Proof with eauto.
  intros * [ nCeqB [ x [ Aox [ Box [ nCox [ nDox [ O [ Oox COD ]]]]]]]] AeqB.
  subst. contradiction.
Qed.
Lemma OH_DiPs_4 :
  forall A B C D : Point,
  [ C | A # B | D ]
    -> B <> D.
Proof with eauto.
  intros * [ nCeqB [ x [ Aox [ Box [ nCox [ nDox [ O [ Oox COD ]]]]]]]] AeqB.
  subst. contradiction.
Qed.
Lemma OH_DiPs_5 :
  forall A B C D : Point,
  [ C | A # B | D ]
    -> B <> C.
Proof with eauto.
  intros * [ nCeqB [ x [ Aox [ Box [ nCox [ nDox [ O [ Oox COD ]]]]]]]] AeqB.
  subst. contradiction.
Qed.
Lemma OH_DiPs_6 :
  forall A B C D : Point,
  [ C | A # B | D ]
    -> A <> D.
Proof with eauto.
  intros * [ nCeqB [ x [ Aox [ Box [ nCox [ nDox [ O [ Oox COD ]]]]]]]] AeqB.
  subst. contradiction.
Qed.

Lemma OH_nColPs :
  forall A B C D : Point,
  [ C | A # B | D ]
    -> ~ [ A, B, C ].
Proof.
  intros * [ nCeqB [ x [ Aox [ Box [ nCox _ ]]]]]; ncolps.
Qed.

Lemma OHa_sym :
  forall O A B C : Point,
  [ B | O # A | C ]
    -> [ B | A # O | C ].
Proof with eauto.
  intros * [ nOeqA [ x [ Oox [ Aox SSxBC ]]]].
  apply (OS_sym B C x) in SSxBC; split; dips.
  exists x; split; try split... apply OS_sym...
Qed.
Lemma OHb_sym :
  forall O A B C : Point,
  [ B | O # A | C ]
    -> [ C | O # A | B ].
Proof with eauto.
  intros * [ nOeqA [ x [ Oox [ Aox OSxBC ]]]]; split; dips.
  exists x; split; try split... apply OS_sym...
Qed.

End BETWEEN.

Hint Resolve
  BetPs_DiPs_1 BetPs_DiPs_2 BetPs_DiPs_3
  BetPs_DiPs_4 BetPs_DiPs_5 BetPs_DiPs_6
  BetPs_DiPs
  : DiPs.
Hint Resolve
  BetPs_IncPt_1 BetPs_IncPt_2 BetPs_IncPt_3
  BetPs_IncPt_4 BetPs_IncPt_5 BetPs_IncPt_6
  : IncPt.
Hint Resolve
  BetPs_ColPs BetPs_ColPs_1 BetPs_ColPs_2 BetPs_ColPs_3
  BetPs_ColPs_4 BetPs_ColPs_5
  : ColPs.

Hint Resolve
  BetPs_nBetPerPs BetPs_nBetPerPs_2
  BetPs_nBetPerPs_3 BetPs_nBetPerPs_1 BetPs_sym
  : BetPs.

Tactic Notation "betps"
  := try solve
  [ eauto with BetPs
  | intuition eauto with BetPs ].
Tactic Notation "betps" integer(n)
  := try solve
  [ eauto n with BetPs
  | intuition (auto n with BetPs) ].
Tactic Notation "betcolinc"
  := try solve
  [ congruence
  | eauto with
    DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs BetPs
  | intuition eauto with
    DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs BetPs ].
Tactic Notation "betcolinc" integer(n)
  := try solve
  [ congruence
  | eauto n with
    DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs BetPs
  | intuition (auto n with
    DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs BetPs) ].

(*****************************************************************************)
(* 4 *) Section HALFPLANE.
Context `{ cr : Circles }.
(*****************************************************************************)

Example DrawIntersectionOfLineAndSegment :
  forall (A B : Point)(x : Line),
  [ A | x | B ]
    -> { O : Point | [ O @ x ] /\ [ A # O # B ] }.
Proof with eauto.
  intros * OSxAB.
  assert (nAeqB : A <> B). { eapply OS_irrefl... }
  destruct (DrawExtensionLinePP A B) as [ y [ Aoy Boy ]]...
  assert (nxpary : x >< y).
  { split.
    { intros xeqy; subst; firstorder. }
    { destruct OSxAB as [ nAox [ nBox [ O [ Oox BetAOB ]]]].
      exists O; split; auto. eapply (ColPs_IncPt A B O); inc.
    }
  }
  destruct (DrawIntersectionPointLL x y) as [ O [ Oox Ooy ]]...
  exists O; split...
  destruct OSxAB as [ nAox [ nBox [ O' [ O'ox BetAOB ]]]].
  rewrite (DiLs_EqPs O O' x y); repeat split; dils...
  eapply BetPs_IncPt...
Defined.

Example DrawOppositePoint :
  forall (O A : Point),
  O <> A
    -> { B : Point | [ A -- O -- B ] }.
Proof with eauto.
  intros * nOeqA.
  destruct (DrawIntersectionPointLC O A A nOeqA) as [ B [ H1 H2 ]].
  exists B.
  split; auto.
  destruct H1 as [ H |[ H1 H3 ]]; subst...
  symmetry in H2. apply EqSgs_EqPs in H2. contradiction.
Defined.

(** Problem #9 *)
(* If two different points A and O are given, it is possible to construct
 a point B so that the point O lies between points A and B at equal distance
 from them. *)
Definition DrawSegmentExtension :
  forall (A B : Point),
  A <> B
    -> { C : Point | [ A # B # C ] }.
Proof with inc.
  intros * nAeqB.
  destruct (DrawIntersectionPointLC B A A) as [ C [ BetBAC H ]]...
  exists C.
  destruct BetBAC as [ H1 |[ H2 H3 ]]; subst...
  symmetry in H. apply EqSgs_EqPs in H; subst. contradiction.
Defined.

(** Problem #10 *)
(** Hilbert, Chapter 1 : Theorem 3. *)
(* For any two points A and C, there exists at least one point B
   on the line AC lying between A and C. *)
Definition DrawPointInsideSegment :
  forall (A C : Point),
  A <> C
    -> { B : Point | [ A # B # C ] }.
Proof with inc 4.
  intros A B nAeqB.
  destruct (DrawExtensionLinePP A B) as [ x [ Aox Box ]]...
  destruct (DrawPointApartLine x) as [ C nCox ].
  assert (nBeqC : B <> C). { apply (nIncPt_DiPs B C x)... }
  destruct (DrawOppositePoint C B) as [ D [ BetBCD _ ]]...
  destruct (DrawLineThroughOrderedPoints B C D) as [ y [ Boy [ Coy Doy ]]]...
  assert (nDeqA : D <> A).
  { contradict nCox; subst. eapply BetPs_IncPt... }
  destruct (DrawOppositePoint A D) as [ E [ BetDAE _ ]]...
  destruct (DrawLineThroughOrderedPoints D A E) as [ z [ Doz [ Aoz Eoz ]]]...
  assert (nCeqE : C <> E).
  { intros CeqE; subst E.
    assert (yeqz : y = z). { apply (DiPs_EqLs C D y z); dips; incpt. }
    subst z.
    assert (xeqy : x = y). { apply (DiPs_EqLs A B x y)... }
    subst y; contradiction.
  }
  destruct (DrawExtensionLinePP C E nCeqE) as [ t [ Cot Eot ]].
  assert (OStAB : [ A | t | B ]).
  { assert (nCeqD : C <> D). { apply (BetPs_3DiPs B C D BetBCD). }
    assert (nzeqy : z <> y).
    { assert (nAoy : ~ [ A @ y ]).
      { contradict nAeqB. eapply (DiLs_EqPs A B x y)... }
      apply (nIncPt_DiLs A z y Aoz nAoy).
    }
    assert (nteqz : t <> z).
    { assert (nCoz : ~ [ C @ z ]).
      { contradict nzeqy; apply (DiPs_EqLs C D z y nCeqD)... }
      apply (nIncPt_DiLs C t z Cot nCoz).
    }
    assert (OStBD : [ B | t | D ]).
    { assert (nEoy : ~ [ E @ y ]).
      { assert (nDeqE : D <> E). { apply (BetPs_3DiPs D A E BetDAE). }
        contradict nzeqy; apply (DiPs_EqLs D E z y nDeqE)...
      }
      assert (nteqy : t <> y). { apply (nIncPt_DiLs E t y Eot nEoy). }
      assert (nDot : ~ [ D @ t ]).
      { contradict nteqy; apply (DiPs_EqLs C D t y nCeqD)... }
      assert (nBot : ~ [ B @ t ]).
      { contradict nteqy; apply (DiPs_EqLs B C t y nBeqC)... }
      repeat split...
    }
    assert (nOStDA : ~ [ D | t | A ]).
    { intros [ _ [ _ [ F [ Fot BetAFD ]]]].
      assert (Foz : [ F @ z ]). { apply (BetPs_IncPt D A F z)... }
      destruct (classic (E = F)) as [ EeqF | nEeqF ].
      { subst; apply BetPs_nBetPerPs_2 in BetAFD; contradiction. }
      { contradict nEeqF; apply (DiLs_EqPs E F t z nteqz); firstorder. }
    }
    assert (nAot : ~ [ A @ t ]).
    { assert (nAeqE : A <> E). { apply (BetPs_3DiPs D A E BetDAE). }
      contradict nteqz; apply (DiPs_EqLs A E t z nAeqE); firstorder.
    }
    destruct (DecideTwoSides B A D t nAot OStBD)
      as [ OStBA |[ _ [ _ [ F [ Fot BetAFD ]]]]]. apply OS_sym...
    apply BetPs_sym in BetAFD. contradict nOStDA; repeat split...
  }
  destruct (DrawIntersectionOfLineAndSegment A B t OStAB)
    as [ O [ Oot BetAOB ]].
  exists O...
Defined.

Example DrawLineBetweenDistinctPoints :
  forall (A B : Point),
  A <> B
    -> { x : Line | [ A | x | B ] }.
Proof with inc 4.
  intros A B nAeqB.
  destruct (DrawExtensionLinePP A B) as [ t [ Aot Bot ]]...
  destruct (DrawPointInsideSegment A B nAeqB) as [ O AOB ].
  destruct (DrawPointApartLine t) as [ C nCot ].
  assert (nOeqC : O <> C). { apply (nIncPt_DiPs O C t)... }
  destruct (DrawExtensionLinePP O C nOeqC) as [ x [ Oox Cox ]]...
  exists x; repeat split.
  { intros Aox.
    assert (Box : [B @ x]). { apply (BetPs_IncPt A O B)... }
    assert (xeqt : x = t); eqls.
  }
  { intros Box.
    assert (Aox : [A @ x]). { apply (BetPs_IncPt B O A)... }
    assert (xeqt : x = t); eqls.
  }
  { exists O; repeat split... }
Defined.

(** Problem #11 *)
(** Hilbert, Chapter 1 : Theorem 4. *)
(* Among any three points A, B and C lying on a line, there exists
 exactly only one lying between the two other points. *)
Definition DecidePointsBetweenness :
  forall (A B C : Point),
  A <> B
    -> B <> C
    -> A <> C
    -> [ A, B, C ]
    -> { [ A # B # C ] } + { [ B # C # A ] } + { [ B # A # C ] }.
Proof with inc.
  intros * nAeqB nBeqC nAeqC ColABC.
  destruct (DrawExtensionLinePP A B) as [ x [ Aox Box ]]...
  assert (Cox : [ C @ x ]). { apply (ColPs_IncPt A B C x)... }
  destruct (DrawPointApartLine x) as [ O nOox].
  assert (nAeqO : A <> O); dips.
  assert (nBeqO : B <> O); dips.
  assert (nCeqO : C <> O); dips.
  destruct (DrawOppositePoint O B) as [ D [ BetBOD _ ]]...
  destruct (BetPs_3DiPs B O D) as [ _ [ nOeqD nBeqD ]]...
  destruct (DrawExtensionLinePP A O) as [ a [ Aoa Ooa ]]...
  destruct (DrawLineThroughOrderedPoints B O D)
    as [ b [ Bob [ Oob Dob ]]]...
  destruct (DrawExtensionLinePP C O) as [ c [ Coc Ooc ]]...
  assert (nDox : ~ [D @ x]). { contradict nOox... }
  assert (nxeqa : x <> a); dils.
  assert (nxeqb : x <> b); dils.
  assert (nxeqc : x <> c); dils.
  assert (nBoa : ~ [B @ a]). { contradict nxeqa; eqls. }
  assert (nCoa : ~ [C @ a]). { contradict nxeqa; eqls. }
  assert (nDoa : ~ [D @ a]). { contradict nBoa; incpt 2. }
  assert (nAob : ~ [A @ b]). { contradict nxeqb; eqls. }
  assert (nCob : ~ [C @ b]). { contradict nxeqb; eqls. }
  assert (nBoc : ~ [B @ c]). { contradict nxeqc; eqls. }
  assert (nAoc : ~ [A @ c]). { contradict nxeqc; eqls. }
  assert (nDoc : ~ [D @ c]). { contradict nBoc. incpt 2. }
  assert (naeqb : a <> b); dils.
  assert (nbeqc : b <> c); dils.
  assert (naeqc : a <> c); dils.
  assert (nColBDC : ~ [B, D, C]); ncolps.
  assert (nColBDA : ~ [B, D, A]); ncolps.
  assert (OSaBD : [ B | a | D ]). { repeat split... }
  assert (OScBD : [ B | c | D ]). { repeat split... }
  destruct (DecideTwoSides B C D a) as [ OSaBC | OSaDC ]...
  { right. destruct OSaBC as [ _ [ _ [ P [ Poa BetBPC ]]]];
    elim (DiLs_EqPs P A x a nxeqa); repeat split; incpt 2.
  }
  { apply OS_sym in OSaDC.
    destruct (DecideTwoSides B A D c) as [ OScBA | OScDA ]...
    { left; right. destruct OScBA as [ _ [ _ [ P [ Poc BetBPA ]]]];
      elim (DiLs_EqPs P C x c nxeqc); repeat split; incpt 2.
    }
    { apply OS_sym in OScDA. left; left.
      assert (OSaCD := OSaDC).
      destruct OSaDC as [ _ [ _ [ E [ Eoa BetDEC ]]]].
      destruct (BetPs_3DiPs D E C) as [ nDeqE [ nEeqC nDeqC ]]...
      assert (nEeqO : E <> O).
      { contradict nBeqC; subst. apply (DiLs_EqPs B C x b)... }
      assert (nEoc : ~ [E @ c]). { contradict nDoc; incpt 2. }
      assert (nEob : ~ [E @ b]). { contradict naeqb... }
      assert (nEox : ~ [E @ x]). { contradict nDox; incpt 2. }
      assert (nEeqA : E <> A). { contradict nEox; subst... }
      assert (OScAD := OScDA).
      destruct OScDA as [ _ [ _ [ F [ Foc BetDFA]]]].
      destruct (BetPs_3DiPs D F A) as [ nDeqF [ nFeqA nDeqA ]]...
      assert (nFeqO : F <> O).
      { contradict nAeqB; subst. apply (DiLs_EqPs A B x b)... }
      assert (nFoa : ~ [F @ a]). { contradict nDoa; incpt 2. }
      assert (nFob : ~ [F @ b]). { contradict nbeqc... }
      assert (nFox : ~ [F @ x]). { contradict Aox; incpt 4. }
      assert (nFeqC : F <> C); dips.
      destruct (DecideTwoSides D E A c) as [ OScDE | OScAE ]...
      { destruct OScDE as [ _ [ _ [ P [ Poc BetDPE ]]]].
        assert (P = C); subst.
        { destruct (DrawExtensionLinePP D E nDeqE) as [ t [ Dot Eot ]].
          apply (DiLs_EqPs P C t c); repeat split; auto.
          { intro; subst; contradiction. }
          { apply (ColPs_IncPt D E P t); colinc. }
          apply (ColPs_IncPt D E C t)...
        }
        apply BetPs_nBetPerPs_2 in BetDEC; contradiction.
      }
      { apply OS_sym in OScAE.
        assert (OSbEA : [ E | b | A ]).
        { destruct OScAE as [ _ [ _ [ P [ Pox BetAPE ]]]].
          assert (PeqO : P = O); subst.
          { apply (DiLs_EqPs P O a c naeqc); repeat split; incpt 2. }
          apply BetPs_sym in BetAPE.
          repeat split; auto.
          exists O; auto.
        }
        destruct (DecideTwoSides E C A b) as [ OSbEC | OSbAC ]...
        { destruct OSbEC as [ _ [ _ [ P [ Pob BetEPC]]]].
          assert (P = D); subst.
          { destruct (DrawExtensionLinePP E C nEeqC) as [ t [ Eot Cot ]].
            apply (DiLs_EqPs P D t b); repeat split; auto.
            { intro; subst; contradiction. }
            { apply (ColPs_IncPt E C P t); colinc. }
            apply (ColPs_IncPt E C D t); incpt.
          }
          apply BetPs_nBetPerPs in BetDEC; contradiction.
        }
        { apply OS_sym in OSbAC.
          destruct OSbAC as [ _ [ _ [ P [ Pob BetAPC ]]]].
          assert (P = B); subst; auto.
          apply (DiLs_EqPs P B x b); repeat split; auto.
          apply (ColPs_IncPt A C P x); colinc.
        }
      }
    }
  }
Defined.

Lemma ColPs_nBetPs_BetPs :
  forall (A B C : Point),
  A <> B
    -> B <> C
    -> A <> C
    -> [ A, B, C ]
    -> ~ [ B # C # A ]
    -> ~ [ B # A # C ]
    -> [ A # B # C ].
Proof.
  intros * nAeqB nBeqC nAeqC ColABC nBetACB nBetBAC.
  destruct (DecidePointsBetweenness A B C nAeqB nBeqC nAeqC ColABC)
    as [[ H1 | H2 ]| H3 ]; eauto; contradiction.
Qed.

Lemma PaschAuxiliary :
  forall (A B C : Point)(x : Line),
  ~ ([ A | x | B ] /\ [ B | x | C ] /\ [ A | x | C ]).
Proof with incpt 2.
  assert (PaschAuxiliary_nCol : forall (A B C : Point)(x : Line),
    ~ [ A, B, C ] -> ~ ([ A | x | B ] /\ [ B | x | C ] /\ [ A | x | C ])).
  { intros A B C x nColABC [ OSxAB [ OSxBC OSxAC ]];
    elim OSxBC; intros nBox [ nCox [ A' [ A'ox BetBA'C ]]];
    elim OSxAC; intros nAox [ _ [ B' [ B'ox BetAB'C ]]];
    elim OSxAB; intros _ [ _ [ C' [ C'ox BetAC'B ]]];
    destruct (BetPs_3DiPs B A' C BetBA'C) as [ nBeqA' [ nA'eqC nBeqC ]];
    destruct (BetPs_3DiPs A B' C BetAB'C) as [ nAeqB' [ nB'eqC nAeqC ]];
    destruct (BetPs_3DiPs A C' B BetAC'B) as [ nAeqC' [ nC'eqB nAeqB ]];
    destruct (DrawLineThroughOrderedPoints B A' C BetBA'C)
      as [ a [ Boa [ A'oa Coa ]]];
    destruct (DrawLineThroughOrderedPoints A B' C BetAB'C)
      as [ b [ Aob [ B'ob Cob ]]];
    destruct (DrawLineThroughOrderedPoints A C' B BetAC'B)
      as [ c [ Aoc [ C'oc Boc ]]].
    assert (naeqb : a <> b).
    { contradict nColABC; rewrite_all nColABC; exists b; auto. }
    assert (naeqc : a <> c).
    { contradict nColABC; rewrite_all nColABC; exists c; auto. }
    assert (nbeqc : b <> c).
    { contradict nColABC; rewrite_all nColABC; exists c; auto. }
    assert (nAoa : ~ [ A @ a ]). { contradict nColABC; exists a; auto. }
    assert (nBob : ~ [ B @ b ]). { contradict nColABC; exists b; auto. }
    assert (nCoc : ~ [ C @ c ]). { contradict nColABC; exists c; auto. }
    assert (nA'eqB' : A' <> B').
    { contradict naeqb; destruct naeqb;
      apply (DiPs_EqLs A' C a b nB'eqC); firstorder.
    }
    assert (nB'eqC' : B' <> C').
    { contradict nbeqc; destruct nbeqc;
      apply (DiPs_EqLs A B' b c nAeqC'); firstorder.
    }
    assert (nA'eqC' : A' <> C').
    { contradict naeqc; destruct naeqc;
      apply (DiPs_EqLs A' B a c nC'eqB); firstorder.
    }
    assert (ColA'B'C' : [A', B', C']). { exists x; auto. }
    destruct (DecidePointsBetweenness A' B' C')
      as [[ BetA'B'C' | BetB'C'A' ]| BetB'A'C' ]; auto.
    { assert (OSbA'C' : [A' | b | C']).
      { repeat split; auto.
        contradict naeqb; eqls. contradict nbeqc; eqls.
        exists B'; split; auto.
      }
      destruct (DecideTwoSides A' B C' b) as [ OSbA'B | OSbC'B ]; auto.
      { destruct OSbA'B as [ nA'ob [ _ [ Q [ Qob BetA'CB ]]]].
        assert (QeqC : Q = C ).
        { apply (DiLs_EqPs Q C a b naeqb); repeat split... }
        subst Q.
        apply BetPs_nBetPerPs_2 in BetBA'C.
        apply BetPs_sym in BetA'CB; contradiction.
      }
      { destruct OSbC'B as [ nC'ob [ _ [ Q [ Qob BetC'AB ]]]].
        assert (QeqA : Q = A ).
        { apply (DiLs_EqPs Q A b c nbeqc); repeat split... }
        subst Q.
        apply BetPs_nBetPerPs_3 in BetAC'B; contradiction.
      }
    }
    { assert (OScB'A' : [B' | c | A']).
      { repeat split. contradict nbeqc; eqls. contradict naeqc; eqls.
        exists C'; split...
      }
      destruct (DecideTwoSides B' C A' c) as [ OScB'C | OScA'C ]; auto.
      { destruct OScB'C as [ nB'oc [ _ [ Q [ Qoc BetB'AC ]]]].
        assert (QeqA : Q = A ).
        { apply (DiLs_EqPs Q A b c nbeqc); repeat split... }
        subst Q.
        apply BetPs_nBetPerPs in BetAB'C; contradiction.
      }
      { destruct OScA'C as [ nA'oc [ _ [ Q [ Qoc BetA'BC ]]]].
        assert (QeqB : Q = B ).
        { apply (DiLs_EqPs Q B a c naeqc); repeat split... }
        subst Q.
        apply BetPs_nBetPerPs_3 in BetBA'C; contradiction.
      }
    }
    { assert (OSaB'C' : [B' | a | C']).
      { repeat split; auto.
        { contradict naeqb; eqls. }
        { contradict naeqc; eqls. }
        { exists A'; split; auto. }
      }
      destruct (DecideTwoSides B' A C' a)
        as [ OSaB'A | OSaC'A ]; auto.
      { destruct OSaB'A as [ nB'oa [ _ [ Q [ Qoa BetB'CA ]]]].
        assert (QeqC : Q = C ).
        { apply (DiLs_EqPs Q C a b naeqb); repeat split... }
        subst Q.
        apply BetPs_nBetPerPs_2 in BetAB'C.
        apply BetPs_sym in BetB'CA; contradiction.
      }
      { destruct OSaC'A as [ nC'oa [ _ [ Q [ Qoa BetC'BA ]]]].
        assert (QeqB : Q = B ).
        { apply (DiLs_EqPs Q B a c naeqc); repeat split... }
        subst Q.
        apply BetPs_nBetPerPs_2 in BetAC'B; contradiction.
      }
    }
  }
  intros * [ OSxAB [ OSxBC OSxAC ]].
  elim OSxBC; intros nBox [ nCox [ D [ Dox BetBDC ]]];
  elim OSxAC; intros nAox [ _ [ B' [ B'ox BetAB'C ]]];
  elim OSxAB; intros _ [ _ [ C' [ C'ox BetAC'B ]]].
  destruct (BetPs_3DiPs B D C BetBDC) as [ nBeqD [ nDeqC _ ]];
  destruct (BetPs_3DiPs A B' C BetAB'C) as [ nAeqB' [ nB'eqC _ ]];
  destruct (BetPs_3DiPs A C' B BetAC'B) as [ nAeqC' [ nC'eqB _ ]].
  assert (nAeqB : A <> B).
  { destruct OSxAB as [ _ [ _ [ O [ Oox BetAOB ]]]].
    apply (BetPs_3DiPs A O B BetAOB).
  }
  assert (nBeqC : B <> C).
  { destruct OSxBC as [ _ [ _ [ O [ Oox BetBOC ]]]].
    apply (BetPs_3DiPs B O C BetBOC).
  }
  assert (nAeqC : A <> C).
  { destruct OSxAC as [ _ [ _ [ O [ Oox BetAOC ]]]].
    apply (BetPs_3DiPs A O C BetAOC).
  }
  destruct (classic ([A, B, C])) as [[ y [ Aoy [ Boy Coy ]]]| nColABC ];
  [ idtac | apply (PaschAuxiliary_nCol A B C x nColABC) ]; auto.
  assert (nxeqy : x <> y).
  { apply sym_not_eq. apply (nIncPt_DiLs B y x Boy nBox). }
  assert (Doy : [ D @ y ]).
  { apply BetPs_ColPs in BetBDC. apply (ColPs_IncPt B C D)... }
  assert (B'oy : [ B' @ y ]).
  { apply BetPs_ColPs in BetAB'C. apply (ColPs_IncPt A C B')... }
  assert (C'oy : [ C' @ y ]).
  { apply BetPs_ColPs in BetAC'B. apply (ColPs_IncPt A B C')... }
  assert (DeqB' : D = B').
  { apply (DiLs_EqPs D B' x y); firstorder. }
  subst B'.
  assert (DeqC' : D = C').
  { apply (DiLs_EqPs D C' x y); firstorder. }
  subst C'.
  clear B'ox C'ox B'oy C'oy.
  destruct (DrawDistinctPointOnLine D x Dox) as [ E [ nDeqE Eox ]].
  assert (nEoy : ~ [ E @ y ]).
  { contradict nxeqy; apply (DiPs_EqLs E D x y); firstorder. }
  assert (nEeqB : E <> B).
  { apply not_eq_sym. apply (nIncPt_DiPs B E y Boy nEoy). }
  destruct (DrawOppositePoint B E) as [ F [ BetEBF _ ]]; auto.
  destruct (BetPs_3DiPs E B F BetEBF) as [ _ [ nBeqF nEeqF ]].
  destruct (DrawExtensionLinePP E B nEeqB) as [ z [ Eoz Boz ]].
  assert (nzeqx : z <> x). { apply (nIncPt_DiLs B z x Boz nBox). }
  assert (Foz : [ F @ z ]). { apply (BetPs_IncPt E B F z); firstorder. }
  assert (nFox : ~ [ F @ x ]).
  { contradict nzeqx. apply (DiPs_EqLs E F z x nEeqF); firstorder. }
  assert (nzeqy : z <> y). { apply (nIncPt_DiLs E z y Eoz nEoy). }
  destruct (DecideTwoSides A F B x ) as [ OSxAF | OSxBF ]; auto.
  { destruct (DecideTwoSides B F C x ) as [ OSxBF | OSxCF ]; auto.
    { destruct OSxBF as [ _ [ _ [ Q [ Qox BetBQF ]]]].
      assert (QeqE : Q = E ).
      { apply (DiLs_EqPs Q E x z); repeat split... }
      subst Q.
      apply BetPs_nBetPerPs in BetEBF; contradiction.
    }
    { assert (nFoy : ~ [ F @ y ]).
      { contradict nzeqy; apply (DiPs_EqLs B F z y nBeqF); firstorder. }
      assert (nColACF : ~ [ A, C, F ]).
      { contradict nFoy. apply (ColPs_IncPt A C F y nAeqC)... }
      apply (PaschAuxiliary_nCol A C F x nColACF).
      apply OS_sym in OSxCF. split...
    }
  }
  { apply OS_sym in OSxBF.
    destruct OSxBF as [ _ [ _ [ Q [ Qox BetBQF ]]]].
    assert (QeqE : Q = E ).
    { apply (DiLs_EqPs Q E x z); repeat split... }
    subst Q.
    apply BetPs_nBetPerPs in BetEBF; contradiction.
  }
Qed.

(** Theorem #6 *)
(** Hilbert, Chapter 1 : Theorem 8. *)
(* Each line a separates the points of the plane which do not lie
 on the line, into two nonempty regions R and S called half planes
 which have the following properties:
 (i) for any two points A in the halfplane R and B in the halfplane S,
   the segment AB intersects line a;
 (ii) for any two points A and A' in the halfplane R,
   the segment AA' does not intersect the line a;
 (iii) for any two points B and B' in the half plane S,
   the segment BB' does not intersect the line a. *)
Theorem OOS_trans :
  forall (A B C : Point)(x : Line),
  [ A | x | B ]
    -> [ B | x | C ]
    -> [ x | A, C ].
Proof.
  intros * OSxAB OSxBC.
  elim (OSxAB); intros nAox [ nBox [ D [ Dox BetADB ]]];
  elim (OSxBC); intros _ [ nCox [ E [ Eox BetBEC ]]].
  assert (nOSxABC : ~ ([A | x | B] /\ [B | x | C] /\ [A | x | C])).
  { apply (PaschAuxiliary A B C x). }
  repeat split; auto; contradict nOSxABC.
  split; auto. split; auto.
  repeat split; nincpt.
Qed.
Theorem OSO_trans :
  forall (A B C : Point)(x : Line),
  [ A | x | B ]
    -> [ x | B, C ]
    -> [ A | x | C ].
Proof.
  intros * OSxAB SSxBC.
  assert (nAox : ~ [ A @ x ]). { firstorder. }
  assert (nCox : ~ [ C @ x ]). { firstorder. }
  destruct (classic ([ A | x | C])) as [ OSxAC | nOSxAC ]; auto.
  destruct (classic ([ x | A, C])) as [ SSxAC | nSSxAC ]; auto.
  { assert (nSSxBA : ~ [ x | B, A ]).
    { apply (OS_sym A B x) in OSxAB; firstorder. }
    assert (nSSxCA : ~ [ x | C, A ]).
    { contradict nSSxBA; apply (SS_trans B C A x SSxBC nSSxBA). }
    apply (SS_sym A C x) in SSxAC. contradiction.
  }
  { contradict nSSxAC. repeat split; auto.
    contradict nOSxAC. repeat split; auto.
  }
Qed.

Lemma OOH_trans :
  forall O A B C D : Point,
  [ B | O # A | C ]
    -> [ C | O # A | D ]
    -> [ O # A | B, D ].
Proof with inc.
  intros * [ nOeqA [ x [ Oox [ Aox OSxBC ]]]].
  intros [ _ [ y [ Oou [ Aoy OSxCD ]]]].
  assert (xeqy : x = y)...
  subst y. split; auto.
  exists x; split; auto.
  split; auto.
  eapply OOS_trans...
Qed.
Lemma OHO_trans :
  forall O A B C D : Point,
  [ B | O # A | C ]
    -> [ O # A | C, D ]
    -> [ B | O # A | D ].
Proof with eauto.
  intros * [ nOeqA [ x [ Oox [ Aox OSxBC ]]]].
  intros [ _ [ y [ Oou [ Aoy OSxCD ]]]].
  assert (xeqy : x = y); eqls.
  subst y.
  split...
  exists x; split...
  split...
  eapply OSO_trans...
Qed.

Example DecideSameSide :
  forall (A B : Point)(x : Line),
  ~ [ A @ x ]
    -> ~ [ B @ x ]
    -> { [ x | A, B ] } + { [ A | x | B ] }.
Proof with eauto.
  intros * nAox nBox.
  destruct (DrawPointOnLine x) as [ O Oox ].
  assert (nAeqO : A <> O). { contradict nAox. destruct nAox... }
  destruct (DrawOppositePoint O A) as [ C [ BetAOC _ ]]...
  assert (OSxAC : [ A | x | C ]).
  { repeat split...
    contradict nAox. apply BetPs_sym in BetAOC.
    apply (BetPs_IncPt C O A x); firstorder.
  }
  destruct (DecideTwoSides A B C x) as [ OSxAB | OSxCB ]...
  { left; apply (OOS_trans A C B x)... apply OS_sym... }
Defined.
Example PlaneSeparation :
  forall (A B P : Point)(x : Line),
  ~ [ P @ x ]
    -> [ A | x | B ]
    -> { [ A | x | P ] /\ [ x | B, P ] } + { [ x | A, P ] /\ [ B | x | P ] }.
Proof.
  intros * nPox OSxAB.
  assert (nAox : ~ [ A @ x ]). { firstorder. }
  destruct (DecideSameSide A P x nAox nPox) as [ SSxAP | OSxAP ].
  { assert (OSxBP : [ B | x | P ]).
    { apply (OS_sym A B x) in OSxAB;
      apply (OSO_trans B A P x OSxAB SSxAP).
    }
    right; auto.
  }
  { assert (SSxBP : [ x | B, P ]).
    { apply (OS_sym A B x) in OSxAB;
      apply (OOS_trans B A P x OSxAB OSxAP).
    }
    left; auto.
  }
Defined.

Example DecideSameHalfplane :
  forall A B C D : Point,
  ~ [ A, B, C ]
    -> ~ [ A, B, D ]
    -> { [ A # B | C, D ] } + { [ C | A # B | D ] }.
Proof with eauto.
  intros * nColABC nColABD.
  assert (nAeqB : A <> B); dips.
  destruct (DrawExtensionLinePP A B nAeqB) as [ x [ Aox Box ]].
  destruct (DecideSameSide C D x) as [ SSxCD | OSxCD ]; nincpt.
  { left; split... }
  { right; split... }
Defined.

Example DrawSameHalfplaneBorderLine :
  forall (O A B C : Point),
  [ O # A | B, C ]
    -> { x : Line | [ O @ x ] /\ [ A @ x ] /\ [ x | B, C ] }.
Proof.
  intros * OAsfBC.
  assert (nOeqA : O <> A). { firstorder. }
  destruct (DrawExtensionLinePP O A nOeqA) as [ x [ Oox Aox ]].
  assert (SSxBC : [ x | B, C ]).
  { destruct OAsfBC as [ _ [ x' [ Oox' [ Aox' SSxBC ]]]].
    assert (xeqx' : x = x').
    { apply (DiPs_EqLs O A x x' nOeqA); firstorder. }
    subst x'; auto.
  }
  exists x; auto.
Defined.
Example DrawOppositeHalfplaneBorderLine :
  forall (O A B C : Point),
  [ B | O # A | C ]
    -> { x : Line | [ O @ x ] /\ [ A @ x ] /\ [ B | x | C ] }.
Proof with eauto.
  intros * OAofBC.
  assert (nOeqA : O <> A). { firstorder. }
  destruct (DrawExtensionLinePP O A) as [ x [ Oox Aox ]]...
  assert (OSxBC : [ B | x | C ]).
  { destruct OAofBC as [ _ [ x' [ Oox' [ Aox' OSxBC ]]]].
    assert (xeqx' : x = x'); eqls.
  }
  exists x...
Defined.

Lemma OS_IncPs_ConvLs :
  forall (A B : Point)(x y : Line),
  [ A | x | B ]
    -> [ A, B @ y ]
    -> x >< y.
Proof with eauto.
  intros * OSxAB [ Aoy Boy ].
  assert (nAeqB : A <> B). { eapply OS_irrefl... }
  destruct OSxAB as [ nAox [ nBox [ O [ Oox BetAOB ]]]].
  assert (nxeqy : x <> y); dils.
  split...
  exists O; split; incpt 2.
Qed.

End HALFPLANE.

Hint Resolve
  OS_irrefl SH_DiPs_1 SH_DiPs_2 SH_DiPs_3 SH_DiPs_4 SH_DiPs_5
  OH_DiPs_1 OH_DiPs_2 OH_DiPs_3 OH_DiPs_4 OH_DiPs_5 OH_DiPs_6
  : DiPs.

Hint Resolve
  OH_nColPs SH_nColPs
  : nColPs.

Hint Resolve
  ColPs_nBetPs_BetPs
  : BetPs.

Hint Resolve
  OS_irrefl
  OS_sym SS_refl SS_sym SHa_sym SHb_sym
  OHa_sym OHb_sym
  : OrdPs.

Hint Resolve
  SS_trans OOS_trans OSO_trans
  : OrdPerPs.

Tactic Notation "ord"
  := try solve
  [ eauto with BetPs OrdPs
  | intuition eauto with BetPs OrdPs ].
Tactic Notation "eord" integer(n)
  := try solve
  [ eauto n with BetPs OrdPs
  | intuition (auto n with BetPs OrdPs) ].

Tactic Notation "ordper"
  := try solve
  [ eauto with BetPs OrdPs OrdPerPs
  | intuition eauto with BetPs OrdPs OrdPerPs ].
Tactic Notation "ordper" integer(n)
  := try solve
  [ eauto n with BetPs OrdPs OrdPerPs
  | intuition (auto n with BetPs OrdPs OrdPerPs) ].

Tactic Notation "geo"
  := try solve
  [ congruence
  | eauto with
    DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs BetPs OrdPs
  | intuition eauto with
    DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs BetPs OrdPs ].
Tactic Notation "geo" integer(n)
  := try solve
  [ congruence
  | eauto n with
    DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs BetPs OrdPs
  | intuition (auto n with
    DiPs DiLs EqPs EqLs IncPt nIncPt ColPs nColPs BetPs OrdPs) ].

(*****************************************************************************)
(* 5 *) Section HALFLINE.
Context `{ cr : Circles }.
(*****************************************************************************)

Lemma SR_DiPs_1 :
  forall (O A B : Point),
  [ O # A, B ]
    -> O <> A.
Proof.
  intros; firstorder.
Qed.
Lemma SR_DiPs_2 :
  forall (O A B : Point),
  [ O # A, B ]
    -> O <> B.
Proof.
  intros; firstorder.
Qed.
Lemma SR_ColPs :
  forall (O A B : Point),
  [ O # A, B ]
    -> [ A, O, B ].
Proof with eauto.
  intros * [ OxA [ OxB [[ y [ Aoy [ Ooy Boy ]]] nBetAOB ]]].
  exists y...
Qed.
Lemma SR_IncPt_1 :
  forall (A B C : Point)(x : Line),
  [ A # B, C ]
    -> [ A @ x ]
    -> [ B @ x ]
    -> [ C @ x ].
Proof with inc.
  intros * [ nBeqA [ nCeqA [[ y [ Aoy [ Boy Coy ]]] nBet ]]] Aox Box.
  assert (xeqy : x = y); subst...
Qed.
Lemma SR_IncPt_2 :
  forall (A B C : Point)(x : Line),
  [ A # B, C ]
    -> [ A @ x ]
    -> [ C @ x ]
    -> [ B @ x ].
Proof with inc.
  intros * [ nBeqA [ nCeqA [[ y [ Aoy [ Boy Coy ]]] nBet ]]] Aox Cox.
  assert (xeqy : x = y); subst...
Qed.

Lemma nColPs_SR_inv :
  forall O A B A' B' : Point,
  ~ [ A, O, B ]
    -> [ O # A, A' ]
    -> [ O # B, B' ]
    -> ~ [ A', O, B' ].
Proof.
  intros * nColAOB OsrAA' OsrBB'.
  contradict nColAOB.
  destruct OsrAA' as [ nOeqA [ nOeqA' [ ColOAA' _ ]]].
  destruct OsrBB' as [ nOeqB [ nOeqB' [ ColOBB' _ ]]].
  destruct nColAOB as [ x [ A'ox [ Oox B'ox ]]].
  exists x; repeat split; incpt 6.
Qed.

Lemma nColPs_BetPs_inv :
  forall O A B A' B' : Point,
  ~ [ A, O, B ]
    -> [ A # O # A' ]
    -> [ B # O # B' ]
    -> ~ [ A', O, B' ].
Proof.
  intros * nColAOB AOA' BOB'.
  destruct (nColPs_3DiPs A O B nColAOB) as [ nOeqA [ nOeqB nAeqB ]].
  contradict nColAOB.
  destruct nColAOB as [ x [ A'ox [ Oox B'ox ]]].
  exists x; repeat split; eauto.
  { apply (BetPs_IncPt A' O A); inc. }
  { apply (BetPs_IncPt_1 B' O B); inc. apply BetPs_sym; eauto. }
Qed.

Example DrawLineThroughPointsOnRay :
  forall (A B C : Point),
  [ A # B, C ]
    -> { x : Line | [ A, B, C @ x ] }.
Proof with eauto.
  intros * SR.
  assert (nAeqC : A <> C). { eapply SR_DiPs_2... }
  destruct (DrawExtensionLinePP A C) as [ x [ Aox Cox ]]...
  exists x; repeat split; auto.
  eapply (ColPs_IncPt A C B)...
  apply SR_ColPs in SR.
  firstorder.
Defined.

(** Theorem #7 *)
Theorem SR_SS :
  forall (O A P : Point)(x : Line),
  [ O @ x ]
    -> ~ [ A @ x ]
    -> [ O # A, P ]
    -> [ x | A, P ].
Proof with inc.
  intros * Oox nAox O_AP.
  destruct O_AP as [ nAeqO [ nPeqO [[ y [ Ooy [ Aoy Poy ]]] nBetAOP ]]].
  repeat split; auto.
  { contradict nAox... }
  { contradict nBetAOP.
    destruct nBetAOP as [ O' [ O'ox BetAO'P ]].
    erewrite (DiLs_EqPs O O' x y); dils...
  }
Qed.
Theorem OR_OS :
  forall (O A P : Point)(x : Line),
  [ O @ x ]
    -> ~ [ A @ x ]
    -> [ A # O # P ]
    -> [ A | x | P ].
Proof with inc.
  intros * Oox nAox BetAOP.
  repeat split...
Qed.
(** Theorem #8 *)
Theorem SS_SR :
  forall (O A P : Point)(x : Line),
  [ O @ x ]
    -> [ O, A, P ]
    -> [ x | A, P ]
    -> [ O # A, P ].
Proof with inc.
  intros * Oox [ y [ Ooy [ Aoy Poy ]]][ nAox [ nPox SSxAP ]].
  repeat split.
  { intros AeqO; subst; contradiction. }
  { intros PeqO; subst; contradiction. }
  { exists y; auto. }
  { contradict SSxAP. exists O; auto. }
Qed.
Theorem OS_OR :
  forall (O A P : Point)(x : Line),
  [ O @ x ]
    -> [ O, A, P ]
    -> [ A | x | P ]
    -> [ A # O # P ].
Proof with inc.
  intros * Oox ColOAP [ nAox [ nPox [ O' [ O'ox BetAOP ]]]].
  destruct ColOAP as [ y [ Ooy [ Aoy Poy ]]].
  assert (OeqO' : O = O'). { apply (DiLs_EqPs O O' x y)... }
  subst...
Qed.

Lemma SR_SH :
  forall (A B C D : Point),
  ~ [ A, B, C ]
    -> [ A # C, D ]
    -> [ A # B | C, D ].
Proof with inc 2.
  intros * nColABC AsrCD.
  assert (nAeqB : A <> B); dips.
  destruct (DrawExtensionLinePP A B nAeqB) as [ x [ Aox Box ]].
  split; eauto.
  exists x; split; eauto.
  split; eauto.
  apply (SR_SS A C D x)...
Qed.
Lemma SH_SR :
  forall (A B C D : Point),
  [ A # B | C, D ]
    -> [ A, C, D ]
    -> [ A # C, D ].
Proof.
  intros * ABsfCD ColACD.
  destruct ABsfCD as [ nBeqA [ x [ Aox [ Box SSxCD ]]]].
  apply (SS_SR A C D x); auto.
Qed.

Lemma SHa_inv :
  forall O A B C A' B' C' : Point,
  O <> A'
   -> [ O, A, A' ]
   -> [ O # B, B' ]
   -> [ O # C, C' ]
   -> [ O # A | B, C ]
   -> [ O # A' | B', C' ].
Proof with inc.
  intros * nOeqA' [ x [ Oox [ Aox A'ox ]]] OsrBB' OsrCC' SH;
  split; eauto.
  exists x; split; eauto.
  split; eauto.
  destruct SH as [ nOeqA [ y [ Ooy [ Aoy SSxBC ]]]].
  assert (xeqy : x = y)...
  subst y.
  assert (SSxBB' : [ x | B, B' ]). { apply (SR_SS O B B' x Oox); firstorder. }
  assert (SSxCC' : [ x | C, C' ]). { apply (SR_SS O C C' x Oox); firstorder. }
  eapply (SS_trans B C C' x) in SSxBC...
  eapply (SS_trans B' B C' x)...
  eapply SS_sym...
Qed.
Lemma SHb_inv :
  forall O A B C A' B' C' : Point,
  O <> A'
    -> [ O, A, A' ]
    -> [ B # O # B' ]
    -> [ C # O # C' ]
    -> [ O # A | B, C ]
    -> [ O # A' | B', C' ].
Proof with inc.
  intros * nOeqA' [ x [ Oox [ Aox A'ox ]]] BOB' COC' SH;
  split; eauto.
  exists x; split; eauto.
  split; eauto.
  destruct SH as [ nOeqA [ y [ Ooy [ Aoy SSxBC ]]]].
  assert (xeqy : x = y)...
  subst y.
  assert (OSxBB' : [ B | x | B' ]). { apply (OR_OS O B B' x Oox); firstorder. }
  assert (OSxCC' : [ C | x | C' ]). { apply (OR_OS O C C' x Oox); firstorder. }
  eapply OS_sym in OSxBB'...
  eapply (OSO_trans B' B C x) in OSxBB'...
  eapply OS_sym in OSxBB'...
  eapply (OOS_trans B' C C' x)...
  eapply OS_sym...
Qed.
Lemma SHc_inv :
  forall O A B C A' B' C' : Point,
  O <> A'
    -> [ O, A, A' ]
    -> [ O # B, B' ]
    -> [ C # O # C' ]
    -> [ O # A | B, C ]
    -> [ B' | O # A' | C' ].
Proof with inc.
  intros * nOeqA' [ x [ Oox [ Aox A'ox ]]] OsrBB' COC' SH;
  split; eauto.
  exists x; split; eauto.
  split; eauto.
  destruct SH as [ nOeqA [ y [ Ooy [ Aoy SSxBC ]]]].
  assert (xeqy : x = y)...
  subst y.
  assert (SSxBB' : [ x | B, B' ]). { apply (SR_SS O B B' x Oox); firstorder. }
  assert (OSxCC' : [ C | x | C' ]). { apply (OR_OS O C C' x Oox); firstorder. }
  eapply OS_sym...
  eapply OS_sym in OSxCC'...
  eapply (OSO_trans C' C B' x)...
  eapply (SS_trans C B B' x)...
  eapply SS_sym...
Qed.
Lemma OHa_inv :
  forall O A B C A' B' C' : Point,
  O <> A'
    -> [ O, A, A' ]
    -> [ O # B, B' ]
    -> [ O # C, C' ]
    -> [ B | O # A | C ]
    -> [ B' | O # A' | C' ].
Proof with inc.
  intros * nOeqA' [ x [ Oox [ Aox A'ox ]]] OsrBB' OsrCC' OH;
  split; eauto.
  exists x; split; eauto.
  split; eauto.
  destruct OH as [ nOeqA [ y [ Ooy [ Aoy OSxBC ]]]].
  assert (xeqy : x = y)...
  subst y.
  assert (SSxBB' : [ x | B, B' ]). { apply (SR_SS O B B' x Oox); firstorder. }
  assert (SSxCC' : [ x | C, C' ]). { apply (SR_SS O C C' x Oox); firstorder. }
  apply (OSO_trans B C C' x) in OSxBC...
  eapply OS_sym...
  apply (OSO_trans C' B B' x)...
  eapply OS_sym...
Qed.
Lemma OHb_inv :
  forall O A B C A' B' C' : Point,
  O <> A'
    -> [ O, A, A' ]
    -> [ B # O # B' ]
    -> [ C # O # C' ]
    -> [ B | O # A | C ]
    -> [ B' | O # A' | C' ].
Proof with inc.
  intros * nOeqA' [ x [ Oox [ Aox A'ox ]]] BOB' COC' OH;
  split; eauto.
  exists x; split; eauto.
  split; eauto.
  destruct OH as [ nOeqA [ y [ Ooy [ Aoy OSxBC ]]]].
  assert (xeqy : x = y)...
  subst y.
  assert (OSxBB' : [ B | x | B' ]). { apply (OR_OS O B B' x Oox); firstorder. }
  assert (OSxCC' : [ C | x | C' ]). { apply (OR_OS O C C' x Oox); firstorder. }
  eapply OS_sym in OSxBC...
  eapply (OOS_trans C B B' x) in OSxBB'...
  eapply OS_sym...
  eapply OS_sym in OSxCC'...
  eapply (OSO_trans C' C B' x)...
Qed.
Lemma OHc_inv :
  forall O A B C A' B' C' : Point,
  O <> A'
    -> [ O, A, A' ]
    -> [ O # B, B' ]
    -> [ C # O # C' ]
    -> [ B | O # A | C ]
    -> [ O # A' | B', C' ].
Proof with inc.
  intros * nOeqA' [ x [ Oox [ Aox A'ox ]]] OsrBB' COC' OH; split; eauto.
  exists x; split; eauto.
  split; eauto.
  destruct OH as [ nOeqA [ y [ Ooy [ Aoy OSxBC ]]]].
  assert (xeqy : x = y)...
  subst y.
  assert (SSxBB' : [ x | B, B' ]). { apply (SR_SS O B B' x Oox); firstorder. }
  assert (OSxCC' : [ C | x | C' ]). { apply (OR_OS O C C' x Oox); firstorder. }
  eapply OS_sym in OSxBC...
  eapply (OOS_trans B' C C' x)...
  eapply OS_sym...
  eapply (OSO_trans C B B' x)...
Qed.

(** Theorem #9 *)
(* The relation SameRay is equivalence relation, i.e. it is
 reflexive, symmetric and transitive. *)
Theorem SR_refl :
  forall O A : Point,
  O <> A
    -> [ O # A, A ].
Proof.
  intros * nOeqA;
  destruct (DrawExtensionLinePP O A nOeqA) as [ x [ Oox Aox ]].
  repeat split; try (exists x); auto; intros BetAOA;
  apply (BetPs_3DiPs A O A) in BetAOA; tauto.
Qed.
Theorem SR_sym :
  forall O A B : Point,
  [ O # A, B ]
    -> [ O # B, A ].
Proof.
  intros * [ nAeqO [ nBeqO [[ x [ Oox [ Aox Box ]]] nBetAOB ]]].
  repeat split; try (exists x); auto; contradict nBetAOB;
  apply (BetPs_sym B O A) in nBetAOB; auto.
Qed.
Theorem SR_trans :
  forall O A B C : Point,
  [ O # A, B ]
    -> [ O # B, C ]
    -> [ O # A, C ].
Proof with inc.
  intros O A B C OsrAB OsrBC.
  elim OsrAB; intros nAeqO [ nBeqO [[ x [ Oox [ Aox Box ]]] _ ]].
  elim OsrBC; intros _ [ nCeqO [[ x' [ Oox' [ Box' Cox ]]] _ ]].
  assert (xeqx' : x = x')...
  subst x'.
  destruct (DrawPointApartLine x) as [ E nEox ].
  assert (nOeqE : O <> E).
  { contradict nEox; rewrite <- nEox; auto. }
  destruct (DrawExtensionLinePP O E nOeqE) as [ y [ Ooy Eoy ]].
  assert (nxeqy : x <> y).
  { contradict nEox; rewrite <- nEox in Eoy; auto. }
  assert (nAoy : ~ [ A @ y ]).
  { contradict nxeqy; apply (DiPs_EqLs A O x y)... }
  assert (nBoy : ~ [ B @ y ]).
  { contradict nxeqy; apply (DiPs_EqLs B O x y)... }
  assert (ColOAC : [ O, A, C ]). { exists x... }
  assert (SSyAB : [ y | A, B ]). { apply (SR_SS O A B y)... }
  assert (SSyBC : [ y | B, C ]). { apply (SR_SS O B C y)... }
  assert (SSyAC : [ y | A, C ]). { apply (SS_trans A B C y)... }
  apply (SS_SR O A C y)...
Qed.

(** Theorem #10 *)
(* The relation SameRay can be defined through the relation Between. *)
Theorem SR_BetPs :
  forall (O A B : Point),
  [ O # A, B ]
    <-> [ O # A # B ] \/ (A = B /\ A <> O) \/ [ O # B # A ].
Proof with inc.
  intros.
  split.
  { intros OsrAB.
    destruct OsrAB as [ nAeqO [ nBeqO [ ColOAB nBetAOB ]]].
    destruct (classic (A = B)) as [ AeqB | nAeqB ]; dips.
    destruct (DecidePointsBetweenness A O B) as [[ Bet | Bet ]| Bet ]...
  }
  { intros [ BetOAB |[ AeqB | BetOBA ]].
    { repeat split; dips; colper; betps. }
    { destruct AeqB as [ AeqB nAeqO ].
      subst B; repeat split; colps.
      contradict nAeqO; apply BetPs_3DiPs in nAeqO; tauto.
    }
    { repeat split; dips; colps; betps. }
  }
Qed.

(** Theorem #11 *)
(* The relation Between can be defined through relation SameRay. *)
Theorem BetPs_SR :
  forall A B C : Point,
  [ A # B # C ]
    <-> [ A # B, C ] /\ [ C # B, A ].
Proof with inc.
  assert (BetPs_SR : forall A B C : Point, [ A # B # C ] -> [ A # B, C ]).
  { intros * BetABC.
    destruct (BetPs_3DiPs A B C BetABC) as [ nAeqB [ _ nAeqC ]].
    assert (ColABC : [ A, B, C ]). { apply (BetPs_ColPs A B C)... }
    assert (nBetBAC : ~ [ B # A # C ]). { apply (BetPs_nBetPerPs A B C)... }
    repeat split; ord; colps.
  }
  split.
  { intros BetABC.
    split.
    { apply (BetPs_SR A B C BetABC). }
    { apply BetPs_sym in BetABC; apply (BetPs_SR C B A BetABC). }
  }
  { intros [ AsrBC CsrBA ].
    destruct AsrBC as [ nBeqA [ nCeqA [ ColABC nBetBAC ]]].
    destruct CsrBA as [ nBeqC [ _ [ _ nBetBCA ]]].
    destruct (DecidePointsBetweenness A B C) as [[ BetABC | BetBCA ]| BetBAC ];
    dips; colperps.
  }
Qed.
Lemma BetPs_SR_1 :
  forall A B C : Point,
  [ A # B # C ]
    -> [ A # B, C ].
Proof.
  intros; apply -> (BetPs_SR A B C); auto.
Qed.
Lemma BetPs_SR_2 :
  forall A B C : Point,
  [ A # B # C ]
    -> [ C # B, A ].
Proof.
  intros; apply -> (BetPs_SR A B C); auto.
Qed.
Lemma SR_SR_BetPs :
  forall A B C : Point,
  [ A # B, C ]
    -> [ C # B, A ]
    -> [ A # B # C ].
Proof.
  intros; apply <- BetPs_SR; auto.
Qed.

Example DecidePointsOnSameRay :
  forall (O A B : Point),
  A <> O
    -> B <> O
    -> [ O, A, B ]
    -> { [ O # A, B ] } + { [ A # O # B ] }.
Proof with inc.
  intros * nAeqO nBeqO ColOAB.
  destruct (DrawExtensionLinePP A O) as [ x [ Aox Oox ]]...
  destruct (DrawPointApartLine x) as [ C nCox ].
  assert (nCeqO : C <> O). { contradict nCox; subst... }
  destruct (DrawExtensionLinePP C O) as [ y [ Coy Ooy ]]...
  assert (Box : [ B @ x ]). { apply (ColPs_IncPt O A B x)... }
  assert (nAoy : ~ [ A @ y ]).
  { contradict nCox.
    assert (xeqy : x = y). { apply (DiPs_EqLs A O x y)... }
    subst...
  }
  assert (nBoy : ~ [ B @ y ]).
  { contradict nCox.
    assert (xeqy : x = y). { apply (DiPs_EqLs B O x y)... }
    subst...
  }
  destruct (DecideSameSide A B y) as [ SSyAB | OSyAB ]...
  { left; apply (SS_SR O A B y)... }
  { right; apply (OS_OR O A B y)... }
Defined.

(** Theorem #12 *)
(* The relation Between is co-transitive. *)
Theorem BetPs_BetPs_SR :
  forall O A B C : Point,
  [ A # O # B ]
    -> [ A # O # C ]
    -> [ O # B, C ].
Proof with inc.
  intros * BetAOB BetAOC.
  destruct (BetPs_3DiPs A O B) as [ nAeqO [nOeqB nAeqB ]]...
  destruct (BetPs_3DiPs A O C) as [ _ [nOeqC nAeqC ]]...
  destruct (DrawLineThroughOrderedPoints A O B)
    as [ x [ Aox [ Oox Box ]]]...
  destruct (DrawLineThroughOrderedPoints A O C)
    as [ x' [ Aox' [ Oox' Cox ]]]...
  assert (xeqx' : x = x').
  { apply (DiPs_EqLs A O x x' nAeqO)... }
  subst x'.
  destruct (DrawPointApartLine x) as [ E nEox ].
  assert (nOeqE : O <> E). { contradict nEox; rewrite <- nEox... }
  destruct (DrawExtensionLinePP O E nOeqE) as [ y [ Ooy Eoy ]].
  assert (nxeqy : x <> y). { contradict nEox; rewrite <- nEox in Eoy... }
  assert (nAoy : ~ [ A @ y ]).
  { contradict nxeqy; apply (DiPs_EqLs A O x y)... }
  assert (nBoy : ~ [ B @ y ]).
  { contradict nxeqy; apply (DiPs_EqLs B O x y)... }
  assert (nCoy : ~ [ C @ y ]).
  { contradict nxeqy; apply (DiPs_EqLs C O x y)... }
  assert (OSyAB : [ A | y | B ]). { repeat split; auto. exists O; split... }
  assert (OSyAC : [ A | y | C ]). { repeat split; auto. exists O; split... }
  assert (SSyBC : [ y | B, C ]).
  { apply OS_sym in OSyAB. apply (OOS_trans B A C y)... }
  apply (SS_SR O B C y Ooy); auto.
  exists x...
Qed.
Theorem BetPs_SR_BetPs :
  forall O A B C : Point,
  [ A # O # B ]
    -> [ O # B, C ]
    -> [ A # O # C ].
Proof with inc.
  intros * BetAOB OsrBC.
  destruct (BetPs_3DiPs A O B BetAOB) as [ nAeqO [ nOeqB _ ]].
  elim OsrBC; intros _ [ nCeqO [ ColOBC _ ]].
  assert (ColAOC : [ A, O, C ]).
  { apply (BetPs_ColPs A O B) in BetAOB.
    eapply (ColPs_trans O A B C)...
  }
  destruct (classic ([A # O # C])) as [ BetAOC | nBetAOC ]...
  assert (OsrAC : [ O # A, C ]). { repeat split... }
  assert (OsrAB : [ O # A, B ]).
  { apply (SR_sym O B C) in OsrBC.
    apply (SR_trans O A C B OsrAC OsrBC).
  }
  destruct OsrAB as [ _ [ _ [ _ nBetAOB ]]]; contradiction.
Qed.

Lemma BetPs_SR_SR :
  forall O A B C : Point,
  [ A # O # B ]
    -> [ O # B, C ]
    -> [ A # B, C ].
Proof.
  intros * BetAOB OsrBC.
  assert (BetAOC : [ A # O # C ]).
  { apply (BetPs_SR_BetPs O A B C); auto. }
  apply (BetPs_SR A O B) in BetAOB;
  destruct BetAOB as [ BetAOB _ ];
  apply (SR_sym A O B) in BetAOB;
  apply (BetPs_SR A O C) in BetAOC;
  destruct BetAOC as [ BetAOC _ ];
  apply (SR_trans A B O C BetAOB BetAOC).
Qed.

Lemma BetPs_inv :
  forall O A B A' B' : Point,
  [ A # O # B ]
    -> [ O # A, A' ]
    -> [ O # B, B' ]
    -> [ A' # O # B' ].
Proof with eauto.
  intros * BetAOB OsrAA' OsrBB'.
  apply (BetPs_SR_BetPs O A' B B')...
  apply BetPs_sym.
  apply (BetPs_SR_BetPs O B A A')...
  apply BetPs_sym...
Qed.
Lemma SR_inv :
  forall O A B A' B' : Point,
  [ O # A, A' ]
    -> [ A # O # B ]
    -> [ A' # O # B' ]
    -> [ O # B, B' ].
Proof.
  intros * OsrAA' BetAOB BetA'OB'.
  apply BetPs_sym in BetAOB.
  apply (BetPs_SR_BetPs O B A A' BetAOB) in OsrAA'.
  apply BetPs_sym in OsrAA'.
  apply (BetPs_BetPs_SR O A' B B'); auto.
Qed.

(** Theorem #13 *)
(* The relation Between is co-transitive. *)
Theorem BetPs_a_trans :
  forall A B C D : Point,
  [ A # B # D ]
    -> [ B # C # D ]
    -> [ A # B # C # D ].
Proof with incpt 2.
  assert (BetPs_a_trans1 : forall A B C D : Point,
    [ A # B # D ] -> [ B # C # D ] -> [ A # B # C ])...
  { intros * BetABD BetBCD.
    destruct (BetPs_3DiPs A B D) as [ nAeqB [ nBeqD nAeqD ]]...
    destruct (BetPs_3DiPs B C D) as [ nBeqC [ nCeqD _ ]]...
    assert (nAeqC : A <> C).
    { intros AeqC; subst; contradict BetBCD; betps. }
    destruct (DrawLineThroughOrderedPoints A B D)
      as [ x [ Aox [ Box Dox ]]]...
    assert (Cox : [ C @ x ])...
    eapply (BetPs_SR_BetPs B A D C)...
    apply SR_sym. apply BetPs_SR. apply BetPs_sym...
  }
  intros * BetABD BetBCD.
  assert (ABC : [ A # B # C ])...
  repeat split; auto.
  destruct (BetPs_3DiPs A B D) as [ nAeqB [ nBeqD nAeqD ]]...
  destruct (BetPs_3DiPs B C D) as [ nBeqC [ nCeqD _ ]]...
  assert (nAeqC : A <> C); dips.
  destruct (DrawLineThroughOrderedPoints A B D)
    as [ x [ Aox [ Box Dox ]]]...
  assert (Cox : [ C @ x ])...
  assert (ColACD : [ A, C, D ]); inc.
  destruct (DecidePointsBetweenness A C D)
    as [[ BetACD | BetCDA ]| BetCAD ]; betps.
  { apply (BetPs_sym A B D) in BetABD.
    assert (BetCDB : [ C # D # B ]); incpt.
    apply (BetPs_sym B C D) in BetBCD;
    apply (BetPs_nBetPerPs C D B) in BetCDB; contradiction.
  }
Qed.
Theorem BetPs_b_trans :
  forall A B C D : Point,
  [ A # B # C ]
    -> [ B # C # D ]
    -> [ A # B # C # D ].
Proof with incpt 2.
  intros * BetABC BetBCD.
  destruct (BetPs_3DiPs A B C BetABC) as [ nAeqB [ nBeqC nAeqC ]].
  destruct (BetPs_3DiPs B C D BetBCD) as [ _ [ nCeqD nBeqD ]].
  destruct (DrawLineThroughOrderedPoints A B C)
    as [ x [ Aox [ Box Cox ]]]...
  assert (Dox : [ D @ x ])...
  assert (nAeqD : A <> D).
  { intros AeqD; subst; contradict BetBCD; betps. }
  assert (ColABC : [ A, B, C ]); incpt.
  assert (ColACD : [ A, C, D ]); incpt.
  destruct (DrawPointApartLine x) as [ E nEox ].
  assert (nEeqB : E <> B). { intros EeqB; rewrite EeqB in nEox; auto. }
  destruct (DrawExtensionLinePP E B) as [ y [ Eoy Boy ]]...
  assert (nxeqy : x <> y). { intros xeqy; rewrite <- xeqy in Eoy; auto. }
  assert (nAoy : ~ [ A @ y ]). { contradict nxeqy; eqls. }
  assert (nCoz : ~ [ C @ y ]). { contradict nxeqy; eqls. }
  assert (nDoy : ~ [ D @ y ]). { contradict nxeqy; eqls. }
  assert (SSyCD : [ y | C, D ]). { eapply SR_SS... eapply BetPs_SR... betps. }
  assert (SSyDC : [ y | D, C ]). { eapply SS_sym... }
  assert (OSyAC : [ A | y | C ]). { repeat split; incpt. }
  assert (OSyAD : [ A | y | D ]). { apply (OSO_trans A C D y)... }
  destruct (DrawIntersectionOfLineAndSegment A D y)
    as [ F [ Foy BetAFD ]]...
  assert (Fox : [ F @ x ])...
  assert (FeqB : F = B); eqps.
  subst B.
  repeat split...
  eapply (BetPs_a_trans A F C D )...
Qed.
Lemma BetPs_c_trans :
  forall A B C D : Point,
  [ A # B # C ]
    -> [ A # C # D ]
    -> [ A # B # C # D ].
Proof.
  intros * ABC ACD.
  apply BetPs_sym in ABC.
  apply BetPs_sym in ACD.
  apply (BetPs_a_trans D C B A) in ACD; auto.
  destruct ACD as [ DCB [ DCA [ DBA CBA ]]].
  repeat split; apply BetPs_sym; auto.
Qed.

(** Problem #12 *)
(* Given two distinct points A and B, decide whether arbitrary point C
 which is collinear to them ~~~~~. *)
Definition DecidePointsOrderOnLine :
  forall A B C : Point,
  A <> B
    -> [ A, B, C ]
    -> { [ A # B, C ] } + { [ B # A, C ] }.
Proof with inc.
  intros * nAeqB ColABC.
  destruct (DecidePointsDistinction A C B) as [ nAeqC | nBeqC ]...
  { destruct (DecidePointsOnSameRay A B C) as [ SR | OR ]; colps.
    right; eapply BetPs_SR; betps.
  }
  { destruct (DecidePointsOnSameRay B A C) as [ SR | OR ]; colperps.
    left; eapply BetPs_SR; betps.
  }
Defined.

(** Problem #13 *)
(* Line Separation. *)
Definition LineSeparation :
  forall O A B P : Point,
  P <> O
    -> [ A # O # B ]
    -> [ A, O, P ]
    -> { [ O # A, P ] /\ [ B # O # P ] } + { [ A # O # P ] /\ [ O # B, P ] }.
Proof with eauto.
  intros * nPeqO BetAOB ColAOP.
  destruct (BetPs_3DiPs A O B BetAOB) as [ nAeqO [ nOeqB nAeqB ]].
  destruct (DrawLineThroughOrderedPoints A O B BetAOB)
    as [ x [ Aox [ Oox Box ]]].
  assert (Pox : [ P @ x ]).
  { apply (ColPs_IncPt A O P x nAeqO); firstorder. }
  destruct (DrawPointApartLine x) as [ E nEox ].
  assert (nOeqE : O <> E). { contradict nEox; rewrite <- nEox... }
  destruct (DrawExtensionLinePP O E nOeqE) as [ y [ Ooy Eoy ]].
  assert (nxeqy : x <> y). { contradict nEox; rewrite nEox... }
  assert (nAoy : ~ [ A @ y ]).
  { contradict nxeqy; apply (DiPs_EqLs A O x y nAeqO); firstorder. }
  assert (nBoy : ~ [ B @ y ]).
  { contradict nxeqy; apply (DiPs_EqLs O B x y nOeqB); firstorder. }
  assert (nPoy : ~ [ P @ y ]).
  { contradict nxeqy; apply (DiPs_EqLs P O x y nPeqO); firstorder. }
  assert (OSyAB : [ A | y | B ]). { firstorder. }
  destruct (PlaneSeparation A B P y)
    as [[ OSyAP SSyBP ]|[ SSyAP OSyBP ]]...
  { right.
    assert (ColOAP : [ O, A, P ]). { exists x... }
    destruct (DecidePointsOnSameRay O A P) as [ OsrAP | OorAP ]...
    { assert (nOrAP : ~ [ O # A, P ]).
      { assert (nSSyAP : ~ [ y | A, P ]). { firstorder. }
        contradict nSSyAP. apply (SR_SS O A P y Ooy nAoy nSSyAP).
      }
      contradiction.
    }
    { assert (ColOBP : [ O, B, P ]). { exists x... }
      assert (OrBP : [ O # B, P ]).
      { apply (SS_SR O B P y Ooy ColOBP SSyBP). }
      auto.
    }
  }
  { left.
    assert (ColOBP : [ O, B, P ]). { exists x... }
    destruct (DecidePointsOnSameRay O B P) as [ OsrBP | OorBP ]...
    { assert (OorBP : [ B # O # P ]).
      { assert (nOsrBP : ~ [ O # B, P ]).
        { assert (nSSyBP : ~ [ y | B, P ]). { firstorder. }
          contradict nSSyBP; apply (SR_SS O B P y Ooy nBoy nSSyBP).
        }
        contradiction.
      }
      firstorder.
    }
    { assert (ColOAP : [ O, A, P ]). { exists x... }
      assert (OsrAP : [ O # A, P ])...
      { apply (SS_SR O A P y Ooy ColOAP SSyAP). }
    }
  }
Defined.

Example DecidePointsOrderOnRay :
  forall O A B : Point,
  A <> B
    -> [ O # A, B ]
    -> { [ O # B # A ] } + { [ O # A # B ] }.
Proof with betps.
  intros * nAeqB [ nOeqA [ nOeqB [ ColAOB nBetAOB ]]].
  destruct (DecidePointsBetweenness A O B) as [[ H1 | H2 ]| H3 ]...
Defined.

Example DecidePointsOrder_NOP :
  forall A B C O : Point,
  [ A, B, O ]
    -> [ A # B # C ]
    -> { [ B # A, O ] } + { [ A # O # C ] } + { [ B # C, O ] }.
Proof with inc.
  intros * ColABCO ABC.
  destruct (BetPs_3DiPs A B C) as [ nAeqB [ nBeqC nAeqC ]]...
  assert (ColACO : [A, C, O]).
  { destruct (ColPs_trans A O B C); colps. colperps. }
  assert (ColBCO : [B, C, O]).
  { destruct (ColPs_trans B O A C); colps. colperps. }
  destruct (DecidePointsDistinction B O C) as [ nBeqO | nOeqC ]...
  { destruct (DecidePointsOnSameRay B C O) as [ SR | OR ]; eauto.
    left; left. eapply BetPs_BetPs_SR; betps.
  }
  { destruct (DecidePointsDistinction B O A) as [ nBeqO | nAeqO ]...
    { destruct (DecidePointsOnSameRay B A O) as [ SR | OR ]; colperps.
      right. eapply BetPs_BetPs_SR...
    }
    { destruct (DecidePointsBetweenness A O C)
        as [[ AOC | OCA ]| OAC ]; colperps.
      { right. destruct (BetPs_a_trans O C B A); betps.
        eapply BetPs_BetPs_SR... apply BetPs_sym; firstorder.
      }
      { left; left. destruct (BetPs_a_trans O A B C)... eapply BetPs_SR... }
    }
  }
Defined.

Example DecidePointsOrder_OP :
  forall A B C O : Point,
  [ A # B, O ]
    -> [ A # B # C ]
    -> { [ A # O # C ] } + { [ B # C, O ] }.
Proof with inc 4.
  intros * AsrBO ABC.
  destruct (BetPs_3DiPs A B C) as [ nAeqB [ nBeqC nAeqC ]]...
  assert (ColCBO : [ C, B, O ]).
  { destruct AsrBO as [ _ [ _ [ ColABO _ ]]].
    apply BetPs_ColPs in ABC... colperps 4.
  }
  destruct (DecidePointsDistinction B O C) as [ nBeqO | nCeqO ]...
  { destruct (DecidePointsOnSameRay B C O) as [ SR | OR ]...
    { colperps. }
    { assert (BetAOB : [ A # O # B ]).
      { eapply BetPs_SR; split. apply SR_sym... eapply BetPs_BetPs_SR; betps. }
      left; eapply (BetPs_c_trans A O B C)...
    }
  }
  { destruct (DecidePointsOnSameRay C B O) as [ SR | OR ]...
    { left...
      eapply (BetPs_SR A O C); split.
      { eapply (SR_trans A O B C)...
        apply SR_sym...
        apply BetPs_SR; betps.
      }
      { eapply (SR_trans C O B A)...
        apply SR_sym...
        apply BetPs_SR; betps.
      }
    }
    { right. apply BetPs_SR... betps. }
  }
Defined.

Example DecidePointsOrder_O :
  forall A B C D O : Point,
  [ A # O # D ]
    -> [ A # B # C # D ]
    -> { [ A # O # C ] } + { [ B # O # D ] }.
Proof with inc; betps.
  intros * AOD [ ABC [ ABD [ ACD BCD ]]].
  destruct (BetPs_3DiPs A B C) as [ nAeqB [ nBeqC nAeqC ]]...
  destruct (BetPs_3DiPs B C D) as [ _ [ nCeqD nBeqD ]]...
  destruct (BetPs_3DiPs A B D) as [ _ [ _ nAeqD ]]...
  destruct (DecidePointsOrder_OP A B C O) as [ AOC | BsrCO ]...
  { eapply (SR_trans A B D O)...
    eapply BetPs_SR...
    apply SR_sym.
    eapply BetPs_SR...
  }
  { right.
    apply BetPs_SR; split...
    { eapply (SR_trans B O C D)...
      apply SR_sym...
      eapply BetPs_SR...
    }
    { eapply (SR_trans D O A B)...
      eapply BetPs_SR...
      apply SR_sym.
      eapply BetPs_SR...
    }
  }
Defined.

Example DecidePointsOrder :
  forall A B C D E O : Point,
  [ A # O # E ]
    -> [ A # B # C # D # E ]
    -> { [ A # O # C ] } + { [ B # O # D ] } + { [ C # O # E ] }.
Proof with inc.
  intros * AOE [ ABCD [ ABCE [ ABDE [ ACDE BCDE ]]]].
  destruct (DecidePointsOrder_O A B D E O) as [ AOD | BOE ]...
  { destruct (DecidePointsOrder_O A B C D O) as [ AOC | BOD ]... }
  { destruct (DecidePointsOrder_O B C D E O) as [ BOD | COE ]... }
Defined.

Example BetPs_d_trans :
  forall A B C D : Point,
  B <> C
    -> [ A # B # D ]
    -> [ A # C # D ]
    -> { [ A # B # C # D ] } + { [ A # C # B # D ] }.
Proof with eauto.
  intros * nBeqC ABD ACD.
  destruct (BetPs_3DiPs A B D ABD) as [ nAeqB [ nBeqD nAeqD ]].
  destruct (BetPs_3DiPs A C D ACD) as [ nAeqC [ nCeqD _ ]].
  assert (H : ~ [B # A # C]).
  { apply BetPs_SR in ABD. destruct ABD as [ ABD _ ].
    apply BetPs_SR in ACD. destruct ACD as [ ACD _ ].
    assert ( A_BC : [A # B, C]).
    { apply (SR_trans A B D C)... apply SR_sym... }
    destruct A_BC; firstorder.
  }
  destruct (DecidePointsOrderOnRay A B C) as [ G1 | G2 ]; try repeat split...
  { apply (ColPs_trans A B D C); colps. }
  { right. apply BetPs_c_trans... }
  { left. apply BetPs_c_trans... }
Defined.

(** Hilbert, Chapter 1 : Theorem 5. *)
(* Any four points on a line can be notated in a way that all four
 order relations that keep the alphabetic order hold. *)
Example DecideFourPointsOrderOnLine :
  forall (A B C D : Point),
  A <> B
    -> A <> C
    -> A <> D
    -> B <> C
    -> B <> D
    -> C <> D
    -> [ A, B, C, D ]
    -> { [ A # B # C # D ] } + { [ A # B # D # C ] } + { [ A # C # B # D ] }
     + { [ A # C # D # B ] } + { [ A # D # B # C ] } + { [ A # D # C # B ] }
     + { [ B # A # C # D ] } + { [ B # A # D # C ] } + { [ B # C # A # D ] }
     + { [ B # C # D # A ] } + { [ B # D # A # C ] } + { [ B # D # C # A ] }
     + { [ C # A # B # D ] } + { [ C # A # D # B ] } + { [ C # B # A # D ] }
     + { [ C # B # D # A ] } + { [ C # D # A # B ] } + { [ C # D # B # A ] }
     + { [ D # A # B # C ] } + { [ D # A # C # B ] } + { [ D # B # A # C ] }
     + { [ D # B # C # A ] } + { [ D # C # A # B ] } + { [ D # C # B # A ] }.
Proof with eauto.
  intros * nAeqB nAeqC nAeqD nBeqC nBeqD nCeqD ColABCD.
  destruct (DecidePointsBetweenness A B C) as [[ H1 | H2 ]| H3 ]...
  { firstorder. }
  { destruct (DecidePointsBetweenness A C D) as [[ G1 | G2 ]| G3 ]...
    firstorder.
    { assert ([A # B # C # D]). { apply BetPs_c_trans... }
      tauto.
    }
    { apply BetPs_sym in G2.
      destruct (BetPs_d_trans A B D C) as [ Q1 | Q2 ]; tauto...
    }
    { assert ([D # A # B # C]).
      { apply BetPs_a_trans... apply BetPs_sym; auto. }
      tauto.
    }
  }
  { apply BetPs_sym in H2...
    destruct (DecidePointsBetweenness A B D) as [[ G1 | G2 ]| G3 ]...
    { firstorder. }
    { assert ([A # C # B # D]). { apply BetPs_c_trans... }
      tauto.
    }
    { apply BetPs_sym in G2.
      destruct (BetPs_d_trans A C D B) as [ Q1 | Q2 ]; tauto...
    }
    { assert ([D # A # C # B]).
      { apply BetPs_a_trans... apply BetPs_sym; auto. }
      tauto.
    }
  }
  { destruct (DecidePointsBetweenness B C D) as [[ G1 | G2 ]| G3 ]...
    { firstorder. }
    { assert ([B # A # C # D]). { apply BetPs_c_trans... }
      tauto.
    }
    { apply BetPs_sym in G2.
      destruct (BetPs_d_trans B A D C) as [ Q1 | Q2 ]; tauto...
    }
    { assert ([D # B # A # C]).
      { apply BetPs_a_trans... apply BetPs_sym; auto. }
      tauto.
    }
  }
Defined.

Example DrawBoundaryPoint :
  forall (A B : Point)(x : Line),
  [ A, B @ x ]
    -> { O : Point | [ O @ x ] /\ [ O # A, B ] }.
Proof with colps.
  intros * [ Aox Box ].
  destruct (DrawDistinctPointOnLine A x) as [ C [ nCeqA Cox ]]...
  assert (ColCAB : [C, A, B])...
  destruct (DecidePointsOrderOnLine C A B) as [ CsrAB | H2 ]...
  destruct (DrawOppositePoint A C) as [ D [ BetACD _ ]]...
  exists D; split; incpt 2. apply BetPs_sym in BetACD.
  eapply (BetPs_SR D A B)... eapply BetPs_SR_BetPs...
Defined.

Example DrawPointOnOppositeSide :
  forall (A : Point)(x : Line),
  ~ [ A @ x ]
    -> { B : Point | [ A | x | B ] }.
Proof.
  intros * nAox.
  destruct (DrawPointOnLine x) as [ O Oox ].
  assert (nAeqO : A <> O).
  { apply not_eq_sym. apply (nIncPt_DiPs O A x Oox nAox). }
  destruct (DrawOppositePoint O A) as [ B [ BetAOB _ ]]; auto.
  assert (nBeqO : B <> O).
  { apply (BetPs_sym A O B) in BetAOB.
    apply (BetPs_3DiPs B O A BetAOB).
  }
  assert (nBox : ~ [ B @ x ]).
  { contradict nAox.
    apply (BetPs_sym A O B) in BetAOB.
    apply (BetPs_ColPs B O A) in BetAOB.
    apply (ColPs_IncPt B O); firstorder.
  }
  assert (OSxAB : [ A | x | B ]). { repeat split; auto. exists O; auto. }
  exists B; auto.
Defined.

Example DrawBoundaryPoints :
  forall (A B : Point)(x : Line),
  [ A, B @ x ]
    -> { C : Point & { D : Point |
            [ C @ x ] /\ [ D @ x ] /\ [ C # A # D ] /\ [ C # B # D ] } }.
Proof with ord.
  intros * [ Aox Box ].
  destruct (DrawBoundaryPoint A B x) as [ O [ Oox OsrAB ]]...
  exists O.
  assert (nOeqA : O <> A). { destruct OsrAB... }
  assert (nOeqB : O <> B). { destruct OsrAB... }
  destruct (DrawOppositePoint A O) as [ A' [ BetOAA' _ ]]; auto.
  destruct (DrawOppositePoint B O) as [ B' [ BetOBB' _ ]]; auto.
  destruct (DrawLineThroughOrderedPoints O A A' BetOAA')
    as [ y [ Ooy [ Aoy A'oy ]]].
  assert (xeqy : x = y). { apply (DiPs_EqLs O A x y)... }
  subst y.
  destruct (DrawLineThroughOrderedPoints O B B' BetOBB')
    as [ y [ O'oy [ Boy B'oy ]]].
  assert (xeqy : x = y). { apply (DiPs_EqLs O B x y)... }
  subst y.
  assert (nAeqA' : A <> A'). { apply (BetPs_3DiPs O A A')... }
  assert (ColAA'B' : [A, A', B']). { exists x... }
  destruct (DecidePointsOrderOnLine A A' B') as [ CsrAB | H2 ]; auto.
  { assert (nBeqB' : B <> B'). { apply (BetPs_3DiPs O B B')... }
    assert (ColBB'A' : [B, B', A']). { exists x... }
    destruct (DecidePointsOrderOnLine B B' A') as [ CsrBA | H3 ]; auto.
    { exists A'. repeat split... apply (BetPs_SR_BetPs B O B' A')... }
    { exists B'. repeat split... apply (BetPs_SR_BetPs A O A' B')... }
  }
  { exists A'.
    repeat split; auto.
    apply (BetPs_c_trans O B B' A'); eauto.
    apply BetPs_SR; split.
    { apply BetPs_SR in BetOAA'.
      destruct BetOAA' as [ A'srAO OsrAA' ].
      apply BetPs_SR in BetOBB'.
      destruct BetOBB' as [ B'srBO OsrBB' ]...
      apply SR_trans with B. apply SR_sym...
      apply SR_sym in OsrAB. apply SR_trans with A...
    }
    { apply SR_sym... apply SR_trans with A...
      apply SR_sym... apply BetPs_SR...
    }
  }
Defined.

(** Theorem #14 *)
(* The relation Between is co-transitive. *)
Theorem ConvexHalfplane :
  forall (A B C : Point)(x : Line),
  [ A # B # C ]
    -> [ x | A, C ]
    -> [ x | A, B ].
Proof with eauto.
  intros * BetABC SSxAC.
  destruct (DrawLineThroughOrderedPoints A B C)
    as [ y [ Aoy [ Boy Coy ]]]...
  assert (nAox : ~ [ A @ x ]). { firstorder. }
  assert (nBox : ~ [ B @ x ]). { firstorder. }
  assert (nCox : ~ [ C @ x ]). { firstorder. }
  destruct (DecideSameSide A B x) as [ SSxAB | OSxAB ]...
  destruct (DrawIntersectionOfLineAndSegment A B x)
    as [ O [ Oox BetAOB ]]...
  assert (OSxAC : [ A | x | C ]).
  { repeat split...
    exists O; split; eauto.
    apply BetPs_sym; apply (BetPs_a_trans C B O A); betps.
  }
  firstorder.
Qed.

End HALFLINE.

Hint Resolve
  SR_SR_BetPs BetPs_SR_1 BetPs_SR_2 SR_refl SR_sym
  SH_SR SS_SR BetPs_BetPs_SR BetPs_SR_BetPs BetPs_inv SR_inv BetPs_SR_SR
  BetPs_a_trans BetPs_b_trans BetPs_c_trans
  : BetPs.

Hint Resolve
  SR_IncPt_1 SR_IncPt_2
  : IncPt.

Hint Resolve
  SR_DiPs_1 SR_DiPs_2
  : DiPs.

Hint Resolve
  SR_ColPs
  : ColPs.

Hint Resolve
  nColPs_SR_inv nColPs_BetPs_inv SS_SR OS_OR SH_SR
  : BetPsPs.

Hint Resolve
  SR_SS OR_OS SR_SH SHc_inv OHc_inv SHa_inv OHa_inv
  : OrdPs.

(*****************************************************************************)
(* 6 *) Section INTERIOR.
Context `{ cr : Circles }.
(*****************************************************************************)

(** Theorem #15 *)
Theorem nColPs_BetPs_BR :
  forall (O A B C : Point),
  ~ [ O, A, C ]
    -> [ A # B # C ]
    -> [ O | A; B; C ].
Proof.
  intros O A B C nColOAC BetABC.
  destruct (DrawExtensionLinePP O A ) as [ x [ Oox Aox ]]; dips.
  destruct (DrawExtensionLinePP O C ) as [ y [ Ooy Coy ]]; dips.
  assert (SSxBC : [ x | B, C ]).
  { apply SS_sym.
    apply (SR_SS A C B x Aox).
    apply (nColPs_nIncPt O A C x); firstorder.
    apply SR_BetPs; auto.
  }
  assert (SSyBA : [ y | B , A ]).
  { apply (BetPs_sym A B C) in BetABC.
    apply SS_sym. apply (SR_SS C A B y Coy).
    contradict nColOAC.
    exists y; auto. apply SR_BetPs; auto.
  }
  repeat split; dips.
Qed.

(** Theorem #16 *)
Theorem ColPs_BR_BetPs :
  forall (O A B C : Point),
  [ A, B, C ]
    -> [ O | A; B; C ]
    -> [ A # B # C ].
Proof with dips.
  intros O A B C ColABC
   [[ nAeqO [ x [ _ [ Aox [ nBox [ nCox SSxCB ]]]]]]
   [ nOeqC [ y [ _ [ Coy [ nBoy [ nAoy SSyAB ]]]]]]].
  assert (nAeqB : A <> B)...
  assert (nBeqC : B <> C)...
  assert (nAeqC : A <> C)...
  destruct (DecidePointsBetweenness A B C)
    as [[ BetABC | BetBCA ]| BetBAC ]...
  { apply (BetPs_sym B C A) in BetBCA; contradict SSyAB;
    exists C; split... apply BetPs_sym...
  }
  { apply (BetPs_sym B A C) in BetBAC; contradict SSxCB;
    exists A; split... apply BetPs_sym...
  }
Qed.

Lemma BR_inv :
  forall O A B C A' B' C' : Point,
  [ O | A; B; C ]
    -> [ O # A, A' ]
    -> [ O # B, B' ]
    -> [ O # C, C' ]
    -> [ O | A'; B'; C' ].
Proof.
  intros O A B C A' B' C' BetRayOABC OsrAA' OsrBB' OsrCC'.
  destruct BetRayOABC as [ H1 H2 ].
  destruct H1 as [ _ [ x [ Aox [ Oox SSxBC ]]]].
  destruct H2 as [ _ [ y [ Ooy [ Coy SSyBA ]]]].
  assert (SSxB'C' : [ x | B', C' ]).
  { apply (SS_trans B' B C' x).
    { apply (SS_sym B B' x).
      apply (SR_SS O B B' x); eauto; firstorder.
    }
    { apply (SS_trans B C C' x SSxBC).
      apply (SR_SS O C C' x); eauto; firstorder.
    }
  }
  assert (SSyB'A' : [ y | B', A' ]).
  { apply (SS_trans B' B A' y).
    { apply (SS_sym B B' y).
      apply (SR_SS O B B' y); eauto; firstorder.
    }
    { apply (SS_trans B A A' y SSyBA).
      apply (SR_SS O A A' y); eauto; firstorder.
    }
  }
  repeat split; eauto; [ firstorder | exists x | firstorder | exists y ];
  split; auto; split; auto; eapply SR_IncPt_1; eauto.
Qed.

Example SH_nColPs_BR :
  forall (O A B C : Point),
  [ O # A | B, C ]
    -> ~ [ O, B, C ]
    -> { [ O | A; B; C ] } + { [ O | A; C; B ] }.
Proof with eauto.
  intros O A B C OAsfBC nColOBC.
  assert (nOeqA : O <> A). { destruct OAsfBC... }
  destruct (DrawSameHalfplaneBorderLine O A B C OAsfBC)
    as [ x [ Oox [ Aox SSxBC ]]].
  assert (nBox : ~ [ B @ x ]). { firstorder. }
  assert (nCox : ~ [ C @ x ]). { firstorder. }
  assert (nOeqC : O <> C); dips.
  assert (nColOAC : ~ [ O, A, C ]); ncolps.
  destruct (DrawExtensionLinePP O C nOeqC) as [ z [ Ooz Coz ]].
  destruct (DecideSameSide A B z) as [ SSzAB | OSzAB ]; nincpt...
  { left. split... split...
    exists z... split... split... apply SS_sym...
  }
  destruct (DrawIntersectionOfLineAndSegment A B z OSzAB)
    as [ E [ Eoz BetAEB ]].
  assert (nEox : ~ [ E @ x ]). { contradict nBox; incpt 2. }
  assert (nAeqE : O <> E); dips.
  assert (OsrEC : [O # E, C]).
  { assert (SSxEC : [ x | E, C ]). { apply (SS_trans E B C x); ord. }
    eapply SS_SR. apply Oox. colps... auto.
  }
  assert (nColOAB : ~ [ O, A, B ]); ncolps.
  assert (OoAEB : [ O | A; E; B ]).
  { apply (nColPs_BetPs_BR O A E B nColOAB BetAEB). }
  right...
  apply (BR_inv O A E B A C B); try apply SR_refl; dips.
Defined.

Lemma BR_sym :
  forall O A B C : Point,
  [ O | A; B; C ]
    -> [ O | C; B; A ].
Proof.
  intros O A B C [ H1 H2 ].
  destruct H1 as [ nAeqO [ x [ Aox [ Oox SSxCB ]]]].
  destruct H2 as [ nOeqC [ y [ Ooy [ Coy SSyAB ]]]].
  repeat split; auto; [exists y | exists x ]; eauto.
Qed.

Lemma BetPs_BR_BR :
  forall O A B C D : Point,
  [ A # O # D ]
    -> ([ O | A; B; C ] <-> [ O | B; C; D ]).
Proof with eauto.
  intros O A B C D BetAOD.
  split.
  { intros [ H1 H2 ].
    destruct H1 as [ nAeqO [ x [ Aox [ Oox SSxBC ]]]].
    destruct H2 as [ nOeqC [ y [ Ooy [ Coy SSyAB ]]]].
    assert (nCox : ~ [ C @ x ]). { destruct SSxBC as [ _ [ nCox _ ]]... }
    assert (nColOAC : ~ [ O, A, C ]); ncolps.
    assert (nxeqy : x <> y); dils.
    assert (Dox : [ D @ x ]); incpt 2.
    assert (nOeqD : O <> D); dips.
    assert (nDoy : ~ [ D @ y ]). { contradict nxeqy; eqls. }
    assert (OSyDB : [ D | y | B ]). { apply (OSO_trans D A B y); ord. }
    assert (nOoCBD : ~ [ O | C; B; D ]).
    { contradict OSyDB.
      destruct OSyDB as [ OCsfBD ODsfBC ].
      destruct OCsfBD as [ _ [ y' [ Ooy' [ Coy' SSyBD ]]]].
      assert (yeqy' : y = y'); eqls.
      subst y'. apply SS_sym in SSyBD. firstorder.
    }
    assert (ODsfCB : [ O # D | C, B ]).
    { repeat split... exists x; ord. }
    assert (nBoy : ~ [ B @ y ]). { firstorder. }
    assert (nColOCB : ~ [ O, C, B ]).
    { contradict nBoy.
      apply (ColPs_IncPt O C B y); geo; firstorder.
    }
    destruct (SH_nColPs_BR O D C B) as [ AoDCE | AoCDE ]...
    { apply (BR_sym O D C B)... }
    { apply (BR_sym O D B C) in AoCDE; contradiction. }
  }
  { intros OsfBCD.
    apply BR_sym. apply BR_sym in OsfBCD.
    rename B into B'. rename A into A'. rename D into A.
    rename C into B. rename B' into C. rename A' into D.
    apply BetPs_sym in BetAOD.
    destruct OsfBCD as [ H1 H2 ].
    destruct H1 as [ nAeqO [ x [ Oox [Aox SSxBC ]]]].
    destruct H2 as [ nOeqC [ y [ Ooy [ Coy SSyBA ]]]].
    assert (nCox : ~ [ C @ x ]). { destruct SSxBC as [ _ [ nCox _ ]]... }
    assert (nColOAC : ~ [ O, A, C ]); ncolps.
    assert (nxeqy : x <> y); dils.
    assert (Dox : [ D @ x ]); incpt 2.
    assert (nOeqD : O <> D); dips.
    assert (nDoy : ~ [ D @ y ]). { contradict nxeqy; eqls. }
    assert (OSyDB : [ D | y | B ]). { apply (OSO_trans D A B y); ord. }
    assert (nOoCBD : ~ [ O | C; B; D ]).
    { contradict OSyDB.
      destruct OSyDB as [ OCsfBD ODsfBC ].
      destruct OCsfBD as [ _ [ y' [ Ooy' [ Coy' SSyBD ]]]].
      assert (yeqy' : y = y'); eqls.
      subst y'. apply SS_sym in SSyBD. firstorder.
    }
    assert (ODsfCB : [ O # D | C, B ]).
    { apply SHb_sym. repeat split... }
    assert (nBoy : ~ [ B @ y ]). { firstorder. }
    assert (nColOCB : ~ [ O, C, B ]); ncolps.
    destruct (SH_nColPs_BR O D C B ODsfCB nColOCB)
      as [ AoDCE | AoCDE ].
    { apply (BR_sym O D C B)... }
    { apply (BR_sym O D B C) in AoCDE; contradiction. }
  }
Qed.

(** Problem #14 *)
(** Hartshorne, Proposition 7.3 - Crossbar Theorem *)
(* Let AOC be an angle, and let B be a point in the interior of the angle.
 Then the ray OB must meet the segment AC *)
Definition DrawPointCrossBar :
  forall (O A B C : Point),
  [ O | A; B; C ]
    -> { B' : Point | [ A # B' # C ] /\ [ O # B, B' ] }.
Proof with eauto.
  intros O A B C [ OAsfBC OCsfBA ].
  destruct (DrawSameHalfplaneBorderLine O A B C)
    as [ a [ Ooa [ Aoa SSaBC ]]]...
  assert (nOeqB : O <> B); dips.
  destruct (DrawExtensionLinePP O B nOeqB) as [ b [ Oob Bob ]].
  destruct (DrawSameHalfplaneBorderLine O C B A)
    as [ c [ Ooc[ Coc SScBA ]]]...
  assert (nAeqO : A <> O); dips.
  destruct (DrawOppositePoint O A) as [ F [ BetAOF _ ]]...
  assert (nbeqa : b <> a). { intros beqa; subst; firstorder. }
  assert (nBoa : ~ [ B @ a ]). { contradict nbeqa; eqls. }
  assert (nAob : ~ [ A @ b ]). { contradict nbeqa; eqls. }
  assert (SSbFC : [ b | F, C ]).
  { destruct (BetPs_BR_BR O A B C F)
      as [[[ _ [ t [ Oot [ Bot SSbCF ]]]] _ ] _ ]...
    assert (beqt : b = t); eqls. subst t; ord.
  }
  assert (OSbAF : [ A | b | F ]). { repeat split; eauto; firstorder. }
  assert (OSbAC : [ A | b | C ]).
  { apply (OSO_trans A F C b OSbAF SSbFC). }
  destruct (DrawIntersectionOfLineAndSegment A C b OSbAC)
    as [ B' [B'oy BetAB'C ]].
  assert (nCoa : ~ [ C @ a ]). { firstorder. }
  assert (nColOAC : ~ [ O, A, C ]); ncolps.
  assert (SSaCB' : [ a | C, B' ]).
  { destruct (nColPs_BetPs_BR O A B' C)
      as [[ _ [ t [ Oot [ Aot SSxCB' ]]]] _ ]; ord.
  }
  exists B'. split; auto.
  apply (SS_SR O B B' a Ooa)...
  apply (SS_sym C B' a) in SSaCB'.
  apply SS_sym.
  eapply SS_trans. apply SSaCB'. apply SS_sym...
Defined.

Lemma BR_OS :
  forall (O A B C : Point)(x : Line),
  [ O | A; B; C ]
    -> [ O, B @ x ]
    -> [ A | x | C ].
Proof with eauto.
  intros O A B C x OoABC [ Oox Box ].
  destruct (DrawPointCrossBar O A B C)
    as [ B' [ BetAB'C [ nBeqO [ _ [ ColOBB' _ ]]]]]...
  assert (B'ox : [ B' @ x ]). { apply (ColPs_IncPt O B B' x)... }
  assert (nAox : ~ [ A @ x ]).
  { intros Aox.
    assert (Cox : [ C @ x ]); incpt 2.
    destruct OoABC as [[ nOeqA [ t [ Oot [ Aot [ nCot _ ]]]]] _ ].
    assert (xeqt : x = t); eqls.
  }
  assert (nCox : ~ [ C @ x ]). { contradict nAox; incpt 2. }
  repeat split...
Qed.

(** Theorem #17 *)
Theorem BR_OH :
  forall O A B C : Point,
  [ O | A; B; C ]
    -> [ A | O # B | C ].
Proof with eauto.
  intros O A B C OoABC.
  assert (nOeqB : O <> B).
  { destruct OoABC as [[ _ [ x [ Oox [ _ [ nBox _ ]]]]] _ ]; dips. }
  destruct (DrawExtensionLinePP O B nOeqB) as [ x [ Oox Box ]].
  split; auto. exists x; split; auto. split; auto.
  apply (BR_OS O A B C x OoABC)...
Qed.

(** Theorem #18 *)
Theorem OH_OH_BR :
  forall A B C D : Point,
  [ B | A # C | D ]
    -> [ A | B # D | C ]
    -> [ A | B; C; D ].
Proof with eauto.
  assert (OF_OF_SF : forall A B C D : Point,
    [ B | A # C | D ] -> [ A | B # D | C ] -> [ A # B | C, D ]).
  { intros A B C D.
    intros [ nAeqC [ x [ Aox [ Cox [ nBox [ nDox [ O [ Oox BOD ]]]]]]]].
    intros [ nBeqD [ y [ Boy [ Doy [ nAoy [ nCoy [ O' [ Ooy AOC ]]]]]]]].
    assert (OeqO' : O = O').
    { apply (DiLs_EqPs O O' x y).
      intros xeqy.
      subst y... repeat split; incpt 2.
    }
    subst O'.
    assert (nAeqB : A <> B); dips.
    destruct (DrawExtensionLinePP A B nAeqB) as [ b [ Aob Bob ]].
    assert (nbeqx : b <> x); dils.
    assert (SSbOC : [ b | O, C ]).
    { apply (SR_SS A O C b Aob).
      contradict nbeqx.
      apply (DiPs_EqLs A O b x); [intros H; subst; auto | firstorder .. ].
      apply SR_BetPs...
    }
    assert (SSbOD : [ b | O, D ]).
    { apply (SR_SS B O D b Bob).
      contradict nbeqx.
      apply (DiPs_EqLs B O b x); [ intros H; subst; auto | firstorder .. ].
      apply SR_BetPs...
    }
    assert (SSbCD : [ b | C, D ]).
    { apply (SS_sym O C b) in SSbOC.
      apply (SS_trans C O D b SSbOC SSbOD).
    }
    split...
  }
  intros A B C D ACofBD BDofAC.
  split.
  { apply (OF_OF_SF A B C D)... }
  { apply (OF_OF_SF A D C B)...
    apply (OHb_sym A C B D)...
    apply (OHa_sym B D A C)...
  }
Qed.

End INTERIOR.

Hint Resolve
  nColPs_BetPs_BR
  ColPs_BR_BetPs
  BR_sym
  ConvexHalfplane
  : OrdPs.

Hint Resolve
  OS_IncPs_ConvLs
  : ColLs.

(*****************************************************************************)
(* 7 *) Section RAY.
Context `{ cr : Circles }.
(*****************************************************************************)

(* Ray equivalence relation *)

Lemma EqRays_refl :
  reflexive Ray EqRays.
Proof.
  unfold reflexive.
  intros [ O A nAeqO ].
  split; simpl; auto; apply SR_refl; auto.
Qed.
Lemma EqRays_sym :
  symmetric Ray EqRays.
Proof.
  unfold symmetric.
  intros [ O A nAeqO ][ O' B nBeqO ][ OeqO' OsrAB ].
  simpl in *; destruct OeqO'; split; simpl; auto; apply SR_sym; auto.
Qed.
Lemma EqRays_trans :
  transitive Ray EqRays.
Proof.
  unfold transitive.
  intros x y z [ OeqO' OsrAB ][ O'eqO'' OsrBC ].
  destruct x as [ O A nAeqO ].
  destruct y as [ O' B nBeqO ].
  destruct z as [ O'' C nCeqO ].
  simpl in *; subst; split; auto;
  eapply SR_trans; eauto.
Qed.
Global Instance EqRays_equiv :
  Equivalence EqRays
  := Build_Equivalence EqRays
     EqRays_refl
     EqRays_sym
     EqRays_trans.

Lemma DiRs_sym :
  forall a b : Ray,
  a =/= b
    -> b =/= a.
Proof.
  intros a b naeqb.
  contradict naeqb; symmetry; trivial.
Qed.

Lemma nColRs_sym :
  forall (a b : Ray),
  ![ a # b ]
    -> ![ b # a ].
Proof with eauto.
  intros a b [ roab diab ].
  unfold nColRs; split...
  destruct roab; ncolperps.
Qed.

Lemma nColRs_inv :
  forall (a b c : Ray),
  ![ a # b ]
    -> b == c
    -> ![ a # c ].
Proof with eauto.
  unfold nColRs.
  intros [ O A nOeqA ][ O' B nOeqB ][ O'' C nOeqC].
  intros [ roab diab ][ robc beqc ]; simpl in *.
  subst O'' O'; split...
  contradict diab. colperps.
Qed.

(** Problem #15 *)
Definition DrawOpRay :
  forall (a : Ray),
  { b : Ray | a <==> b }.
Proof.
  intros [ O A nAeqO ]; simpl.
  destruct (DrawOppositePoint O A) as [ B [ BetAOB _ ]]; auto.
  destruct (BetPs_3DiPs A O B BetAOB) as [ _ [ nOeqB _ ]].
  exists ({{ O # B | nOeqB }}).
  unfold OpRays; simpl; eauto.
Defined.

Definition OpRay : Ray -> Ray
  := fun a : Ray => proj1_sig (DrawOpRay a).
Notation " ! a "
  := (OpRay a)(at level 50).

Global Instance OpRays_compat :
  Proper (EqRays ==> EqRays) OpRay.
Proof with eauto.
  intros [ O A nAeqO ][ O' B nBeqO ][ OeqO' OsrAB ].
  unfold EqRays, OpRay.
  simpl in *. subst O'.
  destruct (DrawOppositePoint O A) as [ A' [ BetAOA' _ ]]...
  destruct (BetPs_3DiPs A O A' BetAOA') as [ _ [ nOeqA' nAeqA' ]].
  destruct (DrawOppositePoint O B) as [ B' [ BetBOB' _ ]]...
  destruct (BetPs_3DiPs B O B' BetBOB') as [ _ [ nOeqB' nBeqB' ]].
  split; simpl...
  apply (BetPs_BetPs_SR O A A' B')... apply BetPs_sym.
  apply (BetPs_SR_BetPs O B' B A). apply BetPs_sym... apply SR_sym...
Defined.

(** Problem #16 *)
Definition DecideRayApartness :
  forall (a b c : Ray)(roac : da a = da c),
  ![ a # b ]
    -> { ![ a # c ] } + { ![ b # c ] }.
Proof with eauto.
  intros [ O A nAeqO ][ O' B nBeqO ][ O'' C nCeqO ] roac [ roab diab ];
  unfold nColRs, EqRays, OpRays in *; simpl in *.
  subst O'' O'.
  destruct (nColPs_trans O A C B) as [ ColBOC | nColAOC ]...
  right; ncolperps.
Defined.

Example DrawRayApart :
  forall (a : Ray),
  { b : Ray | ![ a # b ] }.
Proof.
  intros a.
  destruct a as [ O A nOeqA ].
  destruct (DrawNonCollinearPoint A O) as [ B nColAOB ]; auto.
  assert (nOeqB : O <> B). { apply (nColPs_3DiPs A O B nColAOB). }
  exists ({{ O # B | nOeqB }}); simpl; split; eauto.
Defined.

Lemma OpRays_0 :
  forall (a : Ray),
  da a = da (!a).
Proof.
  intros [ O A nAeqO ]. unfold OpRay; simpl.
  destruct (DrawOppositePoint O A) as [ A' [ BetAOA' _ ]]; auto.
  destruct (BetPs_3DiPs A O A') as [ _ [ nOeqA' nAeqA' ]]; simpl; auto.
Qed.
Lemma OpRays_1 :
  forall (a : Ray),
  [ db a # da a # db (!a) ].
Proof.
  intros [ O A nAeqO ]. unfold OpRay; simpl.
  destruct (DrawOppositePoint O A) as [ A' [ BetAOA' _ ]]; auto.
  destruct (BetPs_3DiPs A O A') as [ _ [ nOeqA' nAeqA' ]]; simpl; auto.
Qed.

Lemma OpRs_BetPs :
  forall (A O B : Point)(nOeqA : O <> A)(nOeqB : O <> B),
  {{ O # A | nOeqA }} == !({{ O # B | nOeqB }})
    <-> [ A # O # B ].
Proof with eauto.
  intros A O B nAeqO nBeqO.
  unfold EqRays, OpRay; simpl.
  destruct (DrawOppositePoint O B) as [ B' [ BetBOB' _ ]]...
  destruct (BetPs_3DiPs B O B' BetBOB') as [ _ [ nOeqB' nBeqB' ]]; simpl.
  split; auto.
  { intros [ _ OsrAB' ].
    apply BetPs_sym. apply (BetPs_inv O B B' B)...
    apply SR_refl... apply SR_sym...
  }
  { intro BetAOB.
    split; auto.
    eapply (BetPs_BetPs_SR O B A B')... apply BetPs_sym...
  }
Qed.

Lemma OpRs_OpRs :
  forall (a b : Ray),
  a == !b
    <-> a <==> b.
Proof with eauto.
  intros [ O A nAeqO ][ O' B nBeqO ]; unfold OpRay; simpl.
  destruct (DrawOppositePoint O' B) as [ B' [ BetBOB' _ ]]...
  destruct (BetPs_3DiPs B O' B' BetBOB') as [ _ [ nB'eqO' nBeqB' ]].
  simpl. split.
  { intros [ orab BetPs ]; simpl in *.
    subst O'.
    split; simpl...
    apply BetPs_sym. apply (BetPs_SR_BetPs O B B' A)... apply SR_sym...
  }
  { intros [ orab BetAOB ]; simpl in *.
    subst O'.
    split; simpl...
    apply SR_sym... apply (BetPs_BetPs_SR O B B' A)... apply BetPs_sym...
  }
Qed.

Lemma OpOpRs :
  forall (a : Ray),
  a == !(!a).
Proof with eauto.
  intros a; case a; intros O A nAeqO.
  unfold EqRays, OpRay; simpl.
  destruct (DrawOppositePoint O A) as [ A' [ BetAOA' _ ]]...
  destruct (BetPs_3DiPs A O A' BetAOA') as [ _ [ nOeqA' nAeqA' ]]; simpl.
  destruct (DrawOppositePoint O A') as [ A'' [ BetA'OA'' _ ]]...
  destruct (BetPs_3DiPs A' O A'' BetA'OA'') as [ _ [ nOeqA'' nA'eqA'' ]].
  split...
  apply BetPs_sym in BetAOA'.
  apply (BetPs_BetPs_SR O A' A A'')...
Qed.

Lemma OpRs_irrefl :
  forall (a : Ray),
  a =/= !a.
Proof with eauto.
  intros a; case a; intros O A nAeqO. unfold OpRay; simpl.
  destruct (DrawOppositePoint O A) as [ A' [ BetAOA' _ ]]...
  destruct (BetPs_3DiPs A O A' BetAOA') as [ _ [ nOeqA' nAeqA' ]].
  unfold EqRays in *.
  simpl in *.
  intros [ _ OsrAA' ]. firstorder.
Qed.
Lemma OpRs_sym :
  forall (a b : Ray),
  a == !b
    -> b == !a.
Proof.
  intros a b aopb.
  rewrite aopb. apply OpOpRs.
Qed.
Lemma OpRs_trans :
  forall (a b c : Ray),
  a == !b
    -> b == !c
    -> a == c.
Proof.
  intros a b c aopb bopc.
  rewrite aopb. rewrite bopc. symmetry.
  apply OpOpRs.
Qed.

Lemma nColRs_nColPs :
  forall (a b : Ray),
  ![ a # b ]
    <-> da a = da b /\ a =/= b /\ a =/= !b.
Proof with inc 4.
  intros a b.
  destruct a as [ O A nOeqA ].
  destruct b as [ O' B nOeqB ].
  unfold nColRs, OpRay, EqRays; simpl.
  destruct (DrawOppositePoint O' B) as [ B' [ BetBOB' _ ]]...
  destruct (BetPs_3DiPs B O' B' BetBOB') as [ _ [ nOeqB' _ ]]; simpl.
  split.
  { intros [ OeqO' nColAOB ].
    subst O'.
    split; auto; split.
    { contradict nColAOB; destruct nColAOB as [ _ OsrAB ]; colps. }
    { apply BetPs_sym in BetBOB'...
      contradict nColAOB; destruct nColAOB as [ _ OsrAB ].
      apply (ColPs_trans O A B' B); colps.
    }
  }
  { intros [ OeqO' [ H1 H2 ]].
    subst O'.
    split; auto.
    contradict H1; split; eauto. repeat split; auto.
    contradict H2; split; eauto. ord.
  }
Qed.

Lemma nColOpRs_1 :
  forall (a b : Ray),
  ![ a # b ]
    -> ![ !a # b ].
Proof.
  intros a b diab.
  assert (Exc : { c : Ray | a == !c }). { exists (!a). apply OpOpRs. }
  destruct Exc as [ c aopc ].
  assert (copa : !a == c). { rewrite aopc. symmetry. apply OpOpRs. }
  apply nColRs_nColPs in diab.
  apply nColRs_nColPs.
  destruct diab as [ orab [ naeqb naopb ]].
  repeat split.
  { rewrite <- orab. symmetry. apply OpRays_0. }
  { contradict naopb. rewrite <- naopb in *. apply OpOpRs. }
  { contradict naeqb. rewrite copa in *. rewrite aopc. symmetry.
    rewrite naeqb. apply OpOpRs.
  }
Qed.
Lemma nColOpRs_2 :
  forall (a b : Ray),
  ![ a # b ]
    -> ![ a # !b ].
Proof.
  intros [ O A nAeqO ][ O' B nBeqO ][ roab diab ]; simpl in *.
  subst O'.
  unfold OpRay, EqRays in *; simpl.
  destruct (DrawOppositePoint O B) as [ B' [ BetBOB' _ ]]...
  destruct (BetPs_3DiPs B O B' BetBOB') as [ _ [ nOeqB' _ ]]; simpl.
  split; simpl; auto.
  contradict diab.
  destruct diab as [ x [ Aox [ Oox B'ox ]]].
  exists x; repeat split; incpt 2.
Qed.
Lemma nColOpRs_3 :
  forall (a b : Ray),
  ![ a # b ]
    -> ![ !b # a ].
Proof.
  intros a b diab.
  apply nColRs_sym.
  apply nColOpRs_2; auto.
Qed.
Lemma nColOpRs_4 :
  forall (a b : Ray),
  ![ a # b ]
    -> ![ b # !a ].
Proof.
  intros a b diab.
  apply nColRs_sym.
  apply nColOpRs_1; auto.
Qed.
Global Instance nCol_OpRs :
  Proper (nColRs ==> nColRs) OpRay.
Proof.
  intros a b ab.
  apply nColOpRs_1.
  apply nColOpRs_2.
  assumption.
Qed.

Lemma nColRs_nColOpRs :
  forall (a b c d : Ray),
  a == !c
    -> b == !d
    -> ![ a # b ]
    -> ![ c # d ].
Proof.
  intros * aopc bopd diab.
  apply (nColOpRs_1 a b) in diab.
  apply (nColOpRs_2 (!a) b) in diab.
  apply (nColRs_inv (!a)(!b) d) in diab. apply nColRs_sym in diab.
  apply (nColRs_inv d (!a) c) in diab. apply nColRs_sym; auto.
  apply OpRs_sym in aopc. rewrite aopc; reflexivity.
  apply OpRs_sym in bopd. rewrite bopd; reflexivity.
Qed.

Definition DecideCollinearRays :
  forall (a b : Ray)(roab : da a = da b),
  ~ (![ a # b ])
    -> { a == b } + { a == !b }.
Proof with eauto.
  unfold OpRay, EqRays, nColRs; simpl.
  intros [ O A nOeqA ][ O' B nOeqB ] orab ndiab.
  simpl in *; subst O'.
  destruct (DrawOppositePoint O B nOeqB) as [ C [ BetAOB H ]].
  destruct (BetPs_3DiPs B O C BetAOB) as [ nBeqO [ nOeqC nBeqC ]]; simpl.
  assert (ColAOB : [A, O, B]). { tauto. }
  destruct (LineSeparation O B C A) as [[ H1 H2 ]|[ H3 H4 ]]; colperps.
  { left. split... apply SR_sym... }
  { right. split... apply SR_sym... }
Defined.

(* Ray direction *)

Definition EqRaysDir (a b : Ray) : Prop
  := (da a = da b /\ [ da a # db a, db b ])
  \/ ([ da a # da b, db a ] /\ [ da a # da b # db b ])
  \/ ([ da b # da a, db b ] /\ [ da b # da a # db a ]).

Notation " a ~~ b "
  := (EqRaysDir a b)
  (at level 60).
Notation " a ~/~ b "
  := (~ EqRaysDir a b)
  (at level 60).

Lemma EqRaysDir_refl :
  reflexive Ray EqRaysDir.
Proof.
  unfold reflexive.
  intros [ O A nAeqO ].
  unfold EqRaysDir.
  left; split; simpl; auto.
  apply SR_refl; auto.
Qed.
Lemma EqRaysDir_sym :
  symmetric Ray EqRaysDir.
Proof.
  unfold symmetric.
  intros [ O A nAeqO ][ O' B nBeqO ].
  unfold EqRaysDir; simpl.
  intros [[ OeqO' OsrAA' ]|[[ OsrO'A BetOO'A' ]|[ O'srOA' BetO'OA ]]].
  { subst O'. left; split; auto. apply SR_sym; auto. }
  { right. right. split; auto. }
  { right. left. split; auto. }
Qed.
Lemma EqRaysDir_trans :
  transitive Ray EqRaysDir.
Proof with eauto.
  unfold transitive.
  intros [ O A nAeqO ][ O' A' nA'eqO ][ O'' A'' nA''eqO ].
  unfold EqRaysDir; simpl.
  intros [[ OeqO' OAA' ]|[[ OO'A OO'A' ]|[ O'OA' O'OA ]]]
    [[ O'eqO'' O'A'A'' ]|[[ O'O''A' O'O''A'' ]|[ O''O'A'' O''O'A' ]]];
    try subst O''; try subst O'.
  { left; split... apply (SR_trans O A A' A'')... }
  { right; left; split...
    apply SR_sym in OAA'. apply (SR_trans O O'' A' A)...
  }
  { right; right; split...
    apply SR_sym in OAA'. apply (BetPs_SR_BetPs O O'' A' A)...
  }
  { right; left; split...
    apply (BetPs_SR_BetPs O' O A' A'')...
  }
  { right; left.
    assert (BetOO'O'' : [O # O' # O'']).
    { apply SR_sym in O'O''A'. apply (BetPs_SR_BetPs O' O A' O'')... }
    split.
    { apply (SR_trans O O'' O' A)... apply SR_sym.
      apply BetPs_SR. apply BetPs_sym...
    }
    { apply (BetPs_b_trans O O' O'' A'')... }
  }
  { assert (O'OO'' : [O' # O, O'']).
    { apply BetPs_sym in OO'A'. apply BetPs_sym in O''O'A'.
      apply (BetPs_BetPs_SR O' A' O O'')...
    }
    apply (SR_BetPs O' O O'') in O'OO''.
    destruct O'OO'' as [ O'OO'' |[[ OeqO'' nOeqO' ]| O'O''O ]].
    { apply BetPs_sym in O'OO''.
      right; right; split.
      { apply BetPs_SR in O'OO''.
        destruct O'OO'' as [ O''OO' _ ].
        apply (SR_trans O'' O O' A'')...
      }
      { apply (BetPs_SR_BetPs O O'' O' A)... }
    }
    { left; subst O''; split...
      apply SR_sym in OO'A.
      apply (SR_trans O A O' A'')...
    }
    { apply BetPs_sym in O'O''O. right; left; split.
      { apply BetPs_SR in O'O''O.
        destruct O'O''O as [ OO''O' O'O''O ].
        apply (SR_trans O O'' O' A)...
      }
      { apply (BetPs_SR_BetPs O'' O O' A'')... }
    }
  }
  { right; right; split... apply (SR_trans O' O A' A'')... }
  { assert (O'OO'' : [O' # O, O'']).
    { apply SR_sym in O'O''A'.
      apply (SR_trans O' O A' O'')...
    }
    apply (SR_BetPs O' O O'') in O'OO''.
    destruct O'OO'' as [ O'OO'' |[[ OeqO'' nOeqO' ]| O'O''O ]].
    { right; left; split.
      apply (BetPs_BetPs_SR O O' O'' A)...
      apply BetPs_sym in O'OO''. apply BetPs_sym in O'O''A''.
      apply BetPs_sym. apply (BetPs_a_trans A'' O'' O O')...
    }
    { left; subst O''; split...
      apply (BetPs_BetPs_SR O O' A A'')...
    }
    { right; right; split.
      apply (BetPs_BetPs_SR O'' O' O A'')...
      apply BetPs_sym in O'OA. apply BetPs_sym in O'O''O.
      apply BetPs_sym. apply (BetPs_a_trans A O O'' O')...
    }
  }
  { right; right.
    assert (O''O'O : [O''# O'# O]).
    { apply SR_sym in O'OA'. apply (BetPs_SR_BetPs O' O'' A' O)... }
    split.
    { apply (BetPs_SR O'' O' O) in O''O'O...
      destruct O''O'O as [ O''O'O _ ].
      apply SR_sym in O''O'O. apply (SR_trans O'' O O' A'')...
    }
    { apply (BetPs_b_trans O'' O' O A)... }
  }
Qed.

(** Theorem #19 *)
Global Instance RayDir_equiv :
  Equivalence EqRaysDir
  := Build_Equivalence EqRaysDir
     EqRaysDir_refl
     EqRaysDir_sym
     EqRaysDir_trans.

Lemma nOpRsDir :
  forall (a : Ray),
  ~ (a ~~ !a).
Proof with eauto.
  intros [ O A nOeqA ][[ _ H2 ]|[[ H1 H2 ]|[ H1 H2 ]]];
  unfold OpRay in *; simpl in *;
  destruct (DrawOppositePoint O A nOeqA) as [ B [ BetAOB H ]];
  destruct (BetPs_3DiPs A O B BetAOB) as [ nAeqO [ nOeqB nAeqB ]]; simpl in *.
  { destruct H2 as [ H1 [ H2 [ H3 H4 ]]]; contradiction. }
  { apply BetPs_DiPs_1 in H2. contradict H2... }
  { apply BetPs_DiPs_1 in H2. contradict H2... }
Qed.

Lemma EqRsDir_EqRs :
  forall (a b : Ray),
  da a = da b
    -> a ~~ b
    -> a == b.
Proof.
  intros a b roab [ H1 | H3 ]; split; auto; destruct roab; firstorder.
Qed.

Lemma EqRs_EqRsDir :
  forall (a b : Ray),
  a == b
    -> a ~~ b.
Proof.
  intros a b [ roab aeqb ]; left; split; auto.
Qed.

Lemma DiRsDir_sym :
  forall a b : Ray,
  a ~/~ b
    -> b ~/~ a.
Proof.
  intros a b naeqb; contradict naeqb; symmetry; trivial.
Qed.

Lemma EqDirOpOpRs :
  forall (a : Ray),
  a ~~ !(!a).
Proof with simpl; auto.
  intros [ O A nAeqO ]; unfold OpRay, EqRaysDir in *...
  destruct (DrawOppositePoint O A) as [ A' [ BetAOA' _ ]]...
  destruct (BetPs_3DiPs A O A' BetAOA') as [ _ [ nOeqA' nAeqA' ]]...
  destruct (DrawOppositePoint O A') as [ A'' [ BetA'OA'' _ ]]...
  destruct (BetPs_3DiPs A' O A'' BetA'OA'') as [ _ [ nOeqA'' nA'eqA'' ]]...
  left; split...
  apply BetPs_sym in BetAOA'.
  apply (BetPs_BetPs_SR O A' A A'')...
Qed.

Lemma EqDirOpRs_irrefl :
  forall (a : Ray),
  a ~/~ !a.
Proof.
  intros [ O A nAeqO ] EqOp; unfold OpRay, EqRaysDir in *; simpl in *.
  destruct (DrawOppositePoint O A) as [ A' [ BetAOA' _ ]]; auto.
  destruct (BetPs_3DiPs A O A' BetAOA') as [ _ [ nOeqA' nAeqA' ]].
  simpl in *.
  destruct EqOp as [[ _ OsrAA' ]|[[ OsrOA _ ]|[ OsrOA _ ]]].
  { firstorder. }
  { destruct OsrOA as [ nOeqO _ ]; auto. }
  { destruct OsrOA as [ nOeqO _ ]; auto. }
Qed.

Lemma EqDirRs_ColRs :
  forall (a b : Ray),
  a ~~ b
    -> ![ a, b ].
Proof with inc.
  intros a b [ H1 |[[ OsrO'A BetOO'B ]|[ O'srOB BetO'OA ]]].
  destruct H1 as [ orab [ _ [ _ [[ x [ Oox [ Aox Box ]]] _ ]]]].
  exists x; repeat split...
  destruct OsrO'A as [ _ [ _ [[ x [ Oox [ O'ox Aox ]]] _ ]]].
  exists x; repeat split; auto.
  apply (BetPs_IncPt (da a)(da b)(db b) x)...
  destruct O'srOB as [ _ [ _ [[ x [ O'ox [ Oox Box ]]] _ ]]].
  exists x; repeat split; auto.
  apply (BetPs_IncPt (da b)(da a)(db a) x)...
Qed.

(** Problem #17 *)
Definition DecideRayDirection :
  forall (a b : Ray),
  ![ a, b ]
    -> { a ~~ b } + { a ~/~ b }.
Proof with eauto.
  intros [ O A nOeqA ][ O' A' nO'eqA' ] Colab.
  unfold EqRaysDir in *; simpl in *.
  destruct (DrawExtensionLinePP O A nOeqA) as [ x [ Oox Aox ]].
  assert (A'ox : [ A' @ x ]).
  { destruct Colab as [ y [ Ooy [ Aoy [ O'oy A'oy ]]]].
    assert (xeqy : x = y). { apply (DiPs_EqLs O A x y); firstorder. }
    subst y...
  }
  assert (O'ox : [ O' @ x ]).
  { destruct Colab as [ y [ Ooy [ Aoy [ O'oy A'oy ]]]].
    assert (xeqy : x = y). { apply (DiPs_EqLs O A x y); firstorder. }
    subst y...
  }
  destruct (DrawBoundaryPoints O O' x)
    as [ L [ R [ Lox [ Rox [ BetLOR BetLO'R ]]]]]...
  assert (nReqO : R <> O); dips.
  assert (ColOAR : [O, A, R]). { exists x; split... }
  assert (nReqO' : R <> O'); dips.
  assert (ColO'A'R : [O', A', R]). { exists x; split... }
  destruct (DecidePointsOnSameRay O A R) as [ OsrAR | BetAOR ]...
  { destruct (DecidePointsOnSameRay O' A' R) as [ O'srA'R | BetA'O'R ]...
    { left.
      destruct (classic (O = O')) as [ OeqO' | nOeqO' ].
      { left. split...
        subst O'. apply (SR_trans O A R A')... apply SR_sym...
      }
      { right.
        assert (ColOO'R : [O, O', R]). { exists x; split... }
        destruct (DecidePointsOnSameRay O O' R) as [ OsrO'R | BetO'OR ]...
        { left; split.
          { apply (SR_trans O O' R A)... apply SR_sym... }
          { assert (BetOO'R : [ O # O' # R ]).
            { apply BetPs_SR. split...
              apply BetPs_SR in BetLOR. destruct BetLOR as [ _ RslOL ].
              apply BetPs_SR in BetLO'R. destruct BetLO'R as [ _ RsrO'L ].
              apply (SR_trans R O' L O)... apply SR_sym...
            }
            apply (BetPs_SR_BetPs O' O R A')... apply SR_sym...
          }
        }
        { right; split.
          { apply (SR_trans O' O R A')...
            apply BetPs_SR.
            apply BetPs_sym...
            apply SR_sym...
          }
          { apply (BetPs_SR_BetPs O O' R A)... apply SR_sym... }
        }
      }
    }
    { right.
      intros [[ OeqO' OsrAA' ]
             |[[ OsrO'A BetOO'A' ]
             |[ O'srOA' BetO'OA ]]].
      { subst O'. apply SR_sym in OsrAA'.
        apply (SR_trans O A' A R) in OsrAR; firstorder.
      }
      { apply (SR_trans O O' A R) in OsrAR...
        apply BetPs_sym in BetOO'A'.
        apply (BetPs_BetPs_SR O' A' R O) in BetOO'A'...
        assert (BetORO' : [ O # R # O' ]).
        { apply BetPs_SR. split... apply SR_sym... }
        assert (RsrOO' : [ R # O, O' ]).
        { apply BetPs_SR in BetLOR.
          destruct BetLOR as [ _ RsrOL ].
          apply BetPs_SR in BetLO'R.
          destruct BetLO'R as [ _ RsrO'L ].
          apply SR_sym in RsrO'L.
          apply (SR_trans R O L O')...
        }
        { firstorder. }
      }
      { assert (BetO'OR : [ O' # O # R ]).
        { apply (BetPs_inv O O' A O' R)... apply SR_refl; dips. }
        assert (BetOO'R : [ O # O' # R ]).
        { apply BetPs_sym. apply BetPs_sym in BetA'O'R.
          apply (BetPs_inv O' R A' R O)... apply SR_refl; dips.
          apply SR_sym...
        }
        apply BetPs_nBetPerPs in BetOO'R; firstorder.
      }
    }
  }
  { destruct (DecidePointsOnSameRay O' A' R) as [ O'srA'R | BetA'O'R ]...
    { right.
      intros [[ OeqO' OsrAA' ]
             |[[ OsrO'A BetOO'A' ]
             |[ O'srOA' BetO'OA ]]].
      { subst O'. apply (SR_trans O A A' R) in O'srA'R... firstorder. }
      { assert (BetOO'R : [ O # O' # R ]).
        { apply (BetPs_inv O' O A' O R)... apply SR_refl; dips. }
        assert (BetO'OR : [ O' # O # R ]).
        { apply BetPs_sym. apply BetPs_sym in BetAOR.
          apply (BetPs_inv O R A R O')... apply SR_refl; dips.
          apply SR_sym...
        }
        apply BetPs_nBetPerPs in BetO'OR; firstorder.
      }
      { apply (SR_trans O' O A' R) in O'srA'R...
        apply BetPs_sym in BetO'OA.
        apply (BetPs_BetPs_SR O A R O') in BetO'OA...
        assert (BetO'RO : [ O' # R # O ]).
        { apply BetPs_SR. split... apply SR_sym... }
        assert (RsrO'O : [ R # O', O ]).
        { apply BetPs_SR in BetLO'R.
          destruct BetLO'R as [ _ RsrO'L ].
          apply BetPs_SR in BetLOR.
          destruct BetLOR as [ _ RsrOL ].
          apply SR_sym in RsrOL.
          apply (SR_trans R O' L O)...
        }
        { firstorder. }
      }
    }
    { left.
      destruct (classic (O =O')) as [ OeqO' | nOeqO' ].
      { left. split...
        subst O'.
        apply BetPs_sym in BetAOR.
        apply BetPs_sym in BetA'O'R.
        apply (BetPs_BetPs_SR O R A A')...
      }
      { right.
        assert (ColOO'R : [O, O', R]). { exists x; split... }
        destruct (DecidePointsOnSameRay O O' R) as [ OsrO'R | BetO'OR ]...
        { right.
          assert (BetOO'R : [ O # O' # R ]).
          { apply BetPs_SR. split...
            apply BetPs_SR in BetLO'R. destruct BetLO'R as [ _ RslO'L ].
            apply BetPs_SR in BetLOR. destruct BetLOR as [ _ RsrOL ].
            apply (SR_trans R O' L O)... apply SR_sym...
          }
          assert (BetO'OA : [ O' # O # A ]).
          { apply BetPs_sym. apply (BetPs_a_trans A O O' R)... }
          split...
          apply BetPs_sym in BetA'O'R.
          apply BetPs_sym in BetOO'R.
          apply (BetPs_BetPs_SR O' R O A')...
        }
        { left; split.
          { apply BetPs_sym in BetAOR.
            apply BetPs_sym in BetO'OR.
            apply (BetPs_BetPs_SR O R O' A)...
          }
          { apply BetPs_sym. apply (BetPs_a_trans A' O' O R)... }
        }
      }
    }
  }
Defined.

(** Theorem #20 *)
Lemma ColRs_DiDirRs_EqDirOpRs :
  forall (a b : Ray),
  ![ a, b ]
    -> (a ~/~ b <-> a ~~ !b).
Proof with eauto.
  intros a b Colab.
  split.
  { intros H.
    destruct a as [ O A nAeqO ].
    destruct b as [ O' A' nA'eqO' ].
    unfold OpRay, EqRaysDir in *; simpl in *.
    assert (H1 : ~ (O = O' /\ [ O # A, A'])).
    { contradict H. left... }
    assert (H2 : ~ ([ O # O', A] /\ [ O # O' # A'])).
    { contradict H. right; left... }
    assert (H3 : ~ ([ O' # O, A'] /\ [ O' # O # A])).
    { contradict H. right; right... }
    clear H.
    destruct (DrawOppositePoint O' A') as [ B' [ BetA'O'B' _ ]]...
    destruct (BetPs_3DiPs A' O' B') as [ _ [ nO'eqB' nAeqB' ]]...
    simpl in *.
    destruct (DrawExtensionLinePP A O) as [ x [ Aox Oox ]]...
    assert (A'ox : [ A' @ x ]).
    { destruct Colab as [ y [ Ooy [ Aoy [ O'oy A'oy ]]]].
      assert (xeqy : x = y). { apply (DiPs_EqLs O A x y); firstorder. }
      subst y...
    }
    assert (O'ox : [ O' @ x ]).
    { destruct Colab as [ y [ Ooy [ Aoy [ O'oy A'oy ]]]].
      assert (xeqy : x = y). { apply (DiPs_EqLs O A x y); firstorder. }
      subst y...
    }
    assert (B'ox : [ B' @ x ]); incpt 2.
    destruct (classic (O = O')) as [ OeqO' | nOeqO' ].
    { left. split...
      subst O'.
      apply (BetPs_BetPs_SR O A' A B')... apply BetPs_sym.
      assert (nOsrAA' : ~ [ O # A, A']). { contradict H1. split... }
      destruct (DecidePointsOnSameRay O A A') as [ OsrAA' | BetAOA' ]...
      contradiction.
    }
    { right.
      destruct (DecidePointsOnSameRay O O' A) as [ OsrO'A | BetO'OA ]...
      { left; split...
        assert (nBetOO'A' : ~ [ O # O' # A']). { contradict H2. split... }
        assert (BetO'OA' : [ O' # O, A' ]). { repeat split; inc. }
        destruct OsrO'A.
        apply (BetPs_inv O' A' B' O B')...
        apply SR_sym... apply SR_refl. dips.
      }
      { destruct (DecidePointsOnSameRay O' O A') as [ O'srOA' | BetOO'A' ]...
        { right. split...
          assert (nO'srOA' : ~ ([ O' # O, A'])). { contradict H3. split... }
          contradiction.
        }
        { right; split...
          apply BetPs_sym in BetOO'A'.
          apply (BetPs_BetPs_SR O' A' O B')...
        }
      }
    }
  }
  { intros aedob aedb.
    rewrite aedb in aedob.
    apply (EqDirOpRs_irrefl b)...
  }
Qed.

(** Theorem #21 *)
Global Instance OpRaysDir_compat :
  Proper (EqRaysDir ==> EqRaysDir) OpRay.
Proof with eauto.
  intros [ O A nAeqO ][ O' B nBeqO ] H.
  unfold EqRaysDir, OpRay; simpl in *.
  destruct (DrawOppositePoint O A) as [ A' [ BetAOA' _ ]]...
  destruct (BetPs_3DiPs A O A' BetAOA') as [ _ [ nOeqA' nAeqA' ]].
  destruct (DrawOppositePoint O' B) as [ B' [ BetBOB' _ ]]...
  destruct (BetPs_3DiPs B O' B') as [ _ [ nOeqB' nBeqB' ]]... simpl in *.
  destruct H as [[ OeqO' OAB ]|[[ OO'A OO'B ]|[ O'OB O'OA ]]];
  simpl in *; try subst O'.
  { left; simpl; split...
    apply (SR_inv O A A' B B')...
  }
  { right; right; split.
    { apply BetPs_sym in OO'B.
      apply (BetPs_BetPs_SR O' B O B')...
    }
    { apply (BetPs_inv O A A' O' A')...
      apply SR_sym... apply SR_refl...
    }
  }
  { right; left; split.
    { apply BetPs_sym in O'OA.
      apply (BetPs_BetPs_SR O A O' A')...
    }
    { apply (BetPs_inv O' B B' O B')...
      apply SR_sym... apply SR_refl...
    }
  }
Qed.

Lemma EqDirOpRs_sym :
  forall (a b : Ray),
  a ~~ !b
    -> b ~~ !a.
Proof.
  intros a b aopb.
  rewrite aopb.
  apply EqDirOpOpRs.
Qed.

Lemma EqDirOpRs_trans :
  forall (a b c : Ray),
  a ~~ !b
    -> b ~~ !c
    -> a ~~ c.
Proof.
  intros a b c aopb bopc.
  rewrite aopb. rewrite bopc. symmetry.
  apply EqDirOpOpRs.
Qed.

Lemma EqDirRs_EqDirOpRs :
  forall (A B A' B' : Point)(nAeqB : A <> B)(nA'eqB' : A' <> B'),
  ({{ A # B | nAeqB }} ~~ {{ A' # B' | nA'eqB' }})
    -> {{ B # A | not_eq_sym nAeqB }} ~~ {{ B' # A' | not_eq_sym nA'eqB' }}.
Proof with eauto.
  intros A B A' B' nAeqB nA'eqB' [[ H1 H2 ]|[[ H1 H2 ]|[ H1 H2 ]]];
  unfold EqRaysDir; simpl in *; try subst A'.
  { apply (SR_BetPs A B B') in H2.
    destruct H2 as [ H1 |[[ H2 H3 ]| H4 ]]; try subst B'.
    { right; right; split...
      { apply BetPs_SR in H1; tauto. }
      { apply BetPs_sym... }
    }
    { left; split... apply SR_refl; dips. }
    { right; left; split...
      { apply BetPs_SR in H4; tauto. }
      { apply BetPs_sym... }
    }
  }
  { assert (H3 : [A # B, B']).
    { apply (SR_trans A B A')...
      { apply SR_sym... }
      { apply BetPs_SR in H2; tauto. }
    }
    apply (SR_BetPs A B B') in H3.
    destruct H3 as [ H3 |[[ H0 H3 ]| H4 ]]; try subst B'.
    { right; right; split...
      { apply (SR_trans B' B A)...
        { apply BetPs_SR in H3; tauto. }
        { apply SR_sym. apply BetPs_SR in H2; tauto. }
      }
      { apply BetPs_sym... }
    }
    { left; split... apply SR_sym. apply BetPs_SR in H2; tauto. }
    { right; left; split...
      { apply BetPs_SR in H4; tauto. }
      { apply BetPs_sym... eapply BetPs_c_trans... }
    }
  }
  { assert (H3 : [A' # B, B']).
    { apply (SR_trans A' B A)...
      apply SR_sym... apply BetPs_SR in H2; tauto.
    }
    apply (SR_BetPs A' B B') in H3.
    destruct H3 as [ H3 |[[ H0 H3 ]| H4 ]]; try subst B'.
    { right; right; split...
      { apply BetPs_SR in H3; tauto. }
      { apply BetPs_sym. eapply BetPs_c_trans... }
    }
    { left; split... apply BetPs_SR in H2; tauto. }
    { right; left; split...
      { apply SR_sym. apply (SR_trans B A A')...
        { apply BetPs_SR in H2; tauto. }
        { apply SR_sym. apply BetPs_SR in H4; tauto. }
      }
      { apply BetPs_sym... }
    }
  }
Qed.

End RAY.

Hint Resolve
  OpRays_0
  OpRays_1
  OpRs_irrefl
  OpOpRs
  DiRs_sym
  OpRs_sym
  OpRs_trans
  OpRay
  OpRs_BetPs
  nColRs_inv
  nColRs_sym
  nColOpRs_1
  nColOpRs_2
  nColRs_nColOpRs
  EqRsDir_EqRs
  EqRs_EqRsDir
  DiRsDir_sym
  EqDirOpOpRs
  EqDirOpRs_irrefl
  EqDirOpRs_sym
  EqDirOpRs_trans
  EqDirRs_ColRs
  : Ray.

Notation " ! a "
  := (OpRay a)
  (at level 50).
Notation " a ~~ b "
  := (EqRaysDir a b)
  (at level 60).
Notation " a ~/~ b "
  := (~ EqRaysDir a b)
  (at level 60).

(*****************************************************************************)
(* 8 *) Section ORDER.
Context `{ cr : Circles }.
(*****************************************************************************)

Definition SameSideRays (a b c : Ray) : Prop
  := da a = da b /\ da a = da c /\ ([ da a # db a | db b, db c ]).
Notation " ![ a # b , c ] "
  := (SameSideRays a b c)
  (at level 60).

Definition BetRs (a b c : Ray) : Prop
  := da a = da b /\ da b = da c /\ [ da a | db a; db b; db c ].
Notation " ![ a # b # c ] "
  := (BetRs a b c)
  (at level 60).
Notation " ![ a ; b # c ] "
  := (![ a # b # c ] \/ (a == b /\ ![ b # c ]))
  (at level 60).
Notation " ![ a # b ; c ] "
  := (![ a # b # c ] \/ (![ a # b ] /\ b == c))
  (at level 60).
Notation " ![ a ; b ; c ] "
  := (![ a # b # c ] \/ (a == b /\ b <=/=> c) \/ (a <=/=> b /\ b == c))
  (at level 60).
Notation " ![ a # b # c # d ] "
  := (![ a # b # c ] /\ ![ a # b # d ] /\ ![ a # c # d ] /\ ![ b # c # d ])
  (at level 60).

Lemma SameSideRs_inv :
  forall (a b c a' b' c' : Ray),
  a == a'
    -> b == b'
    -> c == c'
    -> ![ a # b, c ]
    -> ![ a' # b', c' ].
Proof with eauto.
  intros a b c a' b' c' aeqa' beqb' ceqc' aSFbc.
  destruct aeqa' as [ roaa' OsrAA' ].
  destruct beqb' as [ robb' OsrBB' ].
  destruct ceqc' as [ rocc' OsrCC' ].
  destruct aSFbc as [ roab [ roac SF ]].
  unfold SameSideRays.
  destruct robb', rocc', roab, roac; auto.
  do 2 try split...
  rewrite roaa' in *.
  apply (SHa_inv (da a')(db a)(db b)(db c)(db a')(db b')(db c'))...
  { apply (dp a'). }
  { colper. }
Qed.

(** Theorem #22 *)
Lemma SameSideRs_refl :
  forall (a b : Ray),
  ![ a # b ]
    -> ![ a # b, b ].
Proof with eauto.
  intros a b [ roab diab ].
  do 2 try split...
  destruct (DrawExtensionLinePP (da a)(db a)(dp a))
    as [ x [ Oox Aox ]].
  split...
  { apply (dp a). }
  { exists x; do 2 try split...
    apply SS_refl.
    contradict diab.
    exists x.
    repeat split; auto.
  }
Qed.
Lemma SameSideRs_sym :
  forall (a b c : Ray),
  ![ a # b, c ]
    -> ![ a # c, b ].
Proof with eauto.
  intros a b c [ roab [ roac [ nroOeqA [ x [ Oox [ Aox SSxBC ]]]]]].
  repeat split...
  exists x.
  do 2 try split...
  apply (SS_sym (db b)(db c) x)...
Qed.
Lemma SameSideRs_trans :
  forall (a b c d : Ray),
  ![ a # b, c ]
    -> ![ a # c, d ]
    -> ![ a # b, d ].
Proof with eauto.
  intros a b c d [ roab [ roac [ nOeqA [ x [ Oox [ Aox SSxBC ]]]]]]
                 [ _ [ road [ _ [ x' [ Oox' [ Aox' SSxCD ]]]]]].
  assert (xeqx' : x = x'); eqls.
  subst x'.
  do 3 try split...
  exists x.
  do 2 try split...
  apply (SS_trans (db b)(db c)(db d) x)...
Qed.

Lemma SameSideRs_nColRs :
  forall (a b c : Ray),
  ![ a # b, c ]
    -> ![ a # b ] /\ ![ a # c ].
Proof with ncolps.
  intros a b c [ roab [ roac H ]].
  destruct H as [ nroOeqA [ x [ Oox [ Aox [ nBox [ nCox SSxBC ]]]]]].
  do 2 split...
Qed.

(** Theorem #23 *)
Lemma OppositeSideRs_irrefl :
  forall (a b : Ray),
  ~ ![ a # b, !b ].
Proof with eauto.
  intros b a [ roab [ roba aba ]].
  unfold OpRay in *.
  destruct (DrawOpRay a) as [ c aopb ]; simpl in *.
  destruct a as [ O A nOeqA ]; destruct b as [ O' B nOeqB ];
  destruct c as [ O'' C nOeqC ]; simpl in *. subst O'' O'.
  destruct aopb as [ _ H2 ]; simpl in *. apply SHb_sym in aba.
  apply (OHO_trans O B A C A) in aba.
  apply OH_DiPs_2 in aba. contradiction.
  repeat split...
  destruct aba as [ _ [ x [ Oox [ Box H ]]]].
  exists x; repeat split; destruct H as [ nCox [ nAox _ ]]...
Qed.

(** Theorem #24 *)
Lemma SameSideRs_OpRs :
  forall (a b c : Ray),
  ![ a # b, c ]
    -> ![ a # !b, !c ].
Proof with eauto.
  intros [ O A nAeqO ][ O' B nBeqO ][ O'' C nCeqO ] H.
  destruct H as [ roab [ roac [ nroOeqA [ x [ Oox [ Aox SSxBC ]]]]]];
  unfold OpRay in *; simpl in *.
  destruct (DrawOppositePoint O' B nBeqO) as [ B' [ BetBOB' H1 ]].
  destruct (DrawOppositePoint O'' C nCeqO) as [ C' [ BetCOC' H2 ]].
  destruct (BetPs_3DiPs B O' B' BetBOB') as [ _ [ nOeqB' nBeqB' ]];
  destruct (BetPs_3DiPs C O'' C' BetCOC') as [ _ [ nOeqC' nCeqC' ]];
  subst O'; simpl in *. subst O''.
  repeat split; simpl...
  exists x; simpl in *; do 2 try split...
  assert (nBox : ~ [B @ x]). { destruct SSxBC... }
  assert (nB'ox : ~ [B' @ x]).
  { contradict nBox. apply (BetPs_IncPt B' O B x); tauto. }
  assert (nCox : ~ [C @ x]). { destruct SSxBC as [ _ [ H _ ]]... }
  assert (nC'ox : ~ [C' @ x]).
  { contradict nCox. apply (BetPs_IncPt C' O C x); tauto. }
  eapply OOS_trans with B...
  { apply OS_sym... repeat split... }
  { apply OS_sym. eapply OSO_trans with C...
    { repeat split... exists O; split... apply BetPs_sym... }
    { apply SS_sym... }
  }
Qed.

Lemma OppositeSideRs_inv :
  forall (a b c a' b' c' : Ray),
  a == a'
    -> b == b'
    -> c == c'
    -> ![ b # c, !a ]
    -> ![ b' # c', !a' ].
Proof with eauto.
  intros * aeqa beqb ceqc bca.
  eapply SameSideRs_inv...
  rewrite aeqa; reflexivity.
Qed.

Lemma SameSideRs_OpRs_inv :
  forall (a b c : Ray),
  ![ a # b, c ]
    <-> ![ !a # b, c ].
Proof with eauto.
  intros [ O A nAeqO ][ O' B nBeqO ][ O'' C nCeqO ].
  unfold OpRay; simpl in *.
  destruct (DrawOppositePoint O A) as [ A' [ BetAOA' _ ]]...
  destruct (BetPs_3DiPs A O A' BetAOA') as [ _ [ nOeqA' nAeqA' ]].
  split;
  intros [ O'eqO [ O'eqO'' [ _ [ x [ Oox [ Aox SSxBC ]]]]]];
  simpl in *; subst O'' O'; repeat split; simpl; eauto;
  exists x; do 2 try split; incpt 2.
Qed.

(** Problem #18 *)
Example DecideRaysSide :
  forall (a b c : Ray),
  ![ a # b ]
    -> ![ a # c ]
    -> { ![ a # b, c ] } + { ![ a # c, !b ] }.
Proof with eauto.
  intros [ O A nAeqO ][ O' B nBeqO ][ O'' C nCeqO ] diab diac.
  destruct diab as [ roab diab ].
  destruct diac as [ roac diac ].
  simpl in *. subst O'' O'.
  destruct (DrawExtensionLinePP A O) as [ x [ Oox Aox ]]...
  assert (nBox : ~ [ B @ x ]); nincpt.
  assert (nCox : ~ [ C @ x ]); nincpt.
  destruct (DecideSameSide B C x) as [ SF | nSF ];
  eauto; [ left | right ]; repeat split; simpl in *...
  { rewrite <- OpRays_0; simpl... }
  { exists x. do 2 try split...
    unfold OpRay.
    destruct (DrawOpRay ({{O # B | nBeqO}}))
      as [[ O' D nOeqD ][ OeqO' H ]]; simpl in *. subst O'.
    eapply OOS_trans. apply OS_sym. apply nSF.
    repeat split... contradict nBox. incpt 2.
  }
Defined.

(** Theorem #25 *)
Lemma nSameAndOppositeSideRs :
  forall (a b c : Ray),
  ~ (![ a # b, c ] /\ ![ a # c, !b ]).
Proof with eauto.
  intros [ O A nAeqO ][ O' B nBeqO ][ O'' C nCeqO ].
  intros [ H1 H2 ].
  destruct H1 as [ OeqO' [ OeqO'' [ _ [ x [ Oox [ Aox SSxBC ]]]]]].
  destruct H2 as [ _ [ _ [ _ [ y [ Ooy [ Aoy OSyBC ]]]]]].
  simpl in *; subst O' O''.
  assert (xeqy : x = y); eqls.
  subst.
  unfold OpRay in *.
  destruct (DrawOpRay ({{O # B | nBeqO}}))
    as [[ O' D nOeqD ][ OeqO' H ]]; simpl in *. subst O'.
  apply (SS_trans B C D y) in OSyBC...
  destruct OSyBC as [ nBoy [ nDoy H1]].
  contradict H1. exists O; repeat split...
Qed.

Lemma nSameSideRs_OppositeSideRs :
  forall (a b c : Ray),
  ![ a # b ]
    -> ![ a # c ]
    -> (~ ![ a # b, c ] <-> ![ a # c, !b ]).
Proof with eauto.
  intros a b c diab diac.
  split.
  { intros nSF.
    destruct (DecideRaysSide a b c diab diac) as [ SF | OF ]...
    contradiction.
  }
  { intros OF SF.
    apply (nSameAndOppositeSideRs a b c).
    split...
  }
Qed.

Lemma OOS_SideRs_trans :
  forall (a b c d : Ray),
  ![ b # c, !a ]
    -> ![ b # d, !a ]
    -> ![ b # c, d ].
Proof with eauto.
  intros * bca bda.
  apply SameSideRs_trans with (!a)...
  apply SameSideRs_sym...
Qed.

Lemma OSO_SideRs_trans :
  forall (a b c d : Ray),
  ![ b # c, !a ]
    -> ![ b # c, d ]
    -> ![ b # d, !a ].
Proof with eauto.
  intros * bca bcd.
  apply SameSideRs_trans with c...
  apply SameSideRs_sym...
Qed.

Lemma OpRs_OppositeSideRs :
  forall (a b : Ray),
  ![ a # b ]
    -> ![ b # !a, !a ].
Proof with eauto.
  intros * diab.
  apply SameSideRs_refl...
  apply nColOpRs_2...
  apply nColRs_sym...
Qed.

Lemma OppositeSideRs_sym :
  forall (a b c : Ray),
  ![ b # c, !a ]
    -> ![ b # a, !c ].
Proof with eauto.
  intros [ O'' C nCeqO ][ O A nAeqO ][ O' B nBeqO ] H.
  apply SameSideRs_sym.
  destruct H as [ roab [ roac [ nroOeqA [ x [ Oox [ Aox SSxBC ]]]]]].
  unfold OpRay in *; simpl in *.
  destruct (DrawOppositePoint O' B nBeqO) as [ B' [ BetBOB' H1 ]].
  destruct (DrawOppositePoint O'' C nCeqO) as [ C' [ BetCOC' H2 ]].
  destruct (BetPs_3DiPs B O' B' BetBOB') as [ _ [ nOeqB' nBeqB' ]];
  destruct (BetPs_3DiPs C O'' C' BetCOC') as [ _ [ nOeqC' nCeqC' ]];
  subst O'; simpl in *. subst O''.
  repeat split...
  assert (nBox : ~ [B @ x]). { destruct SSxBC... }
  assert (nC'ox : ~ [C' @ x]). { destruct SSxBC as [ H3 [ H4 _ ]]... }
  exists x; simpl in *.
  do 2 try split...
  eapply OOS_trans with B...
  { apply OS_sym.
    repeat split...
    { contradict nBox; incpt 2. }
  }
  { apply OS_sym. eapply OSO_trans with C'...
    repeat split...
    { contradict nC'ox; incpt 2. }
    { apply SS_sym... }
  }
Qed.

Lemma OppositeSideRs_nColRs :
  forall (a b c : Ray),
  ![ a # c, !b ]
    -> ![ a # b ] /\ ![ a # c ].
Proof with ncolps.
  intros a b c [ roab [ roac H ]].
  destruct H as [ nOeqA [ x [ Oox [ Aox [ nBox [ nCox SSxBC ]]]]]].
  do 2 split...
  { rewrite roac. symmetry. apply OpRays_0. }
  { assert (bopb : [db b # da b # db (!b)]). { apply (OpRays_1 b). }
    contradict nCox.
    destruct nCox as [ x' [ Aox' [ Oox' Box ]]].
    assert (xeqx' : x = x'); eqls. subst x'.
    eapply BetPs_IncPt; try split...
    assert (dd : da b = da (!b)). { apply (OpRays_0 b). }
    rewrite dd. rewrite <- roac...
  }
Qed.

Lemma BetRs_SameSideRs :
  forall (a b c : Ray),
  ![ a # b # c ]
    <-> ![ a # b, c ] /\ ![ c # b, a ].
Proof with eauto.
  intros a b c.
  split.
  { intros [ roab [ robc [ aSFbc cSFba ]]].
    split.
    { split... destruct roab. split... }
    { split... destruct robc, roab. split... }
  }
  { intros [[ roab [ roac aSFbc ]][ rocb [ roca cSFba ]]].
    split.
    { destruct roac, roab... }
    { do 2 try split... destruct roac, roab... }
  }
Qed.

(** Theorem #26 *)
Lemma BetRs_nColRs :
  forall (a b c : Ray),
  ![ a # b # c ]
    -> ![ a # b ] /\ ![ b # c ] /\ ![ a # c ].
Proof with eauto.
  intros a b c.
  case a; intros O A nAeqO.
  case b; intros O' B nBeqO.
  case c; intros O'' C nCeqO.
  intros [ roab [ robc [ OAsfCB OCsfAB ]]].
  simpl in *; subst O'' O'.
  unfold nColRs; simpl.
  repeat split; eauto.
  { apply SH_nColPs in OAsfCB; ncolperps. }
  { apply SH_nColPs in OCsfAB; ncolperps. }
  { apply SHb_sym in OAsfCB. apply SH_nColPs in OAsfCB; ncolperps. }
Qed.

Lemma BetRs_inv :
  forall (a b c a' b' c' : Ray),
  a == a'
    -> b == b'
    -> c == c'
    -> ![ a # b # c ]
    -> ![ a' # b' # c' ].
Proof with eauto.
  intros a b c a' b' c' aeqa' beqb' ceqc' BetRabc.
  apply (BetRs_SameSideRs a b c) in BetRabc.
  destruct BetRabc as [ F1 F2 ].
  apply (BetRs_SameSideRs a' b' c').
  split; eapply SameSideRs_inv...
Qed.

(** Theorem #27 *)
Theorem BetRs_sym :
  forall (a b c : Ray),
  ![ a # b # c ]
    -> ![ c # b # a ].
Proof with eauto.
  intros a b c [ roab [ robc OoABC ]].
  do 2 try split...
  destruct robc, roab.
  apply (BR_sym (da a)(db a)(db b)(db c) OoABC).
Qed.

(** Theorem #28 *)
Lemma BR_nPerBR :
  forall O A B C : Point,
  [ O | A; B; C ]
    -> ~ [ O | B; A; C ].
Proof.
  intros O A B C OoABC OoBAC.
  elim OoABC; intros H1 H2.
  destruct H1 as [ nOeqA [ x [ Oox [ Aox SSxBC ]]]].
  destruct H2 as [ nOeqC [ y [ Ooy [ Coy SSyBA ]]]].
  assert (OSxBC : [ B | x | C ]).
  { apply (BR_OS O B A C x OoBAC); firstorder. }
  destruct SSxBC as [ _ [ _ SSxBC ]].
  contradict SSxBC.
  firstorder.
Qed.
Lemma BetRs_nPerBetRs :
  forall (a b c : Ray),
  ![ a # b # c ]
    -> ~ ![ b # a # c ].
Proof.
  intros a b c [ roab [ robc BetRabc ]][ roba [ roac BetRbac ]].
  destruct roab.
  apply (BR_nPerBR (da a)(db a)(db b)(db c)); auto.
Qed.

(** Problem #19 *)
Definition DrawRayInsideAngle :
  forall (a c : Ray),
  ![ a # c ]
    -> { b : Ray | ![ a # b # c ] }.
Proof with eauto.
  intros [ O A nAeqO ][ O' C nCeqO ] diac.
  destruct diac as [ roac diac ]; simpl in *.
  subst O'.
  assert (nAeqC : A <> C); dips.
  destruct (DrawPointInsideSegment A C nAeqC) as [ B BetABC ].
  assert (nOeqB : O <> B). { contradict diac; subst; colps. }
  exists ({{ O # B | nOeqB }}).
  do 2 split...
  apply (nColPs_BetPs_BR O A B C); ncolperps.
Defined.

Lemma BetRs_PerBetRs :
  forall (a b c : Ray),
  ![ a # b # c ]
    <-> ![ b # c # !a ].
Proof with eauto.
  intros a b c.
  split.
  { intro BetRabc.
    assert (Exc : { d : Ray | a == !d }). { exists (!a). apply OpOpRs. }
    destruct Exc as [ d aopd ].
    assert (dopa : !a == d).
    { eapply OpRs_sym in aopd. apply EqRays_sym... }
    apply OpRs_OpRs in aopd. destruct aopd as [ road BetAOD ].
    destruct BetRabc as [ roab [ robc BetRabc ]].
    unfold BetRs.
    split; auto. split.
    { rewrite <- robc. rewrite <- roab. apply OpRays_0. }
    { rewrite <- roab.
      apply -> (BetPs_BR_BR (da a)(db a)(db b)(db c)(db (!a)))...
      apply (BetPs_inv (da a)(db a)(db d)(db a)(db (!a)))...
      { apply SR_refl... apply (dp a). }
      { apply EqRays_sym in dopa.
        unfold EqRays in dopa.
        destruct dopa as [ _ OsrAD ]. rewrite road...
      }
    }
  }
  { intro BetRbca.
    assert (Exc : { d : Ray | a == !d }). { exists (!a). apply OpOpRs. }
    destruct Exc as [ d aopd ].
    assert (dopa : !a == d). { rewrite aopd. symmetry. apply OpOpRs. }
    apply OpRs_OpRs in aopd.
    destruct aopd as [ road BetAOD ].
    destruct BetRbca as [ robc [ roca' BetRbca' ]].
    assert (roab : da a = da b).
    { rewrite robc. rewrite roca'. apply OpRays_0. }
    unfold BetRs. split... split... rewrite <- roab in *.
    apply <- (BetPs_BR_BR (da a)(db a)(db b)(db c)(db (!a)))...
    symmetry in dopa. apply (OpRs_sym d a) in dopa.
    apply (BetPs_inv (da a)(db a)(db d)(db a)(db (!a)))...
    { apply SR_refl... apply (dp a). }
    { apply (OpRs_sym a d) in dopa.
      unfold EqRays in dopa.
      destruct dopa as [ _ OsrAD ]. rewrite road...
    }
  }
Qed.

(** Problem #20 *)
Definition DrawRayOutsideAngle :
  forall (a b : Ray),
  ![ a # b ]
    -> { c : Ray | ![ a # b # c ] }.
Proof with eauto.
  intros a b [ roab diab ].
  assert (dibd : ![ b # !a ]).
  { apply (nColOpRs_2 b a). apply nColRs_sym. repeat split... }
  destruct (DrawRayInsideAngle b (!a) dibd) as [ c BetRbcd ].
  exists c.
  apply BetRs_sym in BetRbcd. apply BetRs_sym.
  apply (BetRs_PerBetRs (!a) c b) in BetRbcd...
  assert (aeqa : a == !(!a)). { apply OpOpRs. }
  destruct BetRbcd as [ rocb [ roba H ]].
  do 2 try split... unfold EqRays in aeqa.
  destruct aeqa as [ roaa H1 ].
  apply (BR_inv (da c)(db c)(db b)(db (!(!a)))(db c)(db b)(db a))...
  { apply SR_refl; auto. apply (dp c). }
  { apply SR_refl; auto. rewrite rocb. apply (dp b). }
  { apply SR_sym. rewrite rocb. rewrite <- roab. auto. }
Defined.

(** Problem #21 *)
Definition DecideRaysOrderOnSameSide :
  forall (a b c : Ray),
  b =/= c
    -> ![ a # b, c ]
    -> { ![ a # b # c ] } + { ![ a # c # b ] }.
Proof with eauto.
  intros [ O A nOeqA ][ O' B nOeqB ][ O'' C nOeqC ].
  intros nbeqc [roab [ roac aSFbc ]]; simpl in *.
  subst O'' O'.
  unfold EqRays in *; simpl in *.
  assert (nOsrBC : ~ [O # B, C]). { contradict nbeqc... }
  destruct (SH_nColPs_BR O A B C) as [ H1 | H2 ]; ord;
  [ left | right ]; split; simpl...
Defined.

Lemma BetRs_OppositeSideRs :
  forall (a b c : Ray),
  ![ a # b # c ]
    -> ![ b # c, !a ].
Proof with eauto.
  intros a b c BetRabc.
  apply BetRs_PerBetRs in BetRabc. apply BetRs_SameSideRs in BetRabc.
  destruct BetRabc...
Qed.

Lemma OrdRs_sym :
  forall (a b c d : Ray)(roab : da a = da b)
    (robc : da b = da c)(rocd : da c = da d),
  ![ a # b # c # d ]
    -> ![ d # c # b # a ].
Proof.
  intros a b c d roab robc rocd [ abc [ abd [ acd bcd ]]].
  do 3 try split; try apply BetRs_sym; auto.
Qed.

Lemma BR_SS_SS :
  forall (O A B C : Point)(x : Line),
  [ O | A; B; C ]
    -> [ O @ x ]
    -> [ x | A, C ]
    -> [ x | A, B ].
Proof with eauto.
  intros O A B C x OoABC Oox SSxAC.
  destruct (DrawPointCrossBar O A B C) as [ B' [ BetAB'C OsrBB' ]]...
  assert (nBox : ~ [ B @ x ]).
  { destruct SSxAC as [ nAox [ nCox SSxAC ]].
    contradict SSxAC. exists B'. split; incpt.
  }
  assert (SSxAB' : [ x | A, B' ]).
  { apply (ConvexHalfplane A B' C x BetAB'C SSxAC). }
  assert (SSxBB' : [ x | B, B' ]).
  { apply (SR_SS O B B' x Oox nBox)... }
  apply (SS_trans A B' B x SSxAB' (SS_sym B B' x SSxBB')).
Qed.

Lemma BR_BR_SH :
  forall O A B C D : Point,
  [ O | A; B; C ]
    -> [ O | A; B; D ]
    -> [ O # B | C, D ].
Proof with eauto.
  intros O A B C D OoABC OoABD.
  elim OoABC; intros H1 H2.
  destruct H1 as [ nOeqA [ a [ Ooa [ Aoa SSaBC ]]]].
  destruct H2 as [ _ [ c [ Ooc [ Coc SScBA ]]]].
  elim OoABD; intros H1 H2.
  destruct H1 as [ _ [ a' [ Ooa' [ Aoa' _ ]]]].
  destruct H2 as [ nOeqD [ d [ Ood [ Dod SSdBA ]]]].
  assert (aeqa' : a = a'); eqls.
  subst a'.
  elim SSaBC; intros nBoa [ nCoa _ ].
  elim SScBA; intros nBoc [ nAoc _ ].
  elim SSdBA; intros nBod [ nAod _ ].
  assert (nOeqB : O <> B); dips.
  assert (nOeqC : O <> C); dips.
  destruct (DrawExtensionLinePP O B nOeqB) as [ b [ Oob Bob ]].
  assert (OSbAC : [ A | b | C ]).
  { destruct (DrawPointCrossBar O A B C) as [ B' [ BetAB'C OrBB' ]]...
    assert (nAob : ~ [ A @ b ]).
    { contradict nBoa. assert (naeqb : a = b); eqls. }
    assert (nCob : ~ [ C @ b ]).
    { contradict nBoc. assert (nceqb : c = b); eqls. }
    repeat split...
    exists B'; split...
    destruct OrBB' as [ _ [ _ [ ColOBB' _ ]]].
    apply (ColPs_IncPt O B B' b nOeqB); incpt.
  }
  assert (OSbAD : [ A | b | D ]).
  { destruct (DrawPointCrossBar O A B D) as [ B' [ BetAB'D OrBB' ]]...
    assert (nAob : ~ [ A @ b ]).
    { contradict nBoa. assert (naeqb : a = b); eqls. }
    assert (nDob : ~ [ D @ b ]).
    { contradict nBod. assert (nceqb : d = b); eqls. }
    repeat split...
    exists B'; split...
    destruct OrBB' as [ _ [ _ [ ColOBB' _ ]]].
    apply (ColPs_IncPt O B B' b nOeqB); incpt.
  }
  assert (SSbCD : [ b | C, D ]).
  { apply (OOS_trans C A D b (OS_sym A C b OSbAC) OSbAD). }
  split; auto; exists b; split...
Qed.

(** Theorem #29 *)
Lemma BR_trans :
  forall O A B C D : Point,
  [ O | A; B; C ]
    -> [ O | A; C; D ]
    -> [ O | A; B; D ] /\ [ O | B; C; D ].
Proof with eauto.
  intros O A B C D [ OABC OCBA ][ OACD ODCA ].
  elim OABC; intros nOeqA [ a [ Ooa [ Aoa SSaBC ]]].
  elim OCBA; intros nOeqC [ c [ Ooc [ Coc SScBA ]]].
  elim OACD; intros _ [ a' [ Ooa' [ Aoa' SSaCD ]]].
  elim ODCA; intros nDeqO [ d [ Ood [ Dod SSdCA ]]].
  assert (aeqa' : a = a'); eqls.
  subst a'.
  elim SSaBC; intros nBoa [ nCoa _ ].
  elim SSdCA; intros nCod [ nAod _ ].
  elim SScBA; intros nBoc [ nAoc _ ].
  assert (SSaBD : [ a | B, D ]). { apply (SS_trans B C D a)... }
  assert (SSdBA : [ d | B, A ]).
  { destruct (DrawPointCrossBar O A B C) as [ B' [ BetAB'C OsrBB' ]].
    split...
    assert (SSdAB' : [ d | A, B' ]).
    { apply (ConvexHalfplane A B' C d BetAB'C (SS_sym C A d SSdCA)). }
    assert (SSdB'B : [ d | B', B ]).
    { apply (SR_SS O B' B d Ood). firstorder. apply SR_sym... }
    apply (SS_sym A B d). apply (SS_trans A B' B d SSdAB' SSdB'B).
  }
  assert (OoABD : [ O | A; B; D ]). { repeat split... }
  assert (OBsfCD : [ O # B | C, D ]).
  { apply (BR_BR_SH O A B C D)... }
  split...
  destruct OoABD as [ _ [ nOeqD [ x [ Oox [ Dox SSxBA ]]]]].
  destruct ODCA as [ _ [ x' [ Oox' [ Dox' SSxCA ]]]].
  assert (xeqx' : x = x'); eqls.
  subst x'.
  split...
  repeat split; dips.
  exists x. split; try split; dips.
  apply SS_sym in SSxBA.
  apply (SS_trans C A B x)...
Qed.
Lemma BetRs_a_trans :
  forall (a b c d : Ray),
  ![ a # b # c ]
    -> ![ a # c # d ]
    -> ![ a # b # c # d ].
Proof.
  intros a b c d [ roab [ robc BetRabc ]][ roac [ rocd BetRacd ]].
  destruct (BR_trans (da a)(db a)(db b)(db c)(db d)); auto.
  unfold BetRs.
  destruct rocd, robc, roab.
  do 2 split; auto.
Qed.

(** Problem #22 *)
Definition BetRs_b_trans :
  forall (a b c d : Ray),
  b =/= c
    -> ![ a # b # d ]
    -> ![ a # c # d ]
    -> { ![ a # b # c # d ] } + { ![ a # c # b # d ] }.
Proof with eauto.
  intros a b c d nbeqc abd acd.
  destruct (BetRs_nColRs a b d abd) as [ diab [ dibd diad ]].
  destruct (BetRs_nColRs a c d acd) as [ diac [ dicd _ ]].
  assert (aSFbc : ![ a # b, c ]).
  { apply BetRs_SameSideRs in abd. destruct abd as [ a_bd _ ].
    apply BetRs_SameSideRs in acd. destruct acd as [ a_cd _ ].
    apply (SameSideRs_trans a b d c)... apply SameSideRs_sym...
  }
  destruct (DecideRaysOrderOnSameSide a b c) as [ abc | acb ]...
  { left. apply (BetRs_a_trans a b c d)... }
  { right. apply (BetRs_a_trans a c b d)... }
Defined.

Example DrawThirdRayApart :
  forall (a b : Ray)(roab : da a = da b),
  { c : Ray | ![ a # c ] /\ ![ b # c ] }.
Proof with eauto.
  intros a b roab.
  destruct (DrawRayApart a) as [ c diac ].
  destruct (DecideRayApartness a c b roab diac) as [ diab | dicb ].
  { destruct (DrawRayInsideAngle a b diab) as [ d BetRadb ].
    exists d; split...
    { apply (BetRs_nColRs a d b BetRadb). }
    { apply nColRs_sym. apply (BetRs_nColRs a d b BetRadb). }
  }
  exists c; split...
  apply nColRs_sym...
Defined.

Lemma BetRs_BetOpRs :
  forall (a b c : Ray),
  ![ a # b # c ]
    <-> ![ !a # !b # !c ].
Proof with eauto.
  intros a b c.
  split.
  { intro abc.
    assert (bca' : ![b # c # !a]). { apply -> BetRs_PerBetRs... }
    assert (ca'b' : ![c # !a # !b]). { apply -> BetRs_PerBetRs... }
    apply -> BetRs_PerBetRs...
  }
  { intro abc.
    assert (bca' : ![c # !a # !b]). { apply <- BetRs_PerBetRs... }
    assert (ca'b' : ![b # c # !a]). { apply <- BetRs_PerBetRs... }
    apply <- BetRs_PerBetRs...
  }
Qed.

Lemma SSO_Rs_trans :
  forall (a b c : Ray),
  ![ a # b, c ]
    -> ![ c # b, a ]
    -> ![ b # c, !a ].
Proof with eauto.
  intros a b c aSFbc cSFba.
  assert (BetRabc : ![ a # b # c ]). { apply (BetRs_SameSideRs a b c)... }
  apply BetRs_PerBetRs in BetRabc. apply BetRs_SameSideRs in BetRabc.
  destruct BetRabc...
Qed.

Lemma SOS_Rs_trans :
  forall (a b c : Ray),
  ![ a # b, c ]
    -> ![ b # c, !a ]
    -> ![ c # b, a ].
Proof with eauto.
  intros a b c aSFbc bOFac.
  apply SameSideRs_OpRs_inv in aSFbc.
  assert (abc : ![ !a # c # b ]).
  { apply BetRs_SameSideRs; split... apply SameSideRs_sym... }
  apply SameSideRs_sym. apply BetRs_OppositeSideRs in abc.
  apply SameSideRs_sym.
  eapply (SameSideRs_inv c b (!!a) c b a); try reflexivity...
  symmetry. apply OpOpRs.
Qed.

Lemma OOO_Rs_trans :
  forall (a b c : Ray),
  ![ b # c, !a ]
    -> ![ a # c, !b ]
    -> ![ c # b, !a ].
Proof with eauto.
  intros a b c aSFbc bOFac.
  apply (SameSideRs_OpRs_inv a c (!b)) in bOFac. apply SameSideRs_sym.
  apply (SOS_Rs_trans b (!a) c)... apply SameSideRs_sym...
Qed.

Lemma BetRs_SO_Rs :
  forall (a b c : Ray),
  ![ a # b # c ]
    <-> ![ a # b, c ] /\ ![ b # c, !a ].
Proof with eauto.
  intros a b c.
  split.
  { intros BetRabc.
    apply BetRs_SameSideRs in BetRabc.
    destruct BetRabc as [ aSFbc cSFba ].
    split... apply SSO_Rs_trans...
  }
  { intros [ aSFbc bOFac].
    apply BetRs_SameSideRs.
    split... apply SOS_Rs_trans...
  }
Qed.

Lemma nColRs_OpRs_nColRs :
  forall a b c : Ray,
  ![ a # b ]
    -> a == !c
    -> ![ b # c ].
Proof with eauto.
  intros a b c diab aopc.
  apply nColRs_sym in diab.
  apply (nColRs_inv b (!a) c)...
  apply nColOpRs_2...
  apply OpRs_sym in aopc...
  rewrite aopc; reflexivity.
Qed.

Lemma OrdRs_PerOrdRs :
  forall (a b c d : Ray)(roab : da a = da b)
    (robc : da b = da c)(rocd : da c = da d),
  ![ a # b # c # d ]
    <-> ![ b # c # d # !a ].
Proof with eauto.
  intros a b c d roab robc rocd.
  split.
  { intros [ abc [ abd [ acd bcd ]]].
    split; [ idtac | split; try split; try apply BetRs_PerBetRs ]; eauto;
    apply <- BetRs_PerBetRs; apply -> BetRs_BetOpRs...
  }
  { intros [ abc [ abd [ acd bcd ]]].
    split; [ idtac | split; try split; try apply BetRs_PerBetRs ]; eauto;
    apply <- BetRs_PerBetRs; eauto; apply <- BetRs_PerBetRs;
    apply -> BetRs_BetOpRs...
  }
Qed.

Example DecideOppositeRaySide :
  forall (a b c : Ray),
  ![ a # b ]
    -> ![ a # c ]
    -> { ![ a # b, c ] } + { ![ a # b, !c ] }.
Proof with eauto.
  intros [ O A nOeqA ][ O' B nOeqB ][ O'' C nOeqC ].
  intros [ roab diab ][ roac diac ].
  unfold OpRay in *; simpl in *; subst O'' O'.
  destruct (DrawOppositePoint O C nOeqC) as [ D [ COD _ ]].
  destruct (BetPs_3DiPs C O D COD) as [ _ [ nOeqD nCeqD ]]; simpl.
  destruct (DrawExtensionLinePP O A nOeqA) as [ x [ Oox Aox ]].
  assert (SSxCD : [ C | x | D ]).
  { split.
    contradict diac...
    split.
    { contradict diac; inc. }
    { exists O; split... }
  }
  assert (nBox : ~ [B @ x]); nincpt.
  destruct (DecideTwoSides C B D x) as [ SSxBD | OSxBD ]; eauto;
  [ right | left ]; do 3 split; eauto; exists x; do 2 try split; eauto;
  eapply OOS_trans; eauto; apply OS_sym...
Defined.

Example DecideOneRayBetweenTwoOthers :
  forall (a b c : Ray),
  ![ a # b ]
    -> ![ a # c ]
    -> ![ b # c ]
    -> { ![ a # b # c ] } + { ![ a # c # b ] }
     + { ![ a # b # !c ] } + { ![ a # !c # b ] }.
Proof with eauto.
  intros a b c diab diac dibc.
  destruct (DecideOppositeRaySide a b c) as [ aSFbc | aSFbd ]...
  { assert (nbeqc : b =/= c). { apply nColRs_nColPs in dibc; tauto. }
    destruct (DecideRaysOrderOnSameSide a b c nbeqc aSFbc)
      as [ BetRabc | BetRacb ]...
  }
  { assert (nbeqc' : b =/= !c). { apply nColRs_nColPs in dibc; tauto. }
    destruct (DecideRaysOrderOnSameSide a b (!c) nbeqc' aSFbd)
      as [ BetRabd | BetRadb ]...
  }
Defined.

Example DecideThreeRays :
  forall (a b c : Ray),
  ![ a # b ]
    -> ![ a # c ]
    -> ![ b # c ]
    -> { ![ a # c # b ] } + { ![ a # b # c ] }
     + { ![ b # a # c ] } + { ![ b # !a # c ] }.
Proof with eauto.
  intros a b c diab diac dibc.
  destruct (DecideOneRayBetweenTwoOthers a b c)
  as [[[ H1 | H2 ]| H3 ]| H4 ]; auto.
  { left; right.
    apply BetRs_sym.
    apply BetRs_PerBetRs...
  }
  { right.
    apply <- BetRs_PerBetRs; apply BetRs_BetOpRs.
    apply (BetRs_inv a (!c) b (!(!a))(!c)(!(!b)));
    try reflexivity; try apply OpOpRs...
  }
Defined.

Example DecideFourRays :
  forall (a b c d : Ray)(roab : da a = da b)
    (robc : da b = da c)(rocd : da c = da d),
  ![ a # b ]
    -> ![ a # c ]
    -> ![ a # d ]
    -> ![ b # c ]
    -> ![ b # d ]
    -> ![ c # d ]
    -> { ![ a # b # c # d ] } + { ![ a # b # d # c ] }
     + { ![ a # d # b # c ] } + { ![ a # b # c # !d ] }
     + { ![ a # b # !d # c ] } + { ![ a # !d # b # c ] }
     + { ![ a # b # !c # d ] } + { ![ a # b # d # !c ] }
     + { ![ a # d # b # !c ] } + { ![ a # b # !c # !d ] }
     + { ![ a # b # !d # !c ] } + { ![ a # !d # b # !c ] }
     + { ![ a # !c # b # d ] } + { ![ a # !c # d # b ] }
     + { ![ a # d # !c # b ] } + { ![ a # !c # b # !d ] }
     + { ![ a # !c # !d # b ] } + { ![ a # !d # !c # b ] }
     + { ![ a # c # b # d ] } + { ![ a # c # d # b ] }
     + { ![ a # d # c # b ] } + { ![ a # c # b # !d ] }
     + { ![ a # c # !d # b ] } + { ![ a # !d # c # b ] }.
Proof with eauto.
  intros a b c d roab robc rocd diab diac diad dibc dibd dicd.
  assert (roas : da a = da d). { rewrite roab. rewrite robc... }
  destruct (DecideOneRayBetweenTwoOthers a b c)
  as [[[ abc | acb ]| abc' ]| ac'b ]...
  { destruct (DecideThreeRays a c d) as [[[ acd | adc ]| acd' ]| ad'c ]...
    { destruct (BetRs_b_trans a b d c) as [ abdc | adbc ]...
      { apply nColRs_nColPs in dibd.
        destruct dibd as [ _ [ dibd _ ]]...
      }
      { do 22 left... }
      { do 21 left... }
    }
    { do 23 left... apply BetRs_a_trans... }
    { assert (abcd : ![a # b # c # !d]).
      { apply -> OrdRs_PerOrdRs... apply OrdRs_sym...
        apply BetRs_a_trans... apply BetRs_sym... }
      { do 20 left... }
    }
    { assert (adc : ![a # !d # c]).
      { apply BetRs_PerBetRs... apply BetRs_PerBetRs...
        apply (BetRs_inv c (!a) d c (!a)(!(!d))); try reflexivity...
        apply OpOpRs...
      }
      destruct (BetRs_b_trans a b (!d) c) as [ abdc | adbc ]...
      { apply nColRs_nColPs in dibd.
        destruct dibd as [ _ [ _ nbopd ]]...
      }
      { do 19 left... }
      { do 18 left... }
    }
  }
  { destruct (DecideThreeRays a b d) as [[[ abd | adb ]| abd' ]| ad'b ]...
    { destruct (BetRs_b_trans a c d b) as [ acdb | adcb ]...
      { apply nColRs_nColPs in dicd.
        destruct dicd as [ _ [ nbeqd _ ]]...
      }
      { do 4 left; right... }
    }
    { do 5 left; right... apply (BetRs_a_trans a c b d)... }
    { do 2 left; right... apply BetRs_sym in acb.
      assert (bcad : ![b # c # a # d]). { apply (BetRs_a_trans b c a d)... }
      apply OrdRs_sym in bcad...
      apply OrdRs_PerOrdRs in bcad...
      rewrite roab... rewrite roab...
    }
    assert (adb : ![a # !d # b]).
    { apply BetRs_PerBetRs... apply BetRs_PerBetRs...
      apply (BetRs_inv b (!a) d b (!a)(!(!d))); try reflexivity...
      apply OpOpRs...
    }
    destruct (BetRs_b_trans a c (!d) b) as [ acdb | adcb ]...
    apply nColRs_nColPs in dicd. destruct dicd as [ _ [ _ nbopd ]]...
  }
  { destruct (DecideThreeRays a (!c) d)
      as [[[ ac'd | ac'b ]| ac'd' ]| c'a'd ]; try apply nColOpRs_1;
    try apply nColOpRs_2...
    { destruct (BetRs_b_trans a b d (!c)) as [ abdc' | adbc' ]...
      { apply nColRs_nColPs in dibd. destruct dibd as [ _ [ nbeqd _ ]]... }
      { do 16 left... }
      { do 14 left... }
    }
    { do 17 left; right... apply (BetRs_a_trans a b (!c) d)... }
    { do 14 left; right...
      assert (c'bad : ![!c # b # a # d]).
      { apply (BetRs_a_trans (!c) b a d)... apply BetRs_sym in abc'... }
      apply OrdRs_sym in c'bad... apply -> OrdRs_PerOrdRs in c'bad...
      rewrite robc... apply OpRays_0. rewrite robc. symmetry.
      apply OpRays_0.
    }
    { assert (ad'c' : ![a # !d # !c]).
      { apply <- BetRs_PerBetRs. apply <- BetRs_PerBetRs...
        apply (BetRs_inv (!c)(!a) d (!c)(!a)(!(!d))); try reflexivity...
        apply OpOpRs.
      }
      destruct (BetRs_b_trans a b (!d)(!c)) as [ abdc | adbc ]...
      { apply nColRs_nColPs in dibd. destruct dibd as [ _ [ _ nbopd ]]... }
      { do 10 left... }
      { do 10 left... }
    }
  }
  { destruct (DecideThreeRays a b d) as [[[ abd | adb ]| abd' ]| ad'b ]...
    { destruct (BetRs_b_trans a d (!c) b) as [ adcb | acdb ]...
      { apply nColRs_sym in dicd. apply nColRs_nColPs in dicd.
        destruct dicd as [ _ [ _ copd ]]...
      }
      { do 9 left... }
      { do 10 left... }
    }
    { apply nColRs_sym in dicd. do 11 left; right...
      apply (BetRs_a_trans a (!c) b d)...
    }
    { do 8 left; right...
      apply BetRs_sym in ac'b.
      assert (bcad : ![b # !c # a # d]).
      { apply (BetRs_a_trans b (!c) a d)... }
      apply OrdRs_sym in bcad... apply OrdRs_PerOrdRs in bcad...
      rewrite roab... rewrite robc... apply OpRays_0.
      rewrite robc. symmetry. apply OpRays_0.
      rewrite robc. apply OpRays_0. symmetry. rewrite roab. rewrite robc.
      apply OpRays_0.
    }
    { assert (adb : ![a # !d # b]).
      { apply BetRs_PerBetRs... apply BetRs_PerBetRs...
        apply (BetRs_inv b (!a) d b (!a)(!(!d))); try reflexivity...
        apply OpOpRs...
      }
      destruct (BetRs_b_trans a (!c)(!d) b) as [ acdb | adcb ]...
      { apply nColRs_sym in dicd. apply nColRs_sym in dicd.
        apply nColRs_nColPs in dicd. destruct dicd as [ _ [ nbeqd _ ]]...
        contradict nbeqd. apply OpRays_compat in nbeqd.
        rewrite <- OpOpRs in nbeqd. rewrite <- OpOpRs in nbeqd...
      }
      { do 7 left... }
      { do 6 left... }
    }
  }
Defined.

Example DecideRayDirection_NESW :
  forall (a b c : Ray)(roac : da a = da c),
  ![ a # b ]
    -> { ![ a # b, c ] } + { ![ a # c, !b ] }
     + { ![ b # a, c ] } + { ![ b # c, !a ] }.
Proof with eauto.
  intros a b c roac diab.
  destruct (DecideRayApartness a b c roac diab) as [ diac | dibc ].
  { destruct (DecideRaysSide a b c diab diac) as [ aSFbc | aOFbc ].
    { left... }
    { left; left; right... }
  }
  { destruct (DecideRaysSide b a c) as [ bSFac | bOFac ]...
     apply (nColRs_sym a b diab)...
  }
Defined.

Example DecideRayDirection_NES :
  forall (a b c : Ray)(roac : da a = da c),
  a =/= c
    -> ![ a # b ]
    -> { ![ a # b, c ] } + { ![ a # c, !b ] } + { ![ b # c, !a ] }.
Proof with eauto.
  intros a b c roac naeqc diab.
  destruct (DecideRayApartness a b c roac diab) as [ diac | dibc ].
  { destruct (DecideRaysSide a b c diab diac) as [ aSFbc | aOFbc ]... }
  { destruct (DecideRaysSide b a c) as [ bSFac | bOFac ]...
    { apply nColRs_sym... }
    { assert (naopc : a =/= !c).
      { intros aopc. apply DecideRaysOrderOnSameSide in bSFac...
        destruct bSFac as [ bac | bca ]...
        { apply BetRs_nColRs in bac. destruct bac as [ _ [ diac _ ]].
          apply nColRs_nColPs in diac. destruct diac as [ _ [ _ naopc ]].
          contradiction.
        }
        { apply BetRs_nColRs in bca. destruct bca as [ _ [ dica _ ]].
          apply nColRs_sym in dica. apply nColRs_nColPs in dica.
          destruct dica as [ _ [ _ naopc ]].
          contradiction.
        }
      }
      assert (diac : ![ a # c ]). { apply nColRs_nColPs; split... }
      destruct (DecideRaysSide a c b) as [ aSFcb | bOFac ]...
      apply SameSideRs_sym in aSFcb... apply OppositeSideRs_sym in bOFac...
    }
  }
Defined.

Lemma SameSideRs_OpRs_OppositeSide :
  forall (a b c : Ray),
  ![ a # b, !c ]
    -> [ db c | da a # db a | db b ].
Proof with eauto.
  intros [ O A nAeqO ][ O' B nBeqO ][ O'' C nCeqO ][ H0 [ H1 H ]].
  unfold OpRay in *; simpl in *.
  destruct (DrawOppositePoint O'' C nCeqO) as [ D [ BetCOD H2 ]].
  destruct (BetPs_3DiPs C O'' D BetCOD) as [ _ [ nOeqD nCeqD ]]...
  simpl in *. subst O'' O'.
  eapply (OHO_trans O A C D B)...
  { destruct H as [ nOeqA [ x [ Oox [ Aox [ nBox [ nDox H ]]]]]].
    split; try exists x; repeat split... contradict nDox; incpt 2.
  }
  { apply SHb_sym... }
Qed.

Lemma OppositeSide_OpRs_SameSideRs :
  forall (a b c : Ray)(roab : da a = da b)(robc : da b = da c),
  [ db c | da a # db a | db b ]
    -> ![ a # b, !c ].
Proof with eauto.
  intros [ O A nAeqO ][ O' B nBeqO ][ O'' C nCeqO ] roab robc H.
  unfold OpRay in *; simpl in *.
  subst O'' O'.
  destruct (DrawOppositePoint O C nCeqO) as [ D [ COD H1 ]].
  destruct (BetPs_3DiPs C O D COD) as [ _ [ nOeqD nCeqD ]].
  do 2 split; simpl...
  apply (OOH_trans O A B C D). apply OHb_sym...
  destruct H as [ nOeqA [ x [ Oox [ Aox [ nCox [ nBox H ]]]]]].
  repeat split... exists x; repeat split...
  contradict nCox; incpt 2.
Qed.

End ORDER.

Hint Resolve
  nColPs_BetPs_BR
  ColPs_BR_BetPs
  BR_sym
  ConvexHalfplane
  : OrdPs.

Hint Resolve
  OS_IncPs_ConvLs
  : ColLs.

Notation " ![ a # b , c ] "
  := (SameSideRays a b c)
  (at level 60).
Notation " ![ a # b # c ] "
  := (BetRs a b c)
  (at level 60).
Notation " ![ a ; b # c ] "
  := (![ a # b # c ] \/ (a == b /\ ![ b # c ]))
  (at level 60).
Notation " ![ a # b ; c ] "
  := (![ a # b # c ] \/ (![ a # b ] /\ b == c))
  (at level 60).
Notation " ![ a ; b ; c ] "
  := (![ a # b # c ] \/ (a == b /\ b <=/=> c) \/ (a <=/=> b /\ b == c))
  (at level 60).
Notation " ![ a # b # c # d ] "
  := (![ a # b # c ] /\ ![ a # b # d ] /\ ![ a # c # d ] /\ ![ b # c # d ])
  (at level 60).

(*****************************************************************************)
(* 9 *) Section FLAG.
Context `{ cr : Circles }.
(*****************************************************************************)

Definition EqFlags (F G : Flag) : Prop
  := (da F == da G) /\ ![ da F # db F, db G ].
Notation " F === G "
  := (EqFlags F G)
  (at level 60).
Notation " F =//= G "
  := (~ EqFlags F G)
  (at level 60).

Definition F0 : Flag.
Proof with eauto.
  destruct DrawPoint as [ O _ ].
  destruct (DrawDistinctPoint O) as [ A nOeqA ].
  destruct (DrawExtensionLinePP O A nOeqA) as [ x [ Oox Aox ]].
  destruct (DrawPointApartLine x) as [ B nBox ].
  assert (nOeqB : O <> B); dips.
  assert (diab : ![{{ O # A | nOeqA }} # {{ O # B | nOeqB }}]).
  { split; ncolps. }
  apply ({{ {{ O # A | nOeqA }} # {{ O # B | nOeqB }} | diab }}).
Defined.

Definition FlipFlag : Flag -> Flag.
Proof.
  intros [ a b diab ].
  apply ({{ b # a | nColRs_sym a b diab }}).
Defined.
Notation " # F "
  := (FlipFlag F)
  (at level 50).

Lemma EqFlags_refl :
  reflexive Flag EqFlags.
Proof with eauto.
  intros [ a b diba ].
  split; simpl...
  { apply EqRays_refl. }
  { apply SameSideRs_refl; auto. }
Qed.
Lemma EqFlags_sym :
  symmetric Flag EqFlags.
Proof with eauto.
  intros [ a b diba ][ c d didc ][ aeqc aSRbd ].
  split; simpl in *...
  { apply EqRays_sym... }
  { apply SameSideRs_sym...
    apply (SameSideRs_inv a b d c b d); auto; apply EqRays_refl.
  }
Qed.
Lemma EqFlags_trans :
  transitive Flag EqFlags.
Proof with eauto.
  intros [ a b diba ][ c d didc ][ e f dife ][ aeqc aSRbd ][ ceqe cSRde ].
  split; simpl in *...
  { rewrite aeqc... }
  { symmetry in aeqc.
    apply (SameSideRs_inv c d f a d f aeqc) in cSRde; try reflexivity...
    apply (SameSideRs_trans a b d f)...
  }
Qed.
Global Instance Flags_equiv :
  Equivalence EqFlags
    := Build_Equivalence EqFlags
       EqFlags_refl
       EqFlags_sym
       EqFlags_trans.

Lemma FlipFlipFlag :
  forall (F : Flag),
  F === # (# F).
Proof with eauto.
  intros [ a b diab ].
  split; simpl...
  { reflexivity. }
  { apply SameSideRs_refl; auto. }
Qed.

Definition EqFlagsRotation (F G : Flag) : Prop
  := (da F == da G) /\ ![ da F # db F, db G ]
  \/ (da F == ! da G) /\ ![ da F # db G, ! db F ]
  \/ (![ da F # da G, db F ] /\ ![ da G # db G, ! da F ])
  \/ (![ da G # da F, db G ] /\ ![ da F # db F, ! da G ]).

Lemma EqFlagsRotation_refl :
  reflexive Flag EqFlagsRotation.
Proof with eauto.
  intros [ a b diba ].
  left; split; simpl...
  { reflexivity. }
  { apply SameSideRs_refl... }
Qed.
Lemma EqFlagsRotation_sym :
  symmetric Flag EqFlagsRotation.
Proof with eauto.
  intros [ a b diab ][ a' b' dia'b' ].
  intros [ H |[ H |[ H | H ]]]; destruct H as [ Eq Sr ]; simpl in *.
  { left; split; simpl...
    { symmetry... }
    { apply SameSideRs_sym.
      apply (SameSideRs_inv a b b' a' b b'); eauto; reflexivity.
    }
  }
  { right; left; split; simpl...
    { rewrite Eq. apply OpOpRs. }
    { apply SameSideRs_OpRs_inv in Sr.
      apply SameSideRs_sym. apply OpRs_sym in Eq.
      apply (SameSideRs_inv (!a) (!b') b a' (!b') b); auto; try reflexivity.
      symmetry... apply SameSideRs_sym. apply OppositeSideRs_sym...
    }
  }
  { right; right; right; split... }
  { right; right; left; split... }
Qed.
Lemma EqFlagsRotation_trans :
  transitive Flag EqFlagsRotation.
Proof with eauto.
  intros [ a b diab ][ a' b' dia'b' ][ a'' b'' dia''b'' ].
  unfold EqFlagsRotation.
  intros [ H1 |[ H2 |[ H3 | H4 ]]][ H5 |[ H6 |[ H7 | H8 ]]];
  try destruct H1 as [ OeqO' OsrAA' ];
  try destruct H2 as [ OopO' OorAA' ];
  try destruct H3 as [ OsrO'A BetOO'A' ];
  try destruct H4 as [ O'srOA' BetO'OA ];
  try destruct H5 as [ O'eqO'' O'srA'A'' ];
  try destruct H6 as [ O'opO'' O'orA'A'' ];
  try destruct H7 as [ O'srO''A' BetO'O''A'' ];
  try destruct H8 as [ O''srO'A'' BetO''O'A' ];
  simpl in *.
  { left; split; simpl...
    { rewrite OeqO'... }
    { apply (SameSideRs_inv a' b' b'' a b' b'') in O'srA'A'';
      try reflexivity; try symmetry...
      apply (SameSideRs_trans a b b' b'')...
    }
  }
  { right; left; split; auto.
    { rewrite OeqO'... }
    { apply (OppositeSideRs_inv b' a' b'' b' a b'') in O'orA'A'';
      try reflexivity; try symmetry...
      apply OppositeSideRs_sym in O'orA'A''. apply OppositeSideRs_sym.
      apply (OSO_SideRs_trans b'' a b' b)...
      apply SameSideRs_sym; auto.
    }
  }
  { right; right; left; split...
    { apply (SameSideRs_inv a' a'' b' a a'' b') in O'srO''A';
      try reflexivity; try symmetry...
      apply SameSideRs_sym in OsrAA';
      apply (SameSideRs_trans a a'' b' b)...
    }
    { apply (OppositeSideRs_inv a' a'' b'' a a'' b'');
      try reflexivity; try symmetry...
    }
  }
  { right; right; right; split; auto.
    { apply (SameSideRs_inv a'' a' b'' a'' a b'');
      try reflexivity; try symmetry...
    }
    { apply (OppositeSideRs_inv a'' a' b a'' a b);
      try reflexivity; try symmetry...
      apply (SameSideRs_inv a b b' a' b b') in OsrAA'; try reflexivity...
      apply (OSO_SideRs_trans a'' a' b' b)... apply SameSideRs_sym...
    }
  }
  { right; left; split...
    { rewrite OopO'. rewrite O'eqO''. reflexivity. }
    { apply SameSideRs_OpRs_inv in O'srA'A''.
      apply (SameSideRs_inv (!a') b' b'' a b' b'')
        in O'srA'A''; try reflexivity...
      apply (OSO_SideRs_trans b a b' b'')... symmetry...
    }
  }
  { left; split...
    { apply OpRs_sym in O'opO''. rewrite OopO'. symmetry... }
    { rewrite O'opO'' in OopO'. rewrite <- OpOpRs in OopO'.
      rewrite <- OopO' in O'opO''.
      apply SameSideRs_OpRs_inv in O'orA'A''.
      apply OpRs_sym in O'opO''.
      apply (OppositeSideRs_inv b' (!a') b'' b' a b'') in O'orA'A'';
      try reflexivity; try symmetry...
      apply OppositeSideRs_sym in OorAA'.
      apply (OOS_SideRs_trans b' a b b'')...
    }
  }
  { right; right; right; split...
    { apply (SameSideRs_inv a'' (!a') b'' a'' a b'');
      try reflexivity; try symmetry... apply SameSideRs_sym...
    }
    { apply OppositeSideRs_sym. apply (OSO_SideRs_trans b a b' a'')...
      apply SameSideRs_sym.
      apply (SameSideRs_inv (!a') a'' b' a a'' b');
      try reflexivity; try symmetry...
      apply (SameSideRs_OpRs_inv a' a'' b')...
    }
  }
  { right; right; left; split...
    apply (OOS_SideRs_trans b' a a'' b). apply OppositeSideRs_sym.
    apply (OppositeSideRs_inv a'' (!a') b' a'' a b');
    try reflexivity; try symmetry...
    apply SameSideRs_OpRs_inv...
    apply OppositeSideRs_sym... apply OppositeSideRs_sym.
    apply (SameSideRs_inv a' b' (!a'') (!!a') b' (!a'')); try reflexivity...
    apply OpOpRs... apply OppositeSideRs_sym... apply OpRs_sym in OopO'.
    apply (SameSideRs_inv a'' b'' a' a'' b'' (!a)); try reflexivity...
    apply SameSideRs_sym...
  }
  { right; right; left; split...
    { apply (SameSideRs_inv a a' b a a'' b); try reflexivity... }
    { apply (OppositeSideRs_inv a a' b'' a a'' b''); try reflexivity...
      apply (OSO_SideRs_trans a a' b' b'')...
    }
  }
  { right; right; right; split...
    { apply OppositeSideRs_sym in BetOO'A'.
      apply OpRs_sym in O'opO''.
      apply (SameSideRs_inv (!a') a b'' a'' a b'');
      try reflexivity; try symmetry...
      apply (SameSideRs_OpRs_inv a' a b'')...
      apply (OOS_SideRs_trans b' a' a b'')...
    }
    { apply (SameSideRs_inv a b a' a b (!a'')); try reflexivity...
      apply SameSideRs_sym...
    }
  }
  { assert (aeqa'' : a =/= a'').
    { intros aeqa''.
      apply (SameSideRs_inv a' a'' b' a' a b') in O'srO''A'; try reflexivity...
      apply SameSideRs_sym in O'srO''A'.
      apply (OSO_SideRs_trans a a' b' a) in BetOO'A'...
      apply OppositeSideRs_irrefl in BetOO'A'... symmetry...
    }
    { destruct (classic (a == (!a''))) as [ aopa'' | naopa'' ].
      { right. left. split...
        apply OppositeSideRs_sym. apply OppositeSideRs_sym in BetO'O''A''.
        apply (OSO_SideRs_trans b'' a a' b)...
        apply (OppositeSideRs_inv b'' (!a'') a' b'' a a');
        try reflexivity; try symmetry...
        apply (SameSideRs_OpRs_inv a'' a' (!b'' ))...
      }
      { assert (Ord : ![ a' # a'', !a ]).
        { apply SameSideRs_sym in O'srO''A'.
          apply (OSO_SideRs_trans a a' b' a'')...
        }
        assert (diaa'' : ![a # a'']).
        { apply nColRs_nColPs. repeat split...
          destruct OsrO'A as [ roaa' _ ].
          destruct O'srO''A' as [ roa'a'' _ ]. rewrite roaa'...
        }
        destruct (DecideRaysSide a a'' b) as [ aSFa''b | aOFa''b ]...
        { right; right; left; split...
          apply OppositeSideRs_sym. apply OppositeSideRs_sym in BetO'O''A''.
          apply (OSO_SideRs_trans b'' a'' a' a)...
          apply SameSideRs_sym in aSFa''b.
          apply (SameSideRs_trans a a' b a'') in OsrO'A...
          apply (SOS_Rs_trans a a' a'')...
        }
        { right; right; right; split...
          apply (OOS_SideRs_trans a' a'' a b'')...
          apply (OOO_Rs_trans a' a a'')...
          apply OppositeSideRs_sym.
          apply SameSideRs_sym in OsrO'A.
          apply (OSO_SideRs_trans a'' a b a')...
        }
      }
    }
  }
  { destruct (classic (a == a'')) as [ aeqa'' | naeqa'' ].
    { left. split...
      apply (SameSideRs_inv a'' a' b'' a a' b'')
        in O''srO'A''; try reflexivity.
      apply (OppositeSideRs_inv a'' a' b' a a' b')
        in BetO''O'A'; try reflexivity.
      apply (SameSideRs_trans a b a' b'')...
      apply SameSideRs_sym... symmetry... symmetry...
    }
    { destruct (classic (a == (!a''))) as [ aopa'' | naopa'' ].
      { right. left. split...
        apply (SameSideRs_OpRs_inv a'' a' b'') in O''srO'A''.
        apply (SameSideRs_inv (!a'') a' b'' a a' b'') in O''srO'A'';
        try reflexivity; try symmetry... apply SameSideRs_sym in BetO''O'A'.
        apply (SameSideRs_inv a' (!a'') b' a' a b') in BetO''O'A';
        try reflexivity; try symmetry...
        apply (OSO_SideRs_trans a a' b' a) in BetOO'A'.
        { exfalso. apply OppositeSideRs_irrefl in BetOO'A'... }
        { apply SameSideRs_sym... }
      }
      { assert (a'SFaa'' : ![ a' # a, a'' ]).
        { apply OppositeSideRs_sym in BetO''O'A'.
          apply OppositeSideRs_sym in BetOO'A'.
          apply (OOS_SideRs_trans b' a' a a'')...
        }
        assert (diaa'' : ![a # a'']).
        { apply nColRs_nColPs. repeat split...
          destruct OsrO'A as [ roaa' _ ].
          destruct O''srO'A'' as [ roa'a'' _ ]. rewrite roaa'...
        }
        destruct (DecideRaysSide a a'' b) as [ aSFa''b | aOFa''b ]...
        { right; right; left; split...
          apply (OSO_SideRs_trans a a'' a' b'')...
          apply SameSideRs_sym in aSFa''b.
          apply (SameSideRs_trans a a' b a'') in OsrO'A...
          apply (SSO_Rs_trans a a'' a').
          { apply SameSideRs_sym in OsrO'A... }
          { apply SameSideRs_sym in a'SFaa''... }
        }
        right; right; right; split...
        apply (SameSideRs_trans a'' a a' b'')...
        apply (OSO_SideRs_trans a'' a b a') in aOFa''b...
        apply (SOS_Rs_trans a' a a'')...
        apply OppositeSideRs_sym... apply SameSideRs_sym...
      }
    }
  }
  { right; right; right; split...
    { apply (SameSideRs_inv a' a b'' a'' a b''); try reflexivity...
      apply (SameSideRs_trans a' a b' b'')...
    }
    { apply (OppositeSideRs_inv a' a b a'' a b); try reflexivity... }
  }
  { right; right; left; split...
    { apply (SameSideRs_inv a (!a') b a a'' b); try reflexivity...
      symmetry. apply OpRs_sym in O'opO''... apply SameSideRs_sym...
    }
    { apply (SameSideRs_OpRs_inv a'' b'' (!a))...
      apply (OppositeSideRs_inv a a' b'' a (!a'') b''); try reflexivity...
      apply OppositeSideRs_sym. apply OppositeSideRs_sym in O'orA'A''.
      apply (OSO_SideRs_trans b'' a' b' a)... apply SameSideRs_sym...
    }
  }
  { destruct (classic (a == a'')) as [ aeqa'' | naeqa'' ].
  { left. split...
    apply (OppositeSideRs_inv a' a'' b'' a' a b'') in BetO'O''A'';
    try reflexivity...
    apply (OOS_SideRs_trans a' a b b'') in BetO'O''A''... symmetry...
  }
  { destruct (classic (a == (!a''))) as [ aopa'' | naopa'' ].
    { right. left. split...
      apply (SameSideRs_inv a' a'' b' a' (!a) b') in O'srO''A'; try reflexivity.
      { destruct (nSameAndOppositeSideRs a' a b'); split...
        apply SameSideRs_sym...
      }
      { apply OpRs_sym... }
    }
    { assert (diaa'' : ![a # a'']).
      { apply nColRs_nColPs. repeat split...
        destruct O'srOA' as [ roaa' _ ].
        destruct O'srO''A' as [ roa'a'' _ ]. rewrite <- roaa'...
      }
      assert (Ord : ![ a' # a, a'' ]).
      { apply SameSideRs_sym in O'srO''A'.
        apply (SameSideRs_trans a' a b' a'')...
      }
        destruct (DecideRaysSide a a'' b) as [ aSFa''b | aOFa''b ]...
        { right; right; left; split...
          apply OppositeSideRs_sym. apply OppositeSideRs_sym in BetO'O''A''.
          apply (OSO_SideRs_trans b'' a'' a' a)...
          apply SameSideRs_sym in aSFa''b.
          apply (OSO_SideRs_trans a' a b a'') in BetO'OA...
          apply SameSideRs_sym.
          apply (SOS_Rs_trans a' a a'')...
        }
        { right; right; right; split...
          apply (OOS_SideRs_trans a' a'' a b'')...
          apply OppositeSideRs_sym in aOFa''b.
          apply OppositeSideRs_sym in BetO'OA.
          apply SameSideRs_sym in Ord. apply (SSO_Rs_trans a' a'' a)...
          apply (OOS_SideRs_trans b a a'' a')...
        }
      }
    }
  }
  { destruct (classic (a == a'')) as [ aeqa'' | naeqa'' ].
    { left. split...
      apply (SameSideRs_inv a'' a' b'' a a' b'') in O''srO'A'';
      try reflexivity; try symmetry...
      apply (OppositeSideRs_inv a'' a' b' a a' b') in BetO''O'A';
      try reflexivity; try symmetry...
      apply OppositeSideRs_sym in BetO''O'A'.
      apply (OSO_SideRs_trans b' a' a b') in BetO''O'A'...
      exfalso. apply OppositeSideRs_irrefl in BetO''O'A'...
    }
    { destruct (classic (a == (!a''))) as [ aopa'' | naopa'' ].
      { right. left. split...
        apply (SameSideRs_OpRs_inv a'' a' b'') in O''srO'A''.
        apply (SameSideRs_inv (!a'') a' b'' a a' b'') in O''srO'A'';
        try reflexivity; try symmetry... apply SameSideRs_sym in BetO''O'A'.
        apply (SameSideRs_inv a' (!a'') b' a' a b') in BetO''O'A';
        try reflexivity; try symmetry...
        apply OppositeSideRs_sym in BetO'OA.
        apply (OSO_SideRs_trans b a a' b'')...
      }
      { assert (diaa'' : ![a # a'']).
        { apply nColRs_nColPs. repeat split...
          destruct O'srOA' as [ roaa' _ ].
          destruct O''srO'A'' as [ roa'a'' _ ]. rewrite <- roaa'...
        }
        { assert (aSFa'a'' : ![ a' # a'', !a ]).
          { apply OppositeSideRs_sym.
            apply (OSO_SideRs_trans a'' a' b' a)... apply SameSideRs_sym... }
          destruct (DecideRaysSide a a'' b) as [ aSFa''b | aOFa''b ]...
          { right; right; left; split...
            assert (a'OFaa'' : ![ a # a'', !a' ]).
            { apply (OSO_SideRs_trans a' a b a'')... apply SameSideRs_sym... }
            assert (aOFa''a' : ![ a'' # a', !a ]). { apply OOO_Rs_trans... }
            apply (OSO_SideRs_trans a a'' a' b'')...
          }
          { right; right; right; split...
            apply (SameSideRs_trans a'' a a' b'')...
            apply OppositeSideRs_sym in aSFa'a''.
            apply SameSideRs_sym.
            apply OppositeSideRs_sym in aSFa'a''.
            apply (SOS_Rs_trans a a' a'')...
            apply OppositeSideRs_sym in BetO'OA.
            apply OppositeSideRs_sym in aOFa''b.
            apply (OOS_SideRs_trans b a a' a'')...
          }
        }
      }
    }
  }
Qed.
Global Instance FlagsRotation_equiv :
  Equivalence EqFlagsRotation
  := Build_Equivalence EqFlagsRotation
     EqFlagsRotation_refl
     EqFlagsRotation_sym
     EqFlagsRotation_trans.

Lemma EqFlagsRotation_EqFlagsOrg :
  forall (F G : Flag),
  EqFlagsRotation F G
    -> da (da F) = da (da G).
Proof.
  intros [ a a' diaa' ][ b b' dibb' ].
  intros [[ H1 H2 ]|[[[ H2 H4 ] H3 ]|[[ H3 H4 ]| H4 ]]]; simpl in *.
  firstorder. rewrite (OpRays_0 b); auto. firstorder. firstorder.
Qed.

Lemma EqFlagsRotation_inv :
  forall (F G F' G' : Flag),
  F === F'
    -> G === G'
    -> EqFlagsRotation F G
    -> EqFlagsRotation F' G'.
Proof with eauto.
  intros F G F' G' [ feqf' SSff' ][ geqg' SSgg' ].
  intros [[ H1 H2 ]|[[ H1 H2 ]|[[ H1 H2 ]|[ H1 H2 ]]]].
  { left; split.
    { transitivity (da G)... transitivity (da F)... symmetry... }
    { apply (SameSideRs_trans (da F')(db F')(db F)(db G'))...
      { apply (SameSideRs_inv (da F)(db F')(db F)(da F')(db F')(db F));
        try reflexivity... apply SameSideRs_sym...
      }
      { apply (SameSideRs_trans (da F')(db F)(db G)(db G'))...
        apply (SameSideRs_inv (da F)(db F)(db G)(da F')(db F)(db G));
        try reflexivity...
        apply (SameSideRs_inv (da G)(db G)(db G')(da F')(db G)(db G'));
        try reflexivity... transitivity (da F)... symmetry...
      }
    }
  }
  { right; left; split.
    { rewrite <- feqf'. rewrite H1. rewrite <- geqg'; reflexivity. }
    { apply (OppositeSideRs_inv (db F')(da F)(db G')(db F')(da F')(db G'));
      try reflexivity...
      apply (OSO_SideRs_trans (db F')(da F)(db G)(db G'))...
      { apply OppositeSideRs_sym. apply OppositeSideRs_sym in H2.
        apply (OSO_SideRs_trans (db G)(da F)(db F)(db F'))...
      }
      { apply (SameSideRs_inv (!(da G))(db G)(db G')(da F)(db G)(db G'));
        try reflexivity... symmetry...
        apply SameSideRs_OpRs_inv in SSgg'...
      }
    }
  }
  { right; right; left. split.
    apply (SameSideRs_inv (da F)(da G)(db F')(da F')(da G')(db F'));
    try reflexivity...
    { apply (SameSideRs_trans (da F)(da G)(db F)(db F'))... }
    { apply (OppositeSideRs_inv (da F)(da G)(db G')(da F')(da G')(db G'));
      try reflexivity...
      apply (OSO_SideRs_trans (da F)(da G)(db G)(db G'))...
    }
  }
  { right; right; right; split.
    { apply (SameSideRs_inv (da G)(da F)(db G')(da G')(da F')(db G'));
      try reflexivity...
      apply (SameSideRs_trans (da G)(da F)(db G)(db G'))...
    }
    { apply (OppositeSideRs_inv (da G)(da F)(db F')(da G')(da F')(db F'));
      try reflexivity...
      apply (OSO_SideRs_trans (da G)(da F)(db F)(db F'))...
    }
  }
Qed.

Example DrawEqRotatedFlagOnDistinctRay :
  forall (a b c : Ray)(diab : ![ a # b ]),
  ![ a # c ]
    -> { d : Ray | exists (dicd : ![ c # d ]),
                   EqFlagsRotation ({{ a # b | diab }})({{ c # d | dicd }}) }.
Proof with eauto.
  intros a b c diab diac.
  unfold EqFlagsRotation. simpl.
  assert (dica' : ![ c # !a ]).
  { apply nColRs_sym; apply nColOpRs_1... }
  destruct (DecideRaysSide a b c diab diac) as [ aSFbc | aOFbc ].
  { exists (!a), dica'.
    right; right; left; split.
    { apply SameSideRs_sym... }
    { apply OpRs_OppositeSideRs... }
  }
  { apply nColRs_sym in diac.
    exists a, diac.
    right; right; right; split.
    { apply SameSideRs_refl... }
    { apply OppositeSideRs_sym... }
  }
Defined.

Example DrawEqRotatedFlagOnRay :
  forall (a b c : Ray)(diab : ![ a # b ])(roac : da a = da c),
  { d : Ray | exists (dicd : ![ c # d ]),
              EqFlagsRotation ({{ a # b | diab }})({{ c # d | dicd }}) }.
Proof with eauto.
  intros a b c diab roac.
  destruct (DrawThirdRayApart a c) as [ d [ diad dicd ]]...
  destruct (DrawEqRotatedFlagOnDistinctRay a b d diab) as [ e H1 ]...
  assert (dide : ![ d # e ]). { destruct H1 as [ H1 H2 ]... }
  assert (H : EqFlagsRotation ({{ a # b | diab }})({{ d # e | dide }})).
  { destruct H1 as [ H1 H2 ]... }
  destruct (DrawEqRotatedFlagOnDistinctRay d e c dide) as [ f H2 ]...
  { apply (nColRs_sym c d)... }
  { assert (dicf : ![ c # f ]). { destruct H2 as [ H3 H2 ]... }
    assert (H3 : EqFlagsRotation ({{ d # e | dide }})({{ c # f | dicf }})).
    { destruct H2 as [ H3 H2 ]... }
    exists f, dicf.
    transitivity ({{ d # e | dide }})...
  }
Defined.

Example DecideEqFlagsRotation :
  forall (F G : Flag),
  da (da F) = da (da G)
    -> { EqFlagsRotation F G } + { ~ EqFlagsRotation F G } .
Proof with eauto.
  intros [ a b diab ][ c d dicd ] rofoFG; simpl in *.
  destruct (DrawEqRotatedFlagOnRay c d a dicd) as [ b' H ]...
  assert (diab' : ![ a # b' ]). { destruct H as [ H1 H2 ]... }
  assert (H1 : EqFlagsRotation ({{ c # d | dicd }})({{ a # b' | diab' }})).
  { destruct H as [ H1 H2 ]... }
  destruct (DecideRaysSide a b b' diab diab') as [ aSFbb' | aOFbb' ].
  { left. symmetry.
    transitivity ({{ a # b' | diab' }})...
    left; split...
    { reflexivity. }
    { apply SameSideRs_sym... }
  }
  { right.
    intros abeqcd.
    assert (abeqab' : EqFlagsRotation
      ({{ a # b | diab }})({{ a # b' | diab' }})).
    { transitivity ({{ c # d | dicd }})... }
      unfold EqFlagsRotation in abeqab'; simpl in *.
    destruct abeqab' as [ H2 |[[ aopa _ ]|[[ aSFab aOFab' ]| H4 ]]].
    { destruct H2 as [ aeqa aSFbb' ].
      apply (nSameAndOppositeSideRs a b b')...
    }
    { apply (OpRs_irrefl a)... }
    { apply SameSideRs_nColRs in aSFab. destruct aSFab as [[ _ diaa ] _ ].
      contradict diaa; colps.
    }
    { destruct H4 as [ _ aOFab ]. apply OppositeSideRs_nColRs in aOFab.
      destruct aOFab as [[ _ diaa ] _ ].
      contradict diaa; colps.
    }
  }
Defined.

Lemma nEqFlagsRotation_EqInvFlagRotation :
  forall (F G : Flag),
  da (da F) = da (da G)
    -> (~ EqFlagsRotation F G <-> EqFlagsRotation F (#G)).
Proof with eauto.
  intros [ f f' diff' ][ g g' digg' ] rofg; simpl in *.
  assert (roff': da f = da f'). { firstorder. }
  assert (rogg': da g = da g'). { firstorder. }
  split.
  { intros nEqFlagsRot.
    unfold EqFlagsRotation in *; simpl in *.
    assert (H1 : ~ (f == g /\ ![ f # f', g'])).
    { contradict nEqFlagsRot... }
    assert (H2 : ~ (f == !g /\ ![ f # g', !f'])).
    { contradict nEqFlagsRot... }
    assert (H3 : ~ (![ f # g, f'] /\ ![ g # g', !f])).
    { contradict nEqFlagsRot... }
    assert (H4 : ~ (![ g # f, g'] /\ ![ f # f', !g])).
    { contradict nEqFlagsRot... }
    clear nEqFlagsRot.
    destruct (classic (f == g')) as [ feqg' | nfeqg' ].
    { destruct (classic (![ f # f' , g ])) as [ fSFf'g | fOFf'g ]...
      contradict H4.
      split.
      { apply (SameSideRs_inv g g' g' g f g'); try reflexivity...
        { symmetry... }
        { apply SameSideRs_refl... }
      }
      { apply (nSameSideRs_OppositeSideRs f g f')...
        { apply nColRs_sym. apply (nColRs_inv g g' f)... symmetry... }
        { intros fSFf'g. apply SameSideRs_sym in fSFf'g. contradiction. }
      }
    }
    { destruct (classic (f == (!g'))) as [ fopg' | nfopg' ].
      { destruct (classic (![ f # f' , g])) as [ fSFf'g | fOFf'g ]...
        { contradict H3.
          split.
          { apply SameSideRs_sym... }
          { apply (OppositeSideRs_inv (!g') g g' f g g'); try reflexivity...
            symmetry... apply OppositeSideRs_sym. apply OpRs_OppositeSideRs.
            apply nColRs_sym...
          }
        }
        { right; left; split...
          apply (nSameSideRs_OppositeSideRs f f' g)...
          apply nColRs_sym.
          apply (nColRs_inv g (!g') f)...
          apply nColOpRs_2...
          symmetry...
        }
      }
      { destruct (classic (![ f # g' , f' ])) as [ fSFg'f' | fOFg'f' ]...
        { destruct (classic (![ g' # f , g ])) as [ g'SFfg | g'OFfg ]...
          { assert (FG : EqFlagsRotation
              ({{ f # f' | diff'}})({{ g # g' | digg' }})).
            { destruct (classic (f == g)) as [ feqg | nfeqg ].
              { left; simpl; split... apply SameSideRs_sym... }
              { destruct (classic (f == (!g))) as [ fopg | nfopg ].
                { right; left; simpl; split...
                  apply (SameSideRs_inv g' f g g' (!g) g) in g'SFfg;
                  try reflexivity... apply SameSideRs_sym in g'SFfg.
                  apply OppositeSideRs_irrefl in g'SFfg... contradiction.
                }
                { destruct (classic (![ f # g , f' ]))
                    as [ fSFgf' | fOFgf' ]; auto.
                  { right; right; left. simpl; split...
                    apply BetRs_OppositeSideRs.
                    apply BetRs_SameSideRs. split...
                    { apply (SameSideRs_trans f g f'); auto;
                      apply SameSideRs_sym...
                    }
                    { apply SameSideRs_sym... }
                  }
                  { apply nSameSideRs_OppositeSideRs in fOFgf'...
                    { right; right; right.
                      simpl; split... apply SameSideRs_sym in fSFg'f'.
                      apply (OSO_SideRs_trans g f f' g') in fOFgf'...
                      apply SOS_Rs_trans...
                      apply OppositeSideRs_sym...
                    }
                    { apply nColRs_nColPs. repeat split... }
                  }
                }
              }
            }
            { destruct FG as [ H1' |[ H2' |[ H3' | H4' ]]];
              try contradiction.
            }
          }
          { right; right; left. split...
            apply nSameSideRs_OppositeSideRs...
            { apply nColRs_nColPs. repeat split...
              { rewrite rofg. symmetry... }
              { contradict nfeqg'; symmetry... }
              { contradict nfopg'. rewrite nfopg'. apply OpOpRs. }
            }
            { apply nColRs_sym... }
          }
        }
        { apply nSameSideRs_OppositeSideRs in fOFg'f'...
          { destruct (classic (![ g' # f , g ]))
              as [ g'SFfg | g'OFfg ]...
            apply nSameSideRs_OppositeSideRs in g'OFfg.
            { assert (FG : EqFlagsRotation
                ({{ f # f' | diff' }})({{ g # g' | digg' }})).
              { destruct (classic (f == g)) as [ feqg | nfeqg ]...
                { apply (OppositeSideRs_inv f g' g g g' g) in g'OFfg;
                  try reflexivity...
                  apply OppositeSideRs_irrefl in g'OFfg...
                  contradiction.
                }
                { destruct (classic (f == (!g))) as [ fopg | nfopg ].
                  { right; left; simpl; split... apply OppositeSideRs_sym... }
                  { destruct (classic (![ f # g , f' ]))
                      as [ fSFgf' | fOFgf' ]...
                    { right; right; left. simpl; split...
                      apply OOO_Rs_trans...
                      apply (OSO_SideRs_trans g' f f' g)...
                      apply SameSideRs_sym...
                    }
                    { apply nSameSideRs_OppositeSideRs in fOFgf'...
                      { right; right; right. simpl; split...
                        apply SameSideRs_sym. apply BetRs_SameSideRs.
                        apply BetRs_SO_Rs. split...
                        apply OppositeSideRs_sym in fOFg'f'.
                        apply OppositeSideRs_sym in fOFgf'.
                        apply (OOS_SideRs_trans f' f g' g)...
                      }
                      { apply nColRs_nColPs. repeat split... }
                    }
                  }
                }
              }
              { destruct FG
                  as [ H1' |[ H2' |[ H3' | H4' ]]]; try contradiction.
              }
            }
            { apply nColRs_nColPs. repeat split... rewrite rofg.
              symmetry... contradict nfeqg'. symmetry... contradict nfopg'.
              rewrite nfopg'. apply OpOpRs...
            }
            { apply nColRs_sym... }
          }
          { apply nColRs_nColPs. repeat split... rewrite rofg... }
        }
      }
    }
  }
  intros FG FG'.
  symmetry in FG.
  assert (dig'g : ![ g' # g ]). { apply (nColRs_sym g g' digg'). }
  assert (GG' : EqFlagsRotation ({{ g' # g | dig'g }})({{ g # g' | digg' }})).
  { transitivity ({{ f # f' | diff' }})... }
  symmetry in GG'.
  destruct GG' as [[ H0 H1 ]| H2 ]; simpl in *.
  { apply nColRs_nColPs in dig'g. symmetry in H0.
    destruct dig'g as [ G1 [ G2 G3 ]]; contradiction.
  }
  destruct H2 as [[ H0 H1 ]| H2 ]; simpl in *.
  { apply nColRs_sym in dig'g. apply nColRs_nColPs in dig'g.
    destruct dig'g as [ G1 [ G2 G3 ]]; contradiction.
  }
  destruct H2 as [[ H0 H1 ]| H2 ].
  { apply OppositeSideRs_irrefl in H1... }
  destruct H2 as [ H0 H1 ].
  apply OppositeSideRs_irrefl in H1; try contradiction.
Qed.

(* Flag Translation *)

Definition EqFlagsTranslation (F G : Flag) : Prop
  := (da F ~~ da G) /\ [ da (da F) # db (da F) | db (db F), db (db G) ].
Definition EqOpFlagTrans (F G : Flag) : Prop
  := (da F ~~ !(da G)) \/ ((da F ~~ da G)
     /\ [ db (db F) | da (da F) # db (da F) | db (db G) ]).

Lemma EqFlagsTranslation_refl :
  reflexive Flag EqFlagsTranslation.
Proof.
  unfold reflexive.
  intros [ a b diba ].
  unfold EqFlagsTranslation. simpl.
  split; [ reflexivity | apply SameSideRs_refl; auto ].
Qed.
Lemma EqFlagsTranslation_sym :
  symmetric Flag EqFlagsTranslation.
Proof with eauto.
  intros [ a b diab ][ a' b' dia'b' ][ aeqa' aSFbb' ].
  split.
  { symmetry... }
  { assert (Colaa' : ![a, a']). { apply EqDirRs_ColRs... }
    destruct Colaa' as [ x [ Oox [ Aox [ O'ox A'ox ]]]].
    repeat split.
    { apply (dp a'). }
    { destruct aSFbb' as [ H1 [ y [ H2 [ H3 H4 ]]]].
      apply SS_sym in H4.
      assert (xeqy : x = y); eqls.
      subst y.
      exists x; split...
    }
  }
Qed.
Lemma EqFlagsTranslation_trans :
  transitive Flag EqFlagsTranslation.
Proof with eauto.
  unfold transitive.
  intros [ a b diab ][ a' b' dia'b' ][ a'' b'' dia''b'' ].
  intros [ aeqa' aSFbb' ][ a'eqa'' a'SFb'b'' ].
  split; simpl in *.
  { rewrite aeqa'... }
  { assert (Colaa' : ![a, a']). { apply EqDirRs_ColRs... }
    assert (Cola'a'' : ![a', a'']). { apply EqDirRs_ColRs... }
    destruct Colaa' as [ x [ Oox [ Aox [ O'ox A'ox ]]]].
    destruct Cola'a'' as [ x' [ O'ox' [ A'ox' [ O''ox A''ox ]]]].
    assert (x'eqx : x' = x).
    { apply (DiPs_EqLs (da a')(db a') x' x (dp a'))... }
    subst. destruct aSFbb' as [ _ [ x' [ Oox' [ Aox' OAsfBB' ]]]].
    assert (xeqx' : x' = x).
    { apply (DiPs_EqLs (da a)(db a) x' x (dp a))... }
    subst.
    destruct a'SFb'b'' as [ _ [ x' [ Oox'' [ Aox'' OAsfBB'' ]]]].
    assert (xeqx' : x' = x).
    { apply (DiPs_EqLs (da a')(db a') x' x (dp a'))... }
    subst.
    repeat split.
    { apply (dp a). }
    { exists x; do 2 try split...
      apply (SS_trans (db b)(db b')(db b'') x)...
    }
  }
Qed.
Global Instance FlagTransl_equiv :
  Equivalence EqFlagsTranslation
  := Build_Equivalence EqFlagsTranslation
     EqFlagsTranslation_refl
     EqFlagsTranslation_sym
     EqFlagsTranslation_trans.

Example DecideEqFlagsTranslation_1 :
  forall (F G : Flag),
  da F ~~ da G
    -> { EqFlagsTranslation F G } + { ~ EqFlagsTranslation F G } .
Proof with eauto.
  intros [ a b diab ][ c d dicd ] asdc.
  destruct (proj1 (nColRs_nColPs a b) diab) as [ roab [ aeqb aopb ]].
  destruct (proj1 (nColRs_nColPs c d) dicd) as [ rocd [ ceqd copd ]].
  unfold EqFlagsTranslation; simpl in *.
  destruct a as [ O A nAeqO ]. destruct b as [ O' B nBeqO ].
  simpl in *. subst O'.
  destruct c as [ O' C nCeqO' ]. destruct d as [ O'' D nDeqO' ].
  simpl in *. subst O''.
  destruct (DrawOppositePoint O B) as [ B' [ BetBOB' _ ]]...
  destruct (BetPs_3DiPs B O B') as [ _ [ nOeqB' nBeqB' ]]...
  destruct (DrawOppositePoint O' C) as [ C' [ BetCO'C' _ ]]...
  destruct (BetPs_3DiPs C O' C') as [ _ [ nO'eqC' nCeqC' ]]...
  destruct (DrawOppositePoint O' D) as [ D' [ BetDO'D' _ ]]...
  destruct (BetPs_3DiPs D O' D') as [ _ [ nO'eqD' nDeqD' ]]...
  destruct (DrawExtensionLinePP A O) as [ x [ Aox Oox ]]...
  assert (nBox : ~ [B @ x]).
  { contradict aeqb. split; simpl... repeat split...
    contradict aopb. apply OpRs_BetPs...
  }
  assert (nDox : ~ [D @ x]).
  { contradict ceqd. split; simpl...
    repeat split...
    { destruct asdc as [[ OeqO' OsrAC ]|[[ H2 H4 ]|[ H3 H5 ]]];
      simpl in *.
      { subst O'. exists x; split; try split; incpt. }
      { assert ([O # A, C]).
        { apply SR_sym in H2. apply BetPs_sym in H4.
          apply SR_trans with O'... apply BetPs_SR...
        }
        exists x; split; try split; incpt.
      }
      { assert (O'ox : [O' @ x]); incpt 2.
        exists x; repeat split; incpt 2. }
    }
    { contradict copd. apply OpRs_BetPs... }
  }
  destruct (DecideSameSide B D x) as [ SSxBD | OSxBD ]...
  { left; split... split... }
  { right. intros [ _ SSxBD ].
    destruct SSxBD as [ _ [ y [ Ooy [ Aoy SSxBD ]]]].
    assert (xeqy : x = y); eqls.
    subst.
    destruct OSxBD as [ _ [ _ H1 ]], SSxBD as [ _ [ _ H2 ]]; contradiction.
  }
Defined.

Example DecideEqFlagsTranslation_2 :
  forall (F G : Flag),
  ![ da F, da G ]
    -> { EqFlagsTranslation F G } + { EqOpFlagTrans F G }.
Proof with eauto.
  intros [ a a' diaa' ][ b b' dibb' ] diab; simpl in *.
  destruct (DecideRayDirection a b) as [ a_b | na_b ]...
  { remember diaa' as t. destruct t as [ roaa' nColaa' ].
    remember dibb' as t. destruct t as [ robb' nColbb' ].
    unfold EqFlagsTranslation; simpl. clear Heqt Heqt0.
    assert (nColab' : ~ [ da a, db a, db b' ]).
    { apply EqDirRs_ColRs in a_b.
      destruct a_b as [ x [ oax [ pax [ obx pbx ]]]].
      intros [ x' [ oax' [ pax' pb'x' ]]].
      assert (xeqx' : x' = x).
      { apply (DiPs_EqLs (da a)(db a) x' x (dp a))... }
      subst.
      contradict nColbb'. exists x; split...
    }
    destruct (DecideSameHalfplane (da a)(db a)(db a')(db b'))
      as [ SS | OS ]...
    { ncolperps. }
    { right; right; simpl; split... }
  }
  { right; left; simpl... apply ColRs_DiDirRs_EqDirOpRs... }
Defined.

Lemma nEqFlagsTranslation_EqOpFlagsTrans :
  forall (F G : Flag),
  ![ da F, da G ]
    -> (~ EqFlagsTranslation F G <-> EqOpFlagTrans F G).
Proof with eauto.
  intros [ a a' diaa' ][ b b' dibb' ][ x [ oax [ pax [ obx pbx ]]]];
  simpl in *.
  remember diaa' as t. destruct t as [ roaa' nColaa' ].
  remember dibb' as t. destruct t as [ robb' nColbb' ].
  unfold EqFlagsTranslation, EqOpFlagTrans; simpl. clear Heqt Heqt0.
  split.
  { intros nEqFlags.
    destruct (DecideRayDirection a b) as [ a_b | na_b ].
    { exists x; split... }
    { right; simpl; do 2 try split...
      { apply (dp a). }
      { exists x; do 2 try split...
        destruct (DecideSameSide (db a')(db b') x)
          as [ SSxA'B' | OSxA'B' ]...
        contradict nColaa'. exists x; split...
        contradict nColbb'. exists x; split...
        assert (EqF : EqFlagsTranslation
          ({{ a # a' | diaa' }})({{ b # b' | dibb' }})).
        { split; simpl... split... apply (dp a). }
        contradiction.
      }
    }
    { apply ColRs_DiDirRs_EqDirOpRs in na_b.
      left... exists x; split...
    }
  }
  { intros [ H1 |[ H2 H3]][ H4 H5 ]; simpl in *.
    { rewrite H4 in H1. apply EqDirOpRs_irrefl in H1... }
    { destruct H3 as [ _ [ x' [ oax' [ pax' OSxA'B' ]]]].
      assert (xeqx' : x' = x).
      { apply (DiPs_EqLs (da a)(db a) x' x (dp a)); split; split... }
      subst.
      destruct H5 as [ _ [ x'' [ oax'' [ pax'' SSxA'B' ]]]].
      assert (xeqx'' : x'' = x).
      { apply (DiPs_EqLs (da a)(db a) x'' x (dp a)); split; split... }
      subst.
      destruct OSxA'B' as [ _ [ _ G1 ]].
      destruct SSxA'B' as [ _ [ _ G2 ]].
      contradict G2...
    }
  }
Qed.

Lemma EqFlagsTranslation_EqFlagsRotation :
  forall (F G : Flag),
  da (da F) = da (da G)
    -> EqFlagsTranslation F G
    -> EqFlagsRotation F G.
Proof with eauto.
  intros [ a a' diaa' ][ b b' dibb' ] roab [ G1 G2 ]; simpl in *.
  destruct G1 as [[ _ OsrAB ]|[[ H1 H2 ]|[ H3 H4 ]]];
  destruct G2 as [ rca [ x [ Oox [ Aox SSxA'B' ]]]]; simpl in *.
  { left; do 2 split; simpl...
  { firstorder. }
  { split.
    { rewrite roab. firstorder. }
      { split.
        { apply (dp a). }
        { exists x; split... }
      }
    }
  }
  destruct H1 as [ nroab _ ]; symmetry in roab; contradict nroab...
  destruct H3 as [ nroab _ ]; contradict nroab...
Qed.

Lemma EqFlagsRotation_EqFlagsTranslation :
  forall (F G : Flag),
  da F == da G
    -> EqFlagsRotation F G
    -> EqFlagsTranslation F G.
Proof with eauto.
  unfold EqFlagsTranslation, EqFlagsRotation, EqRaysDir.
  intros [ a a' diaa' ][ b b' dibb' ] aeqb [[ _ H ]| H ];
  try destruct H as [[ aopb H ]|[[ H1 H2 ]|[ H3 H4 ]]];
  try destruct H1 as [ roab [ roaa' [ _ [ x [ Oox [ Aox SSxBA' ]]]]]];
  try destruct H2 as [ roba [ robb' [ _ [ y [ Ooy [ Boy OSyAB' ]]]]]];
  try destruct H3 as [ roba [ robb' [ rcb [ x [ Oox [ Box SSxAB' ]]]]]];
  try destruct H4 as [ roab [ roaa' [ rca [ y [ Ooy [ Aoy OSyBA' ]]]]]];
  simpl in *; split; try destruct H as [ H1 [ H2 H ]]...
  { rewrite aeqb in aopb. apply OpRs_irrefl in aopb. contradiction. }
  { do 2 try split... apply (dp a). exists x; do 2 try split...
    destruct aeqb as [ _ [ _ [ _ [[ t [ Oot [ Aot Bot ]]] _ ]]]].
    assert (xeqy : x = y).
    { rewrite (DiPs_EqLs (da a)(db a) x t)...
      apply (DiPs_EqLs (da a)(db b) t y)...
      { rewrite roab. apply (dp b). }
      { repeat split... rewrite roab... }
      { apply (dp a). }
    }
    subst y.
    destruct SSxBA'; contradiction.
  }
  { do 2 try split...
    exists y; do 2 try split...
    destruct aeqb as [ H1 [ H2 [ H3 [[ t [ Oot [ Aot Bot ]]] H4 ]]]].
    assert (xeqy : x = y).
    { rewrite (DiPs_EqLs (da a)(db a) y t)...
      apply (DiPs_EqLs (da a)(db b) x t)...
      { repeat split... rewrite <- roba... }
    }
    subst y.
    assert (H : ![ a # a', (!b)]).
    { repeat split... }
    apply SameSideRs_OpRs_OppositeSide in H...
    destruct H as [ _ [ x' [ ox [ dx H6 ]]]].
    assert (xeqx' : x = x'); eqls. subst x'.
    destruct H6. contradiction.
  }
Qed.

Lemma EqFlagsTranslation_nSSS :
  forall (F G H : Flag),
  ~ (EqFlagsTranslation F (#G)
  /\ EqFlagsTranslation G (#H)
  /\ EqFlagsTranslation H (#F)).
Proof with eauto.
  intros [ a a' diaa' ][ b b' dibb' ][ c c' dicc' ][ H1 [ H2 H3 ]];
  destruct H1 as [ a_b' [ _ [ x [ oaox [ paox SSxA'B ]]]]];
  destruct H2 as [ b_c' [ _ [ y [ oboy [ pboy SSyB'C ]]]]];
  destruct H3 as [ c_a' [ _ [ z [ ocoz [ pcoz SSzC'A ]]]]]; simpl in *.
  assert (roaa' : da a = da a'). { firstorder. }
  assert (robb' : da b = da b'). { firstorder. }
  assert (rocc' : da c = da c'). { firstorder. }
  assert (nxeqy : x <> y).
  { destruct dibb' as [ _ dibb' ]. contradict dibb'. subst y.
    apply EqDirRs_ColRs in a_b'.
    destruct a_b' as [ x' [ oax' [ pax' [ ob'x' pb'x' ]]]].
    assert (xeqx' : x' = x).
    { apply (DiPs_EqLs (da a)(db a) x' x (dp a)); repeat split... }
    subst.
    exists x; repeat split...
  }
  assert (nyeqz : y <> z).
  { destruct dicc' as [ _ dicc' ]. contradict dicc'. subst z.
    apply EqDirRs_ColRs in b_c'.
    destruct b_c' as [ y' [ oby' [ pby' [ oc'y' pc'y' ]]]].
    assert (yeqy' : y' = y).
    { apply (DiPs_EqLs (da b)(db b) y' y (dp b)); repeat split... }
    subst.
    exists y; repeat split...
  }
  assert (nxeqz : x <> z).
  { destruct diaa' as [ _ diaa' ]. contradict diaa'. subst z.
    apply EqDirRs_ColRs in c_a'.
    destruct c_a' as [ z' [ ocz' [ pcz' [ oa'z' pa'z' ]]]].
    assert (zeqz' : z' = x).
    { apply (DiPs_EqLs (da c)(db c) z' x (dp c)); repeat split... }
    subst.
    exists x; repeat split...
  }
  assert (Colab' : ![a, b']). { apply EqDirRs_ColRs... }
  assert (Colbc' : ![b, c']). { apply EqDirRs_ColRs... }
  assert (Colca' : ![c, a']). { apply EqDirRs_ColRs... }
  destruct Colab' as [ x' [ oax [ pax [ ob'x pb'x ]]]].
  assert (xeqx' : x' = x).
  { apply (DiPs_EqLs (da a)(db a) x' x (dp a)); repeat split... }
  subst.
  destruct Colbc' as [ y' [ oby [ pby [ oc'y pc'y ]]]].
  assert (yeqy' : y' = y).
  { apply (DiPs_EqLs (da b)(db b) y' y (dp b)); repeat split... }
  subst.
  destruct Colca' as [ z' [ ocz [ pcz [ oa'z pa'z ]]]].
  assert (zeqz' : z' = z).
  { apply (DiPs_EqLs (da c)(db c) z' z (dp c)); repeat split... }
  subst.
  destruct a_b' as [[ roab' AsrA'B'' ]| F ];
  destruct b_c' as [[ robc' BsrB'C'' ]| G ];
  destruct c_a' as [[ roca' CsrC'A'' ]| H ].
  { assert (aeqb' : a == b'). { split... }
    assert (beqc' : b == c'). { split... }
    assert (ceqa' : c == a'). { split... }
    assert (BetRacb : ![ a # c # b ]).
    { apply BetRs_SameSideRs.
      split.
      { apply (SameSideRs_inv a a' b a c b); try reflexivity; try symmetry...
        repeat split... rewrite roab'... apply (dp a).
      }
      { apply SameSideRs_sym.
        apply (SameSideRs_inv b b' c b a c);
        try reflexivity; try symmetry...
        repeat split... rewrite robc'... apply (dp b).
      }
    }
    { apply BetRs_sym in BetRacb.
      apply (BetRs_inv b c a c' c a) in BetRacb;
      try reflexivity; try symmetry...
      { assert (OSzC'A : [ db c'| z | db a]).
        { destruct BetRacb as [ _ [ roca BR ]].
          apply BR_OH in BR. rewrite <- rocc' in BR.
          destruct BR as [ _ [ z' [ ocz' [ pbz' H2 ]]]].
          assert (zeqz' : z' = z).
          { apply (DiPs_EqLs (da c)(db c) z' z (dp c)); split; split... }
          subst...
        }
        { destruct SSzC'A as [ H1 [ H2 H3 ]].
          destruct OSzC'A as [ F1 [ F2 F3 ]].
          contradiction.
        }
      }
      { symmetry... }
    }
  }
  { destruct H as [[ H1 H2 ]|[ H1 H2 ]];
    assert (nroca' : da c <> da a'); dips.
  }
  { destruct G as [[ G1 G2 ]|[ G1 G2 ]];
    assert (nrobc' : da b <> da c'); dips.
  }
  { destruct H as [[ H1 H2 ]|[ H1 H2 ]]; contradict nyeqz;
    apply (DiPs_EqLs (da c)(da a') y z); do 2 try split; dips.
  }
  { destruct F as [[ H1 H2 ]|[ H1 H2 ]];
    assert (nroab' : da a <> da b'); dips.
  }
  { destruct F as [[ H1 H2 ]|[ H1 H2 ]]; contradict nxeqz;
    apply (DiPs_EqLs (da a)(da b') x z); do 2 try split; dips.
  }
  { destruct F as [[ H1 H2 ]|[ H1 H2 ]]; contradict nxeqy;
    apply (DiPs_EqLs (da a)(da b') x y); do 2 try split; dips.
  }
  { destruct F as [[ F1 F2 ]|[ F3 F4 ]];
    destruct G as [[ G1 G2 ]|[ G3 G4 ]];
    destruct H as [[ H1 H2 ]|[ H3 H4 ]].
    { assert (OSxA'B : [ db a' | x | db b]).
      { apply (OSO_trans (db a')(da c)(db b) x)...
        { split.
          { contradict nxeqz.
            apply (DiPs_EqLs (da a')(db a') x z (dp a')); split; split...
            rewrite <- roaa'...
          }
          { split.
            { contradict nxeqz.
              apply (DiPs_EqLs (da c)(da a') x z).
              firstorder. split; split...
              rewrite <- roaa'...
            }
            { exists (da a'); split... rewrite <- roaa'...
              apply BetPs_sym...
            }
          }
        }
        { apply (SR_SS (da b)(da c)(db b) x)...
          { rewrite robb'... }
          { contradict nxeqz.
            apply (DiPs_EqLs (da c)(da a') x z).
            { firstorder. }
            { split; split... rewrite <- roaa'... }
          }
          { rewrite rocc'... }
        }
      }
      destruct SSxA'B as [ Q1 [ Q2 Q3 ]].
      destruct OSxA'B as [ R1 [ R2 R3 ]].
      contradiction.
    }
    { assert (OSzC'A : [ db c' | z | db a]).
      { apply (OSO_trans (db c')(da b)(db a) z)...
        { split.
          { contradict nyeqz.
            apply (DiPs_EqLs (da c')(db c') y z (dp c')); split; split...
            rewrite <- rocc'...
          }
          { split.
            { contradict nyeqz.
              apply (DiPs_EqLs (da b)(da c') y z). firstorder.
              split; split... rewrite <- rocc'...
            }
            { exists (da c'); split...
              rewrite <- rocc'...
              apply BetPs_sym...
            }
          }
        }
        { apply (SR_SS (da a)(da b)(db a) z)...
          rewrite roaa'... contradict nyeqz.
          apply (DiPs_EqLs (da b)(da c') y z). firstorder.
          split; split; auto. rewrite <- rocc'... rewrite robb'...
        }
      }
      destruct SSzC'A as [ Q1 [ Q2 Q3 ]].
      destruct OSzC'A as [ R1 [ R2 R3 ]].
      contradiction.
    }
    { assert (OSyB'C : [ db b' | y | db c]).
      { apply (OSO_trans (db b')(da a)(db c) y)...
        { split.
          { contradict nxeqy.
            apply (DiPs_EqLs (da b')(db b') x y (dp b')); split; split...
            rewrite <- robb'...
          }
          { split.
            { contradict nxeqy.
               apply (DiPs_EqLs (da a)(da b') x y).
               firstorder. split; split...
               rewrite <- robb'...
            }
            { exists (da b'); split...
              rewrite <- robb'...
              apply BetPs_sym...
            }
          }
        }
        { apply (SR_SS (da c)(da a)(db c) y)...
          { rewrite rocc'... }
          { contradict nxeqy.
            apply (DiPs_EqLs (da a)(da b') x y). firstorder.
            split; split... rewrite <- robb'...
          }
          { rewrite roaa'... }
        }
      }
      destruct SSyB'C as [ Q1 [ Q2 Q3 ]].
      destruct OSyB'C as [ R1 [ R2 R3 ]].
      contradiction.
    }
    { assert (OSxA'B : [ db a' | x | db b]).
      { apply OS_sym.
        apply (OSO_trans (db b)(da c)(db a') x)...
        { split.
          { contradict nxeqy.
            apply (DiPs_EqLs (da b)(db b) x y (dp b)); split; split...
            rewrite robb'...
          }
          { split.
            { contradict nxeqy.
              apply (DiPs_EqLs (da c')(da b) x y).
              { firstorder. }
              split; split...
              rewrite <- rocc'... rewrite robb'...
            }
            { exists (da b); split...
              rewrite robb'... apply BetPs_sym... rewrite rocc'...
            }
          }
        }
        { apply (SR_SS (da a')(da c)(db a') x)...
          { rewrite <- roaa'... }
          { contradict nxeqy.
            apply (DiPs_EqLs (da c')(da b) x y).
            { firstorder. }
            { split; split... rewrite <- rocc'... rewrite robb'... }
          }
        }
      }
      destruct SSxA'B as [ Q1 [ Q2 Q3 ]].
      destruct OSxA'B as [ R1 [ R2 R3 ]].
      contradiction.
    }
    { assert (OSxA'B : [ db a' | x | db b]).
      { apply (OSO_trans (db a')(da c)(db b) x)...
        { split.
          { contradict nxeqz.
            apply (DiPs_EqLs (da a')(db a') x z (dp a')); split; split...
            rewrite <- roaa'...
          }
          { split.
            { contradict nxeqz.
              apply (DiPs_EqLs (da c)(da a') x z).
              { firstorder. }
              { split; split... rewrite <- roaa'... }
            }
            { exists (da a'); split... rewrite <- roaa'...
              apply BetPs_sym...
            }
          }
        }
        { apply (SR_SS (da b)(da c)(db b) x)...
          { rewrite robb'... }
          { contradict nxeqz.
            apply (DiPs_EqLs (da c)(da a') x z). firstorder.
            split; split... rewrite <- roaa'...
          }
          { rewrite rocc'... }
        }
      }
      destruct SSxA'B as [ Q1 [ Q2 Q3 ]].
      destruct OSxA'B as [ R1 [ R2 R3 ]].
      contradiction.
    }
    { assert (OSyB'C : [ db b' | y | db c]).
      { apply OS_sym.
        apply (OSO_trans (db c)(da a)(db b') y)...
        { split.
          { contradict nyeqz.
            apply (DiPs_EqLs (da c)(db c) y z (dp c)); split; split...
            rewrite rocc'...
          }
          { split.
            { contradict nyeqz.
              apply (DiPs_EqLs (da a')(da c) y z).
              { firstorder. }
              { split; split...
                { rewrite <- roaa'... }
                { rewrite rocc'... }
              }
            }
            { exists (da c); split...
              rewrite rocc'... rewrite roaa'.
              apply BetPs_sym...
            }
          }
        }
        { apply (SR_SS (da b')(da a)(db b') y)...
          { rewrite <- robb'... }
          { contradict nyeqz.
            apply (DiPs_EqLs (da a')(da c) y z).
            { firstorder. }
            { split; split...
              { rewrite <- roaa'... }
              { rewrite rocc'... }
            }
          }
        }
      }
      destruct SSyB'C as [ Q1 [ Q2 Q3 ]].
      destruct OSyB'C as [ R1 [ R2 R3 ]].
      contradiction.
    }
    { assert (OSzC'A : [ db c' | z | db a]).
      { apply OS_sym.
        apply (OSO_trans (db a)(da b)(db c') z)...
        { split.
          { contradict nxeqz.
            apply (DiPs_EqLs (da a)(db a) x z (dp a)); split; split...
            rewrite roaa'...
          }
          { split.
            { contradict nxeqz.
              apply (DiPs_EqLs (da b')(da a) x z).
              { firstorder. }
              { split; split...
                { rewrite <- robb'... }
                { rewrite roaa'... }
              }
            }
            { exists (da a); split...
              rewrite roaa'... rewrite robb'. apply BetPs_sym...
            }
          }
        }
        { apply (SR_SS (da c')(da b)(db c') z)...
          { rewrite <- rocc'... }
          { contradict nxeqz.
            apply (DiPs_EqLs (da b')(da a) x z).
            { firstorder. }
            { split; split... rewrite <- robb'... rewrite roaa'... }
          }
        }
      }
      destruct SSzC'A as [ Q1 [ Q2 Q3 ]].
      destruct OSzC'A as [ R1 [ R2 R3 ]].
      contradiction.
    }
    { assert (OSxA'B : [ db a' | x | db b]).
      { apply OS_sym.
        apply (OSO_trans (db b)(da c)(db a') x)...
        { split.
          { contradict nxeqy.
            apply (DiPs_EqLs (da b)(db b) x y (dp b)); split; split...
            rewrite robb'...
          }
          { split.
            { contradict nxeqy.
              apply (DiPs_EqLs (da c')(da b) x y).
              { firstorder. }
              { split; split... rewrite <- rocc'... rewrite robb'... }
            }
            { exists (da b); split...
              { rewrite robb'... }
              { apply BetPs_sym... rewrite rocc'... }
            }
          }
        }
        { apply (SR_SS (da a')(da c)(db a') x)...
          { rewrite <- roaa'... }
          { contradict nxeqy.
            apply (DiPs_EqLs (da c')(da b) x y).
            { firstorder. }
            { split; split...
              { rewrite <- rocc'... }
              { rewrite robb'... }
            }
          }
        }
      }
      destruct SSxA'B as [ Q1 [ Q2 Q3 ]].
      destruct OSxA'B as [ R1 [ R2 R3 ]].
      contradiction.
    }
  }
Qed.

Lemma EqFlagsTranslation_nSOO :
  forall (F G H : Flag),
  da G ~~ db H
    -> da H ~~ db F
    -> ~ (EqFlagsTranslation F (#G)
       /\ EqOpFlagTrans G (#H)
       /\ EqOpFlagTrans H (#F)).
Proof with eauto.
  intros [ a a' diaa' ][ b b' dibb' ][ c c' dicc' ].
  intros b_c' c_a' [ H1 [ H2 H3 ]];
  destruct H1 as [ a_b' [ _ [ x [ oaox [ paox SSxA'B ]]]]];
  destruct H2 as [ H2 |[ _ [ _ [ y [ oboy [ pboy OSyB'C ]]]]]];
  destruct H3 as [ H3 |[ _ [ _ [ z [ ocoz [ pcoz OSzC'A ]]]]]];
  simpl in *.
  { rewrite b_c' in H2. apply EqDirOpRs_irrefl in H2. firstorder. }
  { rewrite b_c' in H2. apply EqDirOpRs_irrefl in H2. firstorder. }
  { rewrite c_a' in H3. apply EqDirOpRs_irrefl in H3. firstorder. }
  { assert (roaa' : da a = da a'). { firstorder. }
    assert (robb' : da b = da b'). { firstorder. }
    assert (rocc' : da c = da c'). { firstorder. }
    assert (nxeqy : x <> y).
    { destruct dibb' as [ _ dibb' ]. contradict dibb'.
      subst y. apply EqDirRs_ColRs in a_b'.
      destruct a_b' as [ x' [ oax' [ pax' [ ob'x' pb'x' ]]]].
      assert (xeqx' : x = x').
      { apply (DiPs_EqLs (da a)(db a) x x' (dp a)); repeat split... }
      subst x'.
      exists x; repeat split...
    }
    assert (nyeqz : y <> z).
    { destruct dicc' as [ _ dicc' ]. contradict dicc'.
      subst z. apply EqDirRs_ColRs in b_c'.
      destruct b_c' as [ y' [ oby' [ pby' [ oc'y' pc'y' ]]]].
      assert (yeqy' : y = y').
      { apply (DiPs_EqLs (da b)(db b) y y' (dp b)); repeat split... }
      subst y'.
      exists y; repeat split...
    }
    assert (nxeqz : x <> z).
    { destruct diaa' as [ _ diaa' ]. contradict diaa'.
      subst z. apply EqDirRs_ColRs in c_a'.
      destruct c_a' as [ z' [ ocz' [ pcz' [ oa'z' pa'z' ]]]].
      assert (zeqz' : x = z').
      { apply (DiPs_EqLs (da c)(db c) x z' (dp c)); repeat split... }
      subst z'.
      exists x; repeat split...
    }
    assert (Colab' : ![a, b']). { apply EqDirRs_ColRs... }
    assert (Colbc' : ![b, c']). { apply EqDirRs_ColRs... }
    assert (Colca' : ![c, a']). { apply EqDirRs_ColRs... }
    destruct Colab' as [ x' [ oax [ pax [ ob'x pb'x ]]]].
    assert (xeqx' : x = x').
    { apply (DiPs_EqLs (da a)(db a) x x' (dp a)); split; split... }
    subst x'.
    destruct Colbc' as [ y' [ oby [ pby [ oc'y pc'y ]]]].
    assert (yeqy' : y = y').
    { apply (DiPs_EqLs (da b)(db b) y y' (dp b)); split; split... }
    subst y'.
    destruct Colca' as [ z' [ ocz [ pcz [ oa'z pa'z ]]]].
    assert (zeqz' : z = z').
    { apply (DiPs_EqLs (da c)(db c) z z' (dp c)); split; split... }
    subst z'.
    destruct a_b' as [[ roab' AsrA'B'' ]| F ];
    destruct b_c' as [[ robc' BsrB'C'' ]| G ];
    destruct c_a' as [[ roca' CsrC'A'' ]| H ].
    { assert (aeqb' : a == b'). { split... }
      assert (beqc' : b == c'). { split... }
      assert (ceqa' : c == a'). { split... }
      assert (BetRabc : ![ a # b # c ]).
      { apply BetRs_SO_Rs.
        split.
        { apply (SameSideRs_inv a b a' a b c);
          try reflexivity; try symmetry...
          repeat split...
          { rewrite roab'... }
          { apply (dp a). }
          { exists x; split... split... apply SS_sym; auto. }
        }
        { apply (OppositeSideRs_inv b' b c a b c);
          try reflexivity; try symmetry...
          { unfold OpRay.
            destruct (DrawOpRay b') as [ d [ robd Betbod ]]; simpl.
            repeat split...
            { rewrite robc'... }
            { rewrite <- robd... }
            { apply (dp b). }
            { exists y. do 2 try split...
              eapply OOS_trans... apply OS_sym...
              assert (pb'y : ~ [db b' @ y]); destruct OSyB'C...
              rewrite <- robb' in Betbod.
              assert (pdy : ~ [db d @ y]). { contradict pb'y. incpt 2. }
              repeat split...
            }
          }
        }
      }
      assert (BetRacb : ![ c # b, !a ]).
      { apply (OppositeSideRs_inv a c c' a c b);
        try reflexivity; try symmetry...
        do 2 try split...
        { rewrite <- OpRays_0. rewrite roab'.
          rewrite rocc'. rewrite <- robc'... }
        { assert (paz : [da a @ z]). { rewrite roaa'... }
          assert (npaz : ~ [db a @ z]).
          { destruct OSzC'A as [ H1 [ H2 _ ]]... }
          assert ([db a # da a # db (!a)]). { apply OpRays_1. }
          do 2 try split...
          { apply (dp c). }
          { exists z; split... split... apply SS_sym...
            apply (OOS_trans (db (!a)) (db a) (db c') z)...
            apply OS_sym. repeat split... contradict npaz. incpt.
            apply OS_sym...
          }
        }
      }
      assert (H := BetRabc). apply BetRs_sym in BetRabc.
      apply BetRs_nPerBetRs in BetRabc. contradict BetRabc.
      apply BetRs_sym. apply BetRs_SO_Rs. split...
      apply BetRs_SameSideRs in H.
      apply SameSideRs_sym. firstorder.
    }
    { assert (nroca' : da c <> da a').
      { destruct H as [[ H1 H2 ]|[ H1 H2 ]]; firstorder. }
      rewrite <- roaa' in nroca'. rewrite roab' in nroca'.
      rewrite <- robb' in nroca'. rewrite robc' in nroca'.
      rewrite rocc' in nroca'. firstorder.
    }
    { assert (nrobc' : da b <> da c').
      { destruct G as [[ H1 H2 ]|[ H1 H2 ]]; firstorder. }
      rewrite <- rocc' in nrobc'. rewrite roca' in nrobc'.
      rewrite robb' in nrobc'. rewrite <- roaa' in nrobc'.
      rewrite roab' in nrobc'. firstorder.
    }
    { assert (nroca' : da c <> da a').
      { destruct H as [[ H1 H2 ]|[ H1 H2 ]]; firstorder. }
      assert (yeqz : y = z).
      { apply (DiPs_EqLs (da c)(da a') y z nroca'); split; split...
        rewrite rocc'... rewrite <- roaa'.
        rewrite roab'. rewrite <- robb'...
      }
      contradiction.
    }
    { assert (nroab' : da a <> da b').
      { destruct F as [[ H1 H2 ]|[ H1 H2 ]]; firstorder. }
      rewrite roaa' in nroab'. rewrite <- roca' in nroab'.
      rewrite rocc' in nroab'. rewrite <- robb' in nroab'. firstorder.
    }
    { assert (nroab' : da a <> da b').
      { destruct F as [[ H1 H2 ]|[ H1 H2 ]]; firstorder. }
      assert (xeqz : x = z).
      { apply (DiPs_EqLs (da a)(da b') x z nroab'); split; split...
        rewrite roaa'... rewrite <- robb'.
        rewrite robc'. rewrite <- rocc'...
      }
      contradiction.
    }
    { assert (nroab' : da a <> da b').
      { destruct F as [[ H1 H2 ]|[ H1 H2 ]]; firstorder. }
      assert (xeqy : x = y).
      { apply (DiPs_EqLs (da a)(da b') x y nroab'); split; split...
        rewrite roaa'. rewrite <- roca'.
        rewrite rocc'... rewrite <- robb'...
      }
      contradiction.
    }
    { destruct F as [[ F1 F2 ]|[ F3 F4 ]];
      destruct G as [[ G1 G2 ]|[ G3 G4 ]];
      destruct H as [[ H1 H2 ]|[ H3 H4 ]].
      { assert (OSxA'B : [ db a' | x | db b]).
        { apply (OSO_trans (db a')(da c)(db b) x)...
          { split.
            { contradict nxeqz.
              apply (DiPs_EqLs (da a')(db a') x z (dp a')); split; split...
              rewrite <- roaa'; auto.
            }
            { split.
              { contradict nxeqz.
                apply (DiPs_EqLs (da c)(da a') x z).
                { firstorder. }
                split; split...
                rewrite <- roaa'; auto.
              }
              { exists (da a'); split...
                { rewrite <- roaa'... }
                apply BetPs_sym...
              }
            }
          }
          { apply (SR_SS (da b)(da c)(db b) x)...
            { rewrite robb'... }
            { contradict nxeqz.
              apply (DiPs_EqLs (da c)(da a') x z).
              { firstorder. }
              split; split... rewrite <- roaa'...
            }
            rewrite rocc'...
          }
        }
        destruct SSxA'B as [ Q1 [ Q2 Q3 ]].
        destruct OSxA'B as [ R1 [ R2 R3 ]].
        contradiction.
      }
      { assert (SSyB'C : [ y | db b', db c]).
        { apply (OOS_trans (db b')(da a)(db c) y)...
          { split.
            { contradict nxeqy.
              apply (DiPs_EqLs (da b')(db b') x y (dp b')); split; split...
              rewrite <- robb'...
            }
            { split.
              { contradict nxeqy.
                apply (DiPs_EqLs (da a)(da b') x y).
                firstorder. split; split... rewrite <- robb'...
              }
              { exists (da b'); split...
                { rewrite <- robb'... }
                apply BetPs_sym...
              }
            }
          }
          { split.
            { contradict nxeqy.
              apply (DiPs_EqLs (da a)(da b') x y).
              { firstorder. }
              split; split...
              rewrite <- robb'...
            }
            { split.
              { contradict nyeqz.
                apply (DiPs_EqLs (da c)(db c) y z (dp c)).
                split; split... rewrite rocc'...
              }
              { exists (da c'); split...
                rewrite <- rocc'... rewrite roaa'...
              }
            }
          }
        }
        destruct SSyB'C as [ Q1 [ Q2 Q3 ]].
        destruct OSyB'C as [ R1 [ R2 R3 ]].
        contradiction.
      }
      { assert (SSzC'A : [ z | db c', db a ]).
        { apply (SS_trans (db c')(da b)(db a) z)...
          { apply (SR_SS (da c')(db c')(da b) z)...
            { rewrite <- rocc'... }
            { contradict nyeqz.
              apply (DiPs_EqLs (da c')(db c') y z (dp c')); split; split...
              rewrite <- rocc'...
            }
            apply SR_sym...
          }
          { apply (SR_SS (da a)(da b)(db a) z)...
            { rewrite roaa'... }
            { contradict nxeqz.
              apply (DiPs_EqLs (da a)(da b') x z).
              { firstorder. }
              split; split...
              { rewrite roaa'... }
              { rewrite <- robb'... }
            }
            rewrite robb'...
          }
        }
        destruct SSzC'A as [ Q1 [ Q2 Q3 ]].
        destruct OSzC'A as [ R1 [ R2 R3 ]].
        contradiction.
      }
      { assert (OSxA'B : [ db a' | x | db b]).
        { apply OS_sym.
          apply (OSO_trans (db b)(da c)(db a') x)...
          { split.
            { contradict nxeqy.
              apply (DiPs_EqLs (da b)(db b) x y (dp b)); split; split...
              rewrite robb'...
            }
            { split.
              { contradict nxeqy.
                apply (DiPs_EqLs (da c')(da b) x y).
                { firstorder. }
                { split; split...
                  { rewrite <- rocc'... }
                  { rewrite robb'... }
                }
              }
              { exists (da b); split...
                { rewrite robb'... }
                { apply BetPs_sym... rewrite rocc'... }
              }
            }
          }
          apply (SR_SS (da a')(da c)(db a') x)...
          { rewrite <- roaa'... }
          { contradict nxeqy.
            apply (DiPs_EqLs (da c')(da b) x y).
            { firstorder. }
            split; split...
            { rewrite <- rocc'... }
            { rewrite robb'... }
          }
        }
        destruct SSxA'B as [ Q1 [ Q2 Q3 ]].
        destruct OSxA'B as [ R1 [ R2 R3 ]].
        contradiction.
      }
      { assert (OSxA'B : [ db a' | x | db b]).
        { apply (OSO_trans (db a')(da c)(db b) x)...
          { split.
            { contradict nxeqz.
              apply (DiPs_EqLs (da a')(db a') x z (dp a')); split; split...
              rewrite <- roaa'...
            }
            { split.
              { contradict nxeqz.
                apply (DiPs_EqLs (da c)(da a') x z).
                { firstorder. }
                split; split...
                rewrite <- roaa'...
              }
              { exists (da a'); split...
                rewrite <- roaa'... apply BetPs_sym...
              }
            }
          }
          { apply (SR_SS (da b)(da c)(db b) x)...
            { rewrite robb'... }
            { contradict nxeqz.
              apply (DiPs_EqLs (da c)(da a') x z).
              { firstorder. }
              split; split... rewrite <- roaa'...
            }
            rewrite rocc'...
          }
        }
        destruct SSxA'B as [ Q1 [ Q2 Q3 ]].
        destruct OSxA'B as [ R1 [ R2 R3 ]].
        contradiction.
      }
      { assert (SSzC'A : [ z | db c', db a ]).
        { apply (OOS_trans (db c')(da b)(db a) z)...
          { split.
            { contradict nyeqz.
              apply (DiPs_EqLs (da c')(db c') y z (dp c')); split; split...
              rewrite <- rocc'...
            }
            { split.
              { contradict nyeqz.
                apply (DiPs_EqLs (da c')(da b) y z).
                { firstorder. }
                split; split... rewrite <- rocc'...
              }
              { exists (da c); split...
                rewrite rocc'... apply BetPs_sym...
              }
            }
          }
          split.
          { contradict nxeqz.
            apply (DiPs_EqLs (da a)(da b') x z).
            { firstorder. }
            split; split...
            { rewrite roaa'... }
            { rewrite <- robb'... }
          }
          { split.
            { contradict nxeqz.
              apply (DiPs_EqLs (da a)(db a) x z (dp a)).
              split; split... rewrite roaa'...
            }
            { exists (da a); split...
              rewrite roaa'... rewrite robb'...
            }
          }
        }
        destruct SSzC'A as [ Q1 [ Q2 Q3 ]].
        destruct OSzC'A as [ R1 [ R2 R3 ]].
        contradiction.
      }
      { assert (SSyB'C : [ y | db b', db c]).
        { apply (SS_trans (db b')(da a)(db c) y)...
          { apply (SR_SS (da b')(db b')(da a) y)...
            { rewrite <- robb'... }
            { contradict nxeqy.
              apply (DiPs_EqLs (da b')(db b') x y (dp b')); split; split...
              rewrite <- robb'...
            }
            apply SR_sym...
          }
          apply (SR_SS (da c)(da a)(db c) y)...
          { rewrite rocc'... }
          { contradict nxeqy.
            apply (DiPs_EqLs (da a)(da b') x y).
            { firstorder. }
            { split; split... rewrite <- robb'... }
          }
          rewrite roaa'...
        }
        destruct SSyB'C as [ Q1 [ Q2 Q3 ]].
        destruct OSyB'C as [ R1 [ R2 R3 ]].
        contradiction.
      }
      { assert (OSxA'B : [ db a' | x | db b]).
        { apply OS_sym.
          apply (OSO_trans (db b)(da c)(db a') x)...
          { split.
            { contradict nxeqy.
              apply (DiPs_EqLs (da b)(db b) x y (dp b)); split; split...
              rewrite robb'...
            }
            { split.
              { contradict nxeqy.
                apply (DiPs_EqLs (da c')(da b) x y).
                { firstorder. }
                split; split...
                { rewrite <- rocc'... }
                { rewrite robb'... }
              }
              { exists (da b); split... rewrite robb'...
                apply BetPs_sym... rewrite rocc'...
              }
            }
          }
          apply (SR_SS (da a')(da c)(db a') x)...
          { rewrite <- roaa'... }
          contradict nxeqy.
          apply (DiPs_EqLs (da c')(da b) x y).
          { firstorder. }
          split; split...
          { rewrite <- rocc'... }
          { rewrite robb'... }
        }
        destruct SSxA'B as [ Q1 [ Q2 Q3 ]].
        destruct OSxA'B as [ R1 [ R2 R3 ]].
        contradiction.
      }
    }
  }
Qed.

Lemma EqFlagsTranslation_SSO :
  forall (F G H : Flag),
  da H ~~ db F
    -> EqFlagsTranslation F (#G)
    -> EqFlagsTranslation G (#H)
    -> EqOpFlagTrans H (#F).
Proof with eauto.
  intros * Colca' FG GH; simpl in *.
  apply (nEqFlagsTranslation_EqOpFlagsTrans H (#F)); simpl in *...
  { apply EqDirRs_ColRs...
    destruct F as [ a a' diaa' ]; destruct H as [ c c' dicc' ]...
  }
  { intros HF.
    apply (EqFlagsTranslation_nSSS F G H); split; auto.
  }
Qed.

Lemma EqFlagsTranslation_SOS :
  forall (F G H : Flag),
  da G ~~ db H
    -> da H ~~ db F
    -> EqFlagsTranslation F (#G)
    -> EqOpFlagTrans G (#H)
    -> EqFlagsTranslation H (#F).
Proof with eauto.
  intros * Colbc' Colca' FG GH.
  destruct (DecideEqFlagsTranslation_2 H (#F)) as [ SF | OF ]; simpl in *...
  { apply EqDirRs_ColRs...
    destruct F as [ a a' diaa' ]; destruct H as [ c c' dicc' ]...
  }
  { destruct (EqFlagsTranslation_nSOO F G H); try split; auto. }
Qed.

Lemma EqFlagsTranslation_OSS :
  forall (F G H : Flag),
  da F ~~ db G
    -> da H ~~ db F
    -> EqOpFlagTrans F (#G)
    -> EqFlagsTranslation G (#H)
    -> EqFlagsTranslation H (#F).
Proof with eauto.
  intros * Colab' Colca' FG GH; simpl in *.
  destruct (DecideEqFlagsTranslation_2 H (#F)) as [ SF | OF ]; simpl in *...
  { apply EqDirRs_ColRs...
    destruct F as [ a a' diaa' ];
    destruct G as [ b b' dibb' ];
    destruct H as [ c c' dicc' ]; simpl in * ...
  }
  { destruct (EqFlagsTranslation_nSOO G H F); try split... }
Qed.

Lemma EqFlagsTranslation_OOO :
  forall (F G H : Flag),
  da F ~~ db G
    -> da G ~~ db H
    -> da H ~~ db F
    -> EqOpFlagTrans F (#G)
    -> EqOpFlagTrans G (#H)
    -> EqOpFlagTrans H (#F).
Proof with eauto.
  intros * Colab' Colbc' Colca' FG GH; simpl in *.
  destruct (DecideEqFlagsTranslation_2 H (#F)) as [ SF | OF ]; simpl in *...
  { apply EqDirRs_ColRs...
    destruct F as [ a a' diaa' ];
    destruct G as [ b b' dibb' ];
    destruct H as [ c c' dicc' ]; simpl in * ...
  }
  { destruct (EqFlagsTranslation_nSOO H F G); try split... }
Qed.

Lemma EqFlagsRotation_EqOpFlagRotation :
  forall (a a' b b' : Ray)(diaa' : ![ a # a' ])(dibb' : ![ b # b' ]),
  EqFlagsRotation ({{ a # a' | diaa' }})({{ b # b' | dibb' }})
    -> EqFlagsRotation ({{ a # a' | diaa' }})
                       ({{ !b # !b' | nCol_OpRs b b' dibb' }}).
Proof with eauto.
  intros * FeqG; simpl in *.
  destruct FeqG as [[ H1 H2 ]|[[ H3 H4 ]|[[ H5 H6 ]|[ H7 H8 ]]]];
  simpl in *.
  { right; left; simpl.
    split.
    { rewrite <- H1. apply OpOpRs. }
    { apply OppositeSideRs_sym.
      apply (SameSideRs_inv a a' b' a a' (!!b')); try reflexivity...
      apply OpOpRs...
    }
  }
  { left; simpl; split...
    apply SameSideRs_sym. apply SameSideRs_sym.
    apply OppositeSideRs_sym...
  }
  { right; right; right; simpl in *.
    split.
    { apply SameSideRs_sym. apply SameSideRs_sym.
      apply OppositeSideRs_sym...
      apply -> SameSideRs_OpRs_inv...
    }
    { eapply (SameSideRs_inv a a' b a a' (!!b)); try reflexivity...
      apply OpOpRs. apply SameSideRs_sym...
    }
  }
  { right; right; left; simpl in *.
    split.
    { apply SameSideRs_sym... }
    { apply -> SameSideRs_OpRs_inv.
      apply OppositeSideRs_sym.
      apply (SameSideRs_inv b a b' b a (!!b')); try reflexivity...
      apply OpOpRs...
    }
  }
Qed.

(* Flag Orientation *)

Definition EqFlagsOrientation (F G : Flag) : Prop
  := exists (F' G' : Flag), (EqFlagsRotation F F')
     /\ (EqFlagsTranslation F' G')
     /\ (EqFlagsRotation G G').
Notation " F ~~~ G "
  := (EqFlagsOrientation F G)
  (at level 70).
Notation " F ~//~ G "
  := (~ EqFlagsOrientation F G)
  (at level 70).

(** Theorem #30 *)
Lemma EqFlagsOrientation_refl :
  reflexive Flag EqFlagsOrientation.
Proof.
  unfold reflexive, EqFlagsOrientation; simpl.
  intros F.
  exists F, F; split; [idtac | split]; setoid_reflexivity.
Qed.
Lemma EqFlagsOrientation_sym :
  symmetric Flag EqFlagsOrientation.
Proof.
  unfold symmetric, EqFlagsOrientation; simpl.
  intros F G [ F' [ G' [ EqF [ EqT EqG ]]]].
  exists G', F'; split; auto; split; auto; setoid_symmetry; auto.
Qed.
Lemma EqFlagsOrientation_trans :
  transitive Flag EqFlagsOrientation.
Proof with eauto.
  unfold transitive, EqFlagsOrientation.
  intros F G H
    [ F1 [ G1 [ FeqF' [ F'eqG' GeqG' ]]]]
    [ G2 [ H2 [ GeqG'' [ G''eqH'' HeqH'' ]]]].
  assert (G'eqG'' : EqFlagsRotation G1 G2).
  { transitivity G... symmetry... }
  destruct F as [ a a' diaa' ];
  destruct G as [ b b' dibb' ];
  destruct H as [ c c' dicc' ];
  destruct F1 as [ a1 a1' dia1a1' ];
  destruct G1 as [ b1 b1' dib1b1' ];
  destruct G2 as [ b2 b2' dib2b2' ];
  destruct H2 as [ c2 c2' dic2c2' ].
  destruct (classic ([ (da a), (da b), (da c) ]))
    as [[ x [ oaox [ obox ocox ]]]| abc ].
  { destruct (classic ( (da a) = (da b))) as [ roab | nroab ].
    { exists ({{ b2 # b2' | dib2b2' }}), ({{ c2 # c2' | dic2c2' }});
      split; try split; try reflexivity...
      apply EqFlagsTranslation_EqFlagsRotation in F'eqG'; simpl...
      { transitivity ({{ b # b' | dibb' }})...
        transitivity ({{ b1 # b1' | dib1b1' }})...
        transitivity ({{ a1 # a1' | dia1a1' }})... symmetry...
      }
      apply EqFlagsRotation_EqFlagsOrg in FeqF';
      apply EqFlagsRotation_EqFlagsOrg in GeqG';
      simpl in *. rewrite <- GeqG'. rewrite <- FeqF'...
    }
    destruct (classic ( (da b) = (da c))) as [ robc | nrobc ].
    { exists ({{ a1 # a1' | dia1a1' }}), ({{ b1 # b1' | dib1b1' }});
      split; try split; try reflexivity...
      apply EqFlagsTranslation_EqFlagsRotation in G''eqH''; simpl.
      { transitivity ({{ b # b' | dibb' }})...
        transitivity ({{ b2 # b2' | dib2b2' }})...
        transitivity ({{ c2 # c2' | dic2c2' }})... symmetry... symmetry...
      }
      apply EqFlagsRotation_EqFlagsOrg in GeqG'';
      apply EqFlagsRotation_EqFlagsOrg in HeqH'';
      simpl in *. rewrite <- GeqG''. rewrite <- HeqH''...
    }
    { assert (Cola1b1 : ![a1, b1]).
      { destruct F'eqG' as [ H1 _ ]; simpl in *. apply EqDirRs_ColRs... }
      assert (Colb2c2 : ![b2, c2]).
      { destruct G''eqH'' as [ H1 _ ]; simpl in *. apply EqDirRs_ColRs... }
      destruct Cola1b1 as [ y [ a1ox [ a1px [ b1ox b1px]]]].
      destruct Colb2c2 as [ z [ b2ox [ b2px [ c2ox c2px]]]].
      assert (roaa1 : da a = da a1).
      { apply EqFlagsRotation_EqFlagsOrg in FeqF'; simpl in *... }
      assert (robb1 : da b = da b1).
      { apply EqFlagsRotation_EqFlagsOrg in GeqG'; simpl in *... }
      assert (robb2 : da b = da b2).
      { apply EqFlagsRotation_EqFlagsOrg in GeqG''; simpl in *... }
      assert (rocc2 : da c = da c2).
      { apply EqFlagsRotation_EqFlagsOrg in HeqH''; simpl in *... }
      assert (xeqy : x = y).
      { rewrite <- roaa1 in *. rewrite <- robb2 in *.
        rewrite <- robb1 in *. rewrite <- rocc2 in *. eqls.
      }
      subst y.
      assert (xeqz : x = z).
      { rewrite <- roaa1 in *. rewrite <- robb2 in *.
        rewrite <- robb1 in *. rewrite <- rocc2 in *. eqls.
      }
      subst z.
      assert (a1b1: a1 ~~ b1). { firstorder. }
      assert (b2c2: b2 ~~ c2). { firstorder. }
      assert (Colb1b2 : ![b1, b2]). { exists x; repeat split... }
      destruct F'eqG' as [ H1 [ H2 [ y [ H3 [ H4 SSxA1B1 ]]]]]; simpl in *.
      assert (xeqy : x = y); eqls. subst y.
      destruct G''eqH'' as [ H1' [ H2' [ y [ H3' [ H4' SSxB2C2 ]]]]];
      simpl in *.
      assert (xeqy : x = y); eqls.
      subst y.
      destruct (DecideRayDirection b1 b2) as [ SD | OD ]...
      { assert (a1c2 : a1 ~~ c2). { transitivity b1... transitivity b2... }
        exists ({{ a1 # a1' | dia1a1' }}), ({{ c2 # c2' | dic2c2' }});
        split; try split...
        split; simpl...
        split.
        { apply (dp a1). }
        { exists x; split... split...
          apply EqFlagsRotation_EqFlagsTranslation in G'eqG''.
          { destruct G'eqG''
              as [ H1'' [ H2'' [ y [ H3'' [ H4'' SSxB1B2 ]]]]]; simpl in *.
            assert (xeqy : x = y); eqls. subst y.
            apply (SS_trans (db a1')(db b1')(db c2') x)...
            apply (SS_trans (db b1')(db b2')(db c2') x)...
          }
          { simpl. apply EqRsDir_EqRs... rewrite <- robb1... }
        }
      }
      { apply ColRs_DiDirRs_EqDirOpRs in OD.
        assert (a1c2 : a1 ~~ !c2).
        { transitivity b1... transitivity (!b2)...
          rewrite b2c2. reflexivity.
        }
        assert (diopb2b2' : ![!b2 # !b2']).
        { apply nColOpRs_1. apply nColOpRs_2... }
        assert (diopc2c2' : ![ !c2 # !c2']).
        { apply nColOpRs_1. apply nColOpRs_2; auto. }
        exists ({{ a1 # a1' | dia1a1' }}), (({{ !c2 # !c2' | diopc2c2' }}));
        split; try split...
        do 2 try split; simpl...
        exists x; do 2 try split...
        destruct G'eqG'' as [[ b1eqb2 H1'' ]|[[ b1eqopb2 H2'' ]|[ H | H ]]];
        try destruct H as [[ G1 [ G2 [ G4 G5 ]]] G3 ]; simpl in *.
        { assert (b1eqopb2 : b1 == !b2).
          { apply EqRsDir_EqRs... destruct b1eqb2 as [ rob1b2 b1eqb2 ].
            rewrite rob1b2. apply OpRays_0...
          }
          rewrite b1eqb2 in b1eqopb2.
          apply OpRs_irrefl in b1eqopb2. contradiction.
        }
        { assert (OSxB1B2 : [ db b1' | x | db b2']).
          { apply SameSideRs_OpRs_OppositeSide in H2''...
            { destruct H2'' as [ H5 [ y [ H7 [ H8 H9 ]]]].
              assert (xeqy : x = y); eqls.
            }
          }
          apply (OSO_trans (db b1')(db b2')(db c2') x) in OSxB1B2...
          apply OS_sym in OSxB1B2. apply SS_sym in SSxA1B1.
          apply (OSO_trans (db c2')(db b1')(db a1') x) in OSxB1B2...
          apply OS_sym in OSxB1B2.
          apply (OOS_trans (db a1')(db c2')(db (!c2')) x)...
          assert (roc2c2' : da c2 = da c2'). { destruct dic2c2'... }
          destruct c2' as [ O C nCeqO ]. simpl in *. symmetry in roc2c2'.
          destruct roc2c2'. unfold OpRay; simpl.
          destruct (DrawOppositePoint O C) as [ C' [ BetCOC' _ ]]...
          destruct (BetPs_3DiPs C O C' BetCOC') as [ _ [ nOeqC' nCeqC' ]];
          simpl in *.
          assert (nCox : ~ [ C @ x ]).
          { destruct SSxB2C2 as [ _ [ nCox _ ]]... }
          assert (nC'ox : ~ [ C' @ x ]). { contradict nCox; incpt 2. }
          split...
        }
        { destruct G5
            as [ y [ ob1ox [ pb1ox [ npb2ox [ npb1'ox SSxb2b1' ]]]]].
          assert (xeqy : x = y); eqls.
        }
        { destruct G5
            as [ y [ ob2ox [ pb2ox [ npb1ox [ npb2'ox SSxb2b1' ]]]]].
          assert (xeqy : x = y); eqls.
        }
        { eapply EqFlagsRotation_EqOpFlagRotation... }
        { exists x; repeat split... }
      }
    }
  }
  { destruct (nColPs_3DiPs (da a)(da b)(da c) abc)
      as [ nroab [ nrobc nroac ]].
    assert (Ex1 : exists a3 : Ray, a3 = {{ da a # da c | nroac }}).
    { exists ({{ da a # da c | nroac }})... }
    destruct Ex1 as [ a3 Defa3 ].
    destruct (DrawSegmentExtension (da a)(da c)) as [ D BetACD ]...
    assert (noceqD : da c <> D); dips.
    assert (Ex2 : exists c3 : Ray, c3 = {{ da c # D | noceqD }}).
    { exists ({{ da c # D | noceqD }})... }
    destruct Ex2 as [ c3 Defc3 ].
    assert (roaa1 : da a = da a1).
    { apply (EqFlagsRotation_EqFlagsOrg ({{ a # a' | diaa' }})
        ({{ a1 # a1' | dia1a1' }}))...
    }
    assert (roaa3 : da a = da a3). { rewrite Defa3. simpl... }
    assert (robb1 : da b = da b1).
    { apply (EqFlagsRotation_EqFlagsOrg ({{ b # b' | dibb' }})
        ({{ b1 # b1' | dib1b1' }}))...
    }
    assert (robb2 : da b = da b2).
    { apply (EqFlagsRotation_EqFlagsOrg ({{ b # b' | dibb' }})
        ({{ b2 # b2' | dib2b2' }}))...
    }
    assert (rocc2 : da c = da c2).
    { apply (EqFlagsRotation_EqFlagsOrg ({{ c # c' | dicc' }})
        ({{ c2 # c2' | dic2c2' }}))...
    }
    assert (rocc3 : da c = da c3). { rewrite Defc3. simpl... }
    destruct (DrawEqRotatedFlagOnRay a1 a1' a3 dia1a1')
      as [ a3' [ dia3a3' FeqF''' ]]; simpl...
    { rewrite <- roaa1... }
    destruct (DrawEqRotatedFlagOnRay c2 c2' c3 dic2c2')
      as [ c3' [ dic3c3' HeqH''' ]]; simpl... { rewrite <- rocc2... }
    exists ({{ a3 # a3' | dia3a3' }}), ({{ c3 # c3' | dic3c3' }});
      split; try split...
    { transitivity ({{ a1 # a1' | dia1a1' }})... }
    { destruct (DrawExtensionLinePP (da a)(da b))
      as [ x [ oaox obox ]]...
    destruct (DrawExtensionLinePP (da b)(da c) nrobc)
      as [ y [ oboy ocoy ]].
    destruct (DrawExtensionLinePP (da a)(da c) nroac)
      as [ z [ oaoz ocoz ]].
    clear FeqF' GeqG' GeqG'' HeqH''. clear dependent a'.
    clear dependent b'. clear dependent c'.
    elim F'eqG'.
    intros a1_b1 [ _ [ x' [ oa1ox [ pa1ox SSxA1B1 ]]]]; simpl in *.
    assert (xeqx' : x = x').
    { apply (DiPs_EqLs (da a)(da b) x x')... split; split...
      rewrite roaa1...
      destruct a1_b1
        as [[ H1 [ _ [ _ [ ColAA1B1 _ ]]]]|[[ H3 H4 ]|[ H5 H6 ]]].
      { rewrite robb1. destruct H1... }
      { destruct H3 as [ H5 [ H6 [ H7 H8 ]]]. rewrite robb1.
        apply (ColPs_IncPt (db a1)(da a1)(da b1) x'); colps.
      }
      { rewrite robb1; incpt 2. }
    }
    subst x'.
    assert (H := a1_b1).
    apply EqDirRs_ColRs in H.
    destruct H as [ x' [ oa1ox' [ pa1ox' [ ob1ox pb1ox ]]]].
    assert (xeqx' : x = x').
    { apply (DiPs_EqLs (da a1)(db a1) x x' (dp a1))... }
    subst x'. clear oa1ox' pa1ox'.
    elim G''eqH''.
    intros b2_c2 [ _ [ y' [ ob2oy [ pb2oy SSyB2C2 ]]]]; simpl in *.
    assert (yeqy' : y = y').
    { apply (DiPs_EqLs (da b)(da c) y y' nrobc). split; split...
      rewrite robb2...
      destruct b2_c2
        as [[ H1 [ _ [ _ [ ColAA1B1 _ ]]]]|[[ H3 H4 ]|[ H5 H6 ]]].
      { rewrite rocc2. destruct H1... }
      { destruct H3 as [ H5 [ H6 [ H7 _ ]]]. rewrite rocc2.
        apply (ColPs_IncPt (db b2)(da b2)(da c2) y'); colps.
      }
      { rewrite rocc2; incpt 2. }
    }
    subst y'.
    assert (H := b2_c2).
    apply EqDirRs_ColRs in H.
    destruct H as [ y' [ ob2oy' [ pb2oy' [ oc2oy pc2oy ]]]].
    assert (yeqy' : y = y').
    { apply (DiPs_EqLs (da b2)(db b2) y y' (dp b2))... }
    subst y'. clear ob2oy' pb2oy'.
    assert (a3_c3 : a3 ~~ c3).
    { unfold EqRaysDir; simpl...
      rewrite Defa3; rewrite Defc3; simpl... right; left; simpl...
      split; try apply SR_refl...
    }
    assert (H := a3_c3).
    apply EqDirRs_ColRs in H.
    destruct H as [ z' [ oa3oz [ pa3oz [ oc3oz pc3oz ]]]].
    assert (zeqz' : z = z').
    { apply (DiPs_EqLs (da a3)(db a3) z z' (dp a3)). split.
      rewrite Defa3; simpl; split... split...
    }
    subst z'.
    assert (nxeqy : x <> y). { contradict abc; subst; colps. }
    assert (nyeqz : y <> z). { contradict abc; subst; colps. }
    assert (nxeqz : x <> z). { contradict abc; subst; colps. }
    assert (a1a3 : ![a1 # a3]).
    { apply nColRs_nColPs. rewrite Defa3.
      do 2 try split; simpl...
      { contradict abc.
        destruct abc
          as [ H1 [ H2 [ H3 [[ t [ oa1ot [ pa1ot ocot ]]] _ ]]]]; simpl in *.
        rewrite roaa1.
        exists t; do 2 try split...
        assert (xeqt : x = t); eqls.
      }
      contradict abc.
      destruct abc as [ _ [ _ [ _ [[ t [ oaot [ pa1ot ocot ]]] _ ]]]].
      rewrite Defa3 in *; simpl in *. unfold OpRay in *; simpl in *.
      destruct (DrawOppositePoint (da a)(da c)) as [ X [ BetX _ ]]...
      destruct (BetPs_3DiPs (da c)(da a) X BetX) as [ X1 [ X2 X3 ]].
      simpl in *. apply BetPs_sym in BetX. rewrite roaa1.
      exists x; repeat split...
      assert (xeqt : x = t).
      { apply (DiPs_EqLs (da a1)(db a1) x t (dp a1)); repeat split... }
      subst t.
      apply (BetPs_IncPt X (da a)(da c) x); try split...
    }
    assert (b1b2 : ![b1 # b2]).
    { apply nColRs_nColPs.
      split.
      { rewrite <- robb1... }
      { split.
        { contradict abc.
          destruct abc as [ _ [ _ [ _ [[ t [ oa1ot [ pa1ot ocot ]]] _ ]]]];
          simpl in *. rewrite robb1.
          assert (xeqt : x = t).
          { apply (DiPs_EqLs (da b1)(db b1) x t (dp b1)); repeat split... }
          subst t. exists x; repeat split...
          assert (xeqy : x = y).
          { apply (DiPs_EqLs (da b2)(db b2) x y (dp b2)). split; split...
            rewrite <- robb2...
          }
          subst y...
        }
        { contradict abc.
          destruct abc as [ _ [ _ [ _ [[ t [ oaot [ pa1ot ocot ]]] _ ]]]].
          rewrite roaa1. exists x; repeat split...
          assert (xeqt : x = t).
          { apply (DiPs_EqLs (da b1)(db b1) x t (dp b1)); repeat split... }
          subst t.
          assert (xeqy : x = y).
          { apply (DiPs_EqLs (da b2)(db b2) x y (dp b2)).
            rewrite <- robb2; split; split; auto; try rewrite <- robb2...
            assert (Betb2 : [ db b2 # da b2 # db (!b2) ]).
            { apply OpRays_1. }
            apply BetPs_sym in Betb2.
            apply (BetPs_IncPt (db (!b2))(da b2)(db b2) x)...
            split... rewrite <- robb2...
          }
          subst y...
        }
      }
    }
    { assert (c2c3 : ![c2 # c3]).
      { apply nColRs_nColPs.
        split.
        { rewrite <- rocc2... }
        { split.
          { contradict abc. rewrite Defc3 in *; simpl.
            destruct abc as [ _ [ _ [ _ [[ t [ oa1ot [ pa1ot ocot ]]] _ ]]]];
            simpl in *. rewrite rocc2. exists t.
            assert (yeqt : y = t).
            { apply (DiPs_EqLs (da c2)(db c2) y t (dp c2));
              repeat split...
            }
            subst t.
            repeat split...
            assert (yeqz : y = z).
            { apply BetPs_sym in BetACD.
              apply (DiPs_EqLs D (da c) y z).
              apply (BetPs_3DiPs D (da c)(da a))...
              do 2 split...
            }
            subst z...
          }
          { contradict abc.
            destruct abc as [ _ [ _ [ _ [[ t [ oaot [ pa1ot ocot ]]] _ ]]]];
            simpl in *. rewrite rocc2. exists t.
            assert (yeqt : y = t).
            { apply (DiPs_EqLs (da c2)(db c2) y t (dp c2)); repeat split... }
            subst t; repeat split...
            assert (Betc3 : [ db c3 # da c3 # db (!c3) ]).
            { apply OpRays_1. }
            assert (yeqz : y = z).
            { apply (DiPs_EqLs (da c3)(db (!c3)) y z).
              rewrite (OpRays_0 c3). apply (dp (!c3)). split; split...
              rewrite <- rocc3...
              apply (BetPs_IncPt (db c3)(da c3)(db (!c3)) z)...
            }
            subst z...
          }
        }
      }
      assert (a3a1 : ![a3 # a1]). { apply (nColRs_sym a1 a3 a1a3). }
      assert (b2b1 : ![b2 # b1]). { apply (nColRs_sym b1 b2 b1b2). }
      assert (c3c2 : ![c3 # c2]). { apply (nColRs_sym c2 c3 c2c3). }
      symmetry in roaa1, robb1, rocc2.
      destruct roaa1, robb1, rocc2. clear a b c.
      assert (F0 := a1a3). apply nColRs_nColPs in F0.
      assert (G0 := b1b2). apply nColRs_nColPs in G0.
      assert (H0 := c2c3). apply nColRs_nColPs in H0.
      destruct FeqF''' as [[ a1_a3 E1 ]|[[ a1_a3 E1 ]| E1 ]]; simpl in *;
      destruct F0 as [ F1 [ F2 F3 ]]; try contradiction.
      destruct G'eqG'' as [[ a1_a3 E2 ]|[[ a1_a3 E2 ]| E2 ]]; simpl in *;
      destruct G0 as [ G1 [ G2 G3 ]]; try contradiction.
      destruct HeqH''' as [[ a1_a3 E3 ]|[[ a1_a3 E3 ]| E3 ]]; simpl in *;
      destruct H0 as [ H1 [ H2 H3 ]]; try contradiction.
      do 2 try split; simpl...
      { apply (dp a3). }
      { exists z; do 2 try split...
        clear F1 F2 F3 G1 G2 G3 H1 H2 H3.
        destruct E1 as [[ E1 E1' ]|[ E1 E1' ]];
        destruct E2 as [[ E2 E2' ]|[ E2 E2' ]];
        destruct E3 as [[ E3 E3' ]|[ E3 E3' ]];
        apply SameSideRs_OpRs_OppositeSide in E1';
        apply SameSideRs_OpRs_OppositeSide in E2';
        apply SameSideRs_OpRs_OppositeSide in E3'.
        { destruct E1
            as [ _ [ roa1a1' [ _ [ x' [ oa1ox' [ pa1ox' SSxE1a ]]]]]].
          assert (xeqx' : x = x').
          { apply (DiPs_EqLs (da a1)(db a1) x x' (dp a1)).
            do 2 split; auto.
          }
          subst x'.
          destruct E1'
            as [ _ [ z' [ oa3oz' [ pa3oz' OSzE1a' ]]]].
          assert (zeqz' : z = z').
          { apply (DiPs_EqLs (da a3)(db a3) z z' (dp a3)); split... }
          subst z'.
          destruct E2
            as [ _ [ rob1b1' [ _ [ x' [ ob1ox' [ pb1ox' SSxE2a ]]]]]].
          assert (xeqx' : x = x').
          { apply (DiPs_EqLs (da b1)(db b1) x x' (dp b1)). do 2 split... }
          subst x'.
          destruct E2'
            as [ _ [ y' [ ob2oy' [ pb2oy' OSyE2a' ]]]].
          assert (yeqy' : y = y').
          { apply (DiPs_EqLs (da b2)(db b2) y y' (dp b2)). do 2 split... }
          subst y'.
          destruct E3
            as [ _ [ roc2c2' [ _ [ y' [ oc2oy' [ pc2oy' SSyE3a ]]]]]].
          assert (yeqy' : y = y').
          { apply (DiPs_EqLs (da c2)(db c2) y y' (dp c2)). do 2 split... }
          subst y'.
          destruct E3'
            as [ _ [ z' [ oc3oz' [ pc3oz' OSzE3a' ]]]].
          assert (zeqz' : z = z').
          { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3)). do 2 split... }
          subst z'.
          assert (SSxB2A3 : [ x | db b2, db a3]).
          { apply (SS_trans (db b2)(db b1')(db a3) x)... apply SS_sym.
            apply (SS_trans (db a3)(db a1')(db b1') x)...
          }
          assert (SSyB1C3 : [ db b1 | y | db c3]).
          { apply (OSO_trans (db b1)(db c2')(db c3) y)...
            apply (OSO_trans (db b1)(db b2')(db c2') y)... apply SS_sym...
          }
          apply (OOS_trans (db a3')(db a1)(db c3') z)... { apply OS_sym... }
          apply OS_sym.
          apply (OSO_trans (db c3')(db c2)(db a1) z)... { apply OS_sym... }
          assert (EqTr_b2a3 : EqFlagsTranslation ({{ c3 # c2 | c3c2 }})
            ({{ a3 # a1 | a3a1 }}))...
          { symmetry in a3_c3.
            eapply (EqFlagsTranslation_SOS
              ({{ a1# a3 | a1a3 }})({{ b2 # b1 | b2b1 }}))...
            { split; simpl... split. apply (dp a1).
              exists x; split... split...
              apply SS_sym...
            }
            right; do 2 try split; simpl... apply (dp b2).
          }
          destruct EqTr_b2a3
            as [ _ [ _ [ z' [ H1 [ H2 H3 ]]]]]; simpl in *.
          assert (zeqz' : z = z').
          { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3)); split; split... }
            subst z'...
          }
          { destruct E1
              as [ _ [ roa1a1' [ _ [ x' [ oa1ox' [ pa1ox' SSxE1a ]]]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da a1)(db a1) x x' (dp a1)).
              do 2 split...
            }
            subst x'.
            destruct E1'
              as [ _ [ z' [ oa3oz' [ pa3oz' OSzE1a' ]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da a3)(db a3) z z' (dp a3)); split... }
            subst z'.
            try rewrite Defa3; simpl...
            { destruct E2
                as [ _ [ rob1b1' [ _ [ x' [ ob1ox' [ pb1ox' SSxE2a ]]]]]].
              assert (xeqx' : x = x').
              { apply (DiPs_EqLs (da b1)(db b1) x x' (dp b1));
                do 2 split...
              }
              subst x'.
              destruct E2'
                as [ _ [ y' [ ob2oy' [ pb2oy' OSyE2a' ]]]].
              assert (yeqy' : y = y').
              { apply (DiPs_EqLs (da b2)(db b2) y y' (dp b2));
                do 2split...
              }
              subst y'.
              destruct E3
                as [ _ [ roc3c3' [ _ [ z' [ oc3oz' [ pc3oz' SSzE3a ]]]]]].
              assert (zeqz' : z = z').
              { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3));
                do 2 split...
              }
              subst z'.
              destruct E3'
                as [ _ [ y' [ oc2oy' [ pc2oy' OSyE3a' ]]]].
              assert (yeqy' : y = y').
              { apply (DiPs_EqLs (da c2)(db c2) y y' (dp c2));
                do 2 split...
              }
              subst y'.
              assert (SSxB2A3 : [ x | db b2, db a3]).
              { apply (SS_trans (db b2)(db b1')(db a3) x)... apply SS_sym.
                apply (SS_trans (db a3)(db a1')(db b1') x)...
              }
              assert (SSyB1C3 : [ y | db b1, db c3]).
              { apply (OOS_trans (db b1)(db b2')(db c3) y)... apply OS_sym...
                apply (OSO_trans (db c3)(db c2')(db b2') y)... apply SS_sym...
              }
              apply (OOS_trans (db a3')(db a1)(db c3') z)...
              { apply OS_sym... }
              apply (OSO_trans (db a1)(db c2)(db c3') z)...
              assert (EqTr_b2a3 : EqOpFlagTrans ({{ c3 # c2 | c3c2 }})
                ({{ a3 # a1 | a3a1 }})).
              { symmetry in a3_c3.
                eapply (EqFlagsTranslation_SSO ({{ a1 # a3 | a1a3 }})
                  ({{ b2 # b1 | b2b1 }}))...
                { do 2 try split; simpl...
                  { apply (dp a1). }
                  { exists x; split... split... apply SS_sym... }
                }
                do 2 try split; simpl... apply (dp b2).
              }
              destruct EqTr_b2a3
                as [ H1 |[ _ [ _ [ z' [ H1 [ H2 H3 ]]]]]]; simpl in *.
              { rewrite a3_c3 in H1.
                apply EqDirOpRs_irrefl in H1; firstorder.
              }
              { assert (zeqz' : z = z').
                { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3));
                  do 2 split...
                }
                subst z'. apply OS_sym...
              }
            }
          }
          { destruct E1
              as [ _ [ roa1a1' [ _ [ x' [ oa1ox' [ pa1ox' SSxE1a ]]]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da a1)(db a1) x x' (dp a1)).
              do 2 split...
            }
            subst x'.
            destruct E1'
              as [ _ [ z' [ oa3oz' [ pa3oz' OSzE1a' ]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da a3)(db a3) z z' (dp a3)).
              do 2 try split...
            }
            subst z'.
            destruct E2
              as [ _ [ rob2b2' [ _ [ y' [ ob2oy' [ pb2oy' OSyE2a' ]]]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da b2)(db b2) y y' (dp b2)).
              do 2 split...
            }
            subst y'.
            destruct E2'
              as [ _ [ x' [ ob1ox' [ pb1ox' SSxE2a ]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da b1)(db b1) x x' (dp b1)).
              do 2 split...
            }
            subst x'.
            destruct E3
              as [ _ [ roc2c2' [ _ [ y' [ oc2oy' [ pc2oy' SSyE3a ]]]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da c2)(db c2) y y' (dp c2)).
              do 2 split...
            }
            subst y'.
            destruct E3'
              as [ _ [ z' [ oc3oz' [ pc3oz' OSzE3a' ]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3)).
              do 2 split...
            }
            subst z'.
            assert (OSxB2A3 : [ db b2 | x | db a3]).
            { apply (OSO_trans (db b2)(db b1')(db a3) x)...
              apply (SS_trans (db b1')(db a1')(db a3) x);
              apply SS_sym...
            }
            assert (SSyB1C3 : [ y | db b1, db c3]).
            { apply (SS_trans (db b1)(db c2')(db c3) y)...
              apply (SS_trans (db b1)(db b2')(db c2') y)...
              apply SS_sym...
            }
            apply (OOS_trans (db a3')(db a1)(db c3') z)...
            { apply OS_sym... }
            apply OS_sym.
            apply (OSO_trans (db c3')(db c2)(db a1) z)...
            { apply OS_sym... }
            assert (EqTr_b2a3 : EqFlagsTranslation ({{ c3 # c2 | c3c2 }})
              ({{ a3 # a1 | a3a1 }})).
            { symmetry in a3_c3.
              apply (EqFlagsTranslation_OSS ({{ a1 # a3 | a1a3 }})
                ({{ b2 # b1 | b2b1 }}))...
              { right; split; simpl... split. apply (dp a1).
                exists x; split... split... apply OS_sym...
              }
              split; simpl...
              split.
              { apply (dp b2). }
              { exists y; split... }
            }
            destruct EqTr_b2a3
              as [ _ [ _ [ z' [ H1 [ H2 H3 ]]]]]; simpl in *.
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3));
              do 2 split...
            }
            subst z'...
          }
          { destruct E1
              as [ _ [ roa1a1' [ _ [ x' [ oa1ox' [ pa1ox' SSxE1a ]]]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da a1)(db a1) x x' (dp a1)).
              do 2 split...
            }
            subst x'.
            destruct E1'
              as [ _ [ z' [ oa3oz' [ pa3oz' OSzE1a' ]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da a3)(db a3) z z' (dp a3)).
              repeat split...
            }
            subst z'.
            destruct E2
              as [ _ [ rob2b2' [ _ [ y' [ ob2oy' [ pb2oy' OSyE2a' ]]]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da b2)(db b2) y y' (dp b2)).
              do 2 split...
            }
            subst y'.
            destruct E2'
              as [ _ [ x' [ ob1ox' [ pb1ox' SSxE2a ]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da b1)(db b1) x x' (dp b1)).
              do 2 split...
            }
            subst x'.
            destruct E3
              as [ _ [ roc3c3' [ _ [ z' [ oc3oz' [ pc3oz' SSzE3a ]]]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3)).
              do 2 split...
            }
            subst z'.
            destruct E3'
              as [ _ [ y' [ oc2oy' [ pc2oy' OSyE3a' ]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da c2)(db c2) y y' (dp c2)).
              do 2 split...
            }
            subst y'.
            assert (OSxB2A3 : [ db b2 | x | db a3]).
            { apply (OSO_trans (db b2)(db b1')(db a3) x)...
              apply (SS_trans (db b1')(db a1')(db a3) x); apply SS_sym...
            }
            assert (OSyB1C3 : [ db b1 | y | db c3]).
            { apply OS_sym.
              apply (OSO_trans (db c3)(db c2')(db b1) y)...
              apply (SS_trans (db c2')(db b2')(db b1) y); auto;
              apply SS_sym...
            }
            apply (OOS_trans (db a3')(db a1)(db c3') z)...
            { apply OS_sym... }
            apply (OSO_trans (db a1)(db c2)(db c3') z)...
            assert (EqTr_b2a3 : EqOpFlagTrans ({{ c3 # c2 | c3c2 }})
              ({{ a3 # a1 | a3a1 }})).
            { symmetry in a3_c3.
              apply (EqFlagsTranslation_OOO ({{ a1 # a3 | a1a3 }})
                ({{ b2 # b1 | b2b1 }}))...
              right; do 2 try split; simpl...
              { apply (dp a1). }
              { exists x; do 2 try split... apply OS_sym... }
              { right; do 2 try split; simpl... apply (dp b2). }
            }
            destruct EqTr_b2a3
              as [ H1 |[ _ [ _ [ z' [ H1 [ H2 H3 ]]]]]]; simpl in *.
            { rewrite a3_c3 in H1.
              apply EqDirOpRs_irrefl in H1; firstorder.
            }
            { assert (zeqz' : z = z').
              { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3));
                do 2 split...
              }
              subst z'.
              apply OS_sym...
            }
          }
          { destruct E1
              as [ _ [ roa3a3' [ _ [ z' [ oa3oz' [ pa3oz' SSzE1a' ]]]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da a3)(db a3) z z' (dp a3)).
              do 2 split...
            }
            subst z'.
            destruct E1'
              as [ _ [ x' [ oa1ox' [ pa1ox' SSxE1a ]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da a1)(db a1) x x' (dp a1)).
              do 2 split...
            }
            subst x'.
            destruct E2
              as [ _ [ rob1b1' [ _ [ x' [ ob1ox' [ pb1ox' SSxE2a ]]]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da b1)(db b1) x x' (dp b1)).
              do 2 split...
            }
            subst x'.
            destruct E2'
              as [ _ [ y' [ ob2oy' [ pb2oy' OSyE2a' ]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da b2)(db b2) y y' (dp b2)).
              do 2 split...
            }
            subst y'.
            destruct E3
              as [ _ [ roc2c2' [ _ [ y' [ oc2oy' [ pc2oy' SSyE3a ]]]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da c2)(db c2) y y' (dp c2)).
              do 2 split...
            }
            subst y'.
            destruct E3'
              as [ _ [ z' [ oc3oz' [ pc3oz' OSzE3a' ]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3)). split... }
            subst z'.
            assert (OSxB2A3 : [ db b2 | x | db a3]).
            { apply OS_sym.
              apply (OSO_trans (db a3)(db b1')(db b2) x)...
              apply (OSO_trans (db a3)(db a1')(db b1') x)...
              apply SS_sym...
            }
            assert (OSyB1C3 : [ db b1 | y | db c3]).
            { apply (OSO_trans (db b1)(db c2')(db c3) y)...
              apply (OSO_trans (db b1)(db b2')(db c2') y)... apply SS_sym...
            }
            apply (SS_trans (db a3')(db a1)(db c3') z)...
            apply SS_sym...
            apply (OOS_trans (db a1)(db c2)(db c3') z)...
            assert (EqTr_b2a3 : EqOpFlagTrans ({{ c3 # c2 | c3c2 }})
              ({{ a3 # a1 | a3a1 }})).
            { symmetry in a3_c3.
              apply (EqFlagsTranslation_OOO ({{ a1 # a3 | a1a3 }})
                ({{ b2 # b1 | b2b1 }}))...
              right; do 2 try split; simpl...
              { apply (dp a1). }
              { exists x; split; auto. split... apply OS_sym... }
              right; do 2 try split; simpl... apply (dp b2).
            }
            destruct EqTr_b2a3
              as [ H1 |[ _ [ _ [ z' [ H1 [ H2 H3 ]]]]]]; simpl in *.
            { rewrite a3_c3 in H1.
              apply EqDirOpRs_irrefl in H1; firstorder.
            }
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3));
              do 2 split...
            }
            subst z'.
            apply OS_sym...
          }
          { destruct E1
              as [ _ [ roa3a3' [ _ [ z' [ oa3oz' [ pa3oz' SSzE1a' ]]]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da a3)(db a3) z z' (dp a3)).
              repeat split...
            }
            subst z'.
            destruct E1'
              as [ _ [ x' [ oa1ox' [ pa1ox' SSxE1a ]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da a1)(db a1) x x' (dp a1)).
              do 2 split...
            }
            subst x'.
            destruct E2
              as [ _ [ rob1b1' [ _ [ x' [ ob1ox' [ pb1ox' SSxE2a ]]]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da b1)(db b1) x x' (dp b1)).
              do 2 split...
            }
            subst x'.
            destruct E2'
              as [ _ [ y' [ ob2oy' [ pb2oy' OSyE2a' ]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da b2)(db b2) y y' (dp b2)).
              do 2split...
            }
            subst y'.
            destruct E3
              as [ _ [ roc3c3' [ _ [ z' [ oc3oz' [ pc3oz' SSzE3a ]]]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3)).
              do 2 split...
            }
            subst z'.
            destruct E3'
              as [ _ [ y' [ oc2oy' [ pc2oy' OSyE3a' ]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da c2)(db c2) y y' (dp c2)).
              do 2 split...
            }
            subst y'.
            assert (OSxB2A3 : [ db b2 | x | db a3]).
            { apply OS_sym.
              apply (OSO_trans (db a3)(db b1')(db b2) x)...
              apply (OSO_trans (db a3)(db a1')(db b1') x)...
              apply SS_sym...
            }
            assert (SSyB1C3 : [ y | db b1, db c3]).
            { apply (OOS_trans (db b1)(db c2')(db c3) y)...
              apply (OSO_trans (db b1)(db b2')(db c2') y)...
              apply OS_sym...
            }
            apply (SS_trans (db a3')(db a1)(db c3') z)...
            { apply SS_sym... }
            apply (SS_trans (db a1)(db c2)(db c3') z)...
            assert (EqTr_b2a3 : EqFlagsTranslation ({{ c3 # c2 | c3c2 }})
              ({{ a3 # a1 | a3a1 }})).
            { symmetry in a3_c3.
              apply (EqFlagsTranslation_OSS ({{ a1 # a3 | a1a3 }})
                ({{ b2 # b1 | b2b1 }}))...
              { right; do 2 try split; simpl... apply (dp a1).
                exists x; do 2 try split... apply OS_sym...
              }
              do 2 try split; simpl... apply (dp b2).
            }
            destruct EqTr_b2a3 as [ _ [ _ [ z' [ H1 [ H2 H3 ]]]]];
            simpl in *.
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3));
              do 2 split...
            }
            subst z'. apply SS_sym...
          }
          { destruct E1
              as [ _ [ roa3a3' [ _ [ z' [ oa3oz' [ pa3oz' SSzE1a' ]]]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da a3)(db a3) z z' (dp a3)).
              repeat split...
            }
            subst z'.
            destruct E1'
              as [ _ [ x' [ oa1ox' [ pa1ox' SSxE1a ]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da a1)(db a1) x x' (dp a1)).
              do 2 split...
            }
            subst x'.
            destruct E2
              as [ _ [ rob2b2' [ _ [ y' [ ob2oy' [ pb2oy' OSyE2a' ]]]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da b2)(db b2) y y' (dp b2)).
              do 2 split...
            }
            subst y'.
            destruct E2'
              as [ _ [ x' [ ob1ox' [ pb1ox' SSxE2a ]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da b1)(db b1) x x' (dp b1)).
              do 2 split...
            }
            subst x'.
            destruct E3
              as [ _ [ roc2c2' [ _ [ y' [ oc2oy' [ pc2oy' SSyE3a ]]]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da c2)(db c2) y y' (dp c2)).
              do 2 split...
            }
            subst y'.
            destruct E3'
              as [ _ [ z' [ oc3oz' [ pc3oz' OSzE3a' ]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3)).
              do 2 split...
            }
            subst z'.
            assert (SSxB2A3 : [ x | db b2, db a3]).
            { apply (OOS_trans (db b2)(db b1')(db a3) x)...
              apply OS_sym.
              apply (OSO_trans (db a3)(db a1')(db b1') x)...
            }
            assert (SSyB1C3 : [ y | db b1, db c3]).
            { apply (SS_trans (db b1)(db c2')(db c3) y)...
              apply (SS_trans (db b1)(db b2')(db c2') y)...
              apply SS_sym...
            }
            apply (SS_trans (db a3')(db a1)(db c3') z)...
            { apply SS_sym... }
            apply (OOS_trans (db a1)(db c2)(db c3') z)...
            assert (EqTr_b2a3 : EqOpFlagTrans ({{ c3 # c2 | c3c2 }})
              ({{ a3 # a1 | a3a1 }})).
            { symmetry in a3_c3.
              apply (EqFlagsTranslation_SSO ({{ a1 # a3 | a1a3 }})
                ({{ b2 # b1 | b2b1 }}))...
              { do 2 try split; simpl...
                { apply (dp a1). }
                { exists x; do 2 try split... apply SS_sym... }
              }
              do 2 try split; simpl... apply (dp b2).
            }
            destruct EqTr_b2a3
              as [ H1 |[ _ [ _ [ z' [ H1 [ H2 H3 ]]]]]]; simpl in *.
            { rewrite a3_c3 in H1.
              apply EqDirOpRs_irrefl in H1; firstorder.
            }
            { assert (zeqz' : z = z').
              { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3));
                do 2 split...
              }
              subst z'.
              apply OS_sym...
            }
          }
          { destruct E1
              as [ _ [ roa3a3' [ _ [ z' [ oa3oz' [ pa3oz' SSzE1a' ]]]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da a3)(db a3) z z' (dp a3)).
              repeat split...
            }
            subst z'.
            destruct E1'
              as [ _ [ x' [ oa1ox' [ pa1ox' SSxE1a ]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da a1)(db a1) x x' (dp a1)).
              repeat split...
            }
            subst x'.
            destruct E2
              as [ _ [ rob2b2' [ _ [ y' [ ob2oy' [ pb2oy' OSyE2a' ]]]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da b2)(db b2) y y' (dp b2)).
              repeat split...
            }
            subst y'.
            destruct E2'
              as [ _ [ x' [ ob1ox' [ pb1ox' SSxE2a ]]]].
            assert (xeqx' : x = x').
            { apply (DiPs_EqLs (da b1)(db b1) x x' (dp b1)).
              repeat split...
            }
            subst x'.
            destruct E3
              as [ _ [ roc3c3' [ _ [ z' [ oc3oz' [ pc3oz' SSzE3a ]]]]]].
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3)).
              repeat split...
            }
            subst z'.
            destruct E3'
              as [ _ [ y' [ oc2oy' [ pc2oy' OSyE3a' ]]]].
            assert (yeqy' : y = y').
            { apply (DiPs_EqLs (da c2)(db c2) y y' (dp c2)).
              repeat split...
            }
            subst y'.
            assert (SSxB2A3 : [ x | db b2, db a3]).
            { apply (OOS_trans (db b2)(db b1')(db a3) x)...
              apply OS_sym.
              apply (OSO_trans (db a3)(db a1')(db b1') x)...
            }
            assert (OSyB1C3 : [ db b1 | y | db c3]).
            { apply OS_sym. apply (OSO_trans (db c3)(db c2')(db b1) y)...
              apply (SS_trans (db c2')(db b2')(db b1) y); auto;
              apply SS_sym...
            }
            apply (SS_trans (db a3')(db c2)(db c3') z)...
            apply (SS_trans (db a3')(db a1)(db c2) z)...
            { apply SS_sym... }
            assert (EqTr_b2a3 : EqFlagsTranslation ({{ c3 # c2 | c3c2 }})
              ({{ a3 # a1 | a3a1 }})).
            { symmetry in a3_c3.
              apply (EqFlagsTranslation_SOS ({{ a1 # a3 | a1a3 }})
                ({{ b2 # b1 | b2b1 }}))...
              { do 2 try split; simpl... apply (dp a1).
                exists x; do 2 try split... apply SS_sym...
              }
              right; do 2 try split; simpl... apply (dp b2).
            }
            destruct EqTr_b2a3
              as [ _ [ _ [ z' [ H1 [ H2 H3 ]]]]]; simpl in *.
            assert (zeqz' : z = z').
            { apply (DiPs_EqLs (da c3)(db c3) z z' (dp c3));
              repeat split...
            }
            subst z'.
            apply SS_sym...
          }
        }
      }
    }
    { transitivity ({{ c2 # c2' | dic2c2' }})... }
  }
Qed.
Global Instance FlagOrientation_equiv :
  Equivalence EqFlagsOrientation
  := Build_Equivalence EqFlagsOrientation
     EqFlagsOrientation_refl
     EqFlagsOrientation_sym
     EqFlagsOrientation_trans.

Definition DecideFlagOrientationOnDistinctPoints :
  forall F G : Flag,
  da (da F) <> da (da G)
    -> { F ~~~ G } + { F ~//~ G }.
Proof with eauto.
  unfold EqFlagsOrientation.
  intros [ a a' diaa' ][ b b' dibb' ] nroab; simpl in *.
  assert (Exc : { c : Ray | c = {{ da a # da b | nroab }} }).
  { exists ({{ da a # da b | nroab }})... }
  destruct Exc as [ c Defc ].
  assert (roac : da a = da c). { rewrite Defc; simpl... }
  destruct (DrawEqRotatedFlagOnRay a a' c diaa' roac) as [ c' H1 ].
  assert (dicc' : ![c # c']). { destruct H1... }
  assert (FH : EqFlagsRotation
    ({{ a # a' | diaa' }})({{ c # c' | dicc' }})).
  { destruct H1... }
  clear H1.
  destruct (DrawSegmentExtension (da a)(da b) nroab) as [ P BetABP ].
  assert (nBeqP : da b <> P); dips.
  assert (Exd : { d : Ray | d = {{ da b # P | nBeqP }} }).
  { exists ({{ da b # P | nBeqP }})... }
  destruct Exd as [ d Defd ].
  assert (nroc'b : db c <> db c').
  { clear FH. apply nColRs_nColPs in dicc'.
    destruct dicc' as [ rocc' [ nceqc' ncopc' ]].
    contradict nceqc'. unfold EqRays. split...
    rewrite <- nceqc'. apply SR_refl... apply (dp c).
  }
  assert (Exd' : { d' : Ray | d' = {{ db c # db c' | nroc'b }} }).
  { exists ({{ db c # db c' | nroc'b }})... }
  destruct Exd' as [ d' Defd' ].
  assert (didd' : ![d # d']).
  { split...
    { rewrite Defd, Defd'; simpl... rewrite Defc; simpl... }
    { assert (nColc : ~ [db c, da c, db c']).
      { elim dicc'. intros. ncolps. }
      contradict nColc.
      rewrite Defc in *; simpl in *...
      rewrite Defd in *; simpl in *...
      apply BetPs_ColPs in BetABP.
      destruct BetABP as [ x [ oaox [ obox Pox ]]].
      destruct nColc as [ x' [ Pox' [ Box' D'ox' ]]].
      assert (xeqx' : x = x'); eqls. subst x'.
      exists x; do 2 try split...
      assert (rpc'd' : db c' = db d'). { rewrite Defd'; simpl... }
      rewrite rpc'd'...
    }
  }
  assert (FG : EqFlagsTranslation
    ({{ c # c' | dicc' }})({{ d # d' | didd' }})).
  { split; simpl...
    { right; left.
      rewrite Defc; rewrite Defd; split; simpl...
      apply SR_refl...
    }
    { split.
      { apply (dp c). }
      { apply BetPs_ColPs in BetABP.
        destruct BetABP as [ x [ oaox [ obox Pox ]]].
        exists x; do 2 try split; try rewrite Defc; simpl...
        rewrite Defd'; simpl; apply SS_refl...
        assert (nColc : ~ [db c, da c, db c']).
        { elim dicc'. intros. ncolps. }
        contradict nColc.
        exists x; rewrite Defc; simpl...
      }
    }
  }
  destruct (DecideEqFlagsRotation ({{ d # d' | didd' }})
    ({{ b # b' | dibb' }})) as [ H1 | H2 ]; simpl...
  { rewrite Defd; simpl... }
  { left.
    exists ({{ c # c' | dicc' }}), ({{ d # d' | didd' }}).
    do 2 try split; simpl... symmetry...
  }
  { right.
    contradict H2.
    destruct H2 as [[ f f' diff' ][[ g g' digg' ][ AF' [ F'G' BG' ]]]];
    simpl in *. symmetry.
    transitivity ({{ g # g' | digg' }})...
    assert (CF : EqFlagsRotation
      ({{ c # c' | dicc' }})({{ f # f' | diff' }})).
    { transitivity ({{ a # a' | diaa' }})... symmetry... }
    unfold EqFlagsTranslation in *; simpl in *.
    destruct FG as [ c_d SFxCD ].
    destruct F'G' as [ f_g SFxFG ].
    assert (rocf : da c = da f).
    { apply (EqFlagsRotation_EqFlagsOrg ({{ c # c' | dicc' }})
        ({{ f # f' | diff' }}))...
    }
    assert (robg : da b = da g).
    { apply (EqFlagsRotation_EqFlagsOrg ({{ b # b' | dibb' }})
        ({{ g # g' | digg' }}))...
    }
    assert (rodg : da d = da g).
    { rewrite <- robg. rewrite Defd. simpl... }
    assert (nrocd : da c <> da d).
    { rewrite <- roac. rewrite rodg. rewrite <- robg... }
    clear dependent a. clear dependent b.
    destruct (DrawExtensionLinePP (da c)(da d) nrocd)
      as [ x [ ocx odx ]].
    assert (pcx : [ db c @ x ]).
    { apply EqDirRs_ColRs in c_d.
      destruct c_d as [ x' [ ocx' [ pcx [ odx' pdx ]]]].
      assert (xeqx' : x = x'); eqls.
    }
    assert (pdx : [ db d @ x ]).
    { apply EqDirRs_ColRs in c_d.
      destruct c_d as [ x' [ ocx' [ pcx' [ odx' pdx ]]]].
      assert (xeqx' : x = x'); eqls.
    }
    assert (ofx : [ da f @ x ]). { rewrite <- rocf... }
    assert (ogx : [ da g @ x ]). { rewrite <- rodg... }
    assert (pfx : [ db f @ x ]).
    { apply EqDirRs_ColRs in f_g.
      destruct f_g as [ x' [ ofx' [ pfx [ ogx' pgx ]]]].
      assert (xeqx' : x = x').
      { apply (DiPs_EqLs (da f)(da g) x x').
        rewrite <- rocf. rewrite <- rodg...
        repeat split...
      }
      subst x'...
    }
    assert (pgx : [ db g @ x ]).
    { apply EqDirRs_ColRs in f_g.
      destruct f_g as [ x' [ ofx' [ pfx' [ ogx' pgx ]]]].
      assert (xeqx' : x = x').
      { apply (DiPs_EqLs (da f)(da g) x x').
        rewrite <- rocf. rewrite <- rodg...
        repeat split...
      }
      subst x'...
    }
    assert (Colcf : ![c, f]). { exists x; repeat split... }
    destruct (DecideRayDirection c f Colcf) as [ c_f | c_f ].
    { assert (g_d : g ~~ d).
      { symmetry. transitivity f... transitivity c... symmetry... }
      apply EqFlagsTranslation_EqFlagsRotation; simpl...
      apply EqFlagsRotation_EqFlagsTranslation in CF; simpl.
      destruct SFxCD as [ _ [ x' [ ocx' [ pcx' SSxCD ]]]].
      assert (xeqx': x = x').
      { apply (DiPs_EqLs (da c)(db c) x x' (dp c)); split; split... }
      subst x'.
      destruct SFxFG as [ _ [ x' [ ofx' [ pfx' SSxFG ]]]].
      assert (xeqx': x = x').
      { apply (DiPs_EqLs (da f)(db f) x x' (dp f)); split; split... }
      subst x'.
      do 2 try split; simpl...
      { apply (dp g). }
      { exists x; do 2 try split...
        destruct CF as [ _ [ _ [ x' [ ocx'' [ pcx'' SSxCF ]]]]];
        simpl in *.
        assert (xeqx': x = x').
        { apply (DiPs_EqLs (da c)(db c) x x' (dp c));
          do 2 split...
        }
        subst x'.
        apply (SS_trans (db g')(db c')(db d') x)...
        apply SS_sym.
        apply (SS_trans (db c')(db f')(db g') x)...
      }
      { apply EqRsDir_EqRs... }
    }
    { apply ColRs_DiDirRs_EqDirOpRs in c_f...
      assert (dopg : d ~~ !g).
      { rewrite <- c_d; rewrite <- f_g... }
      symmetry.
      apply EqFlagsRotation_EqOpFlagRotation in CF.
      apply EqFlagsRotation_EqFlagsTranslation in CF; simpl...
      assert (EqFlagsRotation
        ({{ d # d' | didd' }})(({{ !g # !g' | nCol_OpRs g g' digg' }}))).
      { apply EqFlagsTranslation_EqFlagsRotation; simpl...
        rewrite rodg. apply OpRays_0.
        destruct SFxCD as [ _ [ x' [ ocx' [ pcx' SSxCD ]]]].
        assert (xeqx': x = x').
        { apply (DiPs_EqLs (da c)(db c) x x' (dp c));
          repeat split...
        }
        subst x'.
        destruct SFxFG as [ _ [ x' [ ofx' [ pfx' SSxFG ]]]].
        assert (xeqx': x = x').
        { apply (DiPs_EqLs (da f)(db f) x x' (dp f));
          repeat split...
        }
        subst x'.
        destruct CF as [ _ [ _ [ x' [ ocx'' [ pcx'' SSxCF ]]]]];
        simpl in *.
        do 2 try split; simpl...
        { apply (dp d). }
        { exists x; do 2 try split...
          { apply (SS_trans (db d')(db c')(db (!g')) x)...
            apply SS_sym...
            apply (SS_trans (db c')(db (!f'))(db (!g')) x)...
            assert (xeqx': x = x').
            { apply (DiPs_EqLs (da c)(db c) x x' (dp c));
              repeat split...
            }
            subst x'...
            assert (roff' : da f = da f'). { destruct diff'... }
            assert (rogg' : da g = da g'). { destruct digg'... }
            destruct f' as [ O F' nF'eqO ].
            destruct g' as [ O' G' nG'eqO ].
            unfold OpRay in *; simpl in *.
            destruct (DrawOppositePoint O F')
              as [ F'' [ BetF'OF'' _ ]]...
            destruct (BetPs_3DiPs F' O F'' BetF'OF'')
              as [ _ [ nOeqF'' nF'eqF'' ]].
            destruct (DrawOppositePoint O' G')
              as [ G'' [ BetG'O'G'' _ ]]...
            destruct (BetPs_3DiPs G' O' G'')
              as [ _ [ nOeqG'' nG'eqG'' ]]; simpl in *...
            assert (Oox : [ O @ x ]). { rewrite <-roff'... }
            assert (O'ox : [ O' @ x ]). { rewrite <-rogg'... }
            apply (OOS_trans F'' F' G'' x)...
            { do 2 try split.
              { destruct diff' as [ _ diff' ]. contradict diff'.
                exists x; split; simpl; incpt 3.
              }
              { destruct diff' as [ _ diff' ]. contradict diff'.
                exists x; split; simpl...
              }
              { exists O; split...
                apply BetPs_sym...
              }
            }
            apply OS_sym.
            apply SS_sym in SSxFG.
            apply (OSO_trans G'' G' F' x)...
            do 2 try split.
            { destruct digg' as [ _ digg' ]. contradict digg'.
              exists x; split; simpl; incpt 3.
            }
            { destruct digg' as [ _ digg' ]. contradict digg'.
              exists x; split; simpl...
            }
            exists O'; split...
            apply BetPs_sym...
          }
        }
      }
      assert (H1 : EqFlagsRotation ({{ d # d' | didd' }})
        ({{ !!g # !!g' | nCol_OpRs (!g) (!g') (nCol_OpRs g g' digg') }})).
      { apply EqFlagsRotation_EqOpFlagRotation... }
      assert (H2 :
        ({{ !!g # !!g' | nCol_OpRs (!g) (!g') (nCol_OpRs g g' digg') }})
          === ({{ g # g' | digg' }})).
      { symmetry.
        split; simpl...
        { apply OpOpRs. }
          { assert (g'_g' : g' == !(!g')). { apply OpOpRs. }
            apply SameSideRs_sym.
            apply (SameSideRs_inv g g' g' g (!!g') g'); try reflexivity...
            apply (SameSideRs_refl g g')...
          }
      }
      apply (EqFlagsRotation_inv ({{ d # d' | didd' }})
        ({{ !!g # !!g' | nCol_OpRs (!g) (!g') (nCol_OpRs g g' digg') }}))...
      reflexivity...
      { apply EqRsDir_EqRs... rewrite rocf. apply OpRays_0. }
    }
  }
Defined.

Definition DrawEqOrientedFlagOnDistinctPoint :
  forall (P : Point)(F : Flag),
  P <> da (da F)
    -> { G : Flag | da (da G) = P /\ EqFlagsOrientation F G }.
Proof with eauto.
  intros P F nPeqF.
  apply not_eq_sym in nPeqF.
  assert (Exc : { c : Ray | c = {{ da (da F) # P | nPeqF }} }).
  { exists ({{ da (da F) # P | nPeqF }})... }
  destruct Exc as [ c Defc ].
  assert (roFc : da (da F) = da c). { rewrite Defc; simpl... }
  destruct (DrawEqRotatedFlagOnRay (da F)(db F) c (dp F) roFc)
    as [ d H1 ].
  assert (dicd : ![ c # d ]). { destruct H1 as [ dicd H1 ]... }
  assert (FH : EqFlagsRotation
    ({{ da F # db F | dp F }})({{ c # d | dicd }})).
  { destruct H1 as [ dicd' H1 ]... }
  clear H1.
  destruct (DrawSegmentExtension (da (da F)) P) as [ Q BetFPQ ]...
  assert (nQeqP : P <> Q). { apply (BetPs_3DiPs (da (da F)) P Q BetFPQ). }
  assert (Exc' : { c' : Ray | c' = {{ P # Q | nQeqP }} }).
  { exists ({{ P # Q | nQeqP }})... }
  destruct Exc' as [ c' Defc' ].
  assert (nDeqP : P <> db d).
  { clear FH. apply nColRs_nColPs in dicd.
    destruct dicd as [ rocd [ nceqd H ]].
    contradict nceqd. split... rewrite Defc; simpl... rewrite nceqd.
    apply SR_refl... rewrite <- nceqd...
  }
  assert (Exd' : { d' : Ray | d' = {{ P # db d | nDeqP }} }).
  { exists ({{ P # db d | nDeqP }})... }
  destruct Exd' as [ d' Defd' ].
  assert (dic'd' : ![c' # d']).
  { rewrite Defc', Defd'... split... clear FH.
    rewrite Defc in dicd; simpl in *...
    destruct dicd as [ _ dicd ].
    contradict dicd.
    destruct (BetPs_ColPs (da (da F)) P Q BetFPQ)
      as [ x [ Fox [ Pox Qox ]]].
    destruct dicd as [ x' [ Qox' [ Pox' Dox ]]].
    assert (xeqx' : x = x').
    { apply (DiPs_EqLs P Q x x' nQeqP); split; split... }
    subst x'.
    exists x; repeat split...
  }
  exists ({{ c' # d' | dic'd' }}); simpl; split.
  { rewrite Defc'; simpl... }
  { unfold EqFlagsOrientation.
    exists ({{ c # d | dicd }}), ({{ c' # d' | dic'd' }}).
    do 3 try split; simpl...
    { unfold EqRaysDir. rewrite Defc, Defc'; simpl... right. left. split...
      apply SR_refl...
    }
    { rewrite Defc, Defd'; simpl... split...
      destruct (DrawExtensionLinePP (da (da F)) P nPeqF)
        as [ x [ Fox Pox ]].
      exists x; split... split... apply SS_refl... clear FH.
      destruct dicd as [ _ dicd ]. contradict dicd. rewrite Defc; simpl.
      exists x; split...
    }
    { reflexivity. }
  }
Defined.

(** Problem #23 *)
Definition DecideFlagOrientation :
  forall F G : Flag,
  { F ~~~ G } + { F ~//~ G }.
Proof with eauto.
  intros F G.
  destruct (DrawThirdDistinctPoint (da (da F))(da (da G)))
    as [ P [ nPeqF nPeqG ]].
  destruct (DrawEqOrientedFlagOnDistinctPoint P F nPeqF)
    as [ F' [ H1 F_F' ]].
  destruct (DrawEqOrientedFlagOnDistinctPoint P G nPeqG)
    as [ G' [ H2 G_G' ]].
  destruct (DecideEqFlagsRotation F' G')
    as [ F'_G' | nF'_G' ].
  { rewrite H1. rewrite H2... }
  { left. rewrite F_F'. rewrite G_G'. exists F', F'.
    split; try reflexivity. split; try reflexivity. symmetry...
  }
  { right. contradict nF'_G'. rewrite F_F' in nF'_G'. rewrite G_G' in nF'_G'.
    destruct nF'_G' as [ F'' [ G'' [ F'_F'' [ F''_G'' G'_G'' ]]]].
    transitivity F''... symmetry. transitivity G''...
    apply EqFlagsTranslation_EqFlagsRotation.
    apply EqFlagsRotation_EqFlagsOrg in F'_F''.
    apply EqFlagsRotation_EqFlagsOrg in G'_G''.
    rewrite <- F'_F''. rewrite <- G'_G''.
    rewrite H1. rewrite H2... symmetry...
  }
Defined.

Definition DrawEqOrientedFlagOnPoint :
  forall (P : Point)(F : Flag),
  { G : Flag | da (da G) = P /\ EqFlagsOrientation F G }.
Proof with eauto.
  intros P F.
  destruct (DrawThirdDistinctPoint (da (da F)) P)
    as [ Q [ nQeqF nQeqP ]].
  destruct (DrawEqOrientedFlagOnDistinctPoint Q F)
    as [ F' [ H1 F_F' ]]...
  assert (nPeqF' : P <> da (da F')). rewrite H1. auto.
  destruct (DrawEqOrientedFlagOnDistinctPoint P F')
   as [ F'' H2 ]...
  destruct H2 as [ H2 F'_F'' ].
  exists F''. split... transitivity F'...
Defined.

(** Theorem #31 *)
Lemma DiFlagsOrientation_EqFlipFlagOrientation :
  forall F G : Flag,
  F ~//~ G <-> F ~~~ # G.
Proof with eauto.
  intros F G.
  split.
  { intros nFeqG.
    destruct (DrawEqOrientedFlagOnPoint (da (da G)) F)
      as [ F' [ H2 F_F' ]].
    rewrite F_F'.
    exists F', F'. do 2 try split; try reflexivity.
    symmetry. rewrite F_F' in nFeqG.
    assert (nEqFG : ~ EqFlagsRotation F' G).
    { contradict nFeqG. exists F', F'.
      do 2 try split; try reflexivity. symmetry...
    }
    apply nEqFlagsRotation_EqInvFlagRotation...
  }
  { intros F_G' F_G.
    rewrite F_G in F_G'. clear dependent F.
    destruct F_G' as [ F [ F' [ G_F [ F_F' G'_F' ]]]].
    assert (roGF : da (da G) = da (da F)).
    { apply EqFlagsRotation_EqFlagsOrg... }
    assert (roG'F' : da (da (# G)) = da (da F')).
    { apply EqFlagsRotation_EqFlagsOrg... }
    assert (roGG' : da (da G) = da (da (# G))).
    { destruct G as [ g g' digg' ]. simpl in *.
      destruct digg' as [ rogg' H ]...
    }
    apply EqFlagsTranslation_EqFlagsRotation in F_F'.
    { assert (G_G' : EqFlagsRotation G (#G)).
      { transitivity F... transitivity F'... symmetry... }
      apply nEqFlagsRotation_EqInvFlagRotation in G_G'...
      contradict G_G'. reflexivity...
    }
    rewrite <- roGF. rewrite <- roG'F'...
  }
Qed.

Lemma EqFlags_EqFlagsOrientation :
  forall (F G : Flag),
  F === G
    -> F ~~~ G.
Proof.
  intros F G.
  unfold EqFlagsOrientation; simpl.
  exists F, G. split; try split; try reflexivity.
  destruct H as [ H1 [ H2 [ H4 H5 ]]].
  unfold EqFlagsTranslation; simpl in *.
  split; auto. unfold EqRaysDir. repeat split; eauto.
Qed.

(** Theorem #32 *)
Global Instance FlipFlag_compat :
  Proper (EqFlagsOrientation ==> EqFlagsOrientation) FlipFlag.
Proof with eauto.
  intros F G FeqG.
  destruct (DecideFlagOrientation (#F)(#G)) as [ H1 | H2 ]...
  apply DiFlagsOrientation_EqFlipFlagOrientation in H2.
  rewrite H2. symmetry.
  assert (G_G' : G ~~~ # (#G)).
  { apply EqFlags_EqFlagsOrientation. apply FlipFlipFlag. }
  rewrite <- G_G' in *. rewrite <- FeqG in *. symmetry in H2.
  apply DiFlagsOrientation_EqFlipFlagOrientation in H2.
  contradict H2. reflexivity.
Qed.

Lemma EqFlagsOrientation_EqFlagsRotation :
  forall (F G : Flag),
  da (da F) = da (da G)
    -> F ~~~ G
    -> EqFlagsRotation F G.
Proof with eauto.
  intros F G rofoFG [ F' [ G' [ H1 [ H2 H3 ]]]].
  transitivity F'... symmetry.
  transitivity G'... symmetry.
  apply EqFlagsTranslation_EqFlagsRotation...
  apply EqFlagsRotation_EqFlagsOrg in H1. rewrite <- H1...
  apply EqFlagsRotation_EqFlagsOrg in H3. rewrite <- H3...
Qed.

Lemma EqFlagsOrientation_EqFlagsTranslation :
  forall (F G : Flag),
  da F ~~ da G
    -> F ~~~ G
    -> EqFlagsTranslation F G.
Proof with eauto.
  intros F G fpFG F_G.
  destruct (classic ( (da (da F)) = (da (da G)))) as [ FeqG | nFeqG ].
  { apply EqFlagsOrientation_EqFlagsRotation in F_G...
    apply EqFlagsRotation_EqFlagsTranslation...
    destruct fpFG as [[ H1 H2 ]| H3 ].
    { split... }
    { assert (nFeqG : da (da F) <> da (da G)); dips.
      { destruct H3 as [[ H3 H4 ]|[ H3 H4 ]]; dips. }
    }
  }
  { destruct F_G as [ F' [ G' [ H1 [ H2 H3 ]]]].
    assert (rofoFF' : da (da F) = da (da F')).
    { apply EqFlagsRotation_EqFlagsOrg... }
    assert (rofoGG' : da (da G) = da (da G')).
    { apply EqFlagsRotation_EqFlagsOrg... }
    assert (fpF'G' : da F' ~~ da G'). { destruct H2... }
    assert (Hfg := fpFG).
    apply EqDirRs_ColRs in Hfg.
    destruct Hfg as [ x [ Aox [ Box [ A'ox B'ox ]]]].
    assert (Hf'g' := fpF'G').
    apply EqDirRs_ColRs in Hf'g'.
    destruct Hf'g' as [ x' [ Aox' [ Box' [ A'ox' B'ox' ]]]].
    assert (xeqx' : x = x').
    { destruct rofoFF'. destruct rofoGG'.
      apply (DiPs_EqLs (da (da F))(da (da G)) x x' nFeqG); do 2 split...
    }
    subst x'.
    assert (ColFF' : ![da F, da F']). { exists x; repeat split... }
    assert (ColGG' : ![da G, da G']). { exists x; repeat split... }
    destruct (DecideRayDirection (da F)(da F')) as [ foFF' | nfoFF' ]...
    { assert (foGG' : da G ~~ da G').
      { transitivity (da F)... symmetry... transitivity (da F')... }
      assert (GeqG' : da G == da G').
      { destruct foGG' as [[ H4 H5 ]| H6 ]; split...
        assert (nGeqG' : da (da G) <> da (da G')).
        { destruct H6 as [[[ H4 H4' ] H5 ]|[[ H4 H4' ] H5 ]]... }
        contradiction.
      }
      assert (FeqF' : da F == da F').
      { destruct foFF' as [[ H4 H5 ]| H6 ]; split...
        assert (nFeqF' : da (da F) <> da (da F')).
        { destruct H6 as [[[ H4 H4' ] H5 ]|[[ H4 H4' ] H5 ]]... }
        contradiction.
      }
      apply EqFlagsRotation_EqFlagsTranslation in H1...
      apply EqFlagsRotation_EqFlagsTranslation in H3...
      transitivity F'... transitivity G'; auto; symmetry...
    }
    apply ColRs_DiDirRs_EqDirOpRs in nfoFF'...
    assert (foGG' : da G ~~ !da G').
    { transitivity (da F)...
      { symmetry... }
      transitivity (!da F')... rewrite fpF'G'. reflexivity.
    }
    assert (GeqG' : da G == !da G').
    { destruct foGG' as [[ H4 H5 ]| H6 ].
      { split... }
      { assert (nGeqG' : da (da G) <> da (!da G')).
        { destruct H6 as [[[ H4 H4' ] H5 ]|[[ H4 H4' ] H5 ]]... }
        assert (GeqG' : da (da G) = da (!da G')).
        { rewrite rofoGG'. apply OpRays_0. }
        contradiction.
      }
    }
    assert (FeqF' : da F == !da F').
    { destruct nfoFF' as [[ H4 H5 ]| H6 ].
      { split... }
      { assert (nFeqF' : da (da F) <> da (!da F')).
        { destruct H6 as [[[ H4 H4' ] H5 ]|[[ H4 H4' ] H5 ]]... }
        assert (FeqF' : da (da F) = da (!da F')).
        { rewrite rofoFF'. apply OpRays_0. }
        contradiction.
      }
    }
    destruct F as [ a a' diaa' ].
    destruct G as [ b b' dibb' ].
    destruct F' as [ c c' dicc' ].
    destruct G' as [ d d' didd' ]; simpl in *.
    apply EqFlagsRotation_EqOpFlagRotation in H1...
    apply EqFlagsRotation_EqOpFlagRotation in H3...
    apply EqFlagsRotation_EqFlagsTranslation in H1...
    { apply EqFlagsRotation_EqFlagsTranslation in H3...
      { transitivity (({{!c # !c' | nCol_OpRs c c' dicc'}}))...
        transitivity (({{!d # !d' | nCol_OpRs d d' didd'}}));
        eauto; symmetry... symmetry in H2...
        split; simpl in *.
        { symmetry. transitivity b... transitivity a... symmetry... }
        { assert (Colab : ![ a , b ]).
          { apply EqDirRs_ColRs... }
          clear dependent a. clear dependent b.
          destruct H2 as [ a_b SSxAB ].
          destruct d as [ O A nAeqO ]. destruct d' as [ O'' A' nA'eqO ].
          destruct c as [ O' B nBeqO' ]. destruct c' as [ O''' B' nB'eqO' ].
          destruct didd' as [ roaa diaa ]. destruct dicc' as [ robb dibb ].
          unfold EqFlagsTranslation; simpl in *.
          subst O''' O''.
          unfold EqRaysDir, OpRay in *. simpl in *.
          destruct (DrawOppositePoint O A) as [ C [ BetAOC _ ]]; simpl...
          destruct (DrawOppositePoint O A') as [ C' [ BetA'OC' _ ]]; simpl...
          destruct (DrawOppositePoint O' B') as [ D' [ BetB'O'D' _ ]]; simpl...
          destruct (BetPs_3DiPs A O C BetAOC)
            as [ nOeqA [ nOeqC nAeqC ]]; simpl...
          destruct (BetPs_3DiPs A' O C' BetA'OC')
            as [ nOeqA' [ nOeqC' nA'eqC' ]]; simpl...
          destruct (BetPs_3DiPs B' O' D' BetB'O'D')
            as [ nOeqB' [ nOeqD' nB'eqD' ]]; simpl...
          split; auto.
          destruct SSxAB as [ _ [ x' [ Oox [ Aox SSxAB ]]]].
          assert (xeqx' : x' = x); eqls; subst.
          exists x; do 2 try split; simpl in *; incpt 2.
          apply BetPs_sym in BetA'OC'.
          assert (nA'ox : ~ [A' @ x]). { firstorder. }
          assert (nC'ox : ~ [C' @ x]). { contradict nA'ox; incpt 2. }
          assert (nB'ox : ~ [B' @ x]). { firstorder. }
          assert (nD'ox : ~ [D' @ x]). { contradict nB'ox; incpt 2. }
          apply (OOS_trans C' B' D' x)...
          { apply (OSO_trans C' A' B' x)...
            repeat split; simpl in *...
          }
          repeat split...
        }
      }
    }
  }
Qed.

End FLAG.

Notation " # F "
  := (FlipFlag F)
  (at level 50).
Notation " F === G "
  := (EqFlags F G)
  (at level 60).
Notation " F =//= G "
  := (~ EqFlags F G)
  (at level 60).
Notation " F ~~~ G "
  := (EqFlagsOrientation F G)
  (at level 70).
Notation " F ~//~ G "
  := (~ EqFlagsOrientation F G)
  (at level 70).
Tactic Notation "pir" constr(E) "=>" constr(F)
  := replace E with F in * by apply proof_irrelevance; auto; try clear E.

(*****************************************************************************)
(* 10 *) Section ORIENTATION.
Context `{ cr : Circles }.
(*****************************************************************************)

Global Instance on : Orientations (qs).
Proof with eauto.
  eapply (Build_Orientations dc df qs). Unshelve.
  { intros [ a b ab ].
  destruct (DecideFlagOrientation ({{ a # b | ab }}) F0).
  { apply true. }
  { apply false. }
  }
  { apply nColPs_3DiPs. }
  { apply nColPerPs_1. }
  { apply nColPerPs_2. }
Defined.

Definition DecideOrientations :
  forall (T1 T2 : bool),
  { T1 = T2 } + { T1 = negb T2 }.
Proof with eauto.
  intros T1 T2.
  induction T1, T2...
Defined.

Definition ClockwiseTriangle (T : Triangle) : bool :=
  match nColPs_DiPs (ta T)(tb T)(tc T)(tp T) with
  | conj nOeqA (conj nOeqB _) =>
    let a := {{ (tb T) # (ta T) | nOeqA }} in
    let b := {{ (tb T) # (tc T) | nOeqB }} in
    ConvexFlag ({{ a # b | (conj eq_refl (tp T)) }})
  end.
Notation " %[ a # b | ab ] "
  := (ConvexFlag ({{ a # b | ab }}))
  (at level 60).
Notation " %[ A # O # B | AOB ] "
  := (ClockwiseTriangle ({{ A # O # B | AOB }}))
  (at level 60).

Definition DecideRaysOrientation :
  forall (a b : Ray)(diab : ![ a # b ]),
  { %[ a # b | diab ] = true } + { %[ a # b | diab ] = false }.
Proof.
  intros a b diab.
  induction (%[a # b | diab]); [ left | right ]; auto.
Defined.

Example DecideOrientationsRs :
  forall (a b c d : Ray)(diab : ![ a # b ])(dicd : ![ c # d ]),
  { %[ a # b | diab ] = %[ c # d | dicd ] } +
  { %[ a # b | diab ] = negb (%[ c # d | dicd ]) }.
Proof with eauto.
  intros a b c d diab dicd.
  induction (%[a # b | diab]), (%[ c # d | dicd ])...
Defined.

Lemma OsPs_OsRs :
  forall (A O B : Point)(nColAOB : ~ [ A, O, B ]),
  exists (nOeqA : O <> A)(nOeqB : O <> B)
    (diab : ![ {{ O # A | nOeqA }} # {{ O # B | nOeqB }} ]),
  %[ A # O # B | nColAOB ]
    = %[ {{ O # A | nOeqA }} # {{ O # B | nOeqB }} | diab ].
Proof with eauto.
  intros A O B nColAOB.
  unfold ConvexFlag, ClockwiseTriangle; simpl.
  destruct (nColPs_3DiPs A O B nColAOB)
    as [ nOeqA [ nOeqB nAeqB ]].
  destruct (nColRs_nColPs ({{ O # A | nOeqA }})({{ O # B | nOeqB }}))
    as [ H _ ]; simpl in *.
  exists nOeqA, nOeqB, (conj (eq_refl O) nColAOB); reflexivity.
Qed.
Lemma OsRs_OsPs :
  forall (A O B : Point)(nOeqA : O <> A)(nOeqB : O <> B)
    (diab : ![ {{ O # A | nOeqA }} # {{ O # B | nOeqB }} ]),
  exists (nColAOB : ~ [ A, O, B ]),
  %[ {{ O # A | nOeqA }} # {{ O # B | nOeqB }} | diab ]
    = %[ A # O # B | nColAOB ].
Proof.
  intros A O B nOeqA nOeqB diAB.
  unfold ConvexFlag, ClockwiseTriangle; simpl.
  assert (nColAOB : ~ [A, O, B]). { destruct diAB; auto. }
  exists nColAOB; simpl.
  destruct (nColPs_3DiPs A O B nColAOB)
    as [ nOeqA' [ nOeqB' nAeqB ]].
  pir nOeqA' => nOeqA. pir nOeqB' => nOeqB.
  destruct diAB as [ roab diAB ]; simpl in *.
  pir (conj (eq_refl O) nColAOB) => (conj roab diAB).
Qed.
Lemma OsRs_OsPs' :
  forall (A O B : Point)(nOeqA : O <> A)(nOeqB : O <> B)
    (nColAOB : ~ [ A, O, B ])
    (diab : ![ {{ O # A | nOeqA }} # {{ O # B | nOeqB }} ]),
  %[ {{ O # A | nOeqA }} # {{ O # B | nOeqB }} | diab ]
    = %[ A # O # B | nColAOB ].
Proof.
  intros A O B nAeqO nBeqO nColAOB diAB.
  destruct (OsPs_OsRs A O B nColAOB) as [ H1 [ H2 [ H3 H4 ]]].
  pir H1 => nAeqO. pir H2 => nBeqO. pir H3 => diAB.
Qed.

Lemma DiFlipFlagTurn :
  forall (F : Flag),
  % F = negb ( % ( # F )).
Proof.
  intros F.
  destruct (DecideFlagOrientation F (# F)) as [ H1 | H2 ].
  { apply DiFlagsOrientation_EqFlipFlagOrientation in H1.
    contradict H1. apply EqFlagsOrientation_refl.
  }
  { unfold ConvexFlag, FlipFlag in *.
    destruct F as [ a b ab ]; simpl in *.
    induction (DecideFlagOrientation ({{a # b | ab}}) F0) as [ i1 | i2 ];
    induction (DecideFlagOrientation ({{b # a | nColRs_sym a b ab}}) F0)
      as [ i3 | i4 ]; try discriminate; simpl in *; try reflexivity.
    { contradict H2. rewrite i1. rewrite i3. reflexivity. }
    { apply DiFlagsOrientation_EqFlipFlagOrientation in i2.
      apply DiFlagsOrientation_EqFlipFlagOrientation in i4.
      contradict H2. rewrite i2. rewrite i4. reflexivity.
    }
  }
Qed.

Lemma EqFlagsOrientations :
  forall (F G : Flag),
  (% F = % G) <-> (F ~~~ G).
Proof.
  intros F G.
  split.
  { unfold ConvexFlag in *; simpl in *.
    intros tF_tG. unfold ConvexFlag, FlipFlag.
    destruct F as [ a b ab ]; destruct G as [ c d cd ]; simpl in *.
    induction (DecideFlagOrientation ({{a # b | ab}}) F0) as [ i1 | i2 ];
    induction (DecideFlagOrientation ({{c # d | cd}}) F0) as [ i3 | i4 ];
    try discriminate.
    { apply EqFlagsOrientation_trans with F0; auto.
      apply EqFlagsOrientation_sym; auto.
    }
    { apply DiFlagsOrientation_EqFlipFlagOrientation in i2.
      apply DiFlagsOrientation_EqFlipFlagOrientation in i4.
      apply EqFlagsOrientation_trans with (# F0); auto.
      apply EqFlagsOrientation_sym; auto.
    }
  }
  { intro FeqG. unfold ConvexFlag; simpl.
    destruct F as [ a b ab ]; destruct G as [ c d cd ]; simpl in *.
    induction (DecideFlagOrientation ({{a # b | ab}}) F0) as [ i1 | i2 ];
    induction (DecideFlagOrientation ({{c # d | cd}}) F0) as [ i3 | i4 ];
    try discriminate; auto.
    { contradict i4.
      apply EqFlagsOrientation_trans with ({{a # b | ab}}); auto.
      apply EqFlagsOrientation_sym; auto.
    }
    { contradict i2.
      apply EqFlagsOrientation_trans with ({{c # d | cd}}); auto.
    }
  }
Qed.

(** Theorem #33 *)
Theorem DiOsRs :
  forall (a b : Ray)(diab : ![ a # b ])(diba : ![ b # a ]),
  %[ a # b | diab ] = negb (%[ b # a | diba ]).
Proof.
  intros a b diab diba.
  assert (H : (% {{a # b | diab}}) = negb (% # ({{a # b | diab}}))).
  { apply (DiFlipFlagTurn ({{a # b | diab}})). }
  unfold FlipFlag in *. pir (nColRs_sym a b diab) => diba.
Qed.

Lemma OrientationRs_LR :
  forall (a b : Ray)(diab : ![ a # b ])(diba : ![ b # a ]),
  %[ a # b | diab ] = true
    -> %[ b # a | diba ] = false.
Proof.
  intros * abL.
  rewrite (DiOsRs b a diba diab).
  rewrite abL; simpl; reflexivity.
Qed.
Lemma OrientationRs_RL :
  forall (a b : Ray)(diab : ![ a # b ])(diba : ![ b # a ]),
  %[ a # b | diab ] = false
    -> %[ b # a | diba ] = true.
Proof.
  intros * abL.
  rewrite (DiOsRs b a diba diab).
  rewrite abL; simpl; reflexivity.
Qed.

Lemma EqOs_EqOpOs :
  forall (a b c d : Ray)(diab : ![ a # b ])(dicd : ![ c # d ]),
  %[ a # b | diab ] = %[ c # d | dicd ]
    -> %[ b # a | nColRs_sym a b diab ] = %[ d # c | nColRs_sym c d dicd ].
Proof.
  intros a b c d diab dicd ab_cd.
  assert (abba : %[ b # a | nColRs_sym a b diab ] = negb (%[ a # b | diab ])).
  { apply (DiOsRs b a). }
  assert (cddc : %[ d # c | nColRs_sym c d dicd ] = negb (%[ c # d | dicd ])).
  { apply (DiOsRs d c). }
  rewrite abba. rewrite cddc. rewrite ab_cd; reflexivity.
Qed.

Lemma OpTsPs :
  forall (A B C : Point)(nColABC : ~ [A, B, C])(nColCBA : ~ [C, B, A]),
  %[ C # B # A | nColCBA ] = negb (%[ A # B # C | nColABC ]).
Proof.
  intros A B C nColABC nColCBA.
  unfold ClockwiseTriangle; simpl.
  destruct (nColPs_3DiPs A B C nColABC) as [ nBeqA [ nBeqC _ ]].
  destruct (nColPs_3DiPs C B A nColCBA) as [ H1 [ H2 _ ]].
  pir H2 => nBeqA. pir H1 => nBeqC.
  cut (%[ {{B # C | nBeqC}} # {{B # A | nBeqA}} | conj eq_refl nColCBA ]
  = negb (%[ {{B # A | nBeqA}} # {{B # C | nBeqC}} | conj eq_refl nColABC ])).
  { unfold ConvexFlag; simpl; auto. }
  { apply DiOsRs. }
Qed.

(** Theorem #34 *)
Theorem OpRs_EqOs_Left :
  forall (a b c : Ray)(diab : ![ a # b ])(dibc : ![ b # c ]),
  a == !c
    -> %[ a # b | diab ] = %[ b # c | dibc ].
Proof with eauto.
  intros * aopc.
  apply EqFlagsOrientations...
  unfold EqFlagsOrientation, ConvexFlag, EqFlagsTranslation; simpl.
  exists ({{a # b | diab}}), ({{a # b | diab}}).
  unfold EqFlagsRotation; simpl.
  split.
  { left; split; try reflexivity.
    apply SameSideRs_refl...
  }
  { do 2 try split; try reflexivity.
    { apply SameSideRs_refl... }
    { do 3 right; split.
      { apply SameSideRs_refl... }
      { apply OppositeSideRs_sym.
        apply (OppositeSideRs_inv c b (!c) c b a);
        try reflexivity.
        rewrite aopc; reflexivity.
        apply (OpRs_OppositeSideRs c b).
        apply nColRs_sym...
      }
    }
  }
Qed.
Lemma OpRs_EqOs_Right :
  forall (a b c : Ray)(diab : ![ a # b ])(dica : ![ c # a ]),
  b == !c
    -> %[ a # b | diab ] = %[ c # a | dica ].
Proof with eauto.
  intros * bopc.
  symmetry.
  apply (OpRs_EqOs_Left c a b dica).
  rewrite bopc. apply OpOpRs.
Qed.

(** Theorem #35 *)
Theorem SameSideRs_EqOs :
  forall (a b c : Ray)(diab : ![ a # b ])(diac : ![ a # c ]),
  ![ a # b, c ]
    <-> %[ a # b | diab ] = %[ a # c | diac ].
Proof.
  intros a b c diab diac.
  assert (roab : da a = da b). firstorder.
  assert (roac : da a = da c). firstorder.
  split.
  { intros aSFbc.
    apply EqFlagsOrientations.
    unfold EqFlagsOrientation.
    exists ({{a # b | diab}}), ({{a # b | diab}}).
    do 2 try split; try reflexivity.
    unfold EqFlagsRotation; simpl.
    left; split; try reflexivity.
    apply SameSideRs_sym; auto.
  }
  { intros beqc.
    apply EqFlagsOrientations in beqc.
    apply EqFlagsOrientation_EqFlagsTranslation in beqc; simpl;
    try reflexivity.
    unfold EqFlagsTranslation in *; simpl in *.
    destruct beqc as [ _ SSxBC ].
    split; auto.
  }
Qed.
Lemma SH_SameOrientation :
  forall (A B C D : Point)(nColABC : ~ [ A, B, C ])(nColABD : ~ [ A, B, D ]),
  [ A # B | C, D ]
    <-> %[ A # B # C | nColABC ] = %[ A # B # D | nColABD ].
Proof with eauto.
  intros *.
  destruct (nColPs_3DiPs A B C nColABC) as [ nBeqA [ nBeqC nAeqC ]].
  destruct (nColPs_3DiPs A B D nColABD) as [ nBeqA' [ nBeqD nAeqD ]].
  pir nBeqA' => nBeqA.
  erewrite <- (OsRs_OsPs' A B C nBeqA nBeqC)...
  erewrite <- (OsRs_OsPs' A B D nBeqA nBeqD)...
  rewrite <- SameSideRs_EqOs. unfold SameSideRays; simpl.
  split.
  { intros ABsfCD.
    apply SHa_sym in ABsfCD; do 2 split...
    Unshelve.
    { split; simpl... }
    { split; simpl... }
  }
  { intros [ _ [ _ ABCD ]].
    apply SHa_sym...
  }
Qed.

Lemma OppositeSideRs_DiOs :
  forall (a b c : Ray)(diab : ![ a # b ])(diac : ![ a # c ]),
  ![ a # c, !b ]
    <-> %[ a # c | diac ] = negb (%[ a # b | diab ]).
Proof with eauto.
  intros a b c diab diac.
  assert (roab : da a = da b). firstorder.
  assert (roac : da a = da c). firstorder.
  split.
  { intros aOFbc.
    eapply SameSideRs_EqOs in aOFbc.
    rewrite aOFbc. erewrite <- DiOsRs.
    erewrite OpRs_EqOs_Right; reflexivity.
  }
  { intros nbeqc.
    destruct (DecideRaysSide a b c) as [ H1 | H2 ]...
    apply -> (SameSideRs_EqOs a b c diab diac) in H1.
    rewrite nbeqc in H1.
    induction(%[ a # b | diab]); simpl in *; try discriminate.
    Unshelve. apply nColOpRs_2... apply nColRs_sym...
  }
Qed.

Lemma nColPs_nColRs :
  forall (O A B : Point)(nOeqA : O <> A)(nOeqB : O <> B),
  ~ [ A, O, B ]
    <-> ![ {{ O # A | nOeqA }} # {{ O # B | nOeqB }} ].
Proof with eauto.
  intros O A B nAeqO nBeqO.
  unfold nColRs; simpl; split; intros H; try split...
  destruct H...
Qed.

Lemma OH_DiOrientation :
  forall (A B C D : Point)(nColABC : ~ [ A, B, C ])(nColABD : ~ [ A, B, D ]),
  [ C | A # B | D ]
    <-> %[ A # B # C | nColABC ] = negb (%[ A # B # D | nColABD ]).
Proof with eauto.
  intros *.
  destruct (nColPs_3DiPs A B C nColABC) as [ nBeqA [ nBeqC nAeqC ]].
  destruct (nColPs_3DiPs A B D nColABD) as [ nBeqA' [ nBeqD nAeqD ]].
  pir nBeqA' => nBeqA.
  erewrite <- (OsRs_OsPs' A B C nBeqA nBeqC)...
  erewrite <- (OsRs_OsPs' A B D nBeqA nBeqD)...
  rewrite <- OppositeSideRs_DiOs.
  split.
  { intros ABofCD.
    apply OppositeSide_OpRs_SameSideRs; simpl.
    apply OHa_sym in ABofCD. split...
    Unshelve.
    { split; simpl... }
    { apply OHa_sym; apply OHb_sym... }
    { apply nColPs_nColRs... }
    { apply nColPs_nColRs... }
  }
  { intros H.
    apply SameSideRs_OpRs_OppositeSide in H; simpl in *.
    apply OHa_sym; apply OHb_sym; auto.
  }
Qed.

Lemma BetRs_EqOs :
  forall (a b c : Ray)(diab : ![ a # b ])
         (dibc : ![ b # c ])(diac : ![ a # c ]),
  ![ a # b # c ]
    <-> (%[ a # b | diab ] = %[ a # c | diac ])
     /\ (%[ b # c | dibc ] = %[ a # c | diac ]).
Proof with eauto.
  intros a b c diab dibc diac.
  split.
  { intros BetRabc.
    destruct (BetRs_SameSideRs a b c) as [[ aSFbc cSFba ] _ ]; auto.
    split.
    { eapply SameSideRs_EqOs... }
    { assert ((% {{c # b | nColRs_sym b c dibc }})
        = (% {{c # a | nColRs_sym a c diac }})).
      { eapply SameSideRs_EqOs... }
      eapply (EqOs_EqOpOs c b c a) in H.
      pir (nColRs_sym c b (nColRs_sym b c dibc)) => dibc.
      pir (nColRs_sym c a (nColRs_sym a c diac)) => diac.
    }
  }
  { intros [ abeqac bceqac ].
    apply BetRs_SameSideRs...
    split.
    { eapply SameSideRs_EqOs... }
    { apply <- SameSideRs_EqOs. apply EqOs_EqOpOs. apply bceqac. }
  }
Qed.

Lemma DiOrientation :
  forall (A B C : Point)(nColABC : ~ [A, B, C])(nColBAC : ~ [B, A, C]),
  %[ A # B # C | nColABC ] = negb (%[ B # A # C | nColBAC ]).
Proof with eauto.
  intros *.
  destruct (nColPs_3DiPs A B C nColABC) as [ nBeqA [ nBeqC nAeqC ]].
  assert (nAeqB : A <> B)...
  assert (nColCAB : ~ [ C, A, B ]); ncolperps.
  erewrite <- (OsRs_OsPs' A B C nBeqA nBeqC)...
  erewrite <- (OsRs_OsPs' B A C nAeqB nAeqC)...
  erewrite <- DiOsRs.
  rewrite EqFlagsOrientations.
  edestruct (DrawOppositePoint B A) as [ D [ BetABD _ ]]...
  destruct (BetPs_3DiPs A B D BetABD) as [ _ [ nBeqD nAeqD ]].
  assert (nDeqB : D <> B); dips.
  assert (nColCBD : ~ [ C, B, D ]).
  { contradict nColCAB.
    destruct nColCAB as [ x [ H1 [ H2 H3 ]]].
    exists x; repeat split... incpt 2.
  }
  assert (nColDBC : ~ [ D, B, C ]); ncolperps.
  eassert (H : {{ {{ B # A | nBeqA }} # {{ B # C | nBeqC }} | _ }}
          ~~~ {{ {{ B # C | nBeqC }} # {{ B # D | nBeqD }} | _ }}).
  { apply EqFlagsOrientations.
    apply OpRs_EqOs_Left. apply OpRs_OpRs.
    unfold OpRays; simpl; split; auto.
  }
  eassert (H1 : {{ {{ B # D | nBeqD }} # {{ B # C | nBeqC }} | _ }}
            ~~~ {{ {{ A # B | nAeqB }} # {{ A # C | nAeqC }} | _ }} ).
  { unfold EqFlagsOrientation.
    exists ({{ {{ B # D | nBeqD }}
             # {{ B # C | nBeqC }} | conj eq_refl nColDBC }});
    exists ({{ {{ A # B | nAeqB }}
             # {{ A # C | nAeqC }} | conj eq_refl nColBAC}});
    do 2 try split; try reflexivity.
    split; simpl.
    { right; right; simpl. split... apply SR_refl... }
    { apply SH_refl... }
  }
  rewrite H. eapply FlipFlag_compat in H1.
  unfold FlipFlag in *; simpl in *...
  Unshelve.
    apply nColPs_nColRs; ncolperps.
    apply nColPs_nColRs; ncolperps.
Qed.

Lemma OrientationAroundTriangle :
  forall (A B C : Point)(nColABC : ~ [A, B, C])(nColCAB : ~ [C, A, B]),
  %[ A # B # C | nColABC ] = %[ C # A # B | nColCAB ].
Proof with eauto.
  intros *.
  destruct (nColPs_3DiPs A B C nColABC) as [ nBeqA [ nBeqC nAeqC ]].
  assert (nColBAC : ~ [ B, A, C ]); ncolperps.
  assert (nAeqB : A <> B)...
  assert (H : %[ C # A # B | nColCAB] = negb (%[ B # A # C | nColBAC])).
  { apply OpTsPs. }
  assert (H1 : %[ A # B # C | nColABC] = negb (%[ B # A # C | nColBAC])).
  { eapply DiOrientation. }
  induction (%[ C # A # B | nColCAB]),
    (%[ B # A # C | nColBAC]),
    (%[ A # B # C | nColABC])...
Qed.

Lemma Orientation_asym :
  forall (A B C : Point)(nColABC : ~ [A, B, C])(nColACB : ~ [A, C, B]),
  %[ A # B # C | nColABC ] = negb (%[ A # C # B | nColACB ]).
Proof with eauto.
  intros *.
  assert (nColCAB : ~ [ C, A, B ]); ncolperps.
  erewrite (OrientationAroundTriangle A B C nColABC nColCAB)...
  eapply (DiOrientation C A B)...
Qed.

Lemma Orientation_inv :
  forall (O A B A' B' : Point)(nColAOB : ~ [ A, O, B ])
         (nColA'OB' : ~ [ A', O, B' ]),
  [ O # A, A' ]
    -> [ O # B, B' ]
    -> %[ A # O # B | nColAOB ] = %[ A' # O # B' | nColA'OB' ].
Proof with eauto.
  intros * OsrAA' OsrBB'.
  destruct (nColPs_3DiPs A O B nColAOB)
    as [ nOeqA [ nOeqB nAeqB ]].
  destruct (nColPs_3DiPs A' O B' nColA'OB')
    as [ nOeqA' [ nOeqB' nA'eqB' ]].
  erewrite <- (OsRs_OsPs' A O B nOeqA nOeqB)...
  erewrite <- (OsRs_OsPs' A' O B' nOeqA' nOeqB')...
  apply EqFlagsOrientations. unfold EqFlagsOrientation.
  exists ({{ {{ O # A | nOeqA }}
           # {{ O # B | nOeqB }} | conj eq_refl nColAOB }}).
  exists ({{ {{ O # A' | nOeqA' }}
           # {{O # B' | nOeqB'}} | conj eq_refl nColA'OB' }}).
  split; try reflexivity.
  split; try reflexivity.
  split; simpl.
  { left; split... }
  { apply SR_SH; ncolperps... }
Qed.

Example DrawPointOnGivenSide :
  forall (A B : Point)(T : bool),
  A <> B
    -> { C : Point | exists nCol : ~ [ A, B, C ], %[ A # B # C | nCol ] = T }.
Proof with eauto.
  intros * nAeqB.
  destruct (DrawExtensionLinePP A B nAeqB) as [ x [ Aox Box ]].
  destruct (DrawPointApartLine x) as [ C nCox ].
  assert (nCeqA : C <> A); dips.
  assert (nColABC : ~ [ A, B, C ]); ncolps.
  destruct (DrawSegmentExtension C A nCeqA) as [ D BetCAD ].
  assert (nColABD : ~ [ A, B, D ]). contradict nColABC.
  { destruct nColABC as [ t [ H1 [ H2 H3 ]]].
    exists t; repeat split... incpt 2.
  }
  destruct (DecideOrientations (%[ A # B # C | nColABC ]) T)
    as [ ABCeqT | nABCeqT ].
  { exists C, nColABC... }
  { exists D, nColABD...
    assert (ABsfDC : [D | A # B | C]).
    { repeat split...
      exists x; repeat split...
      { contradict nColABD. exists x; split... }
      { exists A; split... apply BetPs_sym... }
    }
    destruct
      (OH_DiOrientation A B D C nColABD nColABC)
      as [ H1 _ ]. apply H1 in ABsfDC. clear H1.
    induction (%[A # B # D | nColABD]), (%[A # B # C | nColABC]), T...
  }
Defined.

Lemma BR_EqOs :
  forall (O A B C : Point)(nColOAB : ~ [O, A, B])
         (nColOAC : ~ [O, A, C])(nColOBC : ~ [O, B, C]),
  [ O | A; B; C ]
  <-> %[ O # A # B | nColOAB ] = %[ O # A # C | nColOAC ]
   /\ %[ O # B # C | nColOBC ] = %[ O # A # C | nColOAC ].
Proof with eauto.
  intros O A B C nColOAB nColOAC nColOBC.
  split.
  { intros [ OA_BC OC_BA ].
    split.
    { apply SH_SameOrientation... }
    { apply SHa_sym in OC_BA.
      erewrite (OrientationAroundTriangle O B C nColOBC)...
      erewrite (OrientationAroundTriangle O A C nColOAC)...
      apply SH_SameOrientation...
    }
  }
  { intros [ OABoOAC OBCoOAC ].
    split.
    { apply SH_SameOrientation in OABoOAC... }
    { assert (nColOCA : ~ [O, C, A]); ncolperps.
      assert (nColOCB : ~ [O, C, B]); ncolperps.
      eapply (SH_SameOrientation O C B A nColOCB nColOCA).
      assert (H1 : %[ O # B # C | nColOBC] = negb (%[ O # C # B | nColOCB])).
      { apply (Orientation_asym O B C nColOBC nColOCB). }
      assert (H2 : %[ O # A # C | nColOAC] = negb (%[ O # C # A | nColOCA ])).
      { apply (Orientation_asym O A C nColOAC nColOCA). }
      induction (%[O # A # C | nColOAC]);
      induction (%[O # B # C | nColOBC]);
      induction (%[O # C # A | nColOCA]);
      induction (%[O # C # B | nColOCB]);
      try contradiction...
    }
  }
  Unshelve. ncolps. ncolperps.
Qed.

End ORIENTATION.

Notation " %[ a # b | ab ] "
  := (ConvexFlag ({{ a # b | ab }}))
  (at level 60).
Notation " %[ A # O # B | AOB ] "
  := (ClockwiseTriangle ({{ A # O # B | AOB }}))
  (at level 60).

(*****************************************************************************)
(* 11 *) Section ANGLE.
Context `{ cr : Circles }.
Context  { an : Angles on }.
(*****************************************************************************)

Definition NullAng :
  { A0 : Angle | forall (a : Ray), [| a, a | eq_refl |] = A0 }.
Proof.
  destruct DrawPoint as [ O _ ].
  destruct (DrawDistinctPoint O) as [ A nOeqA ].
  exists ([| {{ O # A | nOeqA }}, {{ O # A | nOeqA }} | eq_refl |]).
  intros [ O' A' nO'eqA' ]; simpl.
  eapply EqRs_EqRs_EqAs; reflexivity.
Defined.
Definition A0
  := proj1_sig NullAng.
Definition EqAs_A0
  := proj2_sig NullAng.

Definition StraightAng :
  { A180 : Angle | forall (a : Ray), [| a, !a | OpRays_0 a |] = A180 }.
Proof.
  destruct DrawPoint as [ O _ ].
  destruct (DrawDistinctPoint O) as [ A H ].
  exists ([| {{ O # A | H }},!({{ O # A | H }}) | OpRays_0 ({{O # A|H}}) |]).
  intros [ O' A' H' ].
  apply OpRs_OpRs_EqAs; apply OpRs_OpRs; apply OpOpRs.
Defined.
Definition A180
  := proj1_sig StraightAng.
Definition EqAs_A180
  := proj2_sig StraightAng.

Lemma EqAs_EqRs_EqRs : forall (a b c d : Ray)
  (orab : da a = da b)(orcd : da c = da d),
  a == b
    -> ([| a , b | orab |] = [| c , d | orcd |] <-> c == d).
Proof with eauto.
  intros * aeqb.
  split; intros H...
  { erewrite (EqRs_EqRs_EqAs a b c c orab eq_refl) in H...
    apply -> (EqAs_EqRs c c d). apply H. reflexivity.
  }
  { eapply (EqRs_EqRs_EqAs a b c d)... }
Qed.

Lemma EqAs_OpRs_OpRs : forall (a b c d : Ray)
  (orab : da a = da b)(orcd : da c = da d),
  a <==> b
    -> ([| a, b | orab |] = [| c, d | orcd |] <-> c <==> d).
Proof with eauto.
  intros * aopb.
  split; intros H...
  { destruct (DrawOpRay c) as [ e cope ].
    assert (orce : da c = da e). { destruct cope... }
    rewrite (OpRs_OpRs_EqAs a b c e orab orce) in H...
    assert (eeqd : e == d). { apply -> (EqAs_EqRs c e d)... }
    apply OpRs_OpRs in cope. apply OpRs_OpRs. rewrite <- eeqd...
  }
  { eapply (OpRs_OpRs_EqAs a b c d)... }
Qed.

Lemma EqNullAng :
  forall (a b : Ray)(roab : da a = da b),
  a == b
    <-> [| a, b | roab |] = A0.
Proof with eauto.
  intros a b roab.
  assert (EqA0 : [| a, a | eq_refl |] = A0).
  { apply ((proj2_sig NullAng) a). }
  rewrite <- EqA0.
  split.
  { intros aeqb.
    apply (EqAs_EqRs_EqRs a b a a roab eq_refl); try reflexivity...
  }
  { intros ab.
    eapply (EqAs_EqRs_EqRs a a a b eq_refl roab); try reflexivity...
  }
Qed.

Lemma EqStraightAng :
  forall (a b : Ray)(roab : da a = da b),
  a <==> b
    <-> [| a, b | roab |] = A180.
Proof.
  intros a b roab.
  assert (EqA180 : [| a , !a | OpRays_0 a |] = A180).
  { apply ((proj2_sig StraightAng) a). }
  rewrite <- EqA180.
  split.
  { intros aopb.
    eapply (EqAs_OpRs_OpRs a b a (!a)); eauto.
    apply OpRs_OpRs; apply OpRs_sym; reflexivity.
  }
  { intros ab_aa.
    eapply (EqAs_OpRs_OpRs a (!a) a b); eauto.
    apply OpRs_OpRs; apply OpRs_sym; reflexivity.
  }
Qed.

Lemma nA0eqA180 :
  A0 <> A180.
Proof with eauto.
  intros A0eqA180.
  assert (ExB : { B : Angle | B = A0 }). { exists A0... }
  destruct ExB as [ B BeqA0 ].
  rewrite <- BeqA0 in A0eqA180.
  apply eq_sym in A0eqA180.
  destruct (DrawSector B) as [[ a b roab ] abeqB ]. destruct abeqB.
  apply (EqNullAng a b roab) in BeqA0. symmetry in A0eqA180.
  apply (EqStraightAng a b roab) in A0eqA180.
  apply OpRs_OpRs in A0eqA180. rewrite BeqA0 in A0eqA180.
  apply (OpRs_irrefl b); auto.
Qed.

Lemma EqConvexAngRsPs :
  forall (A O B : Point)(nOeqA : O <> A)(nOeqB : O <> B)
         (nColAOB : ~ [ A, O, B ]),
  [| {{ O # A | nOeqA }} # {{ O # B | nOeqB }} | conj eq_refl nColAOB |]
    = [| A # O # B | nColAOB |].
Proof.
  intros *. unfold ConvexAnglePs.
  destruct (nColPs_DiPs A O B nColAOB) as [ nOeqA' [ nOeqB' _ ]].
  pir nOeqA' => nOeqA. pir nOeqB' => nOeqB.
Qed.

(** Theorem #36 *)
Theorem ConvexAngRs_sym :
  forall (a b : Ray)(diab : ![ a # b ])(diba : ![ b # a ]),
  [| a # b | diab |] = [| b # a | diba |].
Proof with eauto.
  intros a b diab diba. unfold ConvexAngleRs.
  assert (H : %[ a # b | diab] = negb (%[ b # a | diba])).
  { apply (DiOsRs a b diab diba). }
  induction (%[a # b | diab]), (%[b # a | diba]);
  simpl in *; try discriminate.
  { pir (eq_sym (proj1 diba)) => (proj1 diab). }
  { pir (eq_sym (proj1 diab)) => (proj1 diba). }
Qed.
Lemma ConvexAngPs_sym :
  forall (A B C : Point)(nColABC : ~ [ A, B, C ])(nColCBA : ~ [ C, B, A ]),
  [| A # B # C | nColABC |] = [| C # B # A | nColCBA |].
Proof.
  intros *.
  unfold ConvexAnglePs.
  destruct (nColPs_DiPs A B C nColABC) as [ nBeqA [ nBeqC nAeqC ]].
  destruct (nColPs_DiPs C B A nColCBA) as [ nBeqC' [ nBeqA' nCeqA ]].
  pir nBeqC' => nBeqC. pir nBeqA' => nBeqA.
  apply (ConvexAngRs_sym ({{ B # A | nBeqA }})({{ B # C | nBeqC }})).
Qed.

Lemma EqAngRs_EqRs_cw :
  forall (a b c : Ray)(roba : da b = da a)(roca : da c = da a),
  [| b, a | roba |] = [| c, a | roca |]
    <-> b == c.
Proof.
  intros a b c roba roca.
  split.
  { intro obaeqca.
    apply EqAs_EqExpAs in obaeqca; auto.
    eapply EqAs_EqRs; eauto.
  }
  { intros beqc.
    pir roba => (eq_sym (eq_sym roba)).
    pir roca => (eq_sym (eq_sym roca)).
    apply (EqAs_EqExpAs a b a c (eq_sym roba)(eq_sym roca)).
    apply (EqAs_EqRs a b c (eq_sym roba)(eq_sym roca)); auto.
  }
Qed.

Lemma EqAngRs_inv :
  forall (a b a' b' : Ray)(roab : da a = da b)(roa'b' : da a' = da b'),
  a == a'
    -> b == b'
    -> [| a, b | roab |] = [| a', b' | roa'b' |].
Proof with eauto.
  intros a b a' b' roab roa'b' aeqa' beqb'.
  assert (roab' : da a = da b').
  { rewrite roab. destruct beqb' as [ H1 _ ]... }
  assert (abeqab' : [| a, b' | roab' |] = [| a', b' | roa'b' |]).
  { pir roab' => (eq_sym (eq_sym roab')).
    pir roa'b' => (eq_sym (eq_sym roa'b')).
    apply (EqAs_EqExpAs b' a b' a' (eq_sym roab')(eq_sym roa'b')).
    apply (EqAs_EqRs b' a a'); auto.
  }
  rewrite <- abeqab'.
  apply (EqAs_EqRs a b b'); auto.
Qed.

Lemma EqAngRs_nColRs_nColRs :
  forall (a b c d : Ray)(roab : da a = da b)(rocd : da c = da d),
  [| a, b | roab |] = [| c, d | rocd |]
    -> ![ a # b ]
    -> ![ c # d ].
Proof.
  intros a b c d roab rocd abeqcd diab.
  apply nColRs_nColPs in diab.
  destruct diab as [ _ [ naeqb naopb ]].
  apply nColRs_nColPs.
  split; auto; split.
  { contradict naeqb.
    eapply (EqAs_EqRs_EqRs c d a b); eauto.
  }
  { contradict naopb.
    apply OpRs_OpRs in naopb. apply OpRs_OpRs.
    eapply (EqAs_OpRs_OpRs c d a b); eauto.
  }
Defined.

Lemma nColRs_nColAs :
  forall (a b : Ray)(roab : da a = da b),
  [| a, b | roab |] <> A0 /\ [| a, b | roab |] <> A180
    <-> ![ a # b ].
Proof with eauto.
  intros a b roab.
  split.
  { intros [ nabeqA0 nabeqA180 ].
    repeat split; simpl...
    apply nColRs_nColPs; split; eauto; split.
    { contradict nabeqA0. apply EqNullAng... }
    { contradict nabeqA180. apply EqStraightAng. apply OpRs_OpRs... }
  }
  { intros diab.
    apply nColRs_nColPs in diab.
    destruct diab as [ _ [ naeqb naopb ]].
    split.
    { contradict naeqb. apply EqNullAng in naeqb... }
    { contradict naopb. apply EqStraightAng in naopb.
      apply OpRs_OpRs...
    }
  }
Qed.

Lemma EqTriangle_refl :
  reflexive Triangle EqTriangle.
Proof.
  unfold reflexive.
  intros; split; simpl; auto.
Qed.
Lemma EqTriangle_sym :
  symmetric Triangle EqTriangle.
Proof.
  unfold symmetric.
  intros [ A B C nColABC ][ A' B' C' nColA'B'C' ] H.
  destruct H as [ H1 [ H2 [ H3 [ H4 [ H5 H6 ]]]]].
  split; simpl in *; auto.
Qed.
Lemma EqTriangle_trans :
  transitive Triangle EqTriangle.
Proof.
  unfold transitive.
  intros [ A B C nColABC ]
    [ A' B' C' nColA'B'C' ]
    [ A'' B'' C'' nColA''B''C'' ] H G.
  destruct H as [ H1 [ H2 [ H3 [ H4 [ H5 H6 ]]]]].
  destruct G as [ G1 [ G2 [ G3 [ G4 [ G5 G6 ]]]]].
  unfold EqTriangle. destruct H1, H2, H3, H4, H5, H6.
  repeat split; simpl in *; auto.
Qed.
Global Instance Triangle_equiv :
  Equivalence EqTriangle
  := Build_Equivalence EqTriangle
     EqTriangle_refl
     EqTriangle_sym
     EqTriangle_trans.

Lemma EqPerTr_1 :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  ({{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }})
    -> {{ B # C # A | nColPerPs_1 A B C nColABC }}
   :=: {{ E # F # D | nColPerPs_1 D E F nColDEF }}.
Proof with eauto.
  intros A B C D E F nColABC nColDEF [ H1 [ H2 [ H3 [ H4 [ H5 H6 ]]]]];
  repeat split; simpl in *; eauto; erewrite ConvexAngPs_sym;
  erewrite ConvexAngPs_sym; symmetry; erewrite ConvexAngPs_sym;
  erewrite ConvexAngPs_sym; symmetry...
  Unshelve. ncolperps. ncolperps. ncolperps. ncolperps.
Qed.

Lemma EqPerTr_2 :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  ({{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }})
    -> {{ C # A # B | nColPerPs_2 A B C nColABC }}
  :=: {{ F # D # E | nColPerPs_2 D E F nColDEF }}.
Proof with eauto.
  intros A B C D E F nColABC nColDEF [ H1 [ H2 [ H3 [ H4 [ H5 H6 ]]]]];
  repeat split; simpl in *; eauto; erewrite ConvexAngPs_sym;
  erewrite ConvexAngPs_sym; symmetry; erewrite ConvexAngPs_sym;
  erewrite ConvexAngPs_sym; symmetry...
  Unshelve. ncolperps. ncolperps. ncolperps. ncolperps.
Qed.

Lemma EqPerTr_3 :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  ({{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }})
    -> {{ B # A # C | nColPerPs_3 A B C nColABC }}
   :=: {{ E # D # F | nColPerPs_3 D E F nColDEF }}.
Proof with eauto.
  intros A B C D E F nColABC nColDEF [ H1 [ H2 [ H3 [ H4 [ H5 H6 ]]]]];
  repeat split; simpl in *; try rewrite SegPs_sym; symmetry;
  try rewrite SegPs_sym; eauto; erewrite ConvexAngPs_sym; symmetry;
  erewrite ConvexAngPs_sym...
Qed.

Lemma EqPerTr_4 :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  ({{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }})
    -> {{ A # C # B | nColPerPs_4 A B C nColABC }}
   :=: {{ D # F # E | nColPerPs_4 D E F nColDEF }}.
Proof with eauto.
  intros A B C D E F nColABC nColDEF [ H1 [ H2 [ H3 [ H4 [ H5 H6 ]]]]];
  repeat split; simpl in *; try rewrite SegPs_sym; symmetry;
  try rewrite SegPs_sym; eauto; erewrite ConvexAngPs_sym; symmetry;
  erewrite ConvexAngPs_sym...
Qed.

Lemma EqPerTr_5 :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  ({{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }})
    -> {{ C # B # A | nColPerPs_5 A B C nColABC }}
   :=: {{ F # E # D | nColPerPs_5 D E F nColDEF }}.
Proof with eauto.
  intros A B C D E F nColABC nColDEF [ H1 [ H2 [ H3 [ H4 [ H5 H6 ]]]]];
  repeat split; simpl in *; try rewrite SegPs_sym; symmetry;
  try rewrite SegPs_sym; eauto; erewrite ConvexAngPs_sym; symmetry;
  erewrite ConvexAngPs_sym...
Qed.

Lemma AngPs_inv :
  forall (A O B A' B' : Point)(nOeqA : O <> A)(nOeqB : O <> B)
    (nOeqA' : O <> A')(nOeqB' : O <> B'),
  [ O # A, A' ]
    -> [ O # B, B' ]
    -> [| A , O , B | nOeqA, nOeqB |] = [| A' , O , B' | nOeqA', nOeqB' |].
Proof.
  intros A O B A' B' nAeqO nBeqO nA'eqO nB'eqO OseAA' OsrBB'.
  apply EqAngRs_inv; unfold EqRays; simpl; auto.
Qed.

Lemma nColPs_nColAs :
  forall (A O B : Point)(nOeqA : O <> A)(nOeqB : O <> B),
  ~ [ A, O, B ]
    <-> [| A , O , B | nOeqA, nOeqB |] <> A0
     /\ [| A , O , B | nOeqA, nOeqB |] <> A180.
Proof with eauto.
  intros A O B nOeqA nOeqB.
  split.
  { intros nColAOB.
    split.
    { contradict nColAOB.
      apply EqNullAng in nColAOB. unfold EqRays in nColAOB; simpl in *.
      destruct nColAOB as [ _ [ _ [ _ [ H _ ]]]]...
    }
    { contradict nColAOB.
      apply EqStraightAng in nColAOB. unfold OpRays in *; simpl in *.
      destruct nColAOB as [ _ H ]. colps.
    }
  }
  { intros [ nAeqA0 nAeqA180 ] ColAOB.
    destruct (classic (A = B)) as [ AeqB | nAeqB ].
    contradict nAeqA0. apply EqNullAng. subst.
    pir nOeqB => nOeqA. reflexivity.
    destruct (DecidePointsBetweenness O A B)
      as [ nBetAOB | BetAOB ]; colperps...
    assert (OsrAB : [O # A, B]).
    { repeat split...
      destruct nBetAOB as [ BetOAB | BetOBA ].
      apply BetPs_nBetPerPs... apply BetPs_nBetPerPs_2...
    }
    contradict nAeqA0. apply EqNullAng. unfold EqRays; split...
    contradict nAeqA180. apply EqStraightAng.
    unfold EqRays, OpRays.
    destruct (DrawOppositePoint O B) as [ B' [ BetBOB' _ ]]; simpl...
  }
Qed.

Lemma LeftOrientation_EqAs :
  forall (a b : Ray)(roab : da a = da b)(diab : ![ a # b ]),
  %[ a # b | diab ] = true
    <-> [| a, b | roab |] = [| a # b | diab |].
Proof with eauto.
  intros a b roab diab.
  split.
  { intros TabeqL; unfold ConvexAngleRs.
    symmetry in TabeqL.
    destruct TabeqL. pir (proj1 diab) => roab.
  }
  { intros baeqint; unfold ConvexAngleRs in *.
    induction (%[a # b | diab])...
    pir (eq_sym (proj1 diab)) => (eq_sym roab).
    assert (diba : ![ b # a ]). { apply nColRs_sym... }
    assert (nbaeqab : %[ a # b | diab] = negb (%[ b # a | diba ])).
    { apply (DiOsRs a b diab diba). }
    apply (EqAs_EqTs a b b a roab (sym_eq roab) diab diba) in baeqint.
    rewrite <- baeqint in nbaeqab.
    induction (%[a # b | diab])...
  }
Qed.
Lemma RightOrientation_EqAs :
  forall (a b : Ray)(roab : da a = da b)(diab : ![ a # b ]),
  %[ a # b | diab ] = false
    <-> [| b, a | eq_sym roab |] = [| a # b | diab |].
Proof with eauto.
  intros a b roab diab.
  split.
  { intros TabeqR; unfold ConvexAngleRs.
    symmetry in TabeqR.
    destruct TabeqR. pir (proj1 diab) => roab.
  }
  { intros baeqint; unfold ConvexAngleRs in *.
    induction (%[a # b | diab])...
    pir (proj1 diab) => roab.
    assert (diba : ![ b # a ]). { apply nColRs_sym... }
    assert (nbaeqab : %[ a # b | diab] = negb (%[ b # a | diba ])).
    { apply (DiOsRs a b diab diba). }
    apply (EqAs_EqTs b a a b (sym_eq roab) roab diba diab) in baeqint...
    rewrite baeqint in nbaeqab.
    induction (%[a # b | diab])...
  }
Qed.

Lemma EqConvexAs_EqOs_EqAs :
  forall (a b c d : Ray)(roab : da a = da b)(rocd : da c = da d)
    (diab : ![ a # b ])(dicd: ![ c # d ]),
  [| a # b | diab |] = [| c # d | dicd |]
    -> %[ a # b | diab ] = %[ c # d | dicd ]
    -> [| a, b | roab |] = [| c, d | rocd |].
Proof with eauto.
  intros a b c d roab rocd diab dicd iAeqB tAeqB.
  assert (ExT : exists T : bool, %[c # d | dicd] = T).
  { exists (%[c # d | dicd])... }
  destruct ExT as [ T cdeqT ].
  induction (T); rewrite cdeqT in tAeqB.
  { assert (ab : [| a, b | roab |] = [| a # b | diab |]).
  { apply (LeftOrientation_EqAs a b roab)... }
  rewrite ab...
  assert (cd : [| c, d | rocd |] = [| c # d | dicd |]).
  { apply (LeftOrientation_EqAs c d rocd)... }
    rewrite cd...
  }
  { assert (ba : [| b, a | eq_sym roab |] = [| a # b | diab |]).
    { apply (RightOrientation_EqAs a b roab)... }
    rewrite <- ba in iAeqB.
    assert (dc0 : [| d, c | eq_sym rocd |] = [| c # d | dicd |]).
    { apply (RightOrientation_EqAs c d rocd)... }
    rewrite <- dc0 in iAeqB...
    apply EqAs_EqExpAs in iAeqB.
    pir (eq_sym (eq_sym roab)) => roab.
    pir (eq_sym (eq_sym rocd)) => rocd.
  }
Qed.

Lemma EqAs_EqConvexAs :
  forall (a b c d : Ray)(roab : da a = da b)(rocd : da c = da d)
    (diab : ![ a # b ])(dicd: ![ c # d ]),
  [| a, b | roab |] = [| c, d | rocd |]
    -> [| a # b | diab |] = [| c # d | dicd |].
Proof with eauto.
  intros a b c d roab rocd diab dicd abeqcd.
  unfold ConvexAngleRs.
  pir (proj1 diab) => roab. pir (proj1 dicd) => rocd.
  assert (Tabeqcd : %[ a # b | diab ] = %[ c # d | dicd ]).
  { apply (EqAs_EqTs a b c d roab rocd)... }
  destruct Tabeqcd.
  induction (%[a # b | diab]); simpl...
  apply EqAs_EqExpAs...
Qed.

(** Theorem #37 *)
Theorem SameSideRs_EqConvexAs_EqRs :
  forall (a b c : Ray)(diab : ![ a # b ])(diac : ![ a # c ]),
  ![ a # b, c ]
    -> ([| a # b | diab |] = [| a # c | diac |] <-> b == c).
Proof with eauto.
  intros a b c diab diac aSRbc.
  assert (roab : da a = da b). { destruct diab... }
  assert (roac : da a = da c). { destruct diac... }
  split.
  { intros abeqac.
    apply -> (EqAs_EqRs a b c roab roac)...
    apply (EqConvexAs_EqOs_EqAs a b a c roab roac diab diac)...
    apply SameSideRs_EqOs...
  }
  { intros beqc.
    apply <- (EqAs_EqRs a b c roab roac) in beqc.
    apply (EqAs_EqConvexAs a b a c roab roac)...
  }
Qed.
Lemma SH_EqConvexAs_SR :
  forall (A O B B' : Point)(AOB : ~ [ A, O, B ])(AOB' : ~ [ A, O, B' ]),
  [ O # A | B, B' ]
     -> [| A # O # B | AOB |] = [| A # O # B' | AOB' |] <-> [ O # B, B' ].
Proof with eauto.
  intros A B C C' nColABC nColABC' ABsfCC'.
  destruct (nColPs_DiPs A B C nColABC) as [ nBeqA [ nBeqC nAeqC ]].
  destruct (nColPs_DiPs A B C' nColABC') as [ _ [ nBeqC' _ ]].
  split.
  { intros ABC_ABC'.
    rewrite <- (EqConvexAngRsPs A B C nBeqA nBeqC nColABC) in ABC_ABC'.
    rewrite <- (EqConvexAngRsPs A B C' nBeqA nBeqC' nColABC') in ABC_ABC'.
    assert (BCeqBC' : {{ B # C | nBeqC }} == {{ B # C' | nBeqC' }}).
    { eapply (SameSideRs_EqConvexAs_EqRs
        ({{ B # A | nBeqA }})({{ B # C | nBeqC }}))...
      unfold SameSideRays; simpl in *...
    }
    unfold EqRays in *; simpl in *.
    destruct BCeqBC' as [ _ BsfCC' ]...
  }
  { intros BsrCC'.
    rewrite <- (EqConvexAngRsPs A B C nBeqA nBeqC nColABC).
    rewrite <- (EqConvexAngRsPs A B C' nBeqA nBeqC' nColABC').
    assert (BCeqBC' : {{ B # C | nBeqC }} == {{ B # C' | nBeqC' }}).
    { split... }
    apply SameSideRs_EqConvexAs_EqRs...
    split; simpl...
  }
Qed.

(** Theorem #38 *)
Theorem EqAs_EqConvexAs_EqOs :
  forall (a b c d : Ray)(roab : da a = da b)(rocd : da c = da d)
    (diab : ![ a # b ])(dicd: ![ c # d ]),
  [| a, b | roab |] = [| c, d | rocd |]
    <-> [| a # b | diab |] = [| c # d | dicd |]
     /\ %[ a # b | diab ] = %[ c # d | dicd ].
Proof with eauto.
  intros a b c d roab rocd diab dicd.
  split.
  { intros abcd; split.
    { eapply EqAs_EqConvexAs... }
    { eapply EqAs_EqTs... }
  }
  { intros [ abAcd abOcd ]. eapply EqConvexAs_EqOs_EqAs... }
Qed.

Lemma EqAs_LeftOrientation :
  forall (a b c d : Ray)(roab : da a = da b)(dicd : ![ c # d ]),
  [| a, b | roab |] = [| c # d | dicd |]
    -> exists (diab : ![ a # b ]), %[ a # b | diab ] = true.
Proof with eauto.
  intros a b c d roab dicd abeqcd.
  assert (rocd : da c = da d). { destruct dicd... }
  unfold ConvexAngleRs in *.
  assert (ExTcd : { Tcd : bool | %[ c # d | dicd ] = Tcd }).
  { exists (%[ c # d | dicd ])... }
  destruct ExTcd as [ Tcd Teqcd ].
  assert (diab : ![ a # b ]).
  { induction (%[c # d | dicd]); simpl in *.
    apply (EqAngRs_nColRs_nColRs c d a b rocd roab)...
    pir (proj1 dicd ) => rocd.
    apply (EqAngRs_nColRs_nColRs d c a b (eq_sym rocd) roab)...
    pir (eq_sym (proj1 dicd)) => (eq_sym rocd).
    apply nColRs_sym...
  }
  exists diab.
  assert (didc : ![ d # c ]). { apply nColRs_sym... }
  rewrite Teqcd in *.
  induction (Tcd).
  { pir (proj1 dicd) => rocd.
    apply (EqAs_EqTs a b c d roab rocd diab dicd) in abeqcd.
    rewrite abeqcd.
    induction (%[d # c | didc])...
  }
  pir (proj1 dicd) => rocd.
  apply (EqAs_EqTs a b d c roab (eq_sym rocd) diab didc) in abeqcd.
  rewrite abeqcd...
  eapply OrientationRs_RL. apply Teqcd.
Qed.

Lemma EqConvexAs_inv :
  forall (a b a' b' : Ray)(diab : ![ a # b ])(dia'b' : ![ a' # b' ]),
  a == a'
    -> b == b'
    -> [| a # b | diab |] = [| a' # b' | dia'b' |].
Proof with eauto.
  intros a b a' b' diab dia'b' aeqa' beqb'.
  assert (diab' : ![ a # b' ]). { apply (nColRs_inv a b b')... }
  assert (abeqab' : [| a # b | diab|] = [| a # b' | diab'|]).
  { apply SameSideRs_EqConvexAs_EqRs...
    apply (SameSideRs_inv a b b a b b'); try reflexivity...
    apply SameSideRs_refl...
  }
  rewrite abeqab'.
  rewrite (ConvexAngRs_sym a b' diab' (nColRs_sym a b' diab')).
  symmetry. rewrite (ConvexAngRs_sym a' b' dia'b' (nColRs_sym a' b' dia'b')).
  symmetry in aeqa'.
  apply <- SameSideRs_EqConvexAs_EqRs...
  apply (SameSideRs_inv b' a a b' a' a); try reflexivity...
  symmetry... apply SameSideRs_refl... apply (nColRs_sym a b' diab').
Qed.

Lemma ConvexAngPs_inv :
  forall (A O B A' B' : Point)(nColAOB : ~ [ A, O, B ])
         (nColA'OB' : ~ [ A', O, B' ]),
  [ O # A, A' ]
    -> [ O # B, B' ]
    -> [| A # O # B | nColAOB |] = [| A' # O # B' | nColA'OB' |].
Proof with eauto.
  intros A O B A' B' nColAOB nColA'OB' OsrAA' OsrBB'.
  unfold ConvexAnglePs.
  destruct (nColPs_DiPs A O B nColAOB)
    as [ nAeqO [ nOeqB nAeqB ]].
  destruct (nColPs_DiPs A' O B' nColA'OB')
    as [ nA'eqO [ nOeqB' nA'eqB' ]].
  apply EqConvexAs_inv; split...
Qed.

Lemma EqConvexAs_EqOs_EqAs' :
  forall (A O B A' O' B' : Point)(nOeqA : O <> A)(nOeqB : O <> B)
    (nO'eqA' : O' <> A')(nO'eqB' : O' <> B')
    (nColAOB : ~ [ A, O, B ])(nColA'O'B' : ~ [ A', O', B' ]),
  [| A # O # B | nColAOB |] = [| A' # O' # B' | nColA'O'B' |]
    -> %[ A # O # B | nColAOB ] = %[ A' # O' # B' | nColA'O'B' ]
    -> [| A , O , B | nOeqA, nOeqB |] = [| A' , O' , B' | nO'eqA', nO'eqB' |].
Proof with eauto.
  intros * AOBiaA'O'B' AOBtnA'O'B'.
  eapply (EqConvexAs_EqOs_EqAs
     ({{ O # A | nOeqA }})({{ O # B | nOeqB }})
     ({{ O' # A' | nO'eqA' }})({{ O' # B' | nO'eqB' }}))...
  { rewrite (EqConvexAngRsPs A O B nOeqA nOeqB nColAOB)...
    rewrite (EqConvexAngRsPs A' O' B' nO'eqA' nO'eqB' nColA'O'B')...
  }
  { rewrite (OsRs_OsPs' A O B nOeqA nOeqB nColAOB)...
    rewrite (OsRs_OsPs' A' O' B' nO'eqA' nO'eqB' nColA'O'B')...
  }
Qed.

Definition ConvexAs (A : Angle)(nColA : A <> A0 /\ A <> A180) : Angle.
Proof with eauto.
  destruct (DrawSector A) as [[ a b roab ] abeqA ].
  destruct abeqA.
  apply (nColRs_nColAs a b roab) in nColA.
  apply ([| a # b | nColA |]).
Defined.
Notation " [| A | nColA |] "
  := (ConvexAs A nColA)
  (at level 60).

Definition DrawAngleOrientation : forall A : Angle,
  (A <> A0) /\ (A <> A180) -> bool.
Proof with eauto.
  intros A [ nAeqA0 nAeqA180 ].
  destruct (DrawSector A) as [[ a b roab ] H ].
  assert (diab : ![ a # b ]).
  { rewrite <- H in *.
    apply -> (nColRs_nColAs a b roab).
    split...
  }
  apply (%[ a # b | diab ]).
Defined.
Notation " %[ A | nColA ] "
  := (DrawAngleOrientation A nColA)
  (at level 60).

Definition Convex (A : Angle) : Prop
  := exists (nColA : A <> A0 /\ A <> A180), %[ A | nColA ] = true.
Definition Reflex (A : Angle) : Prop
  := exists (nColA : A <> A0 /\ A <> A180), %[ A | nColA ] = false.

Definition DecideConvexReflexAs : forall (A : Angle),
  A <> A0
    -> A <> A180
    -> { Convex A } + { Reflex A }.
Proof with eauto.
  intros A nAeqA0 nAeqA180; unfold Convex, Reflex in *.
  eassert (ExTA : { TA | %[ A | _ ] = TA }).
  { eexists (%[ A | _ ])... }
  destruct ExTA as [ Tac Teqac ].
  induction (Tac)...
  Unshelve. split...
Defined.

Lemma AngleClassification : forall (A : Angle),
  A = A0 \/ A = A180 \/ Convex A \/ Reflex A.
Proof with eauto.
  intros A.
  destruct (classic (A = A0)) as [ AeqA0 | nAeqA0 ]...
  destruct (classic (A = A180)) as [ AeqA180 | nAeqA180 ]...
  do 2 right.
  destruct (DecideConvexReflexAs A) as [ oxA | rxA ]...
Qed.

Lemma OsRs_OsAs :
  forall (a b : Ray)(roab : da a = da b)(diab : ![ a # b ])
         (nColA : [| a, b | roab |] <> A0 /\ [| a, b | roab |] <> A180),
  %[a # b | diab] = %[[| a, b | roab |]| nColA ].
Proof with eauto.
  intros a b roab diab nColA.
  unfold DrawAngleOrientation.
  destruct nColA as [ nAeqA0 nAeqA180 ].
  destruct (DrawSector ([| a, b | roab |])) as [[ a' b' roa'b' ] H ].
  destruct (nColRs_nColAs a' b' roa'b') as [ H5 _ ].
  assert (dia'b' : ![ a' # b' ]). { apply H5. split; rewrite H... }
  pir (H5 (conj (eq_ind_r (fun A : Angle => A <> A0) nAeqA0 H)
    (eq_ind_r (fun A : Angle => A <> A180) nAeqA180 H))) => dia'b'.
  apply (EqAs_EqTs a b a' b' roab roa'b' diab dia'b')...
Qed.

Lemma OsPs_OsAs :
  forall (A O B : Point)(nOeqA : O <> A)
         (nOeqB : O <> B)(nColAOB : ~ [ A, O, B ])
         (nA0 : [| A , O , B | nOeqA, nOeqB |] <> A0)
         (nA180 : [| A , O , B | nOeqA, nOeqB |] <> A180),
  %[ A # O # B | nColAOB ]
    = %[[| A , O , B | nOeqA, nOeqB |]| conj nA0 nA180 ].
Proof with eauto.
  intros *.
  destruct (OsPs_OsRs A O B nColAOB) as [ nAeqO' H ].
  pir nAeqO' => nOeqA.
  destruct H as [ nBeqO' H ].
  pir nBeqO' => nOeqB.
  destruct H as [ diab EqTn ].
  rewrite EqTn. clear EqTn.
  apply (OsRs_OsAs ({{ O # A | nOeqA }})({{ O # B | nOeqB }}))...
Qed.

Lemma ConvexAng_nAs : forall (A : Angle),
  Convex A <-> (A <> A0) /\ (A <> A180) /\ (~ Reflex A).
Proof with eauto.
  intros A.
  split.
  { intros iA; unfold Convex in *.
    destruct iA as [[ nAeqA0 nAeqA180 ] AeqL ]; repeat split...
    intros xA.
    destruct xA as [[ nAeqA0' nAeqA180' ] AeqR ]; repeat split...
    pir (conj nAeqA0' nAeqA180') => (conj nAeqA0 nAeqA180).
    rewrite AeqL in *. discriminate AeqR.
  }
  { intros [ nAeqA0 [ nAeqA180 nxA ]].
    exists (conj nAeqA0 nAeqA180).
    assert (ExTn : exists T, %[A | conj nAeqA0 nAeqA180] = T).
    { exists (%[A | conj nAeqA0 nAeqA180])... }
    destruct ExTn as [ T AeqT ].
    induction T...
    contradict nxA. unfold Reflex.
    exists (conj nAeqA0 nAeqA180)...
  }
Qed.
Lemma ReflexAng_nAs : forall (A : Angle),
  Reflex A <-> (A <> A0) /\ (A <> A180) /\ (~ Convex A).
Proof with eauto.
  intros A.
  split.
  { intros iA; unfold Convex in *.
    destruct iA as [[ nAeqA0 nAeqA180 ] AeqL ]; repeat split...
    intros xA.
    destruct xA as [[ nAeqA0' nAeqA180' ] AeqR ]; repeat split...
    pir (conj nAeqA0' nAeqA180') => (conj nAeqA0 nAeqA180).
    rewrite AeqL in *. discriminate AeqR.
  }
  { intros [ nAeqA0 [ nAeqA180 niA ]].
    exists (conj nAeqA0 nAeqA180).
    assert (ExTn : exists T, %[A | conj nAeqA0 nAeqA180] = T).
    { exists (%[A | conj nAeqA0 nAeqA180])... }
    destruct ExTn as [ T AeqT ].
    induction T...
    contradict niA. unfold Convex.
    exists (conj nAeqA0 nAeqA180)...
  }
Qed.

Lemma ConvexAngRs_nColRs :
  forall (a b : Ray)(roab : da a = da b),
  Convex ([| a, b | roab |])
    -> ![ a # b ].
Proof with eauto.
  intros a b roab iab.
  apply -> (nColRs_nColAs a b roab)...
  destruct (ConvexAng_nAs ([| a, b | roab |])) as [ H1 _ ].
  destruct (H1 iab) as [ nabeqA0 [ nabeqA180 _ ]].
  split...
Qed.

Lemma ConvexAngRs_Left :
  forall (a b : Ray)(roab : da a = da b)(diab : ![ a # b ]),
  Convex ([| a, b | roab |]) <-> %[ a # b | diab ] = true.
Proof with eauto.
  intros a b roab diab.
  split.
  { destruct (nColRs_nColAs a b roab) as [ _ H1 ]; simpl in H1...
    destruct (H1 diab) as [ nAeqA0 nAeqA180 ].
    intros iab; unfold Convex in *.
    destruct iab as [ nColA H4 ].
    rewrite (OsRs_OsAs a b roab diab nColA)...
  }
  { intros abL; unfold Convex.
    destruct (nColRs_nColAs a b roab) as [ _ nColA ]...
    simpl in nColA.
    exists (nColA diab).
    rewrite <- (OsRs_OsAs a b roab diab)...
  }
Qed.

Lemma ReflexAngRs_Right :
  forall (a b : Ray)(roab : da a = da b)(diab : ![ a # b ]),
  Reflex ([| a, b | roab |]) <-> %[ a # b | diab ] = false.
Proof with eauto.
  intros a b roab diab.
  split.
  { destruct (nColRs_nColAs a b roab) as [ _ H1 ]; simpl in H1...
    destruct (H1 diab) as [ nAeqA0 nAeqA180 ].
    intros xab; unfold Reflex in *.
    destruct xab as [ nColA H4 ].
    rewrite (OsRs_OsAs a b roab diab nColA)...
  }
  { intros abR; unfold Reflex.
    destruct (nColRs_nColAs a b roab) as [ _ nColA ]...
    simpl in nColA.
    exists (nColA diab).
    rewrite <- (OsRs_OsAs a b roab diab)...
  }
Qed.

Lemma ConvexAngRs_ReflexAngRs :
  forall (a b : Ray)(roab : da a = da b),
  Convex ([| a, b | roab |]) <-> Reflex ([| b, a | eq_sym roab |]).
Proof with eauto.
  intros a b roab.
  split.
  { intros iab.
    assert (diab : ![ a # b ]).
    { apply -> (nColRs_nColAs a b roab).
      unfold Convex in *.
      destruct iab as [ H1 H2 ]...
    }
    destruct (ConvexAngRs_Left a b roab diab) as [ H1 _ ].
    edestruct (ReflexAngRs_Right b a) as [ _ H2 ].
    assert (abL : %[ a # b | diab ] = true). { apply (H1 iab). }
    apply H2. eapply OrientationRs_LR. apply abL.
  }
  { intros xab.
    assert (diba : ![ b # a ]).
    { apply -> (nColRs_nColAs b a (eq_sym roab)).
      unfold Reflex in *. destruct xab as [ H1 H2 ]...
    }
    edestruct (ReflexAngRs_Right b a) as [ H1 _ ]...
    edestruct (ConvexAngRs_Left a b) as [ _ H2 ]...
    assert (baR : %[ b # a | diba ] = false). { apply (H1 xab). }
    apply H2. eapply OrientationRs_RL. apply baR.
  }
  Unshelve. apply nColRs_sym... apply nColRs_sym...
Qed.

Lemma ConvexAngRs :
  forall (a b : Ray)(diab : ![ a # b ]),
  Convex ([| a # b | diab |]).
Proof with eauto.
  intros a b diab.
  assert (roab : da a = da b). { destruct diab... }
  assert (ExTs: exists T, %[ a # b | diab ] = T).
  { exists (%[ a # b | diab ])... }
  destruct ExTs as [ T abT ].
  induction T.
  { assert (abab : [| a, b | roab |] = [| a # b | diab |]).
    { apply (LeftOrientation_EqAs a b)... }
    rewrite <- abab.
    apply (ConvexAngRs_Left a b roab diab)...
  }
  { assert (baab : [| b, a | eq_sym roab |] = [| a # b | diab |]).
    { apply (RightOrientation_EqAs a b)... }
    rewrite <- baab.
    apply (ConvexAngRs_Left b a (eq_sym roab)(nColRs_sym a b diab))...
    assert (%[ a # b | diab] = negb (%[ b # a | nColRs_sym a b diab])).
    { apply (DiOsRs a b diab (nColRs_sym a b diab)). }
    induction (%[ b # a | nColRs_sym a b diab ])...
  }
Qed.

Lemma ConvexAngPs :
  forall (A O B : Point)(nColAOB : ~ [ A, O, B ]),
  Convex ([| A # O # B | nColAOB |]).
Proof.
  intros A O B nColAOB.
  unfold ConvexAnglePs.
  destruct (nColPs_DiPs A O B nColAOB)
    as [ nAeqO [ nOeqB nAeqB ]].
  apply ConvexAngRs.
Qed.

End ANGLE.

(*****************************************************************************)
(* 12 *) Section SEGMENT_TRANSFER.
Context `{ cc : Concentricals }.
(*****************************************************************************)

Definition NullSeg :
  { L0 : Length | forall A : Point, [| A, A |] = L0 }.
Proof.
  destruct DrawPoint as [ A _ ].
  exists ([| A, A |]).
  intros B. apply <- EqSgs_EqPs; auto.
Defined.
Definition L0 := proj1_sig NullSeg.
Definition EqPs_L0 := proj2_sig NullSeg.

Lemma NullSeg_def :
  forall (A : Point),
  [| A, A |] = L0.
Proof.
  apply (proj2_sig NullSeg).
Qed.

Lemma NullSeg_EqPs :
  forall (A B : Point),
  [| A, B |] = L0
    -> A = B.
Proof.
  intros * AB.
  rewrite <- (EqSgs_EqPs A B A); auto.
  rewrite AB. symmetry.
  apply (proj2_sig NullSeg).
Qed.

Lemma EqPs_NullSeg :
  forall (A B : Point),
  A = B
    -> [| A, B |] = L0.
Proof.
  intros * AeqB; subst.
  apply (proj2_sig NullSeg).
Qed.

Lemma nNullSeg_DiPs :
  forall (A B : Point),
  [| A, B |] <> L0
    -> A <> B.
Proof.
  intros * AB.
  contradict AB.
  apply EqPs_NullSeg; auto.
Qed.

Lemma DiPs_nNullSeg :
  forall (A B : Point),
  A <> B
    -> [| A, B |] <> L0.
Proof.
  intros * AB; subst.
  contradict AB.
  apply NullSeg_EqPs; auto.
Qed.

Lemma EqPs_EqSgs :
  forall (A B : Point),
  [| A, A |] = [| B, B |].
Proof.
  intros; apply <- EqSgs_EqPs; auto.
Qed.

Lemma EqSgs_DiPs :
  forall (A B C D : Point),
  A <> B
    -> [| A, B |] = [| C, D |]
    -> C <> D.
Proof.
  intros * nAeqB AB_CD.
  contradict nAeqB. subst. apply (EqSgs_EqPs A B D); auto.
Qed.

Lemma CocentricCirclesPointOrder :
  forall O A B A' B' : Point,
  [| O, A |] = [| O, A' |]
    -> [| O, B |] = [| O, B' |]
    -> [ O # A # B ]
    -> [ O # A', B' ]
    -> [ O # A' # B' ].
Proof with eord 4.
  intros * OA_OA' OB_OB' BetOAB OsrA'B'.
  eapply ConcentricCircles...
Qed.

Lemma SR_EqSgs_EqPs :
  forall (O A A' : Point),
  [ O ; A, A' ]
    -> [| O, A |] = [| O, A' |]
    -> A = A'.
Proof with eord 4.
  intros * [ SR | EqPs ] OA.
  { assert (nAeqO : A <> O). destruct SR as [ H _ ]; auto.
    assert (nA'eqO : A' <> O). destruct SR as [ _ [ H _ ]]; auto.
    destruct (classic (A = A')) as [ AeqA' | nAeqA' ]...
    destruct (DecidePointsBetweenness A A' O) as [[ H1 | H2 ]| H3 ]; dips.
    { destruct SR as [ _ [ _ [ H _ ]]]; colperps. }
    { apply BetPs_sym in H1.
      assert (H2 : [ O # A # A' ]).
      { apply (CocentricCirclesPointOrder O A' A A A'); auto. }
      apply BetPs_nBetPerPs_2 in H2. contradiction.
    }
    { apply BetPs_sym in H2. firstorder. }
    { assert (H4 : [ O # A' # A ]).
      { apply (CocentricCirclesPointOrder O A A' A' A); auto.
        apply BetPs_sym; auto. apply SR_sym; auto.
      }
      apply BetPs_sym in H3. apply BetPs_nBetPerPs_2 in H3.
      contradiction.
    }
  }
  { destruct EqPs as [ OeqA | OeqA' ]; subst.
    { symmetry in OA. apply (EqSgs_EqPs A A' A) in OA... }
    { apply (EqSgs_EqPs A' A A') in OA... }
  }
Qed.

Lemma SR_SR_EqSgs_EqPs :
  forall (O A B C : Point),
  A <> O
    -> [ O ; A, B ]
    -> [ O ; A, C ]
    -> [| O, B |] = [| O, C |]
    -> B = C.
Proof.
  intros * nAeqO OsrAB OsrAC OB_OC.
  destruct OsrAB as [ OsrAB | H1 ].
  { destruct OsrAC as [ OsrAC | H2 ].
    { assert (OsrBC : [ O # B, C ]).
      { apply (SR_trans O B A C); auto. apply SR_sym; auto. }
      clear dependent A. apply (SR_EqSgs_EqPs O B C); auto.
    }
    { destruct H2; subst.
      { contradiction. }
      { symmetry. apply (EqSgs_EqPs C B C); auto. }
    }
  }
  { destruct H1; subst.
    { contradiction. }
    { apply (EqSgs_EqPs B C B); auto. }
  }
Qed.

Lemma CircleSegmentArithmetics :
  forall O A B A' B' : Point,
  [ O # A, B ]
    -> [ O # A', B' ]
    -> [| O, A |] = [| O, A' |]
    -> [| O, B |] = [| O, B' |]
    -> [| A, B |] = [| A', B' |].
Proof with ord.
  intros * O_AB O_A'B' OA_OA' OB_OB'.
  apply (SR_BetPs O A B) in O_AB.
  destruct O_AB as [ BetOAB |[[ AeqB nAeqO ]| BetOBA ]].
  { assert (BetOA'B' : [ O # A' # B' ]).
    { apply (CocentricCirclesPointOrder O A B A' B')... }
    apply (ConcentricCircles O A B A' B')...
  }
  { subst.
    assert (A'eqB' : A' = B').
    { apply (SR_EqSgs_EqPs O A' B')... rewrite <- OB_OB'... }
    subst...
    apply EqSgs_EqPs...
  }
  { assert (BetOB'A' : [ O # B' # A' ]).
    { apply (CocentricCirclesPointOrder O B A B' A')... }
    rewrite SegPs_sym. symmetry.
    rewrite SegPs_sym. symmetry.
    apply (ConcentricCircles O B A B' A')...
  }
Qed.

(** Problem #24 *)
(** Euclid, Book I : Proposition 1. *)
(* To construct an equilateral triangle
 on a given finite straight line. *)
Definition DrawEquilateralTriangleSS :
  forall (A B C : Point),
  ~ [ A, B, C ]
    -> { D : Point | [ A # B | C, D ] /\ [| B, D |] = [| A, B |]
                     /\ [| A, D |] = [| A, B |] }.
Proof with inc; ord.
  intros * nColABC.
  destruct (nColPs_3DiPs A B C) as [ nAeqB [ nBeqC nAeqC ]]...
  destruct (DrawOppositePoint B A) as [ D [ BetABD H2 ]]...
  destruct (DrawOppositePoint A B) as [ E [ BetBAE H4 ]]...
  destruct (DrawIntersectionPointCC E A B A B D C)
    as [ F [ H5 [ H6 H7 ]]]; ncolps; try split; betps.
  exists F.
  rewrite H6, H7, H4, SegPs_sym; auto.
Defined.
Definition DrawEquilateralTriangleOS :
  forall (A B C : Point),
  ~ [ A, B, C ]
    -> { D : Point |
      [ C | A # B | D ] /\ [| B, D |] = [| A, B |] /\ [| A, D |] = [| A, B |] }.
Proof with eauto.
  intros * nColABC.
  assert (nAeqB : A <> B); dips.
  destruct (DrawExtensionLinePP A B) as [ x [ Aox Box ]]...
  assert (nCox : ~ [ C @ x ]); nincpt.
  destruct (DrawPointOnOppositeSide C x) as [ C' H ]...
  assert (nColABC' : ~ [ A, B, C' ]).
  { destruct H as [ _ [ nC'ox H ]]. contradict nC'ox.
    apply (ColPs_IncPt A B C'); try split...
  }
  destruct (DrawEquilateralTriangleSS A B C') as [ D [ H2 [ H3 H4 ]]]...
  exists D.
  repeat split...
  exists x; split; try split...
  destruct H2 as [ _ [ x' [ Aox' [ Box' SSxC'D ]]]].
  assert (xeqx' : x = x'); eqls.
  subst x'.
  apply (OSO_trans C C' D x)...
Defined.

Definition DrawPointProjectionOnRay :
  forall (O A B : Point),
  O <> A
    -> { C : Point | [ O ; A, C ] /\ [| O, C |] = [| O, B |] }.
Proof with inc.
  intros * nOeqA.
  destruct (DrawOppositePoint O A) as [ C [ BetAOC _ ]]...
  assert (nOeqC : O <> C); dips.
  destruct (DrawIntersectionPointLC O C B) as [ D [ H1 H2 ]]...
  exists D; split; eauto.
  destruct H1 as [ OsrCD |[ CeqO nOeqD ]]; subst; eauto.
  { left; eapply BetPs_BetPs_SR; betps. }
Defined.

(** Problem #25 *)
(** Euclid, Book I : Proposition 2. *)
(* To place a straight line equal to a given straight line
 with one end at a given point. *)
Definition DrawDistinctSegmentOnRay :
  forall (O A B C : Point),
  O <> A
    -> O <> B
    -> { D : Point | [ O ; A, D ] /\ [| O, D |] = [| B, C |] }.
Proof with eauto.
  intros * nOeqA nOeqB.
  destruct (DrawNonCollinearPoint O B) as [ X nColOBX ]...
  destruct (DrawEquilateralTriangleSS O B X) as [ P [ H1 [ H2 H3 ]]]...
  assert (nPeqB : P <> B).
  { apply SHb_sym in H1. apply SH_nColPs in H1.
    contradict H1. subst. colps.
  }
  destruct (DrawOppositePoint B P) as [ Q [ BetPBQ _ ]]...
  assert (nBeqQ : B <> Q); dips.
  destruct (DrawPointProjectionOnRay B Q C) as [ E [ H6 H7 ]]...
  assert (nPeqO : P <> O).
  { apply SHb_sym in H1. apply SH_nColPs in H1.
    contradict H1. subst. colps.
  }
  destruct (DrawPointProjectionOnRay P O E) as [ F [ H8 H9 ]]...
  destruct (DrawPointProjectionOnRay O A F) as [ D [ H10 H11 ]]...
  exists D.
  destruct H6 as [ BsrQE |[ BeqQ | BeqE ]].
  { split...
    rewrite H11. rewrite <- H7.
    assert (BetPBE : [ P # B # E ]). { apply (BetPs_SR_BetPs B P Q E)... }
    destruct H8 as [ PsrOF |[ PeqO | PeqF ]].
    { assert (BetPOF : [ P # O # F ]).
      { apply (CocentricCirclesPointOrder P B E O F)... rewrite SegPs_sym.
        rewrite H2. rewrite <- H3. apply SegPs_sym.
      }
      apply (CircleSegmentArithmetics P O F B E); ord.
      rewrite SegPs_sym. rewrite H3. rewrite <- H2. apply SegPs_sym.
    }
    { contradiction. }
    { assert (nPeqE : P <> E); dips.
      contradict nPeqE. apply NullSeg_EqPs.
      rewrite <- H9. apply EqPs_NullSeg...
    }
  }
  { contradiction. }
  { assert (FeqO : F = O).
    { apply (SR_SR_EqSgs_EqPs P O F O); auto.
      { left. apply SR_refl. auto. }
      { rewrite H9. destruct BeqE. rewrite SegPs_sym.
        rewrite H2. rewrite <- H3. apply SegPs_sym.
      }
    }
    { subst O.
      split...
      rewrite H11. rewrite <- H7.
      apply EqPs_NullSeg in BeqE.
      rewrite BeqE. apply EqPs_NullSeg...
    }
  }
Defined.
Definition DrawSegmentOnRay :
  forall (O A B C : Point),
  O <> A
    -> { D : Point | [ O ; A, D ] /\ [| O, D |] = [| B, C |] }.
Proof with eauto.
  intros * nOeqA.
  destruct (DrawThirdDistinctPoint O B) as [ P [ nPeqO nPeqB ]].
  destruct (DrawDistinctPoint P) as [ Q nQeqP ].
  destruct (DrawDistinctSegmentOnRay P Q B C) as [ R [ H1 H2 ]]...
  destruct (DrawDistinctSegmentOnRay O A P R) as [ E [ H3 H4 ]]...
  exists E.
  split; geo.
Defined.
Definition DrawSegmentOnOppositeRay :
  forall (O A B C : Point),
  O <> A
    -> { D : Point | [ A # O ; D ] /\ [| O, D |] = [| B, C |] }.
Proof with geo 4.
  intros * nOeqA.
  destruct (DrawOppositePoint O A) as [ D [ BetAOD OAeqOD ]]...
  assert (nOeqD : O <> D). { apply (BetPs_3DiPs A O D BetAOD). }
  destruct (DrawSegmentOnRay O D B C) as [ E [ H1 H2 ]]...
  exists E.
  split...
  destruct H1 as [ OsrDE | OeqE ]...
Defined.
Lemma DiPs_BetPs_SubtractSgs :
  forall A B C D E F : Point,
  A <> D
    -> [ A # B # C ]
    -> [ D # E, F ]
    -> [| A, C |] = [| D, F |]
    -> [| A, B |] = [| D, E |]
    -> [ D # E # F ] /\ [| B, C |] = [| E, F |].
Proof with eauto.
  intros * nAeqD BetABC DsrEF ACDF ABDE.
  destruct (DrawNonCollinearPoint A D) as [ X nColADX ]...
  destruct (DrawEquilateralTriangleSS A D X) as [ O [ H1 [ H2 H3 ]]]...
  assert (nOeqA : O <> A).
  { apply SHb_sym in H1.
    apply SH_nColPs in H1.
    apply not_eq_sym; dips.
  }
  assert (nOeqD : O <> D).
  { apply SHb_sym in H1.
    apply SH_nColPs in H1.
    apply not_eq_sym; dips.
  }
  destruct (DrawOppositePoint A O) as [ P [ BetOAP H5 ]]...
  assert (nAeqP : A <> P); dips.
  destruct (DrawOppositePoint D O) as [ Q [ BetODQ H15 ]]...
  assert (nDeqQ : D <> Q); dips.
  rewrite SegPs_sym in H3. rewrite <- H2 in H3.
  symmetry in H3. rewrite SegPs_sym in H3.
  destruct (DrawPointProjectionOnRay A P B)
    as [ B' [[ H6 |[ AeqP | AeqB' ]] H7 ]]...
  { destruct (DrawPointProjectionOnRay A P C)
      as [ C' [[ H8 |[ AeqP | AeqC' ]] H9 ]]...
    { assert (BetAB'C' : [A # B' # C']).
      { apply (CocentricCirclesPointOrder A B C B' C')... betps. }
      assert (G2 : [|B, C|] = [|B', C'|]).
      { apply (CircleSegmentArithmetics A B C B' C'); betps. }
      rewrite_all <- H9. rewrite_all <- H7. rewrite_all G2.
      clear dependent B. clear dependent C.
      assert (BetOAB'C' : [O # A # B' # C']). { eapply BetPs_a_trans; betps. }
      destruct BetOAB'C' as [ BetOAB' [ BetOAC' [ BetOB'C' _ ]]].
      destruct (DrawPointProjectionOnRay O D B')
        as [ E' [[ H10 |[ OeqD | OeqE' ]] H11 ]]...
      { destruct (DrawPointProjectionOnRay O D C')
          as [ F' [[ H12 |[ OeqD | OeqF' ]] H13 ]]...
        assert (BetODE' : [O # D # E']).
        { apply (CocentricCirclesPointOrder O A B' D E')... }
        assert (BetODF' : [O # D # F']).
        { apply (CocentricCirclesPointOrder O A C' D F')... }
        assert (BetOE'F' : [O # E' # F']).
        { apply (CocentricCirclesPointOrder O B' C' E' F'); betps. }
        assert (BetODE'F' : [O # D # E' # F']).
        { eapply BetPs_c_trans; betps. }
        destruct BetODE'F' as [ _ [ _ [ _ BetDE'F' ]]].
        destruct (DrawPointProjectionOnRay D E E')
          as [ E'' [[ H16 |[ DeqE | DeqE' ]] H17 ]].
        { firstorder. }
        { assert (EeqE'' : E = E'').
          { apply (SR_SR_EqSgs_EqPs D E E E'').
            { destruct H16... }
            { left; apply SR_refl... firstorder. }
            { left... }
            { rewrite H17.
              rewrite <- (CircleSegmentArithmetics O A B' D E'); betps.
            }
          }
          subst E''.
          destruct (DrawPointProjectionOnRay D E F')
            as [ F'' [[ H18 |[ DeqE | DeqF' ]] H19 ]].
          { firstorder. }
          { assert (FeqF'' : F = F'').
            { apply (SR_SR_EqSgs_EqPs D F F F'').
              { destruct DsrEF as [ _ [ H _ ]]; eauto. }
              { left. apply SR_refl; dips. }
              { left. apply (SR_trans D F E F''); auto. apply SR_sym; auto. }
              { rewrite H19.
                rewrite <- (CircleSegmentArithmetics O A C' D F'); betps.
              }
            }
            subst F''.
            assert (BetDEF : [D # E # F]).
            { apply (CocentricCirclesPointOrder D E' F' E F)... }
            split...
            rewrite <- (CircleSegmentArithmetics D E' F' E F); betps.
            rewrite (CircleSegmentArithmetics O B' C' E' F'); betps.
          }
          { destruct H16; contradiction. }
          { subst F''. rewrite EqPs_L0 in H19.
            symmetry in H19. apply NullSeg_EqPs in H19.
            apply BetPs_3DiPs in BetODF'. firstorder.
          }
        }
        { destruct DsrEF; contradiction. }
        { destruct DeqE'. rewrite EqPs_L0 in H17.
          symmetry in H17. apply NullSeg_EqPs in H17.
          apply BetPs_3DiPs in BetODE'. firstorder.
        }
        { contradiction. }
        { subst F'. rewrite EqPs_L0 in H13.
          symmetry in H13. apply NullSeg_EqPs in H13.
          apply BetPs_3DiPs in BetOAC'. firstorder.
        }
      }
      { contradiction. }
      { destruct OeqE'. rewrite EqPs_L0 in H11.
        symmetry in H11. apply NullSeg_EqPs in H11.
        apply BetPs_3DiPs in BetOAB'. firstorder.
      }
    }
    { contradiction. }
    { destruct AeqC'. rewrite EqPs_L0 in H9.
      symmetry in H9. apply NullSeg_EqPs in H9.
      apply BetPs_3DiPs in BetABC. firstorder.
    }
  }
  { contradiction. }
  { destruct AeqB'. rewrite EqPs_L0 in H7.
    symmetry in H7. apply NullSeg_EqPs in H7.
    apply BetPs_3DiPs in BetABC. firstorder.
  }
Qed.

(** Theorem #39 *)
(** Hartshorne, Proposition 8.3 *)
(* Given three points A, B, C on a line such that point B is between
 points A and C, and given points E, F on a ray originating from a point D,
 suppose that AB = DE and AC = DF. Then E will be between D and F,
 and BC = EF *)
Lemma BetPs_SubtractSgs :
  forall A B C D E F : Point,
  [ A # B # C ]
    -> [ D # E, F ]
    -> [| A, C |] = [| D, F |]
    -> [| A, B |] = [| D, E |]
    -> [ D # E # F ] /\ [| B, C |] = [| E, F |].
Proof with eauto.
  intros * BetABC DsrEF ACDF ABDE.
  destruct (DrawThirdDistinctPoint A D) as [ P [ nPeqA nPeqD ]].
  destruct (DrawDistinctPoint P) as [ Q nQeqP ].
  destruct (DrawDistinctSegmentOnRay P Q A B) as [ R [ H1 H2 ]]...
  destruct H1 as [ H1 |[ PeqQ | PeqR ]].
  { destruct (DrawDistinctSegmentOnRay P Q A C) as [ S [ H3 H4 ]]...
    destruct H3 as [ H3 |[ PeqQ | PeqS ]].
    { destruct (DiPs_BetPs_SubtractSgs A B C P R S) as [ H5 H6 ]; dips.
      { apply SR_sym in H1. eapply SR_trans... }
      destruct (DiPs_BetPs_SubtractSgs P R S D E F) as [ H7 H8 ]; dips.
      apply SR_sym in H1.
      split; auto. rewrite H6; auto.
    }
    { contradiction. }
    { apply EqPs_NullSeg in PeqS. rewrite PeqS in H4.
      symmetry in H4. rewrite ACDF in H4. apply NullSeg_EqPs in H4.
      destruct DsrEF as [ _ [ nDeqE _ ]]; contradiction.
    }
  }
  { contradiction. }
  { apply EqPs_NullSeg in PeqR. rewrite PeqR in H2.
    symmetry in H2. rewrite ABDE in H2. apply NullSeg_EqPs in H2.
    destruct DsrEF as [ nDeqE _ ]; firstorder.
  }
Qed.

(** Theorem #40 *)
Lemma BetPs_AddSgs :
  forall A B C D E F : Point,
  [ A # B # C ]
    -> [ D # E # F ]
    -> [| A, B |] = [| D, E |]
    -> [| B, C |] = [| E, F |]
    -> [| A, C |] = [| D, F |].
Proof with dips.
  intros * BetABC BetDEF ABDE BCEF.
  destruct (DrawSegmentOnRay D E A C)
    as [ F' [[ H1 |[ DeqE | DeqF' ]] H2 ]]...
  { destruct (BetPs_SubtractSgs A B C D E F') as [ H3 H4 ]...
    rewrite BCEF in H4.
    assert (nEeqF : E <> F).
    { intros EeqF. apply EqPs_NullSeg in EeqF.
      rewrite EeqF in BCEF. apply NullSeg_EqPs in BCEF.
      apply BetPs_3DiPs in BetABC. firstorder.
    }
    assert (FeqF' : F = F'). { apply (SR_SR_EqSgs_EqPs E F F F'); ord. }
    subst F'; rewrite H2...
  }
  { apply BetPs_DiPs_1 in BetDEF; contradiction. }
  { subst F'.
    rewrite EqPs_L0 in H2. symmetry in H2.
    apply NullSeg_EqPs in H2.
    apply BetPs_3DiPs in BetABC.
    firstorder.
  }
Qed.

(** Problem #26 *)
Definition DrawSegmentCut :
  forall A B C D F : Point,
  [ A # B # C ]
    -> [| A, C |] = [| D, F |]
    -> { E : Point | [ D # E # F ] /\ [| A, B |] = [| D, E |]
                  /\ [| B, C |] = [| E, F |] }.
Proof with eauto.
  intros * BetABC ACeqDF.
  destruct (BetPs_3DiPs A B C BetABC) as [ nAeqB [ nBeqC nAeqC ]].
  assert (nDeqF : D <> F). { eapply EqSgs_DiPs... }
  destruct (DrawSegmentOnRay D F A B) as [ E [ DsrFE DEeqAB ]]...
  exists E.
  destruct DsrFE as [ DsrFE |[ DeqF | DeqE ]].
  { destruct (SR_BetPs D F E) as [[ BetDFE |[ FeqE | BetDEF ]] _ ]...
    { destruct (BetPs_3DiPs D F E) as [ _ [ nFeqE nDeqE ]]...
      destruct (DrawOppositePoint C A) as [ P [ BetACP _ ]]...
      destruct (BetPs_3DiPs A C P BetACP) as [ _ [ nCeqP nAeqP ]].
      destruct (DrawSegmentOnRay C P F E )
        as [ G [[ CsrPG |[ CeqP | CeqG ]] CGeqFE ]]...
      { assert (BetACG : [ A # C # G ]). { apply (BetPs_SR_BetPs C A P G)... }
        assert (AGeqDE : [| A, G |] = [| D, E |]).
        { apply (BetPs_AddSgs A C G D F E)... }
        assert (nBeqG : B <> G).
        { intros BeqG. subst.
          apply BetPs_sym in BetABC; apply BetPs_sym in BetACG;
          apply (BetPs_nBetPerPs C G A) in BetABC; contradiction.
        }
        destruct (DrawSegmentOnRay A B D E)
          as [ B' [[ AsrBB' |[ AeqB | AeqB' ]] DEeqAB' ]]...
        { assert (BeqB' : B = B').
          { apply (SR_EqSgs_EqPs A B B')... rewrite <- DEeqAB... }
          subst B'.
          assert (BeqG : B = G).
          { apply (SR_EqSgs_EqPs A B G).
            { assert (BetABG : [ G # B # A ]).
              { apply (BetPs_a_trans G C B A); betps. }
              { left.
                apply (BetPs_sym G B A) in BetABG.
                apply (BetPs_SR A B G) in BetABG; firstorder.
              }
            }
            rewrite DEeqAB'...
          }
          contradiction.
        }
        { contradiction. }
        { apply EqPs_NullSeg in AeqB'. rewrite AeqB' in DEeqAB'.
          symmetry in DEeqAB'. apply NullSeg_EqPs in DEeqAB'.
          contradiction.
        }
      }
      { contradiction. }
      { apply EqPs_NullSeg in CeqG. rewrite CeqG in CGeqFE.
        symmetry in CGeqFE. apply NullSeg_EqPs in CGeqFE.
        contradiction.
      }
    }
    { destruct FeqE as [ FeqE nFeqD ].
      subst E.
      assert (BeqC : B = C).
      { apply (SR_EqSgs_EqPs A B C).
        apply (BetPs_SR A B C) in BetABC.
        firstorder. rewrite ACeqDF...
      }
      contradiction.
    }
    repeat split...
    apply (BetPs_SubtractSgs A B C D E F); betps.
  }
  { contradiction. }
  { apply EqPs_NullSeg in DeqE. rewrite DeqE in DEeqAB.
    symmetry in DEeqAB. apply NullSeg_EqPs in DEeqAB.
    contradiction.
  }
Defined.

Lemma Bet4Ps_AddSgs :
  forall A B C D E F G H : Point,
  [ A # B # C # D ]
    -> [ E # F # G # H ]
    -> [| A, B |] = [| E, F |]
    -> [| B, C |] = [| F, G |]
    -> [| C, D |] = [| G, H |]
    -> [| A, D |] = [| E, H |].
Proof.
  intros * BetABCD BetEFGH ABEF BCFG CDGH.
  apply (BetPs_AddSgs A C D E G H); eauto; betps.
  apply (BetPs_AddSgs A B C E F G); eauto; betps.
Qed.

Definition DrawAdditionalSegment :
  forall A B C D : Point,
  A <> B
    -> C <> D
    -> { E : Point | [ A # B # E ] /\ [| B, E |] = [| C, D |] }.
Proof with dips.
  intros * nAeqB nCeqD.
  destruct (DrawOppositePoint B A) as [ P [ BetABP _ ]]...
  assert (nBeqP : B <> P)...
  destruct (DrawSegmentOnRay B P C D) as [ E [ BsrPE BEeqCD ]]...
  exists E.
  destruct BsrPE as [ BsrPE |[ BeqP | BeqE ]].
  { assert (BetABE : [ A # B # E ]); betps. }
  { contradiction. }
  { subst. symmetry in BEeqCD. apply EqSgs_EqPs in BEeqCD.
    subst. contradiction.
  }
Defined.

End SEGMENT_TRANSFER.

Hint Resolve
  NullSeg_EqPs
  : EqPs.

Hint Resolve
  EqSgs_DiPs
  SR_EqSgs_EqPs
  nNullSeg_DiPs
  EqSgs_DiPs
  : DiPs.

Hint Resolve
  SR_SR_EqSgs_EqPs
  : CongPs.

(*****************************************************************************)
(* 13 *) Section SEGMENT_ORDER.
Context `{ cc : Concentricals }.
(*****************************************************************************)

Definition LtS (a b : Length) : Prop
  := exists A B C : Point,
     [| A, B |] = a /\ [| A, C |] = b /\ [ A ; B # C ].
Notation " a << b "
  := (LtS a b)(at level 70).

Definition L1 : Length.
Proof.
  destruct DrawPoint as [ A _ ].
  destruct (DrawDistinctPoint A) as [ B nAeqB ].
  apply ([| A, B |]).
Defined.

Lemma LtS_non_trivial :
  L0 << L1.
Proof with eauto.
  unfold L0, L1, LtS.
  destruct DrawPoint as [ A _ ].
  destruct (DrawDistinctPoint A) as [ B nAeqB ].
  exists A, A, B; repeat split.
  { apply (proj2_sig NullSeg). }
  { right; split... }
Qed.

(** Theorem #41 *)
Theorem BetPs_LtS :
  forall A B C : Point,
  [ A # B # C ]
    -> [| A, B |] << [| A, C |].
Proof with eauto.
  intros A B C BetABC.
  unfold LtS.
  exists A, B, C; split...
Qed.

(** Theorem #42 *)
Theorem LtS_SR_BetPs :
  forall A B C : Point,
  [| A, B |] << [| A, C |]
    -> [ A # B, C ]
    -> [ A # B # C ].
Proof with eauto.
  intros A B C ABltAC AsrBC.
  destruct ABltAC as [ A' [ B' [ C' [ AB [ AC H ]]]]].
  destruct H as [ H1 |[ H2 H3 ]].
  { eapply BetPs_SubtractSgs... }
  { exfalso.
    destruct AsrBC as [ nAeqB _ ].
    apply (EqSgs_DiPs A B A' B')...
  }
Qed.

(** Theorem #43 *)
Theorem LtS_positive :
  forall a : Length,
  ~ a << L0.
Proof.
  unfold LtS.
  intros a [ A [ B [ C [ H1 [ H2 [ H3 |[ H4 H5 ]]]]]]];
  apply NullSeg_EqPs in H2; subst;
  try apply BetPs_DiPs_2 in H3; contradiction.
Qed.

(** Theorem #44 *)
Theorem LtS_trichotomy :
  forall a b : Length,
  a << b \/ a = b \/ b << a.
Proof with eauto.
  intros AB CD.
  destruct (DrawSegment AB) as [[ A B ] ABeqAB ]; subst.
  destruct (DrawSegment CD) as [[ C D ] CDeqCD ]; subst.
  destruct (classic (A = B)) as [ AeqB | nAeqB ]; subst.
  { destruct (classic (C = D)) as [ CeqD | nCeqD ]; subst.
    { right; left. apply EqPs_EqSgs. }
    { left. unfold LtS.
      exists C, C, D. repeat split... apply EqPs_EqSgs.
    }
  }
  { destruct (classic (C = D)) as [ CeqD | nCeqD ]; subst.
    { right; right... unfold LtS.
      exists A, A, B. repeat split... apply EqPs_EqSgs.
    }
    { destruct (classic ([|A, B|] = [|C, D|])) as [ ABeqCD | nABeqCD ]; subst.
      { right; left... }
      { destruct (DrawSegmentOnRay C D A B)
          as [ E [[ CsrDE |[ CeqD | CeqE ]] CEeqAB ]]...
        { destruct (SR_BetPs C D E)
            as [[ BetCDE |[[ DeqE nDeqC ]| BetCED ]] _ ]...
          { right; right...
            destruct (DrawSegmentCut C D E A B)
              as [ F [ BetAFB [ CDeqAF DEeqFB ]]]...
            unfold LtS. exists A, F, B. repeat split...
          }
          { subst E. rewrite CEeqAB... }
          { left. unfold LtS.
            exists C, E, D. split...
          }
        }
        { contradiction. }
        { subst E. symmetry in CEeqAB.
          apply EqSgs_EqPs in CEeqAB.
          contradiction.
        }
      }
    }
  }
Qed.

(** Theorem #45 *)
Lemma LtS_irrefl :
  forall a : Length,
  ~ a << a.
Proof with eauto.
  unfold LtS.
  intros a [ A [ B [ C [ H1 [ H2 [ BetACB |[ H4 nBeqC ]]]]]]]; subst.
  { apply (BetPs_SR A B C) in BetACB.
    destruct BetACB as [ AsrBC CsrBA ].
    assert (nBeqC : B <> C); dips.
  }
  { contradict nBeqC. apply EqSgs_EqPs in H2; subst... }
Qed.
Lemma LtS_asymm :
  forall a b : Length,
  a << b
    -> ~ b << a.
Proof with eauto.
  unfold LtS.
  intros a b;
  intros [ A [ B [ C [ H1 [ H2 [ H3 |[ H4 H5 ]]]]]]];
  intros [ A' [ B' [ C' [ H6 [ H7 [ H8 |[ H9 H0 ]]]]]]]; subst.
  { assert (BetA'C'B' : [ A' # C' # B' ]).
    { apply (BetPs_SubtractSgs A B C A' C' B')...
      apply BetPs_SR in H8. destruct H8. apply SR_sym...
    }
    { apply BetPs_nBetPerPs_2 in BetA'C'B'. contradiction. }
  }
  { symmetry in H6. apply EqSgs_EqPs in H6.
    apply BetPs_DiPs_2 in H3. contradict H3...
  }
  { apply EqSgs_EqPs in H7.
    apply BetPs_DiPs_2 in H8. contradict H8...
  }
  { apply EqSgs_EqPs in H7. contradiction. }
Qed.
Lemma LtS_trans :
  forall a b c : Length,
  a << b
    -> b << c
    -> a << c.
Proof with eauto.
  intros a b c;
  intros [ A [ B [ C [ H1 [ H2 [ H3 |[ H4 H5 ]]]]]]];
  intros [ A' [ B' [ C' [ H6 [ H7 [ H8 |[ H9 H0 ]]]]]]]; unfold LtS; subst.
  { destruct (DrawSegmentCut A B C A' B') as [ P [ A'PB' [ AB BC ]]]...
    exists A', P, C'; repeat split...
    left. apply (BetPs_c_trans A' P B' C' )...
  }
  { symmetry in H6. apply EqSgs_EqPs in H6.
    apply BetPs_DiPs_2 in H3. contradict H3...
  }
  { exists A', A', C'; repeat split...
    { apply EqPs_EqSgs. }
    { right; split... apply BetPs_DiPs_2 in H8... }
  }
  { symmetry in H6. apply EqSgs_EqPs in H6. contradiction. }
Qed.
Instance LtS_strorder : StrictOrder LtS.
Proof.
  split.
  exact LtS_irrefl.
  exact LtS_trans.
Qed.

Lemma DiSgs_PosSgs :
  forall a : Length,
  a <> L0
    <-> L0 << a.
Proof with eauto.
  split; intros H...
  { destruct (LtS_trichotomy L0 a) as [ H1 |[ H2 | H3 ]]...
    { subst; contradiction... }
    { apply LtS_positive in H3. contradiction. }
  }
  { intros aeqL0; subst. apply LtS_positive in H... }
Qed.

(** Problem #27 *)
Definition DecideSegmentComparison :
  forall a b : Length,
  a <> b
    -> { a << b } + { b << a }.
Proof with eauto.
  intros AB CD nABeqCD.
  destruct (DrawSegment AB) as [[ A B ] ABeqAB ].
  destruct (DrawSegment CD) as [[ C D ] CDeqCD ].
  destruct (DrawDistinctPoint A) as [ E nAeqE ].
  destruct (DrawSegmentOnRay A E A B) as [ F [ AsrEF' AFeqAB ]]...
  destruct (DrawSegmentOnRay A E C D) as [ G [ AsrEG' AGeqCD ]]...
  rewrite <- ABeqAB in *. rewrite <- CDeqCD in *.
  rewrite <- AFeqAB in *. rewrite <- AGeqCD in *...
  clear ABeqAB CDeqCD.
  assert (nFeqG : F <> G). { contradict nABeqCD. subst G... }
  destruct (DecidePointsDistinction F A G nFeqG) as [ nAeqF | nAeqG ].
  { apply not_eq_sym in nAeqF.
    assert (AsrEF : [A # E, F]).
    { destruct AsrEF' as [ AsrEF |[ AeqE | AeqF ]]; eauto; contradiction. }
    { destruct (DecidePointsOnSameRay F A G) as [ FsrAG | H2 ]...
      { destruct AsrEF as [ H1 [ H2 [[ x [ Eox [ Aox Fox ]]] H4 ]]].
        destruct AsrEG'
          as [[ G1 [ G2 [[ y [ Aoy [ Eoy Goy ]]] G4 ]]]|[ AeqE | AeqG ]].
        { assert (xeqy : x = y); eqls.
          subst y.
          exists x; split; auto.
        }
        { contradiction. }
        { subst G. apply ColPs_23. }
      }
      { right.
        destruct AsrEG' as [ AsrEG |[ AeqE | AeqG ]].
        { assert (AGF : [A # G # F]).
          { apply BetPs_SR; split; eapply SR_trans; betps. }
          eapply BetPs_LtS...
        }
        { contradiction. }
        { eapply EqPs_NullSeg in AeqG... rewrite AeqG in *.
          eapply DiSgs_PosSgs in nABeqCD...
        }
      }
      { left. eapply BetPs_LtS... }
    }
  }
  { assert (AsrEG : [A # E, G]).
    { destruct AsrEG' as [ AsrEG |[ AeqE | AeqG ]]; eauto;
      subst; contradiction.
    }
    clear AsrEG'.
    destruct (DecidePointsOnSameRay G A F) as [ GsrAF | H2 ]...
    { destruct AsrEG as [ H1 [ H2 [[ x [ Eox [ Aox Gox ]]] H4 ]]].
      destruct AsrEF'
        as [[ G1 [ G2 [[ y [ Aoy [ Eoy Foy ]]] G4 ]]]|[ AeqE | AeqG ]].
      { assert (xeqy : x = y); eqls; subst y.
        exists x; split; auto.
      }
      { contradiction. }
      { subst F; colps. }
    }
    { left.
      destruct AsrEF' as [ AsrEF |[ AeqE | AeqG ]].
      { assert (AFG : [A # F # G]).
        { apply BetPs_SR; split. eapply SR_trans; betps. apply SR_sym... }
        eapply BetPs_LtS...
      }
      { contradiction. }
      { eapply EqPs_NullSeg in AeqG... rewrite AeqG in *.
        eapply DiSgs_PosSgs...
      }
    }
    right. eapply BetPs_LtS...
  }
Defined.

(** Problem #28 *)
Definition DecideSegmentOrder :
  forall a b c : Length,
  a << b
    -> { a << c } + { c << b }.
Proof with eauto.
  intros r s t rs.
  destruct DrawPoint as [ X _ ].
  destruct (DrawDistinctPoint X) as [ O nOeqX ].
  destruct (DrawSegment r) as [[ R1 R2 ] Hr ].
  destruct (DrawSegment s) as [[ L1 S2 ] Hs ].
  destruct (DrawSegment t) as [[ T1 T2 ] Ht ].
  destruct (DrawSegmentOnOppositeRay O X R1 R2) as [ R [ H1 H2 ]]...
  destruct (DrawSegmentOnOppositeRay O X L1 S2) as [ S [ H3 H4 ]]...
  destruct (DrawSegmentOnOppositeRay O X T1 T2) as [ T [ H5 H6 ]]...
  rewrite Hr in *. rewrite Hs in *. rewrite Ht in *.
  clear dependent L1. clear dependent S2. clear dependent R1.
  clear dependent R2. clear dependent T1. clear dependent T2.
  destruct H2. destruct H4. destruct H6.
  assert (nXeqR : X <> R).
  { destruct H1 as [ H1 |[ H1 H2 ]].
    destruct (BetPs_3DiPs X O R) as [ H4 [ H2 H0 ]]... subst...
  }
  assert (nXeqS : X <> S).
  { destruct H3 as [ H3 |[ H3 H2 ]].
    destruct (BetPs_3DiPs X O S) as [ H4 [ H2 H0 ]]... subst...
  }
  assert (BetXRS : [X # R # S]).
  { destruct H1 as [ H1 |[ H1 H2 ]];
    destruct H3 as [ H3 |[ H3 H4 ]]; subst...
    { eapply (BetPs_a_trans X O R S)...
      eapply LtS_SR_BetPs...
      apply (BetPs_BetPs_SR O X R S)...
    }
    { exfalso. eapply (LtS_positive ([|S, R|])).
      rewrite NullSeg_def in rs...
    }
    { exfalso. rewrite NullSeg_def in rs... eapply LtS_irrefl... }
  }
  assert (nReqS : R <> S).
  { destruct (BetPs_3DiPs X R S BetXRS) as [ _ [ RS _ ]]... }
  destruct (DecidePointsOrderOnLine R S T nReqS) as [ G1 | G2 ].
  { destruct (DrawLineThroughOrderedPoints X R S)
      as [ x [ Xoz [ Rox Sox ]]]...
    destruct (DrawExtensionLinePP O X) as [ t [ Oot Xot ]]...
    exists t; repeat split.
    { destruct H1 as [ H1 |[ H2 H4]]; subst; incpt 2. }
    { destruct H3 as [ H3 |[ H2 H4]]; subst; incpt 2. }
    { destruct H5 as [ H4 |[ H2 H4]]; subst; incpt 2. }
  }
  { left. exists O, R, T; do 2 split...
    destruct H1 as [ H1 |[ _ H2 ]]...
    { assert (BetXRT : [X # R # T]). { apply (BetPs_SR_BetPs R X S T)... }
      left. apply (BetPs_c_trans X O R T)...
    }
    { subst. right; split... destruct G1 as [ _ [ H _ ]]... }
  }
  { right.
    assert (BetXTS : [X # T # S]).
    { destruct H5 as [ XOT |[ _ H5 ]].
      { destruct H3 as [ XOS |[ _ H3 ]].
        { destruct H1 as [ XOR |[ _ H2 ]]; subst.
          { apply BetPs_SR.
            split.
            { apply (BetPs_SR_SR O X T S)...
              apply (BetPs_BetPs_SR O X T S)...
            }
            { apply (SR_trans S T R X)...
              { apply SR_sym in G2... }
              { apply BetPs_sym in BetXRS.
                apply BetPs_SR in BetXRS; destruct BetXRS...
              }
            }
          }
          { assert (RST : [R # S, T]).
            { apply (BetPs_BetPs_SR R X S T)... }
            apply SR_BetPs in G2.
            destruct G2 as [ G1 |[[ G2 G3 ]| G4 ]]...
            { destruct RST as [ _ [ _ [ _ nSRT ]]]; contradiction. }
            { subst.
              destruct RST as [ H1 [ H2 [ H3 nSRT ]]]. contradiction.
            }
            { apply (BetPs_a_trans X R T S)... apply BetPs_sym... }
          }
        }
        { subst.
          assert (RST : [R # S # T]).
          { apply (BetPs_c_trans X R S T)... }
          destruct G2 as [ _ [ _ [ _ G2 ]]]... contradiction.
        }
      }
      { subst. destruct H3 as [ H3 |[ nXeqT XeqS ]]... subst.
        destruct G2 as [ _ [ H2 _ ]]. contradict H2...
      }
    }
    { exists O, T, S; do 2 split...
      destruct H5 as [ H5 |[ H4 H5 ]]...
      { left. apply (BetPs_c_trans X O T S)... }
      { subst. right; split... destruct G2 as [ _ [ H _ ]]... }
    }
  }
Defined.

Definition DecideDistinctSegments :
  forall (a b c : Length),
  a <> b
    -> { a <> c } + { c <> b }.
Proof with eauto.
  intros r s t nreqs.
  destruct (DecideSegmentComparison r s nreqs) as [ rlts | sltr ].
  { destruct (DecideSegmentOrder r s t rlts) as [ H1 | H2 ].
    { left. intros reqt; subst. apply (LtS_irrefl t)... }
    { right. intros reqt; subst. apply (LtS_irrefl s)... }
  }
  { destruct (DecideSegmentOrder s r t sltr) as [ H1 | H2 ].
    { right. intros reqt; subst. apply (LtS_irrefl s)... }
    { left. intros reqt; subst. apply (LtS_irrefl t)... }
  }
Defined.

End SEGMENT_ORDER.

Notation " a << b "
  := (LtS a b)(at level 70).

(*****************************************************************************)
(* 14 *) Section SEGMENT_ADDITION.
Context `{ cc : Concentricals }.
(*****************************************************************************)

(** Problem #29 *)
Definition PlusLengthDef (a b : Length) :
  { c : Length | forall A B C : Point, [ A ; B ; C ]
                 -> [| A, B |] = a -> [| B, C |] = b -> [| A, C |] = c }.
Proof with eauto.
  destruct (DrawSegment a) as [[ A B ] ABeqAB ].
  destruct (DrawSegment b) as [[ C D ] CDeqCD ].
  destruct (DrawPoint) as [ P _ ].
  destruct (DrawDistinctPoint P) as [ O nOeqP ].
  destruct (DrawSegmentExtension P O) as [ P' BetPOP' ]. auto.
  destruct (DrawSegmentOnRay O P A B) as [ E [ OsrPE OEeqAB ]]. auto.
  assert (nP'eqE : P' <> E).
  { destruct OsrPE as [ OsrPE |[ OeqP | OeqE ]].
    { apply BetPs_sym in BetPOP'.
      apply (BetPs_SR_SR O P' P E BetPOP') in OsrPE.
      firstorder.
    }
    { contradict nOeqP... }
    { subst E.
      apply not_eq_sym.
      apply (BetPs_3DiPs P O P' BetPOP').
    }
  }
  destruct (DrawSegmentExtension P' E nP'eqE) as [ P'' BetP'EP'' ].
  assert (nEeqP'' : E <> P''). { apply (BetPs_3DiPs P' E P'' BetP'EP''). }
  destruct (DrawSegmentOnRay E P'' C D nEeqP'') as [ F [ For' EFeqCD ]].
  exists ([| O, F |]). subst a. subst b. rewrite <- OEeqAB in *.
  rewrite <- EFeqCD in *.
  intros A' B' C' A'B'C' H1 H2.
  destruct A'B'C' as [ A'B'C' |[ A'eqB' | B'eqC' ]].
  { eapply BetPs_AddSgs...
    destruct OsrPE...
    { eapply (BetPs_inv E P' P'' O F )...
	    { apply SR_sym. apply BetPs_SR.
        eapply BetPs_SR_BetPs... apply BetPs_sym...
      }
      destruct For'...
      assert (nEeqF : E <> F).
      { eapply EqSgs_DiPs. apply BetPs_DiPs_3 in A'B'C'.
        apply A'B'C'... apply H2.
      }
      destruct H0; contradiction.
    }
    assert (nOeqE : O <> E).
    { eapply EqSgs_DiPs. apply BetPs_DiPs_1 in A'B'C'.
      apply A'B'C'... apply H1.
    }
    apply not_eq_sym in nOeqP. destruct H; contradiction.
  }
  { subst B'. rewrite H2. symmetry in H1.
    apply EqSgs_EqPs in H1. subst E...
  }
  { destruct OsrPE.
    { assert (nA'eqB' : A' <> B').
      { eapply EqSgs_DiPs. apply SR_DiPs_2 in H.
        apply H... rewrite H1...
      }
      { subst C'. rewrite H1. symmetry in H2.
        apply EqSgs_EqPs in H2. subst F...
      }
    }
    { subst C'. rewrite H1. symmetry in H2.
        apply EqSgs_EqPs in H2. subst F...
    }
  }
Defined.

Definition PlusS : Length -> Length -> Length
  := fun a b : Length => proj1_sig (PlusLengthDef a b).
Notation " a ++ b "
  := (PlusS a b).

(** Theorem #46 *)
Theorem BetPs_PlusS :
  forall A B C : Point,
  [ A ; B ; C ]
    -> [| A, B |] ++ [| B, C |] = [| A, C |].
Proof with eauto.
  unfold PlusS.
  intros A' B' C' BetA'B'C'.
  elim (proj2_sig (PlusLengthDef ([|A', B'|]) ([|B', C'|])) A' B' C')...
Qed.

(** Theorem #47 *)
Theorem PlusS_0_l :
  forall a : Length,
  L0 ++ a = a.
Proof with eauto.
  unfold PlusS.
  intros a.
  destruct (DrawSegment a) as [[ A B ] ABeqAB ]. subst a.
  elim (proj2_sig (PlusLengthDef L0 ([|A, B|])) A A B)...
  eapply (proj2_sig NullSeg)...
Qed.
Theorem PlusS_0_r :
  forall a : Length,
  a ++ L0 = a.
Proof with eauto.
  unfold PlusS.
  intros a.
  destruct (DrawSegment a) as [[ A B ] ABeqAB ]. subst a.
  elim (proj2_sig (PlusLengthDef ([|A, B|]) L0) A B B)...
  eapply (proj2_sig NullSeg)...
Qed.
Theorem PlusS_comm :
  forall a b : Length,
  a ++ b = b ++ a.
Proof with betps.
  intros a b.
  destruct (DrawSegment a) as [[ A B ] ABeqAB ]. subst a.
  destruct (DrawSegment b) as [[ B' C' ] B'C'eqBC ]. subst b.
  destruct (classic (A = B)) as [ AeqB | nAeqB ].
  { apply EqPs_NullSeg in AeqB. rewrite AeqB.
    rewrite PlusS_0_l. rewrite PlusS_0_r; auto.
  }
  { destruct (classic (B' = C')) as [ BeqC | nBeqC ].
    { apply EqPs_NullSeg in BeqC. rewrite BeqC.
      rewrite PlusS_0_l. rewrite PlusS_0_r; auto.
    }
    { destruct (DrawSegmentExtension A B nAeqB) as [ P BetABP ].
      assert (nBeqP : B <> P). { apply (BetPs_3DiPs A B P BetABP). }
      destruct (DrawSegmentOnRay B P B' C')
        as [ C [[ BsrPC |[ BeqP | BeqC ]] BCeqB'C' ]]...
      { assert (BetABC : [ A # B # C ])...
        remember ([|A, B|] ++ [|B', C'|]) as AC.
        rewrite HeqAC.
        assert (ACeqAC : [|A, C|] = AC).
        { assert (ABpBCeqAC : [| A, B |] ++ [| B, C |] = [| A, C |]).
          { apply (BetPs_PlusS A B C); left... }
          rewrite BCeqB'C' in ABpBCeqAC.
          rewrite <- HeqAC in ABpBCeqAC...
        }
        apply (BetPs_sym A B C) in BetABC.
        assert (CBpBAeqCA : [| C, B |] ++ [| B, A |] = [| C, A |]).
        { apply (BetPs_PlusS C B A); left... }
        assert (BCeqCB : [| B, C |] = [| C, B |]). { apply (SegPs_sym B C). }
        rewrite <- BCeqCB in CBpBAeqCA.
        rewrite BCeqB'C' in CBpBAeqCA.
        assert (ABeqBA : [| A, B |] = [| B, A |]). { apply (SegPs_sym A B). }
        rewrite <- ABeqBA in CBpBAeqCA.
        rewrite CBpBAeqCA.
        assert (ACeqCA : [| A, C |] = [| C, A |]). { apply (SegPs_sym A C). }
        rewrite <- ACeqCA. rewrite ACeqAC. auto.
      }
      { apply EqPs_NullSeg in BeqC.
        rewrite BeqC in *. symmetry in BCeqB'C'.
        apply NullSeg_EqPs in BCeqB'C'. contradiction.
      }
    }
  }
Qed.
Theorem PlusS_assoc :
  forall a b c : Length,
  a ++ (b ++ c) = (a ++ b) ++ c.
Proof with eauto.
  intros a b c.
  destruct (DrawSegment a) as [[ A B ] ABeqAB ].
  destruct (DrawSegment b) as [[ B' C' ] BCeqBC ].
  destruct (DrawSegment c) as [[ C'' D'' ] CDeqCD ].
  subst.
  destruct (classic (A = B)) as [ AeqB | nAeqB ].
  { apply EqPs_NullSeg in AeqB. rewrite AeqB.
    rewrite PlusS_0_l. rewrite PlusS_0_l...
  }
  { destruct (classic (B' = C')) as [ B'eqC' | nB'eqC' ].
    { apply EqPs_NullSeg in B'eqC'. rewrite B'eqC'.
      rewrite PlusS_0_r. rewrite PlusS_0_l...
    }
    { destruct (classic (C'' = D'')) as [ C''eqD'' | nC''eqD'' ].
      { apply EqPs_NullSeg in C''eqD''. rewrite C''eqD''.
        rewrite PlusS_0_r. rewrite PlusS_0_r...
      }
      { destruct (DrawSegmentExtension A B nAeqB) as [ P BetABP ].
        assert (nBeqP : B <> P). { apply (BetPs_3DiPs A B P BetABP). }
        destruct (DrawSegmentOnRay B P B' C')
          as [ C [[ BsrPC |[ BeqP | BeqC ]] BCeqBC ]]...
        { assert (BetABC : [ A # B # C ]).
          { apply (BetPs_SR_BetPs B A P C)... }
          assert (ABpBCeqAC : [| A, B |] ++ [| B, C |] = [| A, C |]).
          { apply (BetPs_PlusS A B C); left... }
          rewrite <- BCeqBC. rewrite ABpBCeqAC.
          assert (nBeqC : B <> C).
          { apply (BetPs_3DiPs A B C) in BetABC. tauto. }
          destruct (DrawSegmentExtension B C nBeqC) as [ P' BetBCP' ].
          assert (nCeqP' : C <> P'). { apply (BetPs_3DiPs B C P' BetBCP'). }
          destruct (DrawSegmentOnRay C P' C'' D'')
            as [ D [[ CsrP'D |[ CeqP | CeqD ]] CDeqCD ]]...
          { assert (BetBCD : [ B # C # D ]).
            { apply (BetPs_SR_BetPs C B P' D)... }
            assert (BCpCDeqBD : [| B, C |] ++ [| C, D |] = [| B, D |]).
            { apply (BetPs_PlusS B C D); left... }
            rewrite <- CDeqCD. rewrite BCpCDeqBD.
            destruct (BetPs_b_trans A B C D) as [ _ [ BetABD [ BetACD _ ]]]...
            assert (ACpCDeqAD : [| A, C |] ++ [| C, D |] = [| A, D |]).
            { apply (BetPs_PlusS A C D)... }
            rewrite CDeqCD in ACpCDeqAD. rewrite CDeqCD.
            rewrite ACpCDeqAD.
            assert (ABpBDeqAD : [| A, B |] ++ [| B, D |] = [| A, D |]).
            { apply (BetPs_PlusS A B D). auto. }
            auto.
          }
          { contradiction. }
          { apply EqPs_NullSeg in CeqD.
            rewrite CeqD in *. symmetry in CDeqCD.
            apply NullSeg_EqPs in CDeqCD. contradiction.
          }
        }
        { contradiction. }
        { apply EqPs_NullSeg in BeqC.
          rewrite BeqC in *. symmetry in BCeqBC.
          apply NullSeg_EqPs in BCeqBC. contradiction.
        }
      }
    }
  }
Qed.
Theorem PlusS_cancel_l :
  forall a b c : Length,
  a ++ b = a ++ c
    -> b = c.
Proof with eauto.
  intros a b c.
  destruct (DrawSegment a) as [[ A B ] ABeqAB ].
  destruct (DrawSegment b) as [[ B' C' ] BCeqBC ].
  destruct (DrawSegment c) as [[ C'' D'' ] CDeqCD ].
  subst.
  destruct (classic (A = B)) as [ AeqB | nAeqB ].
  { apply EqPs_NullSeg in AeqB. rewrite AeqB.
    rewrite PlusS_0_l. rewrite PlusS_0_l...
  }
  { destruct (classic (B' = C')) as [ B'eqC' | nB'eqC' ].
    { apply EqPs_NullSeg in B'eqC'.
      rewrite B'eqC'.
      rewrite PlusS_0_r.
      intros ABeqABpCD.
      destruct (classic (C'' = D'')) as [ C''eqD'' | nC''eqD'' ].
      { apply EqPs_NullSeg in C''eqD''. auto. }
      { destruct (DrawAdditionalSegment A B C'' D'')
          as [ C [ BetABC BCeqCD ]]...
        contradict nC''eqD''.
        apply NullSeg_EqPs; auto.
        rewrite <- BCeqCD in *.
        assert (ABeqAC : [| A, B |] = [| A, C |]).
        { rewrite ABeqABpCD. apply (BetPs_PlusS A B C); left... }
        assert (BeqC : B = C).
        { apply (SR_EqSgs_EqPs A B C)...
          left.
          apply (BetPs_SR A B C)...
        }
        apply (EqPs_NullSeg B C)...
      }
    }
    { destruct (classic (C'' = D'')) as [ C''eqD'' | nC''eqD'' ].
      { apply EqPs_NullSeg in C''eqD''.
        rewrite C''eqD'' in *.
        rewrite PlusS_0_r.
        intros ABpBCeqAB.
        destruct (DrawAdditionalSegment A B B' C')
          as [ C [ BetABC BCeqCD ]]...
        contradict nB'eqC'.
        apply NullSeg_EqPs; auto.
        rewrite <- BCeqCD in *.
        assert (ABeqAC : [| A, B |] = [| A, C |]).
        { rewrite <- ABpBCeqAB. apply (BetPs_PlusS A B C); left... }
        assert (BeqC : B = C).
        { apply (SR_EqSgs_EqPs A B C); auto.
          left.
          apply (BetPs_SR A B C); auto.
        }
        apply (EqPs_NullSeg B C); auto.
      }
      destruct (DrawAdditionalSegment A B B' C')
        as [ C [ Cor BCeqBC ]]... destruct BCeqBC.
      destruct (DrawAdditionalSegment A B C'' D'')
        as [ D [ Dor BDeqBD ]]... destruct BDeqBD.
      intros ABpBCeqABpBD.
      assert (ACeqAD : [| A, C |] = [| A, D |]).
      { rewrite <- (BetPs_PlusS A B C); auto.
        rewrite <- (BetPs_PlusS A B D); auto.
      }
      assert (CeqD : C = D).
      { apply (SR_EqSgs_EqPs A C D); auto.
        apply (BetPs_SR A B C) in Cor.
        apply (BetPs_SR A B D) in Dor.
        destruct Cor as [ Cor _ ].
        apply (SR_sym A B C) in Cor.
        left.
        apply (SR_trans A C B D); auto.
        destruct Dor as [ Dor _ ]; auto.
      }
      destruct CeqD. auto.
    }
  }
Qed.
Theorem PlusS_cancel_r :
  forall a b c : Length,
  a ++ c = b ++ c
    -> a = b.
Proof with eauto.
  intros AB CD BC.
  rewrite (PlusS_comm AB BC).
  rewrite (PlusS_comm CD BC).
  apply PlusS_cancel_l.
Qed.

Lemma PlusS_EqSgs :
  forall a b : Length,
  a ++ b = a
    -> b = L0.
Proof.
  intros AB BC ABpBCeqAB.
  apply (PlusS_cancel_l AB BC L0).
  rewrite ABpBCeqAB. symmetry.
  apply PlusS_0_r.
Qed.

Lemma PlusS_EqL0 :
  forall a b : Length,
  a ++ b = L0
    -> a = L0 /\ b = L0.
Proof with eauto.
  intros a b ABpBCeqL0.
  destruct (DrawSegment a) as [[ A B ] ABeqAB ]; subst.
  destruct (DrawSegment b) as [[ D E ] DEeqDE ]; subst.
  destruct (classic ([|A, B|] = L0)) as [ ABeqL0 | nABeqL0 ].
  { rewrite ABeqL0 in *.
    split; auto.
    rewrite PlusS_0_l in ABpBCeqL0...
  }
  { assert (nAeqB : A <> B).
    { contradict nABeqL0; subst. apply NullSeg_def. }
    destruct (DrawSegmentExtension A B nAeqB) as [ C' BetABC' ].
    assert (nBeqC' : B <> C'). { apply (BetPs_3DiPs A B C' BetABC'). }
    destruct (DrawSegmentOnRay B C' D E nBeqC')
      as [ C [[ BsrC'C |[ BeqC | BeqC ]] BCeqDE ]]; subst.
    { assert (BetABC : [ A # B # C ]). { apply (BetPs_SR_BetPs B A C' C)... }
      assert (ABpBCeqAC : [|A, B|] ++ [|B, C|] = [|A, C|]).
      { apply BetPs_PlusS... }
      rewrite BCeqDE in ABpBCeqAC.
      rewrite ABpBCeqL0 in ABpBCeqAC.
      symmetry in ABpBCeqAC.
      apply NullSeg_EqPs in ABpBCeqAC; subst.
      destruct (BetPs_3DiPs C B C) as [ _ [ _ nAeqA ]]...
      contradiction.
    }
    { contradiction. }
    { contradict nABeqL0; subst. destruct BCeqDE.
      rewrite NullSeg_def in ABpBCeqL0.
      rewrite PlusS_0_r in ABpBCeqL0...
    }
  }
Qed.

Lemma Bet4Ps_PlusS :
  forall A B C D : Point,
  [ A # B # C # D ]
    -> [| A, B |] ++ [| B, C |] ++ [| C, D |] = [| A, D |].
Proof with eauto.
  intros * [ ABC [ ABD [ ACD BCD ]]].
  assert (ABpBC : [|A, B|] ++ [|B, C|] = [|A, C|]).
  { apply BetPs_PlusS; left... }
  rewrite PlusS_assoc. rewrite ABpBC.
  apply BetPs_PlusS; left...
Qed.

(** Problem #30 *)
(** Euclid, Book I : Proposition 3. *)
(* Given two unequal straight lines, to cut off from the greater
  a straight line equal to the less. *)
Definition DrawSubtractionOfTwoSegments :
  forall a b : Length,
  a << b
    -> { c : Length | c <> L0 /\ a ++ c = b }.
Proof with eauto.
  intros a b H.
  assert (nbeqL0 : b <> L0).
  { intros beqL0. subst. apply (LtS_positive a)... }
  destruct (DrawSegment a) as [[ A' B' ] ABeqAB ]; subst.
  destruct (DrawSegment b) as [[ A C ] ACeqAC ]; subst.
  assert (nAeqC : A <> C); subst; dips.
  destruct (DrawSegmentOnRay A C A' B') as [ B [ AsrCB ABeqAB ]]...
  exists ([| B, C |]). rewrite <- ABeqAB in *.
  assert (ABC : [A ; B ; C]).
  { destruct AsrCB as [ AsrCB |[ AeqC | AeqB ]]; try contradiction...
    left. eapply LtS_SR_BetPs... apply SR_sym...
  }
  split.
  { intros BeqC.
    apply NullSeg_EqPs in BeqC; subst.
    apply (LtS_irrefl ([|A, C|])); auto.
  }
  { apply BetPs_PlusS... }
Defined.
Lemma PlusS_LtS :
  forall a b : Length,
  b <> L0
    -> a << a ++ b.
Proof with eauto.
  intros a b H.
  destruct (classic (a = L0)) as [ aeqL0 | naeqL0 ]; subst.
  { apply DiSgs_PosSgs... rewrite PlusS_0_l... }
  { destruct (DrawSegment a) as [[ A B ] ABeqAB ]; subst.
    assert (nAeqB : A <> B); dips.
    destruct (DrawSegment b) as [[ B' C' ] B'C'eqB'C' ]; subst.
    destruct (DrawAdditionalSegment A B B' C' nAeqB)
      as [ C [ BetABC BCeqBC ]]; dips.
    destruct (BetPs_3DiPs A B C BetABC) as [ _ [ nBeqC nAeqC ]].
    assert (ACeqAC : [| A, C |] = [|A, B|] ++ [|B, C|]).
    { symmetry. apply (BetPs_PlusS A B C); left... }
    rewrite <- BCeqBC in *. clear dependent B'.
    destruct (LtS_trichotomy ([|A, B|])([|A, B|] ++ [|B, C|]))
      as [ ABltAC |[ ABeqAC | ABgtAC ]]...
    { rewrite <- ABeqAC in *.
      assert (BeqC : B = C).
      { apply (SR_EqSgs_EqPs A B C)... left; betps. }
      contradiction.
    }
    { rewrite <- ACeqAC in ABgtAC .
      assert (BetACB : [A # C # B]).
      { apply LtS_SR_BetPs; colps. apply SR_sym.
        apply BetPs_SR in BetABC. destruct BetABC...
      }
      apply BetPs_nBetPerPs_2 in BetACB. contradiction.
    }
  }
Qed.

(** Theorem #48 *)
Theorem LtS_PlusLtS :
  forall a b c : Length,
  a << b
    <-> a ++ c << b ++ c.
Proof with eauto.
  intros a b c.
  split.
  { intros ab.
    destruct (DrawSubtractionOfTwoSegments a b ab) as [ x [ Hx xL0 ]].
    rewrite (PlusS_comm b c). rewrite (PlusS_comm a c).
    rewrite <- xL0. rewrite PlusS_assoc.
    apply (PlusS_LtS (c ++ a) x)...
  }
  { intros abc.
    destruct (DrawSubtractionOfTwoSegments (a ++ c) (b ++ c) abc)
      as [ x [ H0 H1 ]].
    cut (a ++ x = b).
    { intros H3. rewrite <- H3. apply (PlusS_LtS a x)... }
    rewrite PlusS_comm in H1. rewrite PlusS_assoc in H1.
    rewrite PlusS_comm. rewrite PlusS_comm in H1. symmetry in H1.
    rewrite PlusS_comm in H1. apply PlusS_cancel_l in H1. symmetry...
  }
Qed.

Lemma SR_PlusS_BetPs :
  forall A B C D E : Point,
  [ A ; B, C ]
    -> [| A, B |] ++ [| D, E |] = [| A, C |]
    -> [ A ; B ; C ].
Proof with eauto.
  intros A B C D E AsrBC H.
  destruct (classic (D = E)) as [ DeqE | nDeqE ].
  { subst E. right; right. rewrite NullSeg_def in H.
    rewrite PlusS_0_r in H.
    destruct AsrBC as [ AsrBC |[ AeqB | BeqC ]]; subst.
    { apply (SR_EqSgs_EqPs A B C)... }
    { symmetry in H. apply EqSgs_EqPs in H... }
    { apply EqSgs_EqPs in H... }
  }
  { assert (ABltAC : [|A, B|] << [|A, C|]).
    { rewrite <- H.
      apply (PlusS_LtS ([|A, B|])([|D, E|]))...
      contradict nDeqE. apply NullSeg_EqPs...
    }
    destruct AsrBC as [ AsrBC |[ AeqB | BeqC ]]; subst...
    { left. apply LtS_SR_BetPs... }
    { exfalso. rewrite NullSeg_def in ABltAC. apply LtS_positive in ABltAC... }
  }
Qed.

Lemma LtS_LtS_PlusLtS :
  forall a b c d : Length,
  a << b
    -> c << d
    -> a ++ c << b ++ d.
Proof.
  intros a b c d altb cltd.
  assert (bcd : c ++ b << d ++ b). { apply LtS_PlusLtS; auto. }
  assert (cab : a ++ c << b ++ c). { apply LtS_PlusLtS; auto. }
  rewrite (PlusS_comm c b) in bcd. rewrite (PlusS_comm d b) in bcd.
  apply (LtS_trans (a ++ c)(b ++ c)(b ++ d)); auto.
Qed.

Definition PlusS_ext :
  forall ( a b c d : Length ),
  a ++ b <> c ++ d
    -> { a <> c } + { b <> d }.
Proof.
  intros * H.
  cut ({( a ++ b ) <> ( a ++ d )} + {( a ++ d ) <> ( c ++ d )}).
  { intro H0.
    destruct H0 as [ H1 | H2 ].
    { right. intro su; subst; contradict H1; subst; auto. }
    { left. intro rt; subst; contradict H2; subst; auto. }
  }
  destruct (DecideDistinctSegments (a ++ b)(c ++ d)(a ++ d)); auto.
Defined.

End SEGMENT_ADDITION.

Notation " a ++ b "
  := (PlusS a b).

(*****************************************************************************)
(* 15 *) Section SUPERPOSITION.
Context `{ cc : Concentricals }.
Context  { an : Angles on }.
Context  { sp : Superpositions on }.
(*****************************************************************************)

Lemma ExistsEqualTriangle :
  forall (A B C D E F : Point)
         (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  exists (E' F' : Point)(nColDE'F' : ~ [ D, E', F' ]),
    [ D # E, E' ] /\ [ D # E | F, F' ] /\
    {{ A # B # C | nColABC }} :=: {{ D # E' # F' | nColDE'F' }}.
Proof with eauto.
  intros A B C D E F nColABC nColDEF.
  destruct (nColPs_3DiPs A B C nColABC) as [ nAeqB [ nBeqC nAeqC ]].
  destruct (nColPs_3DiPs D E F nColDEF) as [ nDeqE [ nEeqF nDeqF ]].
  destruct (DrawSegmentOnRay D E A B) as [ E' [ DsrEE' ABeqDE ]]...
  symmetry in ABeqDE.
  assert (nColDE'F : ~ [ D, E', F ]).
  { contradict nColDEF.
    destruct DsrEE' as [[ _ [ nDeqE' [ ColDEE' _ ]]]|[ DeqE | DeqE' ]].
    { destruct nColDEF as [ t [ H1 [ H2 H3 ]]]. repeat split; incpt. }
    { subst E. contradiction. }
    { subst E'. contradict nAeqB. symmetry. eapply EqSgs_EqPs... }
  }
  destruct (SuperpositionPrinciple A B C D E' F nColABC nColDE'F)
    as [ F' [ nColDE'F' [ H2 H3 ]]]...
  exists E', F', nColDE'F'.
  destruct DsrEE' as [ DsrEE' |[ DeqE | DeqE' ]].
  { split... split...
    apply (SHa_inv D E' F F' E F F'); try apply SR_refl; dips. colperps.
  }
  { subst E. contradiction. }
  { contradict DeqE'. apply (nColPs_3DiPs D F' E'); ncolperps. }
Qed.

(** Theorem #49 *)
(** Hilbert, Chapter 1 : Theorem 12. *)
(** Euclid, Book I : Proposition 4. *)
(* If two triangles have two sides equal to two sides respectively,
 and have the angles contained by the equal sides also equal,
 then the two triangles are congruent. *)
Theorem SAS :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  [| A, B |] = [| D, E |]
    -> [| B, C |] = [| E, F |]
    -> [| A # B # C | nColABC |] = [| D # E # F | nColDEF |]
    -> {{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }}.
Proof with eauto.
  intros A B C D E F nColABC nColDEF ABeqDE BCeqEF ABCeqDEF.
  destruct (ExistsEqualTriangle A B C D E F nColABC nColDEF)
    as [ E' [ F' [ nColDE'F' [ DsrEE' [ DEeqFF' EqTr ]]]]].
  assert (EeqE' : E = E').
  { apply (SR_EqSgs_EqPs D E E')...
    destruct EqTr as [ H1 _ ]; simpl in *. rewrite <- H1...
  }
  subst E'.
  assert (EsrFF' : [ E # F, F' ]).
  { apply (SH_EqConvexAs_SR D E F F' nColDEF nColDE'F')...
    apply SHa_sym... rewrite <- ABCeqDEF.
    destruct EqTr as [ _ [ _ [ _ [ H2 _ ]]]]; simpl in *...
  }
  assert (EFeqEF' : [| E, F |] = [| E, F' |]).
  { destruct EqTr as [ _ [ H2 _ ]]; simpl in *. rewrite <- H2... }
  assert (FeqF' : F = F'). { apply (SR_EqSgs_EqPs E F F')... }
  subst F'... pir nColDE'F' => nColDEF.
Qed.

(** Theorem #50 *)
(** Hilbert, Chapter 1 : Theorem 13. *)
(** Euclid, Book I : Proposition 26. *)
(** --- only ASA part, AAS will be proved later --- *)
(* If two triangles have two angles equal to two angles respectively,
 and one side equal to one side, namely, either the side adjoining
 the equal angles, then the remaining sides equal the remaining
 sides and the remaining angle equals the remaining angle. *)
Theorem ASA :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  [| A, C |] = [| D, F |]
  -> [| B # C # A | nColPerPs_1 A B C nColABC |]
    = [| E # F # D | nColPerPs_1 D E F nColDEF |]
  -> [| C # A # B | nColPerPs_2 A B C nColABC |]
    = [| F # D # E | nColPerPs_2 D E F nColDEF |]
  -> {{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }}.
Proof with eauto.
  intros A B C D E F nColABC nColDEF ACeqDF BCAeqEFD CABeqFDE.
  assert (nAeqB : A <> B).
  { apply not_eq_sym. apply (nColPs_3DiPs A B C nColABC). }
  assert (nDeqE : D <> E).
  { apply not_eq_sym. apply (nColPs_3DiPs D E F nColDEF). }
  destruct (DrawSegmentOnRay A B D E nAeqB)
    as [ B' [[ AsrBB' |[ AeqB | AeqB' ]] AB'eqDE ]].
  { assert (nAeqB' : A <> B'). dips.
    assert (nColAB'C : ~ [ A, B', C ]).
    { clear BCAeqEFD CABeqFDE. contradict nColABC.
      destruct AsrBB' as [ _ [ _ [[ x [ Aox [ Box B'ox ]]] _ ]]].
      exists x. repeat split...
      apply (ColPs_IncPt A B' C x); try split; inc.
    }
    assert (trABCeqDEF' :
      {{ A # B' # C | nColAB'C }} :=: {{ D # E # F | nColDEF }}).
    { assert (ABCeqABC' :
      [| C # A # B | nColPerPs_2 A B C nColABC |]
        = [| C # A # B' | nColPerPs_2 A B' C nColAB'C |]).
     { erewrite (ConvexAngPs_inv C A B C B')... apply SR_refl; dips. }
       assert ({{C # A # B' | nColPerPs_2 A B' C nColAB'C}}
         :=: {{F # D # E | nColPerPs_2 D E F nColDEF}}).
       { eapply (SAS C A B' F D E)...
         rewrite SegPs_sym; symmetry; rewrite SegPs_sym...
         rewrite <- ABCeqABC'...
       }
       apply EqPerTr_1 in H.
       pir (nColPerPs_1 C A B' (nColPerPs_2 A B' C nColAB'C))
         => nColAB'C.
       pir (nColPerPs_1 F D E (nColPerPs_2 D E F nColDEF))
         => nColDEF.
    }
    unfold EqTriangle in trABCeqDEF'; simpl in *.
    destruct trABCeqDEF'
      as [ _ [ B'CeqEF [ CAeqFD [ AB'CeqDEF [ B'CAeqEFD CAB'eqFDE ]]]]].
    assert (ACsfBB' : [ A # C | B, B' ]). { apply SR_SH; ncolperps. }
    assert (ACBeqACB'' : [| A # C # B | nColPerPs_4 A B C nColABC |]
      = [| A # C # B' | nColPerPs_4 A B' C nColAB'C |]).
    { erewrite (ConvexAngPs_sym A C B (nColPerPs_4 A B C nColABC)).
      symmetry.
      pir (nColPerPs_5 A C B (nColPerPs_4 A B C nColABC))
        => (nColPerPs_1 A B C nColABC).
      erewrite (ConvexAngPs_sym A C B' (nColPerPs_4 A B' C nColAB'C)).
      pir (nColPerPs_5 A C B' (nColPerPs_4 A B' C nColAB'C))
        => (nColPerPs_1 A B' C nColAB'C).
      rewrite BCAeqEFD. rewrite B'CAeqEFD...
    }
    assert (CsrBB' : [C # B, B']).
    { apply (SH_EqConvexAs_SR A C B B'
      (nColPerPs_4 A B C nColABC)
      (nColPerPs_4 A B' C nColAB'C))...
      apply SHa_sym...
    }
    destruct (AsrBB') as [ _ [ _ [[ x [ Aox [ Box B'ox ]]] _ ]]].
    destruct (CsrBB') as [ _ [ _ [[ y [ Coy [ Boy B'oy ]]] _ ]]].
    assert (nxeqy : x <> y).
    { clear BCAeqEFD CABeqFDE ACBeqACB''.
      contradict nColABC. destruct nColABC. exists x; tauto.
    }
    assert (BeqB' : B = B').
    { apply (DiLs_EqPs B B' x y nxeqy); split; split... }
    subst B'.
    unfold EqTriangle; simpl; repeat split...
    pir nColAB'C => nColABC.
  }
  { subst B. contradiction. }
  { subst B'. symmetry in AB'eqDE. apply EqSgs_EqPs in AB'eqDE.
    contradiction.
  }
Qed.

(** Theorem #51 *)
(** Hilbert, Chapter 1 : Theorem 11. *)
(** Euclid, Book I : Proposition 5. *)
(* In isosceles triangles the angles at the base equal one another,
 and, if the equal straight lines are produced further,
 then the angles under the base equal one another. *)
Theorem IsoscelesTr_EqConvexAs :
  forall (A B C : Point)(nColABC : ~ [ A, B, C ])(nColACB : ~ [ A, C, B ]),
  [| A, B |] = [| A, C |]
    -> [| A # B # C | nColABC |] = [| A # C # B | nColACB |].
Proof with eauto.
  intros A B C nColABC nColACB ABeqAC.
  assert (EqTr : {{ B # A # C | (nColPerPs_3 A B C nColABC) }}
      :=: {{ C # A # B | (nColPerPs_3 A C B nColACB) }}).
  { apply (SAS B A C C A B)...
  { rewrite SegPs_sym. symmetry. rewrite SegPs_sym... }
    erewrite ConvexAngPs_sym.
    pir ( nColPerPs_5 B A C (nColPerPs_3 A B C nColABC))
      => (nColPerPs_3 A C B nColACB).
  }
  destruct EqTr as [ _ [ _ [ _ [ _ [ H _ ]]]]]. simpl in *.
  pir (nColPerPs_1 C A B (nColPerPs_3 A C B nColACB)) => nColABC.
  pir (nColPerPs_1 B A C (nColPerPs_3 A B C nColABC)) => nColACB.
Qed.

(** Theorem #52 *)
(** Hilbert, Chapter 1 : Theorem 24. *)
(** Euclid, Book I : Proposition 6. *)
(* If in a triangle two angles be equal to one another,
 the sides which subtend the equal angles will also be
 equal to one another. *)
Theorem EqConvexAs_IsoscelesTr :
  forall (A B C : Point)(nColABC : ~ [ A, B, C ])(nColACB : ~ [ A, C, B ]),
  [| A # B # C | nColABC |] = [| A # C # B | nColACB |]
    -> [| A, B |] = [| A, C |].
Proof.
  intros A B C nColABC nColACB ABCeqACB.
  assert (EqTr : {{ B # A # C | (nColPerPs_3 A B C nColABC) }}
    :=: {{ C # A # B | (nColPerPs_3 A C B nColACB) }}).
  { eapply (ASA B A C C A B).
    { apply SegPs_sym. }
    { pir (nColPerPs_1 B A C (nColPerPs_3 A B C nColABC))
        => nColACB.
      pir (nColPerPs_1 C A B (nColPerPs_3 A C B nColACB))
        => nColABC.
    }
    { erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
      pir (nColPerPs_5 B C A (nColPerPs_2 C A B
        (nColPerPs_3 A C B nColACB))) => nColACB.
      pir (nColPerPs_5 C B A (nColPerPs_2 B A C
        (nColPerPs_3 A B C nColABC))) => nColABC.
      symmetry. apply ABCeqACB.
    }
  }
  rewrite SegPs_sym. symmetry. rewrite SegPs_sym.
  destruct EqTr; auto.
Qed.

(** Theorem #53 *)
(** Hilbert, Chapter 1 : Theorem 14. *)
(** Hartshorne, Proposition 9.2 *)
(* If angles AOB and BOC are supplementary, and if angles A'O'B' and B'O'C'
 are supplementary, and if AOB = A'O'B', then BOC = B'O'C' *)
Theorem EqSupConvexAngPs :
  forall (O A B C O' A' B' C' : Point)
    (nColAOB : ~ [ A, O, B ])(nColBOC : ~ [ B, O, C ])
    (nColA'O'B' : ~ [ A', O', B' ])(nColB'O'C' : ~ [ B', O', C' ]),
  [ A # O # C ]
    -> [ A' # O' # C' ]
    -> [| A # O # B | nColAOB |] = [| A' # O' # B' | nColA'O'B' |]
    -> [| B # O # C | nColBOC |] = [| B' # O' # C' | nColB'O'C' |].
Proof with eauto.
  intros * BetAOC BetA'O'C' AOB.
  destruct (nColPs_3DiPs A O B nColAOB)
    as [ nAeqO [ nBeqO nAeqB ]]. apply not_eq_sym in nBeqO.
  destruct (nColPs_3DiPs B O C nColBOC)
    as [ _ [ nCeqO nBeqC ]]. apply not_eq_sym in nCeqO.
  destruct (nColPs_3DiPs A' O' B' nColA'O'B')
    as [ nA'eqO' [ nB'eqO' nA'eqB' ]]. apply not_eq_sym in nB'eqO'.
  destruct (nColPs_3DiPs B' O' C' nColB'O'C')
    as [ _ [ nC'eqO' nB'eqC' ]]. apply not_eq_sym in nC'eqO'.
  destruct (DrawSegmentOnRay O A O' A') as [ A'' [ OsrAA'' OA ]]...
  destruct (DrawSegmentOnRay O B O' B') as [ B'' [ OsrBB'' OB ]]...
  destruct (DrawSegmentOnRay O C O' C') as [ C'' [ OsrCC'' OC ]]...
  destruct OsrAA'' as [ OsrAA'' |[ OeqA | OeqA'' ]]...
  { destruct OsrBB'' as [ OsrBB'' |[ OeqB | OeqB'' ]]...
    { destruct OsrCC'' as [ OsrCC'' |[ OeqC | OeqC'' ]]...
      { assert (nColAOB'' : ~ [ A'', O, B'' ]).
        { apply (nColPs_SR_inv O A B A'' B'')... }
        assert (nColBOC'' : ~ [ B'', O, C'' ]).
        { apply (nColPs_SR_inv O B C B'' C'')... }
        assert (BetAOC'' : [ A''# O # C'' ]).
        { apply (BetPs_inv O A C A'' C'')... }
        assert (AOB'' : [| A'' # O # B'' | nColAOB'' |]
          = [|A' # O' # B' | nColA'O'B'|]).
        { erewrite (ConvexAngPs_inv A'' O B'' A B); try apply SR_sym... }
        assert (BOC'' : [| B'' # O # C'' | nColBOC'' |]
          = [| B # O # C | nColBOC |]).
        { erewrite (ConvexAngPs_inv B'' O C'' B C); try apply SR_sym... }
        rewrite <- BOC''.
        clear dependent A. clear dependent B. clear dependent C.
        rename A'' into A. rename B'' into B. rename C'' into C.
        assert (TrAOB : {{ A#O#B | nColAOB'' }}
          :=: {{ A'#O'#B' | nColA'O'B' }}).
        { apply (SAS A O B A' O' B')... rewrite SegPs_sym. symmetry.
          rewrite SegPs_sym...
        }
        assert (AC : [| A, C |] = [| A', C' |]).
        { apply (BetPs_AddSgs A O C A' O' C' BetAOC'' BetA'O'C')...
          rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
        }
        assert (nAeqC : A <> C). { apply (BetPs_3DiPs A O C BetAOC''). }
        assert (nColBAC : ~ [ B, A, C ]).
        { clear TrAOB AOB''. contradict nColAOB''.
          apply BetPs_ColPs in BetAOC''. colperps.
        }
        assert (nA'eqC' : A' <> C').
        { apply (BetPs_3DiPs A' O' C' BetA'O'C'). }
        assert (nColB'A'C' : ~ [ B', A', C' ]).
        { clear TrAOB AOB''. contradict nColA'O'B'.
          apply BetPs_ColPs in BetA'O'C'. colperps.
        }
        assert (TrBAC : {{ B # A # C | nColBAC }}
          :=: {{ B' # A' # C' | nColB'A'C' }}).
        { unfold EqTriangle in TrAOB; simpl in *.
          apply SAS...
          { destruct TrAOB as [ _ [ _ [ H _ ]]]... }
          assert (nColBAO : ~ [ B, A, O ]); ncolperps.
          assert (nColB'A'O' : ~ [ B', A', O' ]); ncolperps.
          rewrite (ConvexAngPs_inv B A C B O nColBAC nColBAO).
          { rewrite (ConvexAngPs_inv B' A' C' B' O' nColB'A'C' nColB'A'O').
            { pir (nColPerPs_2 A O B nColAOB'') => nColBAO.
              pir (nColPerPs_2 A' O' B' nColA'O'B') => nColB'A'O'.
              destruct TrAOB as [ _ [ _ [ _ [ _ [ _ H ]]]]]...
            }
            apply SR_refl... apply SR_sym. apply BetPs_SR. apply BetPs_sym...
          }
          apply SR_refl...
          apply (nColPs_3DiPs A O B)...
          apply SR_sym. apply BetPs_SR. apply BetPs_sym...
        }
        assert (nColBCO : ~ [B, C, O]); ncolperps.
        assert (nColB'C'O' : ~ [B', C', O']); ncolperps.
        unfold EqTriangle in TrBAC. simpl in *.
        destruct TrBAC as [ _ [ _ [ H1 [ _ [ H2 _ ]]]]]...
        assert (TrBOC : {{ B # C # O | nColBCO }}
          :=: {{ B' # C' # O' | nColB'C'O' }}).
        { apply (SAS B C O B' C' O' nColBCO)...
          rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
          rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
          erewrite (ConvexAngPs_inv B C O B A); try apply SR_refl; dips.
          { erewrite (ConvexAngPs_inv B' C' O' B' A'); try apply SR_refl...
            { erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
              pir (nColPerPs_5 B C A (fun H : [B, C, A] => nColBAC
                (ColPerPs_5 C A B (ColPerPs_1 B C A H))))
                 => (nColPerPs_1 B A C nColBAC).
              pir (nColPerPs_5 B' C' A' (fun H : [B', C', A'] => nColB'A'C'
                (ColPerPs_5 C' A' B' (ColPerPs_1 B' C' A' H))))
                => (nColPerPs_1 B' A' C' nColB'A'C'). symmetry. apply H2.
            }
            apply BetPs_SR; auto.
          }
          apply BetPs_SR; auto.
        }
        unfold EqTriangle in TrBOC; simpl in *.
        destruct TrBOC as [ _ [ _ [ _ [ _ [ H _ ]]]]]...
        erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
        pir (nColPerPs_5 B' O' C' nColB'O'C')
          => (nColPerPs_1 B' C' O' nColB'C'O').
        pir (nColPerPs_5 B O C nColBOC'')
          => (nColPerPs_1 B C O nColBCO). symmetry. apply H.
      }
      { subst C. contradiction. }
      { subst C''. symmetry in OC. apply EqSgs_EqPs in OC.
      subst C'. contradict nC'eqO'...
      }
    }
    { subst B. contradiction. }
    { subst B''. symmetry in OB. apply EqSgs_EqPs in OB.
      subst B'. contradict nB'eqO'...
    }
  }
  { subst A. contradiction. }
  { subst A''. symmetry in OA. apply EqSgs_EqPs in OA.
    subst A'. contradict nA'eqO'...
  }
  Unshelve. ncolperps. ncolperps.
Qed.
Theorem EqSupConvexAngRs :
  forall (a b c a' b' c' : Ray)(diab : ![ a # b ])(dibc : ![ b # c ])
         (dia'b' : ![ a' # b' ])(dib'c' : ![ b' # c' ]),
  a == !c
    -> a' == !c'
    -> [| a # b | diab |] = [| a' # b' | dia'b' |]
    -> [| b # c | dibc |] = [| b' # c' | dib'c' |].
Proof with eauto.
  intros [ O A nOeqA ][ O' B nOeqB ][ O'' C nOeqC ].
  intros [ Q A' nOeqA' ][ Q' B' nOeqB' ][ Q'' C' nOeqC' ].
  intros [ roab diab ][ robc dibc ][ roa'b' dia'b' ][ rob'c' dib'c' ].
  intros aopc a'opc' ab. simpl in *.
  subst O'' O' Q'' Q'. rename Q into O'.
  erewrite (EqConvexAngRsPs B O C).
  erewrite (EqConvexAngRsPs B' O' C').
  erewrite (EqConvexAngRsPs A O B) in ab.
  erewrite (EqConvexAngRsPs A' O' B') in ab.
  eapply (EqSupConvexAngPs O A B C O' A' B' C')...
  { apply (OpRs_BetPs A O C nOeqA nOeqC)... }
  { apply (OpRs_BetPs A' O' C' nOeqA' nOeqC')... }
Qed.

(** Theorem #54 *)
(** Euclid, Book I : Proposition 14. *)
(* If with any straight line, and at a point on it, two straight lines
 not lying on the same side make the sum of the adjacent angles
 equal to two right angles, then the two straight lines are in a
 straight line with one another. *)
Theorem EqSupAngRs_BetRs :
  forall (a b c a' b' c' : Ray)(diab : ![ a # b ])(dibc : ![ b # c ])
    (dia'b' : ![ a' # b' ])(dib'c' : ![ b' # c' ]),
  a == !c
    -> [| a # b | diab |] = [| a' # b' | dia'b' |]
    -> [| b # c | dibc |] = [| b' # c' | dib'c' |]
    -> ![ b' # c', !a' ]
    -> a' == !c'.
Proof with eauto.
  intros * aopc ab bc a'b'c'.
  assert (roab : da a = da b). { destruct diab... }
  assert (robc : da b = da c). { destruct dibc... }
  assert (roa'b' : da a' = da b'). { destruct dia'b'... }
  assert (rob'c' : da b' = da c'). { destruct dib'c'... }
  assert (dib'a' : ![ b' # a' ]). { apply nColRs_sym... }
  assert (a'b'_b'a' : %[ a' # b' | dia'b'] = negb (%[ b' # a' | dib'a' ])).
  { apply (DiOsRs a' b' dia'b' dib'a'). }
  apply -> (OppositeSideRs_DiOs b' a' c' dib'a' dib'c') in a'b'c'.
  assert (a'b'_b'c' : %[ a' # b' | dia'b'] = %[ b' # c' | dib'c']).
  { induction (%[ a' # b' | dia'b']),
              (%[ b' # c' | dib'c']),
              (%[ b' # a' | dib'a'])...
  }
  assert (ab_bc : %[ a # b | diab ] = %[ b # c | dibc ]).
  { apply (OpRs_EqOs_Left a b c diab)... }
  destruct (DrawOpRay a') as [ c'' a'opc'' ].
  assert (dib'c'' : ![ b' # c'' ]).
  { apply (nColRs_inv b' (!a') c'' ).
    apply (nColOpRs_2 b' a'). apply nColRs_sym...
    apply OpRs_OpRs in a'opc''. rewrite a'opc''. symmetry.
    apply OpOpRs.
  }
  assert (b'c' : [|b' # c' | dib'c'|] = [|b' # c'' | dib'c''|]).
  { rewrite <- bc.
    apply (EqSupConvexAngRs a b c a' b' c'' diab dibc dia'b')...
    apply OpRs_OpRs in a'opc''...
  }
  assert (a'b'_b'c'' : %[ a' # b' | dia'b'] = %[ b' # c'' | dib'c'']).
  { apply (OpRs_EqOs_Left a' b' c'' dia'b').
    apply OpRs_OpRs in a'opc''...
  }
  rewrite a'b'_b'c' in a'b'_b'c''.
  apply SameSideRs_EqOs in a'b'_b'c''.
  assert (c'eqc'' : c' == c'').
  { apply -> (SameSideRs_EqConvexAs_EqRs b' c' c'')... }
  rewrite c'eqc''. apply OpRs_OpRs in a'opc''...
Qed.
Theorem EqSupAngPs_BetPs :
  forall (O A B C O' A' B' C' : Point)
    (nColAOB : ~ [ A, O, B ])(nColBOC : ~ [ B, O, C ])
    (nColA'O'B' : ~ [ A', O', B' ])(nColB'O'C' : ~ [ B', O', C' ]),
  [ A # O # C ]
    -> [| A # O # B | nColAOB |] = [| A' # O' # B' | nColA'O'B' |]
    -> [| B # O # C | nColBOC |] = [| B' # O' # C' | nColB'O'C' |]
    -> [ A' | O' # B' | C' ]
    -> [ A' # O' # C' ].
Proof with eauto.
  intros * BetAOC AOB BOC AOBC.
  destruct (nColPs_3DiPs A O B) as [ nAeqO [ nOeqB nAeqB ]]...
  destruct (nColPs_3DiPs A' O' B') as [ nA'eqO' [ nO'eqB' nA'eqB' ]]...
  destruct (nColPs_3DiPs B O C) as [ nBeqO [ nOeqC nBeqC ]]...
  destruct (nColPs_3DiPs B' O' C') as [ nB'eqO' [ nO'eqC' nB'eqC' ]]...
  erewrite <- (EqConvexAngRsPs A O B nAeqO nOeqB) in AOB.
  erewrite <- (EqConvexAngRsPs A' O' B' nA'eqO' nO'eqB') in AOB.
  erewrite <- (EqConvexAngRsPs B O C nOeqB nOeqC) in BOC.
  erewrite <- (EqConvexAngRsPs B' O' C' nO'eqB' nO'eqC') in BOC.
  rewrite <- (OpRs_BetPs A' O' C' nA'eqO' nO'eqC')...
  rewrite <- (OpRs_BetPs A O C nAeqO nOeqC) in BetAOC.
  eapply (EqSupAngRs_BetRs ({{ O # A | nAeqO }})({{ O # B | nOeqB }})
    ({{ O # C | nOeqC }})({{ O' # A' | nA'eqO' }})({{ O' # B' | nO'eqB'}})
    ({{ O' # C' | nO'eqC' }}))...
  apply OppositeSide_OpRs_SameSideRs; simpl...
Qed.

Lemma BR_AddConvexAngPs :
  forall (O A B C O' A' B' C' : Point)(nColAOB : ~ [ A, O, B ])
    (nColBOC : ~ [ B, O, C ])(nColAOC : ~ [ A, O, C ])
    (nColA'O'B' : ~ [ A', O', B' ])(nColB'O'C' : ~ [ B', O', C' ])
    (nColA'O'C' : ~ [ A', O', C' ]),
  [ O | A; B; C ]
    -> [ O' | A'; B'; C' ]
    -> [| A # O # B | nColAOB |] = [| A' # O' # B' | nColA'O'B' |]
    -> [| B # O # C | nColBOC |] = [| B' # O' # C' | nColB'O'C' |]
    -> [| A # O # C | nColAOC |] = [| A' # O' # C' | nColA'O'C' |].
Proof with eauto.
  intros * OoABC O'oA'B'C' AOBeqA'O'B' BOCeqB'O'C'.
  destruct (nColPs_3DiPs A O B nColAOB) as [ nAeqO [ nOeqB nAeqB ]].
  destruct (nColPs_3DiPs A O C nColAOC) as [ _ [ nOeqC nAeqC ]].
  destruct (DrawPointCrossBar O A B C OoABC)
    as [ B'' [ BetABC OsrBB'' ]].
  assert (nColAOB'' : ~ [ A, O, B'' ]).
  { apply (nColPs_SR_inv O A B A B''); betps. }
  assert (nColB''OC : ~ [ B'', O, C ]).
  { apply (nColPs_SR_inv O B C B'' C); betps. }
  assert (OoAB''C : [O | A; B''; C ]).
  { apply (BR_inv O A B C A B'' C); betps. }
  assert (AOBeqAOB'' : [|A#O#B'' | nColAOB''|]
    = [|A'#O'#B' | nColA'O'B'|]).
  { rewrite <- AOBeqA'O'B'. symmetry.
  apply (ConvexAngPs_inv A O B A B''); betps.
  }
  assert (BOCeqB''OC : [|B # O # C | nColBOC |]
    = [|B'' # O # C | nColB''OC|]).
  { apply (ConvexAngPs_inv B O C B'' C); betps. }
  symmetry in BOCeqB''OC.
  rewrite BOCeqB'O'C' in BOCeqB''OC.
  clear dependent B. rename B'' into B.
  rename nColAOB'' into nColAOB.
  destruct (DrawSegmentOnRay O' A' O A) as [ A'' [ H O'A'_OA ]]; dips.
  assert (O'_A'A : [O' # A', A'']).
  { destruct H as [ H1 |[ H2 | H3 ]]...
    { clear AOBeqAOB''. apply nColPs_DiPs_12 in nColA'O'B'.
      contradict nColA'O'B'...
    }
    { subst A''. symmetry in O'A'_OA. apply EqSgs_EqPs in O'A'_OA.
      subst A; contradiction.
    }
  }
  clear H.
  assert (nColA''O'C' : ~ [A'', O', C']).
  { apply (nColPs_SR_inv O' A' C' A'' C'); try apply SR_refl; dips. }
  assert (nColA''O'B' : ~ [A'', O', B']).
  { apply (nColPs_SR_inv O' A' B' A'' B'); try apply SR_refl; dips. }
  rewrite (ConvexAngPs_inv A' O' C' A'' C' nColA'O'C' nColA''O'C');
  try apply SR_refl; dips.
  rewrite (ConvexAngPs_inv A' O' B' A'' B' nColA'O'B' nColA''O'B')
    in AOBeqAOB''; try apply SR_refl; dips.
  apply (BR_inv O' A' B' C' A'' B' C') in O'oA'B'C';
  try apply SR_refl; dips.
  clear dependent A'. rename A'' into A'.
  rename nColB''OC into nColBOC.
  rename OoAB''C into OoABC.
  rename nColA''O'B' into nColA'O'B'.
  rename AOBeqAOB'' into AOBeqAOB.
  rename BOCeqB''OC into BOCeqBOC.
  rename nColA''O'C' into nColA'O'C'.
  destruct (nColPs_3DiPs A O B nColAOB) as [ _ [ nOeqB nAeqB ]].
  destruct (DrawSegmentOnRay O' B' O B) as [ B'' [ H O'B'_OB ]]; dips.
  assert (O'_B'B : [O' # B', B'']).
  { destruct H as [ H1 |[ H2 | H3 ]]...
    { clear BOCeqBOC. apply nColPs_DiPs_12 in nColB'O'C'.
      contradict nColB'O'C'...
    }
    { subst B''. symmetry in O'B'_OB. apply EqSgs_EqPs in O'B'_OB.
      subst B; contradiction.
    }
  }
  clear H.
  assert (nColB''O'C' : ~ [B'', O', C']).
  { apply (nColPs_SR_inv O' B' C' B'' C'); try apply SR_refl; dips. }
  assert (nColA'O'B'' : ~ [A', O', B'']).
  { apply (nColPs_SR_inv O' A' B' A' B''); try apply SR_refl; dips. }
  rewrite (ConvexAngPs_inv B' O' C' B'' C' nColB'O'C' nColB''O'C')
    in BOCeqBOC; try apply SR_refl; dips.
  rewrite (ConvexAngPs_inv A' O' B' A' B'' nColA'O'B' nColA'O'B'')
    in AOBeqAOB; try apply SR_refl; dips.
  apply (BR_inv O' A' B' C' A' B'' C') in O'oA'B'C';
  try apply SR_refl; dips.
  clear dependent B'. rename B'' into B'.
  rename nColA'O'B'' into nColA'O'B'.
  rename nColB''O'C' into nColB'O'C'.
  destruct (DrawSegmentOnRay O' C' O C)
    as [ C'' [ H O'C'_OC ]]; dips.
  assert (O'_C'C : [O' # C', C'']).
  { destruct H as [ H1 |[ H2 | H3 ]]...
    { clear BOCeqBOC. apply nColPs_DiPs_23 in nColB'O'C'.
      contradict nColB'O'C'...
    }
    { subst C''. symmetry in O'C'_OC. apply EqSgs_EqPs in O'C'_OC.
      subst C; contradiction.
    }
  }
  clear H.
  assert (nColB'O'C'' : ~ [B', O', C'']).
  { apply (nColPs_SR_inv O' B' C' B' C''); try apply SR_refl; dips. }
  assert (nColA'O'C'' : ~ [A', O', C'']).
  { apply (nColPs_SR_inv O' A' C' A' C''); try apply SR_refl; dips. }
  rewrite (ConvexAngPs_inv B' O' C' B' C'' nColB'O'C' nColB'O'C'')
    in BOCeqBOC; try apply SR_refl; dips.
  rewrite (ConvexAngPs_inv A' O' C' A' C'' nColA'O'C' nColA'O'C'');
  try apply SR_refl; dips.
  apply (BR_inv O' A' B' C' A' B' C'') in O'oA'B'C'; try apply SR_refl; dips.
  clear dependent C'. rename C'' into C'.
  rename nColA'O'C'' into nColA'O'C'.
  rename nColB'O'C'' into nColB'O'C'.
  assert (AOB : {{ A # O # B | nColAOB }}
    :=: {{ A' # O'# B' | nColA'O'B' }}).
  { apply SAS... rewrite SegPs_sym.
    symmetry. rewrite SegPs_sym...
  }
  assert (BOC : {{ B # O # C | nColBOC }}
    :=: {{ B' # O' # C' | nColB'O'C' }}).
  { apply SAS... rewrite SegPs_sym.
    symmetry. rewrite SegPs_sym...
  }
  assert(ABO : [|A # B # O | nColPerPs_4 A O B nColAOB|]
    = [|A' # B' # O' | nColPerPs_4 A' O' B' nColA'O'B'|]).
  { erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
    destruct AOB as [ _ [ _ [ _ [ _ [ H _ ]]]]]; simpl in *...
  }
  pir (nColPerPs_5 A B O (nColPerPs_4 A O B nColAOB))
    => (nColPerPs_1 A O B nColAOB).
  pir (nColPerPs_5 A' B' O' (nColPerPs_4 A' O' B' nColA'O'B'))
    => (nColPerPs_1 A' O' B' nColA'O'B').
  assert (OBC : [| O # B # C | nColPerPs_3 B O C nColBOC |]
    = [| O' # B' # C' | nColPerPs_3 B' O' C' nColB'O'C' |]).
  { erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
    destruct BOC as [ _ [ _ [ _ [ _ [ _ H ]]]]]; simpl in *...
  }
  pir (nColPerPs_5 O' B' C' (nColPerPs_3 B' O' C' nColB'O'C'))
    => (nColPerPs_2 B' O' C' nColB'O'C').
  pir (nColPerPs_5 O B C (nColPerPs_3 B O C nColBOC))
    => (nColPerPs_2 B O C nColBOC).
  assert (BetA'B'C' : [A' # B' # C']).
  { eapply (EqSupAngPs_BetPs B A O C B' A' O' C')...
    apply OHa_sym. apply BR_OH...
  }
  assert (EqTr : {{ O # A # C | nColPerPs_3 A O C nColAOC }}
    :=: {{ O' # A' # C' | nColPerPs_3 A' O' C' nColA'O'C' }}).
  { apply SAS...
  { apply (BetPs_AddSgs A B C A' B' C')...
    { destruct AOB as [ H1 [ H2 [ H3 _ ]]]; simpl in *.
      rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
    }
    destruct BOC as [ H1 [ H2 [ H3 _ ]]]; simpl in *.
    rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
  }
  erewrite (ConvexAngPs_inv O A C O B ); try apply SR_refl; dips.
  { symmetry.
    erewrite (ConvexAngPs_inv O' A' C' O' B'); try apply SR_refl; dips.
    { destruct AOB as [ _ [ _ [ _ [ _ [ _ H ]]]]]; simpl in *.
      erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym...
    }
    { apply SR_sym. apply BetPs_SR in BetA'B'C'. destruct BetA'B'C'... }
  }
  { apply SR_sym. apply BetPs_SR in BetABC. destruct BetABC... }
  }
  pir (nColPerPs_5 O A B (nColPerPs_4 O B A (fun H0 : [O, B, A] =>
    nColAOB (ColPerPs_5 B O A (ColPerPs_3 O B A H0)))))
    => (nColPerPs_2 A O B nColAOB).
  pir (nColPerPs_5 O' A' B' (nColPerPs_4 O' B' A' (fun H0 : [O', B', A'] =>
    nColA'O'B' (ColPerPs_5 B' O' A' (ColPerPs_3 O' B' A' H0)))))
    => (nColPerPs_2 A' O' B' nColA'O'B').
  destruct EqTr as [ _ [ _ [ _ [ _ [ _ H ]]]]]; simpl in *.
  erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym...
  Unshelve. ncolperps. ncolperps.
Qed.

Theorem BR_SubtConvexAngPs :
  forall (O A B C O' A' B' C' : Point)(nColAOB : ~ [ A, O, B ])
    (nColAOC : ~ [ A, O, C ])(nColBOC : ~ [ B, O, C ])
    (nColA'O'B' : ~ [ A', O', B' ])(nColA'O'C' : ~ [ A', O', C' ])
    (nColB'O'C' : ~ [ B', O', C' ]),
  [ O | A; B; C ]
    -> [ O' | A'; B'; C' ]
    -> [| A # O # B | nColAOB |] = [| A' # O' # B' | nColA'O'B' |]
    -> [| A # O # C | nColAOC |] = [| A' # O' # C' | nColA'O'C' |]
    -> [| B # O # C | nColBOC |] = [| B' # O' # C' | nColB'O'C' |].
Proof with try apply SR_refl; dips.
  intros * OoABC O'oA'B'C' AOBeqAOB AOCeqAOC.
  destruct (nColPs_3DiPs A O B nColAOB) as [ nAeqO [ nOeqB nAeqB ]].
  destruct (nColPs_3DiPs A O C nColAOC) as [ _ [ nOeqC nAeqC ]].
  destruct (DrawPointCrossBar O A B C OoABC)
    as [ B'' [ BetABC OsrBB'' ]].
  assert (nColAOB'' : ~ [ A, O, B'' ]).
  { apply (nColPs_SR_inv O A B A B'')... }
  assert (nColB''OC : ~ [ B'', O, C ]).
  { apply (nColPs_SR_inv O B C B'' C)... }
  assert (OoAB''C : [O | A; B''; C ]).
  { apply (BR_inv O A B C A B'' C)... }
  assert (AOBeqAOB'' : [|A # O # B'' | nColAOB''|]
    = [|A' # O' # B' | nColA'O'B'|]).
  { symmetry. rewrite <- AOBeqAOB.
    apply (ConvexAngPs_inv A O B A B'')...
  }
  assert (BOCeqB''OC : [|B # O # C | nColBOC |] = [|B'' # O # C | nColB''OC|]).
  { apply (ConvexAngPs_inv B O C B'' C)... }
  rewrite BOCeqB''OC.
  clear dependent B. rename B'' into B.
  rename nColAOB'' into nColAOB.
  rename OoAB''C into OoABC.
  rename AOBeqAOB'' into AOBeqAOB.
  destruct (DrawSegmentOnRay O' A' O A) as [ A'' [ H O'A'_OA ]]; dips.
  assert (O'_A'A : [O' # A', A'']).
  { destruct H as [ H1 |[ H2 | H3 ]]; eauto.
    { clear AOBeqAOB. apply nColPs_DiPs_12 in nColA'O'B'.
      contradict nColA'O'B'...
    }
    { subst A''. symmetry in O'A'_OA. apply EqSgs_EqPs in O'A'_OA.
      subst A; contradiction.
    }
  }
  clear H.
  assert (nColA''O'C' : ~ [A'', O', C']).
  { apply (nColPs_SR_inv O' A' C' A'' C')... }
  assert (nColA''O'B' : ~ [A'', O', B']).
  { apply (nColPs_SR_inv O' A' B' A'' B')... }
  rewrite (ConvexAngPs_inv A' O' C' A'' C' nColA'O'C' nColA''O'C')
    in AOCeqAOC...
  rewrite (ConvexAngPs_inv A' O' B' A'' B' nColA'O'B' nColA''O'B')
    in AOBeqAOB...
  apply (BR_inv O' A' B' C' A'' B' C') in O'oA'B'C'...
  clear dependent A'. rename A'' into A'.
  rename nColB''OC into nColBOC.
  rename nColA''O'B' into nColA'O'B'.
  rename nColA''O'C' into nColA'O'C'.
  destruct (nColPs_3DiPs A O B nColAOB) as [ _ [ nOeqB nAeqB ]].
  destruct (DrawSegmentOnRay O' B' O B) as [ B'' [ H O'B'_OB ]]...
  assert (O'_B'B : [O' # B', B'']).
  { destruct H as [ H1 |[ H2 | H3 ]]; eauto.
    { clear AOBeqAOB. apply nColPs_DiPs_23 in nColA'O'B'.
      contradict nColA'O'B'...
    }
    { subst B''. symmetry in O'B'_OB. apply EqSgs_EqPs in O'B'_OB.
      subst B; contradiction.
    }
  }
  clear H.
  assert (nColB''O'C' : ~ [B'', O', C']).
  { apply (nColPs_SR_inv O' B' C' B'' C')... }
  assert (nColA'O'B'' : ~ [A', O', B'']).
  { apply (nColPs_SR_inv O' A' B' A' B'')... }
  rewrite (ConvexAngPs_inv B' O' C' B'' C' nColB'O'C' nColB''O'C')...
  rewrite (ConvexAngPs_inv A' O' B' A' B'' nColA'O'B' nColA'O'B'')
    in AOBeqAOB...
  apply (BR_inv O' A' B' C' A' B'' C') in O'oA'B'C'...
  clear dependent B'. rename B'' into B'.
  rename nColA'O'B'' into nColA'O'B'.
  rename nColB''O'C' into nColB'O'C'.
  destruct (DrawSegmentOnRay O' C' O C) as [ C'' [ H O'C'_OC ]]; dips.
  assert (O'_C'C : [O' # C', C'']).
  { destruct H as [ H1 |[ H2 | H3 ]]; eauto.
    { clear AOCeqAOC. apply nColPs_DiPs_23 in nColA'O'C'.
      contradict nColA'O'C'...
    }
    { subst C''. symmetry in O'C'_OC. apply EqSgs_EqPs in O'C'_OC.
      subst C; contradiction.
    }
  }
  clear H.
  assert (nColB'O'C'' : ~ [B', O', C'']).
  { apply (nColPs_SR_inv O' B' C' B' C'')... }
  assert (nColA'O'C'' : ~ [A', O', C'']).
  { apply (nColPs_SR_inv O' A' C' A' C'')... }
  rewrite (ConvexAngPs_inv B' O' C' B' C'' nColB'O'C' nColB'O'C'')...
  rewrite (ConvexAngPs_inv A' O' C' A' C'' nColA'O'C' nColA'O'C'')
    in AOCeqAOC...
  apply (BR_inv O' A' B' C' A' B' C'') in O'oA'B'C'...
  clear dependent C'. rename C'' into C'.
  rename nColA'O'C'' into nColA'O'C'.
  rename nColB'O'C'' into nColB'O'C'.
  assert (AOB : {{ A # O # B | nColAOB }} :=: {{ A' # O' # B' | nColA'O'B' }}).
  { apply SAS; eauto.
    rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
  }
  assert (AOC : {{ A # O # C | nColAOC }} :=: {{ A' # O' # C' | nColA'O'C' }}).
  { apply SAS; eauto.
    rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
  }
  assert ( A'_B'C' : [ A' # B', C' ]).
  { eapply (SH_EqConvexAs_SR O' A' B' C')...
    destruct O'oA'B'C'... apply SHa_sym...
    erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
    pir (nColPerPs_5 O' A' C' (fun H3 : [O', A', C'] => nColA'O'C'
      (ColPerPs_5 C' O' A' (ColPerPs_2 O' A' C' H3))))
      => (nColPerPs_2 A' O' C' nColA'O'C').
    pir (nColPerPs_5 O' A' B' (fun H3 : [O', A', B'] => nColA'O'B'
      (ColPerPs_5 B' O' A' (ColPerPs_2 O' A' B' H3))))
      => (nColPerPs_2 A' O' B' nColA'O'B').
    destruct AOB as [ _ [ _ [ _ [ _ [ _ H1 ]]]]]; simpl in *. rewrite <- H1.
    destruct AOC as [ _ [ _ [ _ [ _ [ _ H2 ]]]]]; simpl in *. rewrite <- H2.
    erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
    eapply (ConvexAngPs_inv O A B O C)... apply BetPs_SR in BetABC.
    destruct BetABC; eauto.
  }
  assert (BetA'B'C' : [A' # B' # C']).
  { apply SR_ColPs in A'_B'C'.
    apply (ColPs_BR_BetPs O' A' B' C'); colperps.
  }
  clear A'_B'C'.
  assert(OCB : [|O # C # B | nColPerPs_1 B O C nColBOC|] =
    [|O' # C' # B' | nColPerPs_1 B' O' C' nColB'O'C'|]).
  { erewrite (ConvexAngPs_inv O C B O A )...
    { erewrite (ConvexAngPs_inv O' C' B' O' A' )...
      { destruct AOC as [ _ [ _ [ _ [ _ [ H _ ]]]]]; simpl in *.
        pir (fun H0 : [O, C, A] => nColAOC (ColPerPs_5 C O A
          (ColPerPs_3 O C A H0))) => (nColPerPs_1 A O C nColAOC).
        pir (fun H0 : [O', C', A'] => nColA'O'C' (ColPerPs_5 C' O' A'
          (ColPerPs_3 O' C' A' H0))) => (nColPerPs_1 A' O' C' nColA'O'C')...
      }
      { apply BetPs_SR in BetA'B'C'. destruct BetA'B'C'... }
    }
    { apply BetPs_SR in BetABC. destruct BetABC... }
  }
  assert (EqTr : {{ O # C # B | nColPerPs_1 B O C nColBOC }}
    :=: {{ O' # C' # B' | nColPerPs_1 B' O' C' nColB'O'C' }}).
  { apply SAS...
    rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
    destruct AOB as [ _ [ _ [ AB _ ]]]; simpl in *.
    rewrite SegPs_sym in AB. symmetry in AB.
    rewrite SegPs_sym in AB...
    destruct AOC as [ _ [ _ [ AC _ ]]]; simpl in *.
    rewrite SegPs_sym in AC. symmetry in AC.
    rewrite SegPs_sym in AC...
    destruct (BetPs_SubtractSgs A B C A' B' C')...
    apply BetPs_SR in BetA'B'C'. destruct BetA'B'C'...
  }
  destruct EqTr as [ _ [ _ [ _ [ _ [ _ H ]]]]]; simpl in *.
  pir (nColPerPs_2 O C B (nColPerPs_1 B O C nColBOC))
    => nColBOC.
  pir (nColPerPs_2 O' C' B' (nColPerPs_1 B' O' C' nColB'O'C'))
    => nColB'O'C'.
  Unshelve. ncolperps. ncolperps. ncolperps. ncolperps.
Qed.
Lemma ConvexAngRs_ConvexAngPs :
  forall (a b : Ray)(diab : ![ a # b ])(nColAOB : ~ [ db a, da a, db b ]),
    [| a # b | diab |] = [| db a # da a # db b | nColAOB |].
Proof.
  intros [ O A nAeqO ][ O' B nBeqO ][ roab diab ] nColAOB.
  simpl in *. subst O'. pir diab => nColAOB.
  apply EqConvexAngRsPs.
Qed.
Lemma BetRs_AddConvexAngRs :
  forall (a b c a' b' c' : Ray)
    (diab : ![ a # b ])(dibc : ![ b # c ])(diac : ![ a # c ])
    (dia'b' : ![ a' # b' ])(dib'c' : ![ b' # c' ])(dia'c' : ![ a' # c' ]),
  ![ a # b # c ]
    -> ![ a' # b' # c' ]
    -> [| a # b | diab |] = [| a' # b' | dia'b' |]
    -> [| b # c | dibc |] = [| b' # c' | dib'c' |]
    -> [| a # c | diac |] = [| a' # c' | dia'c' |].
Proof with eauto.
  intros * [ roab [ robc BetRabc ]][ roa'b' [ rob'c' BetRa'b'c' ]] ab bc.
  assert (nColAOB : ~ [ db a, da a, db b ]). { destruct diab... }
  assert (nColA'O'B' : ~ [ db a', da a', db b' ]). { destruct dia'b'... }
  rewrite (ConvexAngRs_ConvexAngPs a b diab nColAOB) in ab.
  rewrite (ConvexAngRs_ConvexAngPs a' b' dia'b' nColA'O'B') in ab.
  assert (nColBOC : ~ [ db b, da b, db c ]). { destruct dibc... }
  assert (nColB'O'C' : ~ [ db b', da b', db c' ]). { destruct dib'c'... }
  rewrite (ConvexAngRs_ConvexAngPs b c dibc nColBOC) in bc.
  rewrite (ConvexAngRs_ConvexAngPs b' c' dib'c' nColB'O'C') in bc.
  assert (nColAOC : ~ [ db a, da a, db c ]). { destruct diac... }
  assert (nColA'O'C' : ~ [ db a', da a', db c' ]). { destruct dia'c'... }
  rewrite (ConvexAngRs_ConvexAngPs a c diac nColAOC).
  rewrite (ConvexAngRs_ConvexAngPs a' c' dia'c' nColA'O'C').
  destruct robc, roab, rob'c', roa'b'.
  eapply BR_AddConvexAngPs.
  { apply BetRabc. }
  { apply BetRa'b'c'. }
  { apply ab. }
  { apply bc. }
Qed.

(** Theorem #55 *)
(** Hilbert, Chapter 1 : Theorem 18. *)
(** Euclid, Book I : Proposition 8. *)
(* If two triangles have the two sides equal to two sides respectively,
 and have also the base equal to the base,
 they will also have the angles equal
 which are contained by the equal straight lines. *)
Theorem SSS :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  [| A, B |] = [| D, E |]
    -> [| B, C |] = [| E, F |]
    -> [| C, A |] = [| F, D |]
    -> {{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }}.
Proof with try apply SR_refl; dips.
  intros * AB_DE BC_EF CA_FD.
  destruct (nColPs_3DiPs A B C nColABC) as [ nBeqA [ nBeqC nAeqB ]].
  destruct (nColPs_3DiPs D E F nColDEF) as [ nDeqE [ nEeqF nDeqF ]].
  destruct (DrawExtensionLinePP D E) as [ x [ Dox Eox ]]...
  destruct (DrawPointOnOppositeSide F x) as [ F' FxF' ]; nincpt.
  destruct (SuperpositionPrinciple A B C D E F' nColABC)
    as [ G [ nColDEG [ H2 H3 ]]]...
  { destruct FxF' as [ nFox [ nF'ox H ]]; ncolps. }
  destruct (nColPs_3DiPs D E G nColDEG) as [ _ [ nEeqG nDeqG ]].
  assert (FxG : [ F | x | G ]).
  { apply (OSO_trans F F' G x)...
    destruct H2 as [ _ [ t [ Dot [ Eot H7 ]]]]...
    assert (xeqt : x = t); eqls.
  }
  clear H2. rewrite H3.
  destruct H3 as [ _ [ BC_EG [ CA_GD [ H1 [ H2 H3 ]]]]]; simpl in *.
  rewrite CA_FD in CA_GD. rewrite BC_EF in BC_EG.
  clear dependent A. clear dependent B.
  clear dependent C. clear dependent F'.
  destruct FxG as [ nFox [ nGox [ O [ Oox FOG ]]]].
  assert (ColFOG : [F, O, G]); colps.
  assert (FsrOG : [F # O, G]).
  { apply BetPs_SR in FOG. destruct FOG... }
  assert (GsrOF : [G # O, F]).
  { apply BetPs_SR in FOG. destruct FOG... }
  destruct (BetPs_3DiPs F O G FOG) as [ nFeqO [ nOeqG nFeqG ]].
  elim ColFOG; intros y [ Foy [ Ooy Goy ]].
  assert (nxeqy : x <> y); dils.
  destruct (classic (O = E)) as [ OeqE | nOeqE ].
  { subst.
    assert (nDoy : ~ [ D @ y ]). { contradict nxeqy. eqls. }
    assert (nColDFG : ~ [D, F, G]). { contradict nDoy. incpt 2. }
    rewrite SegPs_sym in CA_GD. symmetry in CA_GD.
    rewrite SegPs_sym in CA_GD.
    assert (DFG : [| D # F # E | nColPerPs_4 D E F nColDEF |] =
      [| D # G # E | nColPerPs_4 D E G nColDEG |]).
    { erewrite (ConvexAngPs_inv D F E D G)...
      erewrite (ConvexAngPs_inv D G E D F)...
      apply IsoscelesTr_EqConvexAs...
    }
    assert (EqTr : {{ D # F # E | nColPerPs_4 D E F nColDEF }} :=:
      {{ D # G # E | nColPerPs_4 D E G nColDEG }}).
    { apply SAS...
      rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
    }
    apply EqPerTr_4 in EqTr.
    pir (nColPerPs_4 D F E (nColPerPs_4 D E F nColDEF)) => nColDEF.
    pir (nColPerPs_4 D G E (nColPerPs_4 D E G nColDEG)) => nColDEG.
    rewrite EqTr... reflexivity.
  }
  destruct (classic (O = D)) as [ OeqD | nOeqD ].
  { subst.
    assert (nEoy : ~ [ E @ y ]). { contradict nxeqy. eqls. }
    assert (nColEFG : ~ [E, F, G]). { contradict nEoy. incpt 2. }
    rewrite SegPs_sym in CA_GD. symmetry in CA_GD.
    rewrite SegPs_sym in CA_GD. symmetry in CA_GD.
    assert (DFG : [| D # F # E | nColPerPs_4 D E F nColDEF |] =
      [| D # G # E | nColPerPs_4 D E G nColDEG |]).
    { erewrite (ConvexAngPs_inv D F E G E)...
      erewrite (ConvexAngPs_inv D G E F E)...
      erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
      eapply IsoscelesTr_EqConvexAs...
    }
    assert (EqTr : {{ D # F # E | nColPerPs_4 D E F nColDEF }} :=:
      {{ D # G # E | nColPerPs_4 D E G nColDEG }}).
    { apply SAS...
      rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
    }
    apply EqPerTr_4 in EqTr.
    pir (nColPerPs_4 D F E (nColPerPs_4 D E F nColDEF)) => nColDEF.
    pir (nColPerPs_4 D G E (nColPerPs_4 D E G nColDEG)) => nColDEG.
    rewrite EqTr... reflexivity.
  }
  assert (nDoy : ~ [ D @ y ]). { contradict nxeqy. eqls. }
  assert (nEoy : ~ [ E @ y ]). { contradict nxeqy. eqls. }
  assert (nColOFE : ~ [ O, F, E ]); ncolps.
  assert (nColOFD : ~ [ O, F, D ]); ncolps.
  assert (nColOGE : ~ [ O, G, E ]); ncolps.
  assert (nColOGD : ~ [ O, G, D ]); ncolps.
  assert (nColEFD : ~ [ E, F, D ]); ncolperps.
  assert (nColEGD : ~ [ E, G, D ]); ncolperps.
  assert (nColGFD : ~ [ G, F, D ]). ncolps.
  assert (nColFGD : ~ [ F, G, D ]); ncolps.
  assert (nColFGE : ~ [ F, G, E ]); ncolps.
  assert (nColGFE : ~ [ G, F, E ]); ncolps.
  assert ( OFE : [| O # F # E | nColOFE |] = [| O # G # E | nColOGE |]).
  { erewrite (ConvexAngPs_inv O F E G E nColOFE nColGFE)...
    erewrite (ConvexAngPs_inv O G E F E nColOGE nColFGE)...
    erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
    apply (IsoscelesTr_EqConvexAs E G F)...
  }
  { assert ( OFD : [| O # F # D | nColOFD |] = [| O # G # D | nColOGD |]).
    { erewrite (ConvexAngPs_inv O F D G D nColOFD nColGFD)...
      erewrite (ConvexAngPs_inv O G D F D nColOGD nColFGD)...
      erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
      apply (IsoscelesTr_EqConvexAs D G F)...
      rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
    }
    destruct (DecidePointsBetweenness D E O) as [[ DEO | EOD ]| EDO ]...
    { assert ( EFD : [| E # F # D | nColEFD |] = [| E # G # D | nColEGD |]).
      { eapply (BR_SubtConvexAngPs F O E D G O E D);
        apply BetPs_sym in DEO...
        { apply (nColPs_BetPs_BR F O E D); ncolperps. }
        { apply (nColPs_BetPs_BR G O E D); ncolperps. }
      }
      assert (EqTr : {{ E # F # D | nColEFD }} :=: {{ E # G # D | nColEGD }}).
      { apply SAS... }
      apply EqPerTr_2 in EqTr.
      pir (nColPerPs_2 E F D nColEFD) => nColDEF.
      pir (nColPerPs_2 E G D nColEGD) => nColDEG. symmetry...
    }
    { assert ( EFD : [| E # F # D | nColEFD |] = [| E # G # D | nColEGD |]).
      { eapply (BR_AddConvexAngPs F E O D G E O D)...
        { apply (nColPs_BetPs_BR F E O D); ncolperps. }
        { apply (nColPs_BetPs_BR G E O D); ncolperps. }
        symmetry.
        erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
        pir (nColPerPs_5 E F O (fun H : [E, F, O] => nFox
          (ColPs_IncPt_6 O E F x nOeqE Oox Eox (ColPerPs_3 E F O H))))
          => nColOFE.
        pir (nColPerPs_5 E G O (fun H : [E, G, O] => nFox
          (BetPs_IncPt_6 G O F x FOG
          (ColPs_IncPt_2 O E G x nOeqE Oox Eox H) Oox))) => nColOGE.
        apply OFE.
      }
      assert (EqTr : {{ E # F # D | nColEFD }} :=: {{ E # G # D | nColEGD }}).
      { apply SAS... }
      apply EqPerTr_2 in EqTr.
      pir (nColPerPs_2 E F D nColEFD) => nColDEF.
      pir (nColPerPs_2 E G D nColEGD) => nColDEG. symmetry...
    }
    { assert ( EFD : [| E # F # D | nColEFD |] = [| E # G # D | nColEGD |]).
      { erewrite ConvexAngPs_sym. symmetry.
        erewrite ConvexAngPs_sym. symmetry.
        eapply (BR_SubtConvexAngPs F O D E G O D E);
        apply BetPs_sym in EDO...
        { apply (nColPs_BetPs_BR F O D E); ncolperps. }
        { apply (nColPs_BetPs_BR G O D E); ncolperps. }
      }
      assert (EqTr : {{ E # F # D | nColEFD }} :=: {{ E # G # D | nColEGD }}).
      { apply SAS... }
      apply EqPerTr_2 in EqTr.
      pir (nColPerPs_2 E F D nColEFD) => nColDEF.
      pir (nColPerPs_2 E G D nColEGD) => nColDEG. symmetry...
    }
    Unshelve.
    ncolperps. ncolperps. ncolperps. ncolperps. ncolperps.
    ncolperps. ncolperps. ncolperps. ncolperps. ncolperps.
    ncolperps. ncolperps. ncolperps. ncolperps.
  }
Qed.

Global Instance cg : Congruences (on).
Proof with eauto.
  eapply (Build_Congruences).
  { intros * AB_DE BC_EF.
    split.
    { intros CA_FD.
      apply SSS...
    }
    { intros ABC_DEF.
      edestruct (SAS A B C D E F) as [ _ [ _ [ CA _ ]]]...
    }
  }
Qed.

End SUPERPOSITION.

(*****************************************************************************)
(* 16 *) Section CONGRUENCE.
Context `{ cc : Concentricals }.
Context  { an : Angles on }.
Context  { cg : Congruences on }.
(*****************************************************************************)

Lemma SAS' :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  [| A, B |] = [| D, E |]
    -> [| B, C |] = [| E, F |]
    -> [| A # B # C | nColABC |] = [| D # E # F | nColDEF |]
    -> {{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }}.
Proof with eauto.
  intros * ABeqDE BCeqEF ABCeqDEF.
  assert (CAeqFD : [|C, A|] = [|F, D|]).
  { eapply (TriangleCongruence A B C D E F)... }
  repeat split; simpl...
  { eapply (TriangleCongruence B C A E F D)... }
  { eapply (TriangleCongruence C A B F D E)... }
Qed.

Lemma ASA' :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  [| A, C |] = [| D, F |]
  -> [| B # C # A | nColPerPs_1 A B C nColABC |]
    = [| E # F # D | nColPerPs_1 D E F nColDEF |]
  -> [| C # A # B | nColPerPs_2 A B C nColABC |]
    = [| F # D # E | nColPerPs_2 D E F nColDEF |]
  -> {{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }}.
Proof with eauto.
  intros * ACeqDF BCAeqEFD CABeqFDE.
  assert (nAeqB : A <> B); dips.
  assert (nDeqE : D <> E); dips.
  destruct (DrawSegmentOnRay A B D E nAeqB)
    as [ B' [[ AsrBB' |[ AeqB | AeqB' ]] AB'eqDE ]].
  { assert (nAeqB' : A <> B'); dips.
    assert (nColAB'C : ~ [ A, B', C ]).
    { clear BCAeqEFD CABeqFDE.
      contradict nColABC.
      destruct AsrBB' as [ _ [ _ [[ x [ Aox [ Box B'ox ]]] _ ]]].
      exists x; repeat split...
      apply (ColPs_IncPt A B' C x); try split...
    }
    assert (trABCeqDEF' :
      {{ A # B' # C | nColAB'C }} :=: {{ D # E # F | nColDEF }}).
    { assert (ABCeqABC' :
        [| C # A # B | nColPerPs_2 A B C nColABC |]
          = [| C # A # B' | nColPerPs_2 A B' C nColAB'C |]).
      { erewrite (ConvexAngPs_inv C A B C B')... apply SR_refl; dips. }
      assert ({{ C # A # B' | nColPerPs_2 A B' C nColAB'C}}
        :=: {{ F # D # E | nColPerPs_2 D E F nColDEF}}).
      { eapply (SAS' C A B' F D E)...
        rewrite SegPs_sym; symmetry; rewrite SegPs_sym...
        rewrite <- ABCeqABC'...
      }
      apply EqPerTr_1 in H.
      pir (nColPerPs_1 C A B' (nColPerPs_2 A B' C nColAB'C)) => nColAB'C.
      pir (nColPerPs_1 F D E (nColPerPs_2 D E F nColDEF)) => nColDEF.
  }
    unfold EqTriangle in trABCeqDEF'; simpl in *.
    destruct trABCeqDEF'
      as [ _ [ B'CeqEF [ CAeqFD [ AB'CeqDEF [ B'CAeqEFD CAB'eqFDE ]]]]].
    assert (ACsfBB' : [ A # C | B, B' ]). { apply SR_SH; ncolperps. }
    assert (ACBeqACB'' :
      [| A # C # B | nColPerPs_4 A B C nColABC |]
        = [| A # C # B' | nColPerPs_4 A B' C nColAB'C |]).
    { erewrite (ConvexAngPs_sym A C B (nColPerPs_4 A B C nColABC)).
      symmetry.
      pir (nColPerPs_5 A C B (nColPerPs_4 A B C nColABC))
        => (nColPerPs_1 A B C nColABC).
      erewrite (ConvexAngPs_sym A C B' (nColPerPs_4 A B' C nColAB'C)).
      pir (nColPerPs_5 A C B' (nColPerPs_4 A B' C nColAB'C))
        => (nColPerPs_1 A B' C nColAB'C).
      rewrite BCAeqEFD. rewrite B'CAeqEFD...
    }
    assert (CsrBB' : [C # B, B']).
    { apply (SH_EqConvexAs_SR A C B B' (nColPerPs_4 A B C nColABC)
        (nColPerPs_4 A B' C nColAB'C))...
      apply SHa_sym...
    }
    destruct (AsrBB') as [ _ [ _ [[ x [ Aox [ Box B'ox ]]] _ ]]].
    destruct (CsrBB') as [ _ [ _ [[ y [ Coy [ Boy B'oy ]]] _ ]]].
    assert (nxeqy : x <> y); dils.
    assert (BeqB' : B = B'); eqps.
    subst B'.
    unfold EqTriangle; simpl; repeat split...
    pir nColAB'C => nColABC.
  }
  { contradiction. }
  { eapply (EqSgs_EqPs A B' A) in AeqB'. rewrite AeqB' in AB'eqDE.
   symmetry in AB'eqDE. apply EqSgs_EqPs in AB'eqDE. contradiction.
  }
Qed.

Lemma SSS' :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  [| A, B |] = [| D, E |]
    -> [| B, C |] = [| E, F |]
    -> [| C, A |] = [| F, D |]
    -> {{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }}.
Proof with geo.
  intros * AB_DE BC_EF CA_FD.
  repeat split; simpl...
  { eapply (TriangleCongruence A B C D E F)... }
  { eapply (TriangleCongruence B C A E F D)... }
  { eapply (TriangleCongruence C A B F D E)... }
Qed.

(** Theorem #56 *)
(** Euclid, Book I : Proposition 7. *)
(* Given two straight lines constructed on a straight line
 (from its extremities) and meeting in a point,
 there cannot be constructed on the same straight line
 (from its extremities), and on the same side of it,
 two other straight lines meeting in another point and
 equal to the former two respectively,
 namely each to that has the same extremity with it. *)
Proposition EqTr_EqPs :
  forall A B C C' : Point,
  [ A # B | C, C' ]
    -> [| A, C |] = [| A, C' |]
    -> [| B, C |] = [| B, C' |]
    -> C = C'.
Proof with eauto.
  intros A B C C' ABsfCC' AC_AC' BC_BC'.
  assert (nColABC : ~ [ A, B, C ]).
  { destruct ABsfCC' as [ nAeqB [ x [ Aox [ Box [ nCox _ ]]]]].
    contradict nCox.
    apply (ColPs_IncPt A B C x nAeqB)...
  }
  assert (nColABC' : ~ [ A, B, C' ]).
  { destruct ABsfCC' as [ nAeqB [ x [ Aox [ Box [ _ [ nC'ox _ ]]]]]].
    contradict nC'ox.
    apply (ColPs_IncPt A B C' x nAeqB)...
  }
  assert (nColBAC : ~ [ B, A, C ]); ncolperps.
  assert (nColBAC' : ~ [ B, A, C' ]); ncolperps.
  assert (nColCAB : ~ [ C, A, B ]); ncolperps.
  assert (nColC'AB : ~ [ C', A, B ]); ncolperps.
  assert (ABC_ABC' : {{ A#B#C | nColABC }} :=: {{ A#B#C' | nColABC' }}).
  { apply (SSS' A B C A B C' nColABC)...
    rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
  }
  unfold EqTriangle in ABC_ABC'; simpl in *.
  destruct ABC_ABC' as [ _ [ _ [ _ [ ABC_ABC' [ BCA_BC'A CAB_C'AB ]]]]].
  assert (BsrCC' : [ B # C, C' ]).
  { apply (SH_EqConvexAs_SR A B C C' nColABC nColABC'); ord. }
  assert (AsrCC' : [ A # C, C' ]).
  { apply (SH_EqConvexAs_SR B A C C' nColBAC nColBAC')...
    erewrite (ConvexAngPs_sym C A B) in CAB_C'AB.
    pir (nColPerPs_5 C A B (nColPerPs_2 A B C nColABC)) => nColBAC.
    erewrite (ConvexAngPs_sym C' A B) in CAB_C'AB. apply CAB_C'AB.
  }
  destruct BsrCC'
    as [ nCeqB [ nC'eqB [[ x [ Box [ Cox C'ox ]]] nBetCBC' ]]].
  destruct AsrCC'
    as [ nCeqA [ nC'eqA [[ y [ Boy [ Coy C'oy ]]] nBetCAC' ]]].
  assert (nxeqy : x <> y); dils.
  eqps.
Qed.

Lemma IsoscelesTr_EqConvexAs' :
  forall (A B C : Point)(nColABC : ~ [ A, B, C ])(nColACB : ~ [ A, C, B ]),
  [| A, B |] = [| A, C |]
    -> [| A # B # C | nColABC |] = [| A # C # B | nColACB |].
Proof with eauto.
  intros A B C nColABC nColACB ABeqAC.
  assert (EqTr : {{ B # A # C | (nColPerPs_3 A B C nColABC) }}
    :=: {{ C # A # B | (nColPerPs_3 A C B nColACB) }}).
  { apply (SAS' B A C C A B)...
    rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
    erewrite ConvexAngPs_sym.
    pir ( nColPerPs_5 B A C (nColPerPs_3 A B C nColABC))
      => (nColPerPs_3 A C B nColACB).
  }
  destruct EqTr as [ _ [ _ [ _ [ _ [ H _ ]]]]]; simpl in *.
  pir (nColPerPs_1 C A B (nColPerPs_3 A C B nColACB)) => nColABC.
  pir (nColPerPs_1 B A C (nColPerPs_3 A B C nColABC)) => nColACB.
Qed.
Lemma EqSupConvexAngPs' :
  forall (O A B C O' A' B' C' : Point)
    (nColAOB : ~ [ A, O, B ])(nColBOC : ~ [ B, O, C ])
    (nColA'O'B' : ~ [ A', O', B' ])(nColB'O'C' : ~ [ B', O', C' ]),
  [ A # O # C ]
    -> [ A' # O' # C' ]
    -> [| A # O # B | nColAOB |] = [| A' # O' # B' | nColA'O'B' |]
    -> [| B # O # C | nColBOC |] = [| B' # O' # C' | nColB'O'C' |].
Proof with eauto.
  intros * BetAOC BetA'O'C' AOB.
  destruct (nColPs_3DiPs A O B nColAOB)
    as [ nAeqO [ nBeqO nAeqB ]]. apply not_eq_sym in nBeqO.
  destruct (nColPs_3DiPs B O C nColBOC)
    as [ _ [ nCeqO nBeqC ]]. apply not_eq_sym in nCeqO.
  destruct (nColPs_3DiPs A' O' B' nColA'O'B')
    as [ nA'eqO' [ nB'eqO' nA'eqB' ]]. apply not_eq_sym in nB'eqO'.
  destruct (nColPs_3DiPs B' O' C' nColB'O'C')
    as [ _ [ nC'eqO' nB'eqC' ]]. apply not_eq_sym in nC'eqO'.
  destruct (DrawSegmentOnRay O A O' A') as [ A'' [ OsrAA'' OA ]]...
  destruct (DrawSegmentOnRay O B O' B') as [ B'' [ OsrBB'' OB ]]...
  destruct (DrawSegmentOnRay O C O' C') as [ C'' [ OsrCC'' OC ]]...
  destruct OsrAA'' as [ OsrAA'' |[ OeqA | OeqA'' ]]...
  destruct OsrBB'' as [ OsrBB'' |[ OeqB | OeqB'' ]]...
  destruct OsrCC'' as [ OsrCC'' |[ OeqC | OeqC'' ]]...
  assert (nColAOB'' : ~ [ A'', O, B'' ]).
  { apply (nColPs_SR_inv O A B A'' B'')... }
  assert (nColBOC'' : ~ [ B'', O, C'' ]).
  { apply (nColPs_SR_inv O B C B'' C'')... }
  assert (BetAOC'' : [ A''# O # C'' ]).
  { apply (BetPs_inv O A C A'' C'')... }
  assert (AOB'' : [| A'' # O # B'' | nColAOB'' |]
    = [|A' # O' # B' | nColA'O'B'|]).
  { erewrite (ConvexAngPs_inv A'' O B'' A B); try apply SR_sym... }
  assert (BOC'' : [| B'' # O # C'' | nColBOC'' |]
    = [| B # O # C | nColBOC |]).
  { erewrite (ConvexAngPs_inv B'' O C'' B C); try apply SR_sym... }
  rewrite <- BOC''.
  clear dependent A. clear dependent B. clear dependent C.
  rename A'' into A. rename B'' into B. rename C'' into C.
  assert (TrAOB : {{ A#O#B | nColAOB'' }} :=: {{ A'#O'#B' | nColA'O'B' }}).
  { apply (SAS' A O B A' O' B')... rewrite SegPs_sym. symmetry.
    rewrite SegPs_sym...
  }
  assert (AC : [| A, C |] = [| A', C' |]).
  { apply (BetPs_AddSgs A O C A' O' C' BetAOC'' BetA'O'C')...
    rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
  }
  assert (nAeqC : A <> C); dips.
  assert (nA'eqC' : A' <> C'); dips.
  assert (nColBAC : ~ [ B, A, C ]).
  { clear TrAOB AOB''. contradict nColAOB''. colperps. }
  assert (nColB'A'C' : ~ [ B', A', C' ]).
  { clear TrAOB AOB''. contradict nColA'O'B'. colperps. }
  assert (TrBAC : {{ B # A # C | nColBAC }}
    :=: {{ B' # A' # C' | nColB'A'C' }}).
  { unfold EqTriangle in TrAOB; simpl in *.
    apply SAS'...
    { destruct TrAOB as [ _ [ _ [ H _ ]]]... }
    assert (nColBAO : ~ [ B, A, O ]); ncolperps.
    assert (nColB'A'O' : ~ [ B', A', O' ]); ncolperps.
    rewrite (ConvexAngPs_inv B A C B O nColBAC nColBAO).
    { rewrite (ConvexAngPs_inv B' A' C' B' O' nColB'A'C' nColB'A'O').
      { pir (nColPerPs_2 A O B nColAOB'') => nColBAO.
        pir (nColPerPs_2 A' O' B' nColA'O'B') => nColB'A'O'.
        destruct TrAOB as [ _ [ _ [ _ [ _ [ _ H ]]]]]...
      }
      { apply SR_refl... }
      { apply SR_sym. apply BetPs_SR. apply BetPs_sym... }
    }
    { apply SR_refl; dips. }
    { apply SR_sym. apply BetPs_SR. apply BetPs_sym... }
  }
  assert (nColBCO : ~ [B, C, O]); ncolperps.
  assert (nColB'C'O' : ~ [B', C', O']); ncolperps.
  unfold EqTriangle in TrBAC; simpl in *.
  destruct TrBAC as [ _ [ _ [ H1 [ _ [ H2 _ ]]]]]...
  assert (TrBOC : {{ B # C # O | nColBCO }}
    :=: {{ B' # C' # O' | nColB'C'O' }}).
  { apply (SAS' B C O B' C' O' nColBCO)...
    { rewrite SegPs_sym. symmetry. rewrite SegPs_sym... }
    { rewrite SegPs_sym. symmetry. rewrite SegPs_sym... }
    { erewrite (ConvexAngPs_inv B C O B A); try apply SR_refl; dips; ord.
      { erewrite (ConvexAngPs_inv B' C' O' B' A'); try apply SR_refl; ord.
        { erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
          symmetry. apply H2.
        }
      }
    }
  }
  unfold EqTriangle in TrBOC; simpl in *.
  destruct TrBOC as [ _ [ _ [ _ [ _ [ H _ ]]]]]...
  erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
  symmetry. apply H.
  { subst. contradiction. }
  { subst C''. symmetry in OC.
    apply EqSgs_EqPs in OC. contradict nC'eqO'...
  }
  { subst. contradiction. }
  { subst B''. symmetry in OB.
    apply EqSgs_EqPs in OB. contradict nB'eqO'...
  }
  { subst. contradiction. }
  { subst A''. symmetry in OA.
    apply EqSgs_EqPs in OA. contradict nA'eqO'...
  }
  Unshelve. ncolperps. ncolperps.
Qed.
Lemma EqSupConvexAngRs' :
  forall (a b c a' b' c' : Ray)(diab : ![ a # b ])(dibc : ![ b # c ])
         (dia'b' : ![ a' # b' ])(dib'c' : ![ b' # c' ]),
  a == !c
    -> a' == !c'
    -> [| a # b | diab |] = [| a' # b' | dia'b' |]
    -> [| b # c | dibc |] = [| b' # c' | dib'c' |].
Proof with eauto.
  intros [ O A nOeqA ][ O' B nOeqB ][ O'' C nOeqC ].
  intros [ Q A' nOeqA' ][ Q' B' nOeqB' ][ Q'' C' nOeqC' ].
  intros [ orab diab ][ orbc dibc ][ora'b' dia'b' ][ orb'c' dib'c' ];
  simpl in *.
  intros aopc a'opc' ab; simpl in *.
  subst O'' O'. subst Q'' Q'. rename Q into O'. simpl in *.
  erewrite (EqConvexAngRsPs B O C).
  erewrite (EqConvexAngRsPs B' O' C').
  erewrite (EqConvexAngRsPs A O B) in ab.
  erewrite (EqConvexAngRsPs A' O' B') in ab.
  eapply (EqSupConvexAngPs' O A B C O' A' B' C')...
  { apply (OpRs_BetPs A O C nOeqA nOeqC)... }
  { apply (OpRs_BetPs A' O' C' nOeqA' nOeqC')... }
Qed.

Lemma EqConvexAs_IsoscelesTr' :
  forall (A B C : Point)(nColABC : ~ [ A, B, C ])(nColACB : ~ [ A, C, B ]),
  [| A # B # C | nColABC |] = [| A # C # B | nColACB |]
    -> [| A, B |] = [| A, C |].
Proof.
  intros A B C nColABC nColACB ABCeqACB.
  assert (EqTr : {{ B # A # C | (nColPerPs_3 A B C nColABC) }}
    :=: {{ C # A # B | (nColPerPs_3 A C B nColACB) }}).
  { eapply (ASA' B A C C A B).
    { apply SegPs_sym. }
    { pir (nColPerPs_1 B A C (nColPerPs_3 A B C nColABC)) => nColACB.
      pir (nColPerPs_1 C A B (nColPerPs_3 A C B nColACB)) => nColABC.
    }
    { erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
      pir (nColPerPs_5 B C A (nColPerPs_2 C A B
        (nColPerPs_3 A C B nColACB))) => nColACB.
      pir (nColPerPs_5 C B A (nColPerPs_2 B A C
        (nColPerPs_3 A B C nColABC))) => nColABC.
      symmetry. apply ABCeqACB.
    }
  }
  erewrite SegPs_sym. symmetry. erewrite SegPs_sym.
  destruct EqTr; auto.
Qed.

Lemma EqSupAngRs_BetRs' :
  forall (a b c a' b' c' : Ray)(diab : ![ a # b ])(dibc : ![ b # c ])
    (dia'b' : ![ a' # b' ])(dib'c' : ![ b' # c' ]),
  a == !c
    -> [| a # b | diab |] = [| a' # b' | dia'b' |]
    -> [| b # c | dibc |] = [| b' # c' | dib'c' |]
    -> ![ b' # c', !a' ]
    -> a' == !c'.
Proof with eauto.
  intros * aopc ab bc a'b'c'.
  assert (roab : da a = da b). { destruct diab... }
  assert (robc : da b = da c). { destruct dibc... }
  assert (roa'b' : da a' = da b'). { destruct dia'b'... }
  assert (rob'c' : da b' = da c'). { destruct dib'c'... }
  assert (dib'a' : ![ b' # a' ]). { apply nColRs_sym... }
  assert (a'b'_b'a' : %[ a' # b' | dia'b'] = negb (%[ b' # a' | dib'a' ])).
  { eapply (DiOsRs a' b' dia'b'). }
  apply -> (OppositeSideRs_DiOs b' a' c' dib'a' dib'c') in a'b'c'.
  assert (a'b'_b'c' : %[ a' # b' | dia'b'] = %[ b' # c' | dib'c']).
  { induction (%[ a' # b' | dia'b']),
              (%[ b' # c' | dib'c']),
              (%[ b' # a' | dib'a'])...
  }
  assert (ab_bc : %[ a # b | diab ] = %[ b # c | dibc ]).
  { apply (OpRs_EqOs_Left a b c diab dibc aopc). }
  destruct (DrawOpRay a') as [ c'' a'opc'' ].
  assert (dib'c'' : ![ b' # c'' ]).
  { apply (nColRs_inv b' (!a') c'' ).
    apply (nColOpRs_2 b' a'). apply nColRs_sym...
    apply OpRs_OpRs in a'opc''. rewrite a'opc''. symmetry.
    apply OpOpRs.
  }
  assert (b'c' : [|b' # c' | dib'c'|] = [|b' # c'' | dib'c''|]).
  { rewrite <- bc.
    apply (EqSupConvexAngRs' a b c a' b' c'' diab dibc dia'b')...
    apply OpRs_sym... apply OpRs_OpRs in a'opc''. rewrite a'opc''.
    apply OpOpRs.
  }
  assert (a'b'_b'c'' : %[ a' # b' | dia'b'] = %[ b' # c'' | dib'c'' ]).
  { apply (OpRs_EqOs_Left a' b' c'' dia'b').
    apply OpRs_OpRs...
  }
  rewrite a'b'_b'c' in a'b'_b'c''.
  eapply (SameSideRs_EqOs b' c' c'') in a'b'_b'c''.
  assert (c'eqc'' : c' == c'').
  { apply -> (SameSideRs_EqConvexAs_EqRs b' c' c'')... }
  rewrite c'eqc''. apply OpRs_OpRs...
Qed.
Lemma EqSupAngPs_BetPs' :
  forall (O A B C O' A' B' C' : Point)
    (nColAOB : ~ [ A, O, B ])(nColBOC : ~ [ B, O, C ])
    (nColA'O'B' : ~ [ A', O', B' ])(nColB'O'C' : ~ [ B', O', C' ]),
  [ A # O # C ]
    -> [| A # O # B | nColAOB |] = [| A' # O' # B' | nColA'O'B' |]
    -> [| B # O # C | nColBOC |] = [| B' # O' # C' | nColB'O'C' |]
    -> [ A' | O' # B' | C' ]
    -> [ A' # O' # C' ].
Proof with eauto.
  intros * BetAOC AOB BOC AOBC.
  destruct (nColPs_3DiPs A O B) as [ nOeqA [ nOeqB nAeqB ]]...
  destruct (nColPs_3DiPs A' O' B') as [ nO'eqA' [ nO'eqB' nA'eqB' ]]...
  destruct (nColPs_3DiPs B O C) as [ _ [ nOeqC nBeqC ]]...
  destruct (nColPs_3DiPs B' O' C') as [ _ [ nO'eqC' nB'eqC' ]]...
  erewrite <- (EqConvexAngRsPs A O B nOeqA nOeqB) in AOB.
  erewrite <- (EqConvexAngRsPs A' O' B' nO'eqA' nO'eqB') in AOB.
  erewrite <- (EqConvexAngRsPs B O C nOeqB nOeqC) in BOC.
  erewrite <- (EqConvexAngRsPs B' O' C' nO'eqB' nO'eqC') in BOC.
  erewrite <- (OpRs_BetPs A' O' C' nO'eqA' nO'eqC')...
  erewrite <- (OpRs_BetPs A O C nOeqA nOeqC) in BetAOC.
  eapply (EqSupAngRs_BetRs' ({{ O # A | nOeqA }})
    ({{ O # B | nOeqB }})({{ O # C | nOeqC }})
    ({{ O' # A' | nO'eqA' }})({{ O' # B' | nO'eqB' }})
    ({{ O' # C' | nO'eqC' }})); eauto; split...
  split.
  { simpl; rewrite <- OpRays_0... }
  { apply OppositeSide_OpRs_SameSideRs; simpl... }
Qed.

Definition DrawMiddlePoint :
  forall (A B : Point),
  A <> B
    -> { O : Point | [ A -- O -- B ] }.
Proof with eauto.
  intros A B nAeqB.
  destruct (DrawExtensionLinePP A B nAeqB) as [ x [ Aox Box ]].
  destruct (DrawPointApartLine x) as [ P nPox ].
  destruct (DrawEquilateralTriangleSS A B P)
    as [ C [ AB_PC [ BC_AB AC_AB ]]]; ncolps.
  assert (nCox : ~ [ C @ x ]).
  { destruct AB_PC as [ _ [ t [ H1 [ H2 [ H3 [ H4 H5 ]]]]]].
    assert (xeqt : x = t); eqls.
  }
  destruct (DrawPointOnOppositeSide C x) as [ Q CxQ ]...
  assert (nQox : ~ [ Q @ x ]). { repeat destruct CxQ; tauto. }
  destruct (DrawEquilateralTriangleSS A B Q)
    as [ D [ AB_QD [ BD_AB AD_AB ]]].
  apply SHb_sym in AB_PC; ncolps.
  assert (nDox : ~ [ D @ x ]).
  { destruct AB_QD as [ _ [ t [ H1 [ H2 [ H3 [ H4 H5 ]]]]]].
    assert (xeqt : x = t); eqls.
  }
  assert (CxD : [C | x | D]).
  { apply (OSO_trans C Q D x)...
    destruct AB_QD as [ _ [ t [ H1 [ H3 H4 ]]]].
    assert (xeqt : x = t); eqls.
  }
  clear dependent Q.
  assert (nCeqD : C <> D); dips.
  destruct (DrawExtensionLinePP C D nCeqD) as [ y [ Coy Doy ]].
  assert (nxpary : x >< y). { apply (OS_IncPs_ConvLs C D x)... }
  destruct (DrawIntersectionPointLL x y nxpary) as [ O [ Oox Ooy ]].
  exists O.
  destruct CxD as [ _ [ _ [ O' [ Oox' BetCOD ]]]].
  assert (Ooy' : [ O' @ y ]); incpt 2.
  assert (OeqO' : O = O').
  { apply (DiLs_EqPs O O' x y).
    contradict nxpary. subst y. tauto. do 2 split...
  }
  subst O'. clear Oox' Ooy'.
  assert (nAeqO : A <> O).
  { intros AeqO; subst O.
    assert (nBoy : ~ [ B @ y ]).
    { destruct nxpary as [ nxeqy _ ]. contradict nxeqy; eqls. }
    assert (BetCBD : [C # B # D]).
    { eapply (EqSupAngPs_BetPs' A C B D B C A D)...
      { apply (IsoscelesTr_EqConvexAs' C A B).
        rewrite SegPs_sym. rewrite AC_AB. symmetry. rewrite SegPs_sym...
      }
      { erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
        apply (IsoscelesTr_EqConvexAs' D B A).
        rewrite SegPs_sym. rewrite BD_AB. symmetry. rewrite SegPs_sym...
      }
      split; dips.
      exists x; repeat split...
    }
    contradict nBoy...
    incpt 2.
  }
  assert (nBeqO : B <> O).
  { intros BeqO. subst O.
    { assert (nAoy : ~ [ A @ y ]).
      { destruct nxpary as [ nxeqy _ ]. contradict nxeqy; eqls. }
      assert (BetCAD : [C # A # D]).
      { eapply (EqSupAngPs_BetPs' B C A D A C B D)...
        { apply (IsoscelesTr_EqConvexAs' C B A).
          rewrite SegPs_sym. rewrite BC_AB. symmetry.
          rewrite SegPs_sym...
        }
        { erewrite ConvexAngPs_sym.
          symmetry. erewrite ConvexAngPs_sym.
          apply (IsoscelesTr_EqConvexAs' D A B).
          rewrite SegPs_sym. rewrite AD_AB. symmetry.
          rewrite SegPs_sym...
        }
        split; dips.
        exists x; repeat split...
      }
      contradict nAoy...
      incpt 2.
    }
  }
  split.
  { destruct (DecidePointsBetweenness A O B nAeqO (not_eq_sym nBeqO) nAeqB)
      as [[ AOB | OBA ]| OAB ]; try exists x...
    { destruct (DrawSegmentOnOppositeRay A B B O)
        as [ Q [ H1 AQ_BO ]]; dips.
      assert (BAQ : [B # A # Q]).
      { destruct H1 as [ H1 |[ H2 H3 ]]...
        contradict nBeqO. subst Q.
        symmetry in AQ_BO. apply EqSgs_EqPs in AQ_BO...
      }
      clear H1.
      assert (nColCBO : ~ [ C, B, O ]); ncolps.
      assert (nColDBO : ~ [ D, B, O ]); ncolps.
      assert (Qox : [ Q @ x ]); incpt 2.
      assert (nAeqQ : A <> Q); dips.
      assert (nColCAQ : ~ [ C, A, Q ]); ncolps.
      assert (nColDAQ : ~ [ D, A, Q ]); ncolps.
      assert (TrEq : {{ C # B # O | nColCBO }} :=: {{C # A # Q | nColCAQ }}).
      { apply SAS'...
        { rewrite SegPs_sym. symmetry.
          rewrite SegPs_sym. rewrite BC_AB...
        }
        eapply (EqSupConvexAngPs' B A C O A B C Q); betps.
        erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
        symmetry. apply (IsoscelesTr_EqConvexAs' C B A)... rewrite SegPs_sym.
        rewrite BC_AB. rewrite <- AC_AB. apply SegPs_sym.
      }
      apply EqPerTr_4 in TrEq.
      assert (COB : [|C # O # B | nColPerPs_4 C B O nColCBO|] =
        [|C # Q # A | nColPerPs_4 C A Q nColCAQ|]).
      { destruct TrEq as [ _ [ _ [ _ [ H _ ]]]]; simpl in *... }
      clear TrEq.
      assert (TrEq : {{ D # B # O | nColDBO }} :=: {{D # A # Q | nColDAQ }}).
      { apply SAS'...
        rewrite SegPs_sym. symmetry. rewrite SegPs_sym. rewrite BD_AB...
        eapply (EqSupConvexAngPs' B A D O A B D Q); betps.
        erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
        symmetry. apply (IsoscelesTr_EqConvexAs' D B A)... rewrite SegPs_sym.
        rewrite BD_AB. rewrite <- AD_AB. apply SegPs_sym.
      }
      apply EqPerTr_4 in TrEq.
      assert (DOB : [|D # O # B | nColPerPs_4 D B O nColDBO|] =
        [|D # Q # A | nColPerPs_4 D A Q nColDAQ|]).
      { destruct TrEq as [ _ [ _ [ _ [ H _ ]]]]; simpl in *... }
      clear TrEq.
      assert (BetCQD : [C # Q # D]).
      { eapply (EqSupAngPs_BetPs' O C B D Q C A D)...
        { erewrite ConvexAngPs_sym in DOB. symmetry in DOB.
          erewrite ConvexAngPs_sym in DOB. symmetry...
        }
        repeat split.
        { apply BetPs_3DiPs in BAQ. destruct BAQ as [ _ [ H _ ]]... }
        { exists x. repeat split... }
      }
      destruct nxpary as [ nxeqy nxpary ].
      contradict nxeqy. apply (DiPs_EqLs A B x y nAeqB).
      assert (Qoy : [ Q @ y ]). { incpt 2. }
      assert (OBAQ : [O # B # A # Q]). { apply BetPs_b_trans... }
      destruct OBAQ as [ _ [ OBQ [ OAQ _ ]]].
      repeat split; incpt 2.
    }
    { destruct (DrawSegmentOnOppositeRay B A A O)
        as [ Q [ H1 AQ_BO ]]; dips.
      assert (ABQ : [A # B # Q]).
      { destruct H1 as [ H1 |[ H2 H3 ]]...
        subst Q. contradict nAeqO. symmetry in AQ_BO.
        apply EqSgs_EqPs in AQ_BO...
      }
      clear H1.
      assert (nColCAO : ~ [ C, A, O ]); ncolps.
      assert (nColDAO : ~ [ D, A, O ]); ncolps.
      assert (Qox : [ Q @ x ]); incpt 2.
      assert (nBeqQ : B <> Q); dips.
      assert (nColCBQ : ~ [ C, B, Q ]); ncolps.
      assert (nColDBQ : ~ [ D, B, Q ]); ncolps.
      assert (TrEq : {{ C # A # O | nColCAO }} :=: {{C # B # Q | nColCBQ }}).
      { apply SAS'...
        rewrite SegPs_sym. symmetry.
        rewrite SegPs_sym. rewrite AC_AB...
        eapply (EqSupConvexAngPs' A B C O B A C Q); betps.
        erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
        symmetry. apply (IsoscelesTr_EqConvexAs' C A B)... rewrite SegPs_sym.
        rewrite AC_AB. rewrite <- BC_AB. apply SegPs_sym.
      }
      apply EqPerTr_4 in TrEq.
      assert (COA : [|C # O # A | nColPerPs_4 C A O nColCAO|] =
        [|C # Q # B | nColPerPs_4 C B Q nColCBQ|]).
      { destruct TrEq as [ _ [ _ [ _ [ H _ ]]]]; simpl in *... }
      clear TrEq.
      assert (TrEq : {{ D # A # O | nColDAO }} :=: {{D # B # Q | nColDBQ }}).
      { apply SAS'...
        { rewrite SegPs_sym. symmetry.
          rewrite SegPs_sym. rewrite AD_AB...
        }
        eapply (EqSupConvexAngPs' A B D O B A D Q); betps.
        erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
        symmetry. apply (IsoscelesTr_EqConvexAs' D A B)... rewrite SegPs_sym.
        rewrite AD_AB. rewrite <- BD_AB. apply SegPs_sym.
      }
      apply EqPerTr_4 in TrEq.
      assert (DOA : [|D # O # A | nColPerPs_4 D A O nColDAO|] =
        [|D # Q # B | nColPerPs_4 D B Q nColDBQ|]).
      { destruct TrEq as [ _ [ _ [ _ [ H _ ]]]]; simpl in *... }
      clear TrEq.
      assert (BetCQD : [C # Q # D]).
      { eapply (EqSupAngPs_BetPs' O C A D Q C B D)...
        erewrite ConvexAngPs_sym in DOA. symmetry in DOA.
        erewrite ConvexAngPs_sym in DOA. symmetry... repeat split.
        apply BetPs_3DiPs in ABQ; dips.
        exists x. repeat split...
      }
      destruct nxpary as [ nxeqy nxpary ].
      contradict nxeqy. apply (DiPs_EqLs A B x y nAeqB).
      assert (Qoy : [ Q @ y ]). { incpt 2. }
      assert (OABQ : [O # A # B # Q]). { apply BetPs_b_trans... }
      destruct OABQ as [ _ [ OAQ [ OBQ _ ]]].
      repeat split; incpt 2.
    }
  }
  { assert (nColOCA : ~ [ O, C, A ]); ncolps.
    assert (nColOCB : ~ [ O, C, B ]); ncolps.
    assert (EqTr : {{ O # C # A | nColOCA }} :=: {{ O # C # B | nColOCB }}).
    { apply SAS'...
      { rewrite SegPs_sym. rewrite AC_AB.
        rewrite <- BC_AB. apply SegPs_sym.
      }
      erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
      assert (nColBCD : ~ [ B, C, D ]).
      { contradict nBeqO. apply (DiLs_EqPs B O x y); dils.
        do 2 split... apply (ColPs_IncPt C D B y); tauto.
      }
      assert (nColACD : ~ [ A, C, D ]).
      { contradict nAeqO. apply (DiLs_EqPs A O x y); dils.
        do 2 split... apply (ColPs_IncPt C D A y); tauto.
      }
      erewrite (ConvexAngPs_inv B C O B D).
      { symmetry.
        erewrite (ConvexAngPs_inv A C O A D).
        { apply (SSS' A C D B C D nColACD)...
          { rewrite AC_AB... }
          rewrite SegPs_sym. symmetry. rewrite SegPs_sym.
          rewrite BD_AB...
        }
        { apply SR_refl.
          contradict nColACD. subst.
          exists y; split...
        }
        apply (BetPs_SR C O D); auto.
      }
      { apply SR_refl; dips. }
      apply (BetPs_SR C O D)...
    }
    unfold EqTriangle in *; simpl in *.
    destruct EqTr as [ _ [ _ [ H1 _ ]]].
    rewrite SegPs_sym. rewrite H1. apply SegPs_sym.
  }
  Unshelve.
  ncolps. ncolps. ncolps. ncolps. ncolps. ncolps. ncolps. ncolps.
  ncolps. ncolps. ncolps. ncolps. ncolps. ncolps. ncolps. ncolps.
  ncolps. ncolps. ncolps. ncolps. ncolps. ncolps. ncolps. ncolps.
  ncolps. ncolps. ncolps. ncolps. ncolps. ncolps. ncolps. ncolps.
  ncolps. ncolps. ncolps.
Defined.

Lemma UniqueMiddlePoint :
  forall A O O' B : Point,
  [ A -- O -- B ]
    -> [ A -- O' -- B ]
    -> O = O'.
Proof with eauto.
  intros A B C D [ ABD AB_BD ][ ACD AC_CD ].
  rewrite SegPs_sym in AB_BD. rewrite SegPs_sym in AC_CD.
  destruct (classic (B = C)) as [ BeqC | nBeqC ]...
  destruct (BetPs_3DiPs A B D ABD) as [ nAeqB [ nBeqD nAeqD ]].
  destruct (BetPs_3DiPs A C D ACD) as [ nAeqC [ nCeqD _ ]].
  destruct (BetPs_ColPs A B D ABD) as [ x [ Aox [ Box Dox ]]].
  assert (Cox : [ C @ x ]); incpt 2.
  destruct (DecidePointsBetweenness A B C) as [[ H1 | H2 ]| H3 ]...
  { assert (Ord : [ A # B # C # D ]). { apply (BetPs_c_trans A B C D)... }
    assert (AB_AC : [|A, B|] << [|A, C|]). { apply (BetPs_LtS A B C)... }
    assert (CD_BD : [|C, D|] << [|B, D|]).
    { rewrite (SegPs_sym C D). rewrite (SegPs_sym B D).
      apply (BetPs_LtS)... apply BetPs_sym.
      destruct Ord as [ _ [ _ [ _ H ]]]...
    }
    rewrite <- AC_CD in CD_BD. rewrite <- AB_BD in CD_BD.
    apply LtS_asymm in CD_BD. contradiction.
  }
  { assert (Ord : [ A # C # B # D ]).
    { apply (BetPs_c_trans A C B D)... apply BetPs_sym... }
    assert (AC_AB : [|A, C|] << [|A, B|]).
    { apply (BetPs_LtS A C B); betps. }
    assert (BD_CD : [|B, D|] << [|C, D|]).
    { rewrite (SegPs_sym B D). rewrite (SegPs_sym C D).
      apply (BetPs_LtS D B C)... apply BetPs_sym.
      destruct Ord as [ _ [ _ [ _ H ]]]...
    }
    rewrite <- AB_BD in BD_CD. rewrite <- AC_CD in BD_CD.
    apply LtS_asymm in BD_CD; eqps.
  }
  { assert (Ord : [ C # A # B # D ]).
    { apply (BetPs_b_trans C A B D)... apply BetPs_sym... }
    apply BetPs_nBetPerPs in ACD.
    destruct Ord as [ _ [ H _ ]]. contradiction.
  }
Qed.

(** Problem #31 *)
(** Hilbert, Chapter 1 : Theorem 26. *)
(** Euclid, Book I : Proposition 10. *)
(* To bisect a given finite straight line. *)
Definition DrawHalfLength :
  forall (a : Length),
  a <> L0
    -> { b : Length | b ++ b = a }.
Proof with eauto.
  intros a naeqL0.
  destruct (DrawSegment a) as [[ A B ] ABa ]; subst.
  assert (nAeqB : A <> B). { contradict naeqL0. subst. apply NullSeg_def. }
  destruct (DrawMiddlePoint A B nAeqB) as [ C [ ACB CACB ]].
  exists ([|C, A|]). rewrite SegPs_sym at 1. rewrite CACB.
  apply BetPs_PlusS. left...
Defined.

(** Theorem #57 *)
Lemma UniqueHalfLength :
  forall a b : Length,
  a ++ a = b ++ b
    -> a = b.
Proof with eauto.
  intros AB DE ABeqDE.
  destruct (DrawSegment AB) as [[ A B ] ABeqAB ]; subst.
  destruct (DrawSegment DE) as [[ D E ] DEeqDE ]; subst.
  destruct (classic (A = B)) as [ AeqB | nAeqB ]; subst.
  { rewrite NullSeg_def in *. rewrite PlusS_0_l in ABeqDE.
    symmetry in ABeqDE. symmetry.
    apply PlusS_EqL0 in ABeqDE; tauto.
  }
  { destruct (classic (D = E)) as [ DeqE | nDeqE ]; subst.
    { rewrite NullSeg_def in *. rewrite PlusS_0_l in ABeqDE.
      apply PlusS_EqL0 in ABeqDE; tauto.
    }
    { destruct (DrawOppositePoint B A ) as [ C [ BetABC AB_BC ]]; auto.
      destruct (DrawOppositePoint E D ) as [ F [ BetDEF DE_EF ]]; auto.
      assert (AC_DF : [|A, C|] = [|D, F|]).
      { rewrite SegPs_sym in AB_BC. rewrite AB_BC in ABeqDE at 2.
        rewrite BetPs_PlusS in ABeqDE... rewrite SegPs_sym in DE_EF.
        rewrite DE_EF in ABeqDE at 2. rewrite BetPs_PlusS in ABeqDE...
      }
      destruct (DrawSegmentCut A B C D F BetABC)
        as [ E' [ BetDE'F [ AB_DE BC_EF ]]]; auto.
      assert (EeqE' : E = E'); subst...
      { apply (UniqueMiddlePoint D E E' F); split; auto.
        rewrite <- BC_EF. rewrite SegPs_sym. rewrite <- AB_DE.
        rewrite SegPs_sym; auto.
      }
    }
  }
Qed.

(** Theorem #58 *)
(** Euclid, Book I : Proposition 15. *)
(* If two straight lines cut one another,
 then they make the vertical angles equal to one another. *)
Proposition BetPs_EqVertAngPs :
  forall (O A B A' B' : Point)(nColAOB : ~ [ A, O, B ])
         (nColA'OB' : ~ [ A', O, B' ]),
  [ A # O # A' ]
    -> [ B # O # B' ]
    -> [| A # O # B | nColAOB |] = [| A' # O # B' |nColA'OB' |].
Proof with eauto.
  intros O A B A' B' nColAOB nColA'OB' BetAOA' BetBOB'.
  erewrite ConvexAngPs_sym.
  assert (nColA'OB : ~ [A', O, B]).
  { contradict nColAOB. destruct nColAOB as [ x [ H1 [ H2 H3 ]]].
    exists x; repeat split; incpt.
  }
  assert (nColBOA' : ~ [B, O, A']).
  { contradict nColA'OB. destruct nColA'OB as [ x [ H1 [ H2 H3 ]]].
    exists x; repeat split; incpt.
  }
  eapply (EqSupConvexAngPs' O A' B A O B A' B'); betps.
  erewrite ConvexAngPs_sym. reflexivity.
  Unshelve.
  ncolperps. ncolps. ncolps.
Qed.
Lemma EqVertConvexAngRs :
  forall (a b : Ray)(diab : ![ a # b ])(dia'b' : ![ !a # !b ]),
  [| a # b | diab |] = [| !a # !b | dia'b' |].
Proof with geo.
  intros [ O A nOeqA ][ O' B nOeqB ][ roab diab ][ roa'b' dia'b' ].
  simpl in *. subst O'. unfold OpRay in *; simpl in *.
  destruct (DrawOppositePoint O A nOeqA) as [ A' [ AOA' OA_OA' ]].
  destruct (BetPs_3DiPs A O A' AOA') as [ nAeqO [ nOeqA' nAeqA' ]].
  destruct ( DrawOppositePoint O B nOeqB) as [ B' [ BOB' OB_OB' ]].
  destruct (BetPs_3DiPs B O B' BOB') as [ nBeqO [ nOeqB' nBeqB' ]].
  simpl in *.
  erewrite (EqConvexAngRsPs A O B). pir roa'b' => (eq_refl O).
  erewrite (EqConvexAngRsPs A' O B').
  apply BetPs_EqVertAngPs...
Qed.

Lemma OpRs_OpRs_EqVertConvexAngRs :
  forall (a b c d : Ray)(diab : ![ a # b ]),
  a == !c
    -> b == !d
    -> exists (dicd : ![ c # d ]), [| a # b | diab |] = [| c # d | dicd |].
Proof with eauto.
  intros a b c d diab aopc bopd.
  assert (dicd : ![ c # d ]). { apply (nColRs_nColOpRs a b c d)... }
  exists dicd.
  erewrite (EqVertConvexAngRs a b diab). apply EqConvexAs_inv...
  { apply OpRs_sym in aopc. symmetry... }
  { apply OpRs_sym in bopd. symmetry... }
  Unshelve.
  apply (nColOpRs_2 (!a) b)...
  apply (nColOpRs_1 a b diab)...
Qed.

(** Problem #32 *)
(** Euclid, Book I : Proposition 17. *)
(* In any triangle the sum of any two angles
 is less than two right angles. *)
Definition DrawPointOfEqVertAngPs :
  forall (A B C D : Point)(nColBAC : ~ [ B, A, C ]),
  [ B # C # D ]
    -> { E : Point | [ A # E # D ] /\ exists (nColECA : ~ [ E, C, A ]),
         [| B # A # C | nColBAC |] = [| E # C # A | nColECA |] }.
Proof with eauto.
  intros * BCD.
  destruct (DrawMiddlePoint A C) as [ F [ AFC FA_FC ]]; dips.
  destruct (DrawOppositePoint F B) as [ G [BFG H ]].
  { contradict nColBAC; subst; colps. }
  destruct (DrawExtensionLinePP A C ) as [ x [ Aox Cox ]]; dips.
  assert (nBox : ~ [ B @ x ]); nincpt.
  assert (nGox : ~ [ G @ x ]). { contradict nBox; incpt. }
  assert (nDox : ~ [ D @ x ]). { contradict nBox; incpt. }
  assert (Fox : [ F @ x ]); incpt.
  assert (nColGCA : ~ [G, C, A]).
  { contradict nGox. apply (ColPs_IncPt_6 A C G); dips. }
  assert (ACsfGD : [A # C | G, D]).
  { split; dips.
    exists x; do 2 try split...
    apply (OOS_trans G B D x); do 2 try split...
    exists F; split; betps.
  }
  destruct (DrawExtensionLinePP D C ) as [ y [ Doy Coy ]]; dips.
  assert (Boy : [ B @ y ]); incpt 2.
  assert (nAoy : ~ [ A @ y ]); nincpt 2.
  assert (nGoy : ~ [ G @ y ]). { contradict nAoy; incpt 3. }
  assert (nFoy : ~ [ F @ y ]). { contradict nGoy; incpt 2. }
  assert (DCsfGA : [D # C | G, A]).
  { split; dips.
    exists y; do 2 try split...
    apply (SS_trans G F A y).
    { apply (SR_SS B G F); betps. }
    { apply (SR_SS C F A); betps. }
  }
  destruct (DrawPointCrossBar C A G D) as [ E [ AED C_GE ]].
  { split.
    { apply SHa_sym... }
    { apply SHa_sym... }
  }
  exists E.
  split...
  assert (nEox : ~ [E @ x]). { contradict nDox; incpt 2. }
  assert (nColECA : ~ [E, C, A]).
  { contradict nEox. eapply (ColPs_IncPt C A E); dips. }
  exists nColECA.
  assert (nColBAF : ~ [B, A, F]).
  { contradict nColBAC.
    destruct nColBAC as [ t [ H1 [ H2 H3 ]]].
    exists t; repeat split; incpt 2.
  }
  rewrite (ConvexAngPs_inv B A C B F nColBAC nColBAF).
  { assert (nColGCF : ~ [G, C, F]).
    { contradict nColBAF.
      destruct nColBAF as [ t [ H1 [ H2 H3 ]]].
      exists t; repeat split; incpt 2.
    }
    rewrite (ConvexAngPs_inv E C A G F nColECA nColGCF).
    { assert (nColAFB : ~ [A, F, B]); ncolperps.
      assert (nColCFG : ~ [C, F, G]); ncolperps.
      assert (EqTr : {{ A # F # B | nColAFB }} :=: {{ C # F # G | nColCFG }}).
      { apply SAS'...
        { rewrite SegPs_sym. symmetry. rewrite SegPs_sym... }
        { apply (BetPs_EqVertAngPs F A B C G)... }
      }
      destruct EqTr as [ _ [ _ [ _ [ _ [ _ H1 ]]]]]; simpl in *.
      pir (nColPerPs_2 A F B nColAFB) => nColBAF.
      pir (nColPerPs_2 C F G nColCFG) => nColGCF.
    }
    apply SR_sym...
    destruct ((proj1 (BetPs_SR A F C)) AFC) as [ H1 H2 ].
    apply SR_sym...
  }
  apply SR_refl; dips.
  destruct ((proj1 (BetPs_SR A F C)) AFC) as [ H1 H2 ].
  apply SR_sym...
Defined.

(** Problem #33 *)
(** Hilbert, Chapter 1 : Theorem 22. *)
(** Euclid, Book I : Proposition 16. *)
(* In any triangle, if one of the sides is produced,
 then the exterior angle is greater than either
 of the interior and opposite angles. *)
Definition DrawPointOfEqConvexAngPs :
  forall (A B C D : Point)(nColABC : ~ [ A, B, C ]),
  [ B # C # D ]
    -> { E : Point | [ A # E # D ] /\ exists (nColECD : ~ [ E, C, D ]),
         [| A # B # C | nColABC |] = [| E # C # D | nColECD |] }.
Proof with eauto.
  intros * BCD.
  destruct (DrawOppositePoint C A) as [ E [ ACE _ ]]; dips.
  destruct (DrawPointOfEqVertAngPs B A C E nColABC) as [ F [ BFE H1 ]]...
  assert (nColFCB : ~ [F, C, B]). { destruct H1... }
  assert (ABC_FCB : [|A # B # C | nColABC|] = [|F # C # B | nColFCB|]).
  { destruct H1... pir x => nColFCB. }
  clear H1.
  assert (nCeqF : C <> F); dips.
  destruct (DrawOppositePoint C F) as [ G [ FCG _ ]]...
  assert (nCeqE : C <> E); dips.
  destruct (DrawExtensionLinePP C E nCeqE) as [ y [ Coy Eoy ]].
  assert (nAoy : [ A @ y ]); incpt 2.
  assert (nBoy : ~ [ B @ y ]); nincpt 2.
  assert (nFoy : ~ [ F @ y ]). { contradict nBoy; incpt 2. }
  assert (nGoy : ~ [ G @ y ]). { contradict nFoy; incpt 2. }
  assert (SSyBF : [ y | B, F ]).
  { apply BetPs_sym in BFE. apply SS_sym.
    apply (SR_SS E F B y Eoy); betps.
  }
  destruct (nColPs_3DiPs A B C nColABC) as [ nAeqB [ nBeqC nAeqc ]].
  destruct (BetPs_3DiPs B C D BCD) as [ _ [ nCeqD nBeqD ]].
  destruct (DrawExtensionLinePP B C nBeqC) as [ x [ Box Cox ]].
  assert (Dox : [ D @ x ]); incpt 2.
  assert (nDoy : ~ [ D @ y ]).
  { contradict nBoy. apply (BetPs_IncPt D C B); tauto. }
  assert (OSyBD : [ B | y | D ]). { repeat split... }
  assert (OSyFG : [ F | y | G ]). { repeat split... }
  assert (nFox : ~ [ F @ x ]). { clear ABC_FCB. contradict nColFCB... }
  assert (nGox : ~ [ G @ x ]). { contradict nFox; incpt 2. }
  assert (SSxFE : [ x | F, E ]). { apply (SR_SS B F E x Box nFox); betps. }
  assert (nEox : ~ [ E @ x ]). { destruct SSxFE as [ _ [ H1 _ ]]... }
  assert (nAox : ~ [ A @ x ]). { contradict nEox; incpt 2. }
  assert (OSxAE : [ A | x | E ]). { repeat split... }
  assert (OSxFG : [ F | x | G ]). { repeat split... }
  destruct (DrawPointCrossBar C A G D) as [ K [ AKD C_GK ]].
  { repeat split...
    { exists y.
      do 2 try split...
      apply (OOS_trans G B D y)... apply OS_sym... apply OS_sym.
      apply (OSO_trans G F B y)... apply OS_sym... apply SS_sym...
    }
    { exists x.
      do 2 try split...
      apply (OOS_trans G F A x)... apply OS_sym... apply OS_sym.
      apply (OSO_trans A E F x)... apply SS_sym...
    }
  }
  exists K; split; auto.
  assert (nKox : ~ [ K @ x ]). { contradict nGox; incpt 2. }
  assert (nColKCD : ~ [K, C, D]). { contradict nKox; incpt 2. }
  exists nColKCD.
  rewrite ABC_FCB.
  apply (BetPs_EqVertAngPs C F B K D ); betps.
Defined.

Definition DrawPointOfEqAngleOnOtherSide :
  forall (A B C D : Point)(nColABC : ~ [ A, B, D ]),
  [ A # D # C ]
  -> { E : Point | [ A # E # C ] /\ exists (nColCBE : ~ [ C, B, E ]),
        [| A # B # D | nColABC |] = [| C # B # E | nColCBE |] }.
Proof with eauto.
  intros A C B D nColACD ADB.
  destruct (nColPs_3DiPs A C D nColACD )
    as [ nAeqC [ nCeqD nAeqD ]]. apply not_eq_sym in nAeqC.
  destruct (BetPs_3DiPs A D B ADB )
    as [ _ [ nDeqB nAeqB ]].
  assert (nCeqB : C <> B).
  { contradict nColACD. subst C; colps. }
  destruct (DrawPointProjectionOnRay C B A)
    as [ B' [ H1 CB_CA ]]...
  assert (CsrBB' : [C # B, B']).
  { destruct H1 as [ H1 |[ H2 | H3 ]]...
    { subst. contradiction. }
    { subst B'. symmetry in CB_CA.
      apply EqSgs_EqPs in CB_CA. subst. contradiction.
    }
  }
  clear H1.
  destruct (DrawPointCrossBar C A D B')
    as [ D' [ AD'B' CsrDD' ]]; betps.
  { apply (BR_inv C A D B A D B'); betps.
    apply (nColPs_BetPs_BR C A D B)...
    contradict nColACD. colperps 4.
  }
  destruct (DrawSegmentOnRay B' A A D')
    as [ E' [ H1 B'E'_AD' ]]; dips.
  assert (B'_AE' : [B' # A, E']).
  { destruct H1 as [ H1 |[ H2 | H3 ]]...
    { contradict H2. dips. }
    { subst E'.
      symmetry in B'E'_AD'. apply EqSgs_EqPs in B'E'_AD'.
      symmetry in B'E'_AD'. apply BetPs_3DiPs in AD'B'.
      destruct AD'B'. contradict H...
    }
  }
  clear H1.
  assert (AE'B' : [A # E' # B']).
  { destruct (DiPs_BetPs_SubtractSgs A D' B' B' E' A) as [ H1 _ ]; dips; betps.
    apply SegPs_sym.
  }
  assert (nColCAB : ~ [C, A, B]).
  { contradict nColACD.
    destruct nColACD as [ x [ Cox [ Aox Box ]]].
    exists x; repeat split; incpt 2.
  }
  assert (nColCAB' : ~ [ C, A, B' ]).
  { contradict nColCAB.
    destruct CsrBB' as [ H1 [ H2 [ H3 H4 ]]]. colperps 4.
  }
  assert (C_AD'B' : [ C | A; D'; B' ]).
  { apply (nColPs_BetPs_BR C A D' B')... }
  destruct (DrawPointCrossBar C A E' B) as [ E [ AEB CsrEE' ]].
  { apply (BR_inv C A E' B' A E' B).
    { apply (nColPs_BetPs_BR C A E' B')... }
    { apply SR_refl... }
    { apply SR_refl... intros CeqE'. subst E'.
      contradict nColCAB'; colps.
    }
    apply SR_sym...
  }
  exists E.
  split...
  assert (nColBCE : ~ [B, C, E]).
  { apply (nColPs_SR_inv C B' E B E).
    { contradict nColCAB'.
      destruct nColCAB' as [ t [ H1 [ H2 H3 ]]].
      exists t; repeat split; incpt.
    }
    apply SR_sym... apply SR_refl; dips.
  }
  exists nColBCE.
  assert (nColACD' : ~ [A, C, D']).
  { destruct C_AD'B'. eapply SH_nColPs. apply SHa_sym... }
  assert (nColB'CE' : ~ [B', C, E']).
  { apply (nColPs_SR_inv C B E B' E'); betps. }
  rewrite (ConvexAngPs_inv A C D A D' nColACD nColACD'); betps.
  rewrite (ConvexAngPs_inv B C E B' E' nColBCE nColB'CE'); betps.
  assert (EqTr : {{ D' # A # C | nColPerPs_2 A C D' nColACD' }}
    :=: {{ E' # B' # C | nColPerPs_2 B' C E' nColB'CE' }}).
  { apply SAS'.
    { rewrite SegPs_sym. symmetry. rewrite SegPs_sym... }
    { rewrite SegPs_sym. symmetry. rewrite SegPs_sym... }
    { erewrite (ConvexAngPs_inv D' A C B' C); betps.
      erewrite (ConvexAngPs_inv E' B' C A C); try apply SR_refl; betps; dips.
      erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
      apply (IsoscelesTr_EqConvexAs' C B' A)...
    }
  }
  apply EqPerTr_1 in EqTr.
  pir (nColPerPs_1 D' A C (nColPerPs_2 A C D' nColACD'))
    => nColACD'.
  pir (nColPerPs_1 E' B' C (nColPerPs_2 B' C E' nColB'CE'))
    => nColB'CE'.
  destruct EqTr as [ _ [ _ [ _ [ H _ ]]]]; simpl in *...
  Unshelve. ncolperps. ncolperps. ncolps. ncolperps.
Defined.

(** Problem #34 *)
(** Euclid, Book I : Proposition 18. *)
(* In any triangle the angle opposite the greater side is greater. *)
Definition DrawSmallerAngInsideBigger :
  forall (A B C : Point)(nColABC : ~ [ A, B, C ]),
  [| A, C |] << [| A, B |]
    -> { D : Point | [ A # D # B ] /\ exists (nColBCD : ~ [ B, C, D ]),
         [| A # B # C | nColABC |] = [| B # C # D | nColBCD |] }.
Proof with eauto.
  intros B A C nColBAC AB_BC.
  destruct (DrawPointProjectionOnRay B A C) as [ D [ H1 H2 ]]; dips.
  assert (B_AD : [B # A, D]).
  { destruct H1 as [ H1 |[ H1 | H1 ]]...
    { contradict H1; dips. }
    { subst D. symmetry in H2.
      apply EqSgs_EqPs in H2. subst.
      apply nColPs_3DiPs in nColBAC; tauto.
    }
  }
  clear H1.
  assert (BDA : [B # D # A]).
  { rewrite <- H2 in AB_BC.
    unfold LtS in AB_BC.
    apply (LtS_SR_BetPs B D A); betps; dips.
  }
  assert (nAeqD : A <> D).
  { intros AeqD.
    subst D. unfold LtS in *. rewrite H2 in *.
    apply (LtS_irrefl ([|B, C|]))...
  }
  assert (nAeqC : A <> C); dips.
  assert (nColCAD : ~ [C, A, D]).
  { destruct B_AD as [ nAeqB [ nBeqD [ ColBAD H3 ]]].
    contradict nColBAC. destruct nColBAC as [ x [ H1 [ H5 H4 ]]].
    exists x; repeat split; incpt 2.
  }
  destruct (DrawPointOfEqConvexAngPs C A D B nColCAD) as [ E H ].
  { apply BetPs_sym. apply LtS_SR_BetPs; betps; dips. }
  destruct H as [ CEB H ].
  assert(nColEDB : ~ [E, D, B]). { destruct H... }
  assert (CAD_EDB : [|C # A # D | nColCAD|] =[|E # D # B | nColEDB|]).
  { destruct H... pir x => nColEDB. }
  clear H.
  destruct (DrawPointProjectionOnRay B D E) as [ F [ G0 H3 ]]; dips.
  assert(B_DF : [B # D, F]).
  { destruct G0 as [ H |[ H | H ]]...
    { contradict H; dips. }
    { subst F. symmetry in H3.
      apply EqSgs_EqPs in H3. subst E.
      destruct (BetPs_3DiPs C B B CEB) as [ G1 [ G2 G3 ]].
      contradict G2...
    }
  }
  assert (BFD : [B # F # D]).
  { destruct (BetPs_SubtractSgs B E C B F D) as [ H0 H1 ]; ord. }
  assert (BFA : [B # F # A]). { apply (BetPs_b_trans B F D A); betps. }
  assert (nBeqF : B <> F); dips.
  assert (nColBCF : ~ [B, C, F]).
  { clear CAD_EDB. contradict nColCAD.
    apply BetPs_ColPs in BFD. apply BetPs_ColPs in BFA.
    apply (ColPs_5_trans B F C A D); colperps.
  }
  destruct (DrawPointOfEqAngleOnOtherSide B C A F nColBCF) as [ G H ]...
  exists G.
  destruct H as [ BGA [ nColACG ACG_BCG ]].
  split...
  exists nColACG.
  rewrite <- ACG_BCG.
  erewrite (ConvexAngPs_inv C A D C B nColCAD) in CAD_EDB; betps.
  erewrite ConvexAngPs_sym. rewrite CAD_EDB.
  assert (nColDBE : ~ [D, B, E]); ncolperps.
  assert (nColCBF : ~ [C, B, F]); ncolperps.
  assert (EqTr : {{ D # B # E | nColDBE }} :=: {{ C # B # F | nColCBF }}).
  { apply SAS'...
    rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
    assert (nColDBC : ~ [D, B, C]).
    { eapply (nColPs_SR_inv B D E D C); betps. }
    assert (nColCBD : ~ [C, B, D]); ncolperps.
    rewrite (ConvexAngPs_inv D B E D C nColDBE nColDBC); betps.
    rewrite (ConvexAngPs_inv C B F C D nColCBF nColCBD);
    try apply SR_refl; betps; dips.
    erewrite ConvexAngPs_sym.
    pir(nColPerPs_5 D B C nColDBC) => nColCBD.
  }
  destruct EqTr as [ _ [ _ [ _ [ _ [ _ H ]]]]]; simpl in *.
  pir (nColPerPs_2 D B E nColDBE) => nColEDB.
  symmetry. erewrite ConvexAngPs_sym.
  pir (nColPerPs_5 B C F nColBCF) => (nColPerPs_2 C B F nColCBF).
  symmetry. apply H.
  Unshelve. ncolperps.
Defined.

(** Theorem #59 *)
(** Euclid, Book I : Proposition 20. *)
(* In any triangle the sum of any two sides is greater
 than the remaining one. *)
Proposition TriangleInequality :
  forall A B C : Point,
  ~ [ A, B, C ]
    -> [| A, C |] << [| A, B |] ++ [| B, C |].
Proof with eauto.
  intros * nColABC.
  destruct (nColPs_3DiPs A B C nColABC)
    as [ nAeqB [ nBeqC nAeqc ]].
  destruct (DrawIntersectionPointLC B A C)
    as [ D [ H BD_BC ]]...
  assert (ABD : [A # B # D]).
  { destruct H as [ H |[ H1 H2 ]]...
    subst D. symmetry in BD_BC.
    apply EqSgs_EqPs in BD_BC. contradiction.
  }
  clear H.
  destruct (BetPs_3DiPs A B D) as [ _ [ nBeqD nAeqD ]]...
  assert ( nColACD : ~ [A, C, D]).
  { apply BetPs_ColPs in ABD. contradict nColABC.
    destruct ABD as [ x [ H1 [ H2 H3 ]]].
    exists x; repeat split... incpt 2.
  }
  assert ( nColADC : ~ [A, D, C]); ncolperps.
  assert ( nColBCD : ~ [B, C, D]).
  { apply BetPs_ColPs in ABD. contradict nColABC; colperps. }
  assert ( nColBDC : ~ [B, D, C]); ncolperps.
  assert (BCD_BDC : [|B # C # D | nColBCD|] = [|B # D # C | nColBDC|]).
  { apply (IsoscelesTr_EqConvexAs' B C D)... }
  assert (ABBD : [|A, B|] ++ [|B, D|] = [|A, D|]).
  { apply BetPs_PlusS... }
  rewrite BD_BC in ABBD. rewrite ABBD.
  destruct (LtS_trichotomy ([| A, C |])([|A, D|]))
    as [ LT |[ EQ | GT ]]...
  { assert (ACD_ADC : [|A # C # D | nColACD|] = [|A # D # C | nColADC|]).
    { apply (IsoscelesTr_EqConvexAs' A C D)... }
    rewrite <- (ConvexAngPs_inv A D C B C nColADC) in BCD_BDC;
    try apply SR_refl; betps; dips.
    rewrite <- ACD_ADC in BCD_BDC.
    erewrite ConvexAngPs_sym in BCD_BDC. symmetry in BCD_BDC.
    erewrite ConvexAngPs_sym in BCD_BDC.
    apply SH_EqConvexAs_SR in BCD_BDC.
    { contradict nColABC.
      destruct BCD_BDC as [ _ [ _ [ H2 _ ]]]; colperps.
    }
    apply SHa_sym... apply SR_SH; ncolperps; betps.
  }
  { destruct (DrawSmallerAngInsideBigger A C D nColACD)
      as [ E [ AEC [ nColCED ECD_EDC ]]]...
    { assert ( nColECD : ~ [E, C, D]); ncolperps.
      rewrite (ConvexAngPs_inv A C D E D nColACD nColECD) in ECD_EDC;
      try apply SR_refl; betps; dips.
      { erewrite (ConvexAngPs_sym C D E) in ECD_EDC...
        apply EqConvexAs_IsoscelesTr' in BCD_BDC.
        apply EqConvexAs_IsoscelesTr' in ECD_EDC.
        assert (nBeqE : B <> E).
        { intros BeqE; subst E. contradict nColABC; colps. }
        destruct (DrawExtensionLinePP B E nBeqE) as [ x [ Box Eox ]].
        assert (nAox : ~ [ A @ x ]).
        { contradict nColABC. exists x; repeat split; incpt 2. }
        assert (nCox : ~ [ C @ x ]).
        { contradict nColABC; exists x; repeat split; incpt 2. }
        assert (nDox : ~ [ D @ x ]).
        { contradict nAox; incpt 2. }
        assert (OSxAC : [ A | x | C ]). { repeat split... }
        assert (OSxAD : [ A | x | D ]). { repeat split... }
        assert (CeqD : C = D).
        { apply (EqTr_EqPs B E C D)... split...
          exists x; do 2 try split...
          apply (OOS_trans C A D x)...
          apply OS_sym...
        }
        subst D.
        ord.
      }
    }
  }
  Unshelve.
  ncolperps. ncolperps. ncolperps.
Qed.

(** Theorem #60 *)
Lemma PlusS_BetPs :
  forall A B C : Point,
  [| A, B |] ++ [| B, C |] = [| A, C |]
    -> [ A ; B ; C ].
Proof with eauto.
  intros * ABpBCeqAC.
  destruct (classic (A = B)) as [ AeqB | nAeqB ]; subst...
  destruct (classic (B = C)) as [ BeqC | nBeqC ]; subst...
  assert (nABeqL0 : [| A, B |] <> L0).
  { contradict nAeqB. apply (NullSeg_EqPs A B)... }
  assert (nBCeqL0 : [| B, C |] <> L0).
  { contradict nBeqC. apply (NullSeg_EqPs B C)... }
  destruct (DrawAdditionalSegment A B B C)
    as [ C' [ BetABC' BC'eqBC ]]...
  assert (ACeqAC' : [| A, C |] = [| A, C' |]).
  { destruct (BetPs_PlusS A B C'). left...
    rewrite BC'eqBC. rewrite ABpBCeqAC...
  }
  assert (nAeqC : A <> C).
  { intros AeqC. apply EqPs_NullSeg in AeqC.
    rewrite AeqC in *. symmetry in ACeqAC'.
    apply NullSeg_EqPs in ACeqAC'. destruct ACeqAC'.
    destruct (BetPs_3DiPs A B A BetABC') as [ _ [ _ nAeqA ]]...
  }
  destruct (classic ([A, B, C])) as [ ColABC | nColABC ].
  { destruct (DecidePointsBetweenness A B C)
      as [[ BetABC | BetBCA ]| BetBAC ]...
    { assert (ACpBCeqAB : ([| A, C |]) ++ ([| B, C |]) = ([| A, B |])).
      { rewrite (SegPs_sym A C). rewrite (SegPs_sym A B).
        rewrite (PlusS_comm ([|C, A|])([|B, C|])).
        apply (BetPs_PlusS B C A); left...
      }
      { rewrite <- ACpBCeqAB in ABpBCeqAC.
        rewrite <- (PlusS_assoc ([|A, C|])([|B, C|])([|B, C|])) in ABpBCeqAC.
        assert (ACeqAC : [|A, C|] ++ ([|B, C|] ++ [|B, C|]) = [|A, C|] ++ L0).
        { rewrite PlusS_0_r... }
        apply (PlusS_cancel_l ([|A, C|])([|B, C|] ++ [|B, C|]) L0) in ACeqAC.
        destruct (PlusS_EqL0 ([|B, C|])([|B, C|]) ACeqAC) as [ BCeqL0 _ ].
        contradiction.
      }
    }
    assert (ABpACeqBC : ([| A, B |]) ++ ([| A, C |]) = ([| B, C |])).
    { rewrite (SegPs_sym A B). apply (BetPs_PlusS B A C); left... }
    rewrite <- ABpACeqBC in ABpBCeqAC.
    rewrite (PlusS_assoc ([|A, B|])([|A, B|])([|A, C|])) in ABpBCeqAC.
    rewrite (PlusS_comm ([|A, B|] ++ [|A, B|])([|A, C|])) in ABpBCeqAC.
    assert (ACeqAC : [|A, C|] ++ ([|A, B|] ++ [|A, B|]) = [|A, C|] ++ L0).
    { rewrite PlusS_0_r... }
    apply (PlusS_cancel_l ([|A, C|])([|A, B|] ++ [|A, B|]) L0) in ACeqAC.
    destruct (PlusS_EqL0 ([|A, B|])([|A, B|]) ACeqAC) as [ BCeqL0 _ ].
    contradiction.
  }
  { exfalso.
    assert (H : [|A, C|] << [|A, B|] ++ [|B, C|]).
    apply TriangleInequality...
    rewrite ABpBCeqAC in H. apply LtS_irrefl in H...
  }
Qed.

(** Theorem #61 *)
Lemma IntersectionOfTwoCircles :
  forall (A O B A' O' B' P : Point),
  ~ [ O, O', P ]
    -> [| O, A |] = [| O, P |]
    -> [| O', A' |] = [| O', P |]
    -> [ A -- O -- B ]
    -> [ A' -- O' -- B' ]
    -> [ A # O # O' # B' ]
    -> [ A # A' # B # B' ].
Proof with eauto.
  intros * nColOO'P OA_OP O'A'_O'P [ AOB OA_OB ][ A'O'B' O'A'_O'B' ].
  intros [ AOO' [ AOB' [ AO'B' OO'B' ]]].
  assert (AA'O' : [ A # A' # O']).
  { apply BetPs_sym.
    apply (LtS_SR_BetPs O' A' A); betps; dips.
    rewrite O'A'_O'P.
    rewrite <- (BetPs_PlusS O' O A); betps.
    rewrite OA_OP.
    apply (TriangleInequality O' O P); ncolperps.
  }
  assert (OBB' : [ O # B # B' ]).
  { apply (LtS_SR_BetPs O B B'); betps; dips.
    rewrite <- OA_OB. rewrite OA_OP.
    rewrite <- (BetPs_PlusS O O' B')...
    rewrite <- O'A'_O'B'. rewrite O'A'_O'P.
    apply (TriangleInequality O O' P)...
  }
  assert (AA'B' : [A # A' # B']). { apply (BetPs_b_trans A A' O' B')... }
  assert (ABB' : [A # B # B']). { apply (BetPs_b_trans A O B B')... }
  assert ( A_A'B : [ A # A', B ]). { apply (SR_trans A A' B' B); betps. }
  destruct ((proj1 (SR_BetPs A A' B)) A_A'B)
    as [ AA'B |[[ A'eqB nA'eqA ]| ABA' ]].
  { apply BetPs_b_trans; betps. }
  { exfalso. subst A'.
    apply (LtS_irrefl ([|O, O'|])).
    assert (OO : [|O, O'|] = [|O, P|] ++ [|P, O'|]).
    { rewrite <- OA_OP.
      rewrite (SegPs_sym P O')... rewrite <- O'A'_O'P.
      rewrite OA_OB. rewrite (SegPs_sym O' B)... symmetry.
      apply (BetPs_PlusS O B O'); betps.
    }
    rewrite OO at 2.
    apply TriangleInequality; ncolperps.
  }
  { exfalso.
    assert (OBA'B' : [O # B # A' # O']). { apply BetPs_b_trans; betps. }
    apply (LtS_asymm ([|O, O'|])([|O, P|] ++ [|P, O'|])).
    { apply TriangleInequality; ncolperps. }
    apply Bet4Ps_PlusS in OBA'B'.
    rewrite <- OA_OP. rewrite OA_OB.
    rewrite (SegPs_sym P O'). rewrite <- O'A'_O'P.
    rewrite (SegPs_sym O' A').
    rewrite <- OBA'B'. rewrite PlusS_assoc.
    rewrite PlusS_comm.
    rewrite <- (PlusS_comm ([|A', O'|])(([|O, B|]) ++ [|B, A'|])).
    rewrite PlusS_assoc.
    apply PlusS_LtS.
    intros BeqA'.
    apply NullSeg_EqPs in BeqA'.
    destruct (BetPs_3DiPs A B A' ABA') as [ _ [ nAeqB' _ ]]...
  }
Qed.

(** Problem #35 *)
Definition DrawPointOfEqualTriangle :
  forall (A B C D E F : Point),
  ~ [ A, B, C ]
    -> ~ [ D, E, F ]
    -> [| A, B |] = [| D, E |]
    -> { G : Point | [ D # E | F, G ] /\ [| E, G |] = [| B, C |]
                                      /\ [| D, G |] = [| A, C |] }.
Proof with eauto.
  intros O O' C Q Q' P nColOO'C nColQQ'P OO'_QQ'.
  assert (nOeqO' : O <> O'); dips.
  assert (nQeqQ' : Q <> Q'); dips.
  destruct (DrawPointProjectionOnRay O O' C)
    as [ A [ H1 OA_OP ]]...
  destruct (DrawSegmentOnRay Q Q' O C)
    as [ D [ H1' QD_QP ]]...
  destruct (DrawIntersectionPointLC O O' C)
    as [ B [ H2 OB_OP ]]...
  destruct (DrawSegmentOnOppositeRay Q Q' O C)
    as [ E [ H2' QE_QP ]]...
  destruct (DrawPointProjectionOnRay O' O C)
    as [ A' [ H3 O'A'_O'P ]]...
  destruct (DrawSegmentOnRay Q' Q O' C)
    as [ D' [ H3' Q'D'_Q'P ]]...
  destruct (DrawIntersectionPointLC O' O C)
    as [ B' [ H4 O'B'_O'P ]]...
  destruct (DrawSegmentOnOppositeRay Q' Q O' C)
    as [ E' [ H4' Q'E'_Q'P ]]...
  destruct (nColPs_3DiPs O O' C)
    as [ nO'eqO [ nO'eqC nOeqC ]]...
  assert (BetAOB : [ A # O # B ] /\ [| O, A |] = [| O, B |]).
  { destruct H1 as [ OsrO'A |[ OeqO' | OeqA ]].
    { destruct H2 as [ BetO'OB |[ OeqO' OeqB ]].
      { split.
        { apply BetPs_sym. apply (BetPs_SR_BetPs O B O' A); betps. }
        { rewrite OA_OP... }
      }
      { subst B.
        symmetry in OB_OP. apply EqSgs_EqPs in OB_OP.
        contradiction.
      }
    }
    { contradiction. }
    { subst A.
      symmetry in OA_OP. apply EqSgs_EqPs in OA_OP. subst C.
      contradiction.
    }
  }
  assert (BetDQE : [ D # Q # E ] /\ [| Q, D |] = [| Q, E |]).
  { destruct H1' as [ OsrO'A |[ OeqO' | OeqA ]].
    { destruct H2' as [ BetO'OB |[ OeqO' OeqB ]].
      { split.
        { apply BetPs_sym. apply (BetPs_SR_BetPs Q E Q' D); betps. }
        { rewrite QD_QP... }
      }
      { subst E.
        symmetry in QE_QP. apply EqSgs_EqPs in QE_QP.
        contradiction.
      }
    }
    { contradiction. }
    { subst D.
      symmetry in QD_QP. apply EqSgs_EqPs in QD_QP.
      contradiction.
    }
  }
  assert (BetA'O'B' : [ A' # O' # B' ] /\ [| O', A' |] = [| O', B' |]).
  { destruct H3 as [ O'srOA' |[ OeqO' | O'eqA' ]].
    { destruct H4 as [ BetOO'B' |[ OeqO' O'eqB' ]].
      { split.
        { apply BetPs_sym. apply (BetPs_SR_BetPs O' B' O A'); betps. }
        { rewrite O'B'_O'P... }
      }
      { subst B'.
        symmetry in O'B'_O'P. apply EqSgs_EqPs in O'B'_O'P.
        contradiction.
      }
    }
    { contradiction. }
    { subst A'.
      symmetry in O'A'_O'P. apply EqSgs_EqPs in O'A'_O'P.
      contradiction.
    }
  }
  assert (BetD'Q'E' : [ D' # Q' # E' ] /\ [| Q', D' |] = [| Q', E' |]).
  { destruct H3' as [ O'srOA' |[ OeqO' | O'eqA' ]].
    { destruct H4' as [ BetOO'B' |[ OeqO' O'eqB' ]].
      { split.
        { apply BetPs_sym. apply (BetPs_SR_BetPs Q' E' Q D'); betps. }
        { rewrite Q'E'_Q'P... }
      }
      { subst E'.
        symmetry in Q'E'_Q'P. apply EqSgs_EqPs in Q'E'_Q'P.
        contradiction.
      }
    }
    { contradict nQeqQ'... }
    { subst D'.
      symmetry in Q'D'_Q'P. apply EqSgs_EqPs in Q'D'_Q'P.
      contradiction.
    }
  }
  assert (BOO'B' : [ B # O # O' # B' ]).
  { destruct H2 as [ O'OB |[ _ OeqB ]];
    destruct H4 as [ OO'B' |[ _ O'eqB' ]].
    { apply (BetPs_b_trans B O O' B')... apply BetPs_sym... }
    { subst B'. symmetry in O'B'_O'P. apply EqSgs_EqPs in O'B'_O'P.
      contradiction.
    }
    { subst B. symmetry in OB_OP. apply EqSgs_EqPs in OB_OP.
      contradiction.
    }
    { subst B'. symmetry in O'B'_O'P. apply EqSgs_EqPs in O'B'_O'P.
      contradiction.
    }
  }
  assert (EQQ'E' : [ E # Q # Q' # E' ]).
  { destruct H2' as [ O'OB |[ _ OeqB ]];
    destruct H4' as [ OO'B' |[ _ O'eqB' ]].
    { apply (BetPs_b_trans E Q Q' E')... apply BetPs_sym... }
    { subst E'. symmetry in Q'E'_Q'P. apply EqSgs_EqPs in Q'E'_Q'P.
      contradiction.
    }
    { subst E. symmetry in QE_QP. apply EqSgs_EqPs in QE_QP.
      contradiction.
    }
    { subst E'. symmetry in Q'E'_Q'P. apply EqSgs_EqPs in Q'E'_Q'P.
      contradiction.
    }
  }
  assert (BetBA'AB' : [ B # A' # A # B' ]).
  { apply (IntersectionOfTwoCircles B O A A' O' B' C)...
    destruct BetAOB. split... apply BetPs_sym...
  }
  assert (BA_ED : [| B, A |] = [| E, D |]).
  { destruct BetAOB as [ AOB OA_OB ];
    destruct BetDQE as [ DQE QD_QE ].
    apply ( BetPs_AddSgs B O A E Q D); try apply BetPs_sym...
    { rewrite SegPs_sym. symmetry. rewrite SegPs_sym.
      rewrite QE_QP...
    }
    rewrite OA_OP...
  }
  assert (A'B'_D'E' : [|A', B'|] = [|D', E'|]).
  { destruct BetA'O'B' as [ AOB OA_OB ];
    destruct BetD'Q'E' as [ DQE QD_QE ].
    apply (BetPs_AddSgs A' O' B' D' Q' E')...
    { rewrite SegPs_sym. symmetry.
      rewrite SegPs_sym. rewrite O'A'_O'P...
    }
    rewrite O'B'_O'P...
  }
  assert (BB'_EE' : [|B, B'|] = [|E, E'|]).
  { apply (Bet4Ps_AddSgs B O O' B' E Q Q' E')...
    { rewrite SegPs_sym. rewrite OB_OP. symmetry.
      rewrite SegPs_sym. rewrite QE_QP...
    }
    rewrite O'B'_O'P. rewrite <- Q'D'_Q'P; tauto.
  }
  assert (BetED'DE' : [ E # D'# D # E' ]).
  { destruct H1 as [ OsrO'A |[ H | OeqA ]].
    { destruct H2 as [ BetO'OB |[ _ OeqB ]].
      { destruct H3 as [ O'srOA' |[ H | O'eqA' ]].
        { destruct H4 as [ O'srOB' |[ _ O'eqB' ]].
          { destruct H1' as [ QsrQ'D |[ H | QeqD ]].
            { destruct H2' as [ Q'srQE |[ _ QeqE ]].
              { destruct H3' as [ Q'srQD' |[ H | QeqD' ]].
                { destruct H4' as [ BetQQ'E' |[ _ Q'eqE' ]].
                  { assert (AOB : [ A # O # B ]).
                    { destruct BetAOB as [ AOB OA_OB ]... }
                    assert (A'O'B' : [ A' # O' # B' ]).
                    { destruct BetA'O'B' as [ A'O'B' OA'_OB' ]... }
                    assert (DQE : [ D # Q # E ]).
                    { destruct BetDQE as [ DQE QD_QE ]... }
                    assert (D'Q'E' : [ D' # Q' # E' ]).
                    { destruct BetD'Q'E' as [ D'Q'E' QD'_QE' ]... }
                    assert (BsrAB' : [ B # A, B' ]).
                    { apply (SR_trans B A O B'). apply SR_sym.
                      apply (BetPs_SR B O A)...
                      apply BetPs_sym... apply BetPs_SR...
                      apply BetPs_sym; betps.
                    }
                    assert (B'srA'B : [ B' # A', B ]).
                    { apply (SR_trans B' A' O' B). apply SR_sym.
                      apply (BetPs_SR B' O' A')...
                      apply BetPs_sym... apply BetPs_SR...
                      apply BetPs_sym; betps.
                    }
                    assert (EsrDE' : [ E # D, E' ]).
                    { apply (SR_trans E D Q E'). apply SR_sym.
                      apply (BetPs_SR E Q D)...
                      apply BetPs_sym... apply BetPs_SR...
                      apply BetPs_sym; betps.
                    }
                    assert (E'srD'E : [ E' # D', E ]).
                    { apply (SR_trans E' D' Q' E). apply SR_sym.
                      apply (BetPs_SR E' Q' D')...
                      apply BetPs_sym... apply BetPs_SR...
                      apply BetPs_sym; betps.
                    }
                    assert (ED'E' : [ E # D' # E' ]).
                    { apply BetPs_sym.
                      apply (BetPs_SubtractSgs B' A' B E' D' E)...
                      apply BetPs_sym. betps.
                      rewrite SegPs_sym. symmetry.
                      rewrite SegPs_sym...
                      rewrite SegPs_sym. symmetry.
                      rewrite SegPs_sym...
                    }
                    assert (BA'_ED' : [|B, A'|] = [|E, D'|]).
                    { rewrite SegPs_sym. symmetry.
                      rewrite SegPs_sym.
                      apply (BetPs_SubtractSgs E' D' E B' A' B)...
                      apply BetPs_sym...
                      rewrite SegPs_sym. symmetry.
                      rewrite SegPs_sym...
                      rewrite SegPs_sym. symmetry.
                      rewrite SegPs_sym...
                    }
                    assert (EDE' : [ E # D # E' ]).
                    { apply (BetPs_SubtractSgs B A B' E D E')... betps 2. }
                    assert (AB'_DE' : [|A, B'|] = [|D, E'|]).
                    { symmetry. apply (BetPs_SubtractSgs E D E' B A B')... }
                    assert (ED'D : [ E # D' # D ]).
                    { apply (BetPs_SubtractSgs B A' A E D' D)... betps 2.
                      apply SR_sym. apply (SR_trans E D E' D')...
                      destruct (BetPs_SR E D' E'); betps.
                    }
                    apply (BetPs_c_trans E D' D E')...
                  }
                  { subst E'.
                    symmetry in Q'E'_Q'P.
                    apply EqSgs_EqPs in Q'E'_Q'P.
                    apply nColPs_3DiPs in nColOO'C; tauto.
                  }
                }
                { contradict H; dips. }
                { subst D'.
                  symmetry in Q'D'_Q'P.
                  apply EqSgs_EqPs in Q'D'_Q'P.
                  apply nColPs_3DiPs in nColOO'C; tauto.
                }
              }
              { subst E.
                symmetry in QE_QP.
                apply EqSgs_EqPs in QE_QP.
                apply nColPs_3DiPs in nColOO'C; tauto.
              }
            }
            { contradict H; dips. }
            { subst D.
              symmetry in QD_QP.
              apply EqSgs_EqPs in QD_QP.
              apply nColPs_3DiPs in nColOO'C; tauto.
            }
          }
          { subst B'.
            symmetry in O'B'_O'P.
            apply EqSgs_EqPs in O'B'_O'P.
            apply nColPs_3DiPs in nColOO'C; tauto.
          }
        }
        { contradict H; dips. }
        { subst A'.
          symmetry in O'A'_O'P.
          apply EqSgs_EqPs in O'A'_O'P.
          apply nColPs_3DiPs in nColOO'C; tauto.
        }
      }
      { subst B.
        destruct BOO'B' as [ G1 _ ].
        apply BetPs_3DiPs in G1; tauto.
      }
    }
    { contradict H; dips. }
    { subst A.
      assert (OeqC : O = C).
      { eapply EqSgs_EqPs. symmetry. apply OA_OP. }
      contradiction.
    }
  }
  destruct (DrawIntersectionPointCC E Q D D' Q' E' P)
    as [ F [ H5 [ H6 H7 ]]]; try split...
  { destruct BetDQE; geo. }
  { destruct BetDQE; geo. }
  { destruct BetD'Q'E'; geo. }
  { destruct BetD'Q'E'; geo. }
  { destruct BetED'DE'... }
  { destruct BetED'DE'... }
  { exists F.
    split... split...
    { rewrite H7. rewrite Q'D'_Q'P... }
    { rewrite H6. rewrite QE_QP... }
  }
Defined.
Definition DrawEqualTriangle :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  { E' : Point & { F' : Point |
  exists (nColDE'F' : ~ [ D, E', F' ]), [ D # E, E' ] /\ [ D # E | F, F' ]
      /\ {{ A # B # C | nColABC }} :=: {{ D # E' # F' | nColDE'F' }} } }.
Proof with eauto.
  intros A B C D E F nColABC nColDEF.
  destruct (nColPs_3DiPs A B C nColABC)
    as [ nAeqB [ nBeqC nAeqC ]].
  destruct (nColPs_3DiPs D E F nColDEF)
    as [ nDeqE [ nEeqF nDeqF ]].
  apply not_eq_sym in nAeqB.
  apply not_eq_sym in nDeqE.
  edestruct (DrawSegmentOnRay D E A B)
    as [ E' [ DsrEE' ABeqDE ]]... symmetry in ABeqDE.
  assert (nColDE'F : ~ [ D, E', F ]).
  { contradict nColDEF.
    destruct DsrEE' as [[ _ [ nDeqE' [ ColDEE' _ ]]]|[ DeqE | DeqE' ]].
    { colperps. }
    { contradict DeqE; dips. }
    { subst E'. apply EqSgs_EqPs in ABeqDE. contradiction. }
  }
  destruct (DrawPointOfEqualTriangle A B C D E' F)
    as [ F' [ H [ E'F'_BC DF'_AC ]]]...
  exists E', F'.
  assert (nColDE'F' : ~ [D, E', F']).
  { destruct H as [ nDeqE' [ x [ Dox [ E'ox [ nFox [ nF'ox H ]]]]]].
    contradict nF'ox; incpt 2.
  }
  exists nColDE'F'.
  destruct DsrEE' as [ DsrEE' |[ DeqE | DeqE' ]].
  { split...
    split...
    { apply (SHa_inv D E' F F' E F F'); colperps; apply SR_refl; dips. }
    { apply (SSS' A B C D E' F' nColABC)...
      rewrite SegPs_sym. rewrite <- DF'_AC. apply SegPs_sym.
    }
  }
  { contradict DeqE; dips. }
  { assert (nDeqE' : D <> E').
    { apply nColPs_3DiPs in nColDE'F'. destruct nColDE'F'... }
    contradiction.
  }
Defined.

(** Problem #36 *)
(** Euclid, Book I : Proposition 22. *)
(* To construct a triangle out of three straight lines
 which equal three given straight lines: thus, it is necessary that
 the sum of any two of the straight lines should be greater than
 the remaining one. *)
Definition DrawTriangleFromSegments :
  forall (a b c : Length),
  a << b ++ c
    -> b << a ++ c
    -> c << a ++ b
    -> { A : Point & { B : Point & { C : Point | ~ [ A, B, C ]
         /\ [| A, B |] = a /\ [| B, C |] = b /\ [| A, C |] = c } } }.
Proof with eauto.
  intros * H1 H2 H3.
  destruct (DrawSegment a) as [[ Q R ] H4 ].
  destruct (DrawSegment b) as [[ O O' ] H5 ].
  destruct (DrawSegment c) as [[ S T ] H6 ].
  assert (a0 : a <> L0).
  { intros aeqL0. rewrite aeqL0 in *.
    rewrite (PlusS_0_l c) in H2.
    rewrite (PlusS_0_l b) in H3.
    apply (LtS_asymm b c)...
  }
  assert (b0 : b <> L0).
  { intros beqL0. rewrite beqL0 in *.
    rewrite (PlusS_0_l c) in H1.
    rewrite (PlusS_0_r a) in H3.
    apply (LtS_asymm a c)...
  }
  assert (c0 : c <> L0).
  { intros ceqL0. rewrite ceqL0 in *.
    rewrite (PlusS_0_r b) in H1.
    rewrite (PlusS_0_r a) in H2.
    apply (LtS_asymm a b)...
  }
  subst.
  assert (nQeqR : Q <> R).
  { contradict a0. eapply EqPs_NullSeg... }
  assert (nOeqO' : O <> O').
  { contradict b0. eapply EqPs_NullSeg... }
  assert (nSeqT : S <> T).
  { contradict c0. eapply EqPs_NullSeg... }
  clear a0 b0 c0.
  destruct (DrawSegmentOnOppositeRay O' O S T)
    as [ B' [ H5 H4 ]]...
  assert (OO'B' : [O # O' # B']).
  { destruct H5 as [ OO'B' |[ _ O'eqB' ]]...
    subst. symmetry in H4. apply EqSgs_EqPs in H4. contradiction.
  }
  clear H5.
  destruct (DrawSegmentOnRay O' O S T)
    as [ A' [ H6 O'A'_O'B' ]]...
  assert (O'_OA' : [O' # O, A']).
  { destruct H6 as [ O'_OA' |[ OeqO' | O'eqA' ]]...
    { subst. contradiction. }
    { subst. symmetry in O'A'_O'B'. apply EqSgs_EqPs in O'A'_O'B'.
      contradiction.
    }
  }
  clear H6.
  assert (A'O'B' : [A' # O' # B']); betps.
  destruct (DrawSegmentOnOppositeRay O O' Q R)
    as [ A [ H7 OA_OB ]]...
  assert (AOO' : [A # O # O']).
  { apply BetPs_sym.
    destruct H7 as [ AOO' |[ _ OeqA ]]...
    subst. symmetry in OA_OB.
    apply EqSgs_EqPs in OA_OB.
    contradiction.
  }
  clear H7.
  destruct (DrawSegmentOnRay O O' Q R) as [ B [ H8 H7 ]]...
  assert (O_O'B : [O # O', B]).
  { destruct H8 as [ O_O'B |[ OeqO' | OeqB ]]...
    { subst. contradiction. }
    { subst. symmetry in H7. apply EqSgs_EqPs in H7.
      contradiction.
    }
  }
  clear H8.
  assert (AOB : [A # O # B]); betps.
  destruct (BetPs_b_trans A O O' B' AOO' OO'B')
    as [ _ [ AOB' [ AO'B' _ ]]].
  destruct H4. destruct H7.
  assert (AA'O' : [ A # A' # O']).
  { apply BetPs_sym.
    apply (LtS_SR_BetPs O' A' A); dips; betps.
    rewrite O'A'_O'B'. rewrite <- OA_OB in H3.
    rewrite (SegPs_sym O A) in H3. rewrite (SegPs_sym O' A).
    rewrite BetPs_PlusS in H3...
  }
  assert (OBB' : [ O # B # B' ]).
  { apply (LtS_SR_BetPs O B B'); dips; betps.
    rewrite BetPs_PlusS in H1...
  }
  assert (AA'B' : [A # A' # B']). { apply (BetPs_b_trans A A' O' B')... }
  assert (ABB' : [A # B # B']). { apply (BetPs_b_trans A O B B')... }
  assert ( A_A'B : [ A # A', B ]). { apply (SR_trans A A' B' B); betps. }
  assert (nA'eqB : A' <> B).
  { intros A'eqB. subst.
    rewrite <- O'A'_O'B' in H2.
    rewrite (SegPs_sym O' B) in H2.
    rewrite BetPs_PlusS in H2. { apply LtS_irrefl in H2... }
    betps.
  }
  destruct (DecidePointsOrderOnRay A A' B) as [ ABA' | AA'B ]; dips.
  { exfalso.
    apply BetPs_sym in ABA'.
    assert (OBA'B' : [O # B # A' # O']).
    { apply BetPs_b_trans; betps. }
    apply (LtS_asymm ([|O, O'|])([|O, B|] ++ [|O', B'|]))...
    apply Bet4Ps_PlusS in OBA'B'.
    rewrite <- O'A'_O'B'. rewrite <- OBA'B'.
    rewrite (PlusS_comm ([|B, A'|])([|A', O'|])).
    rewrite (SegPs_sym O' A').
    rewrite PlusS_assoc.
    apply PlusS_LtS.
    intros BeqA'. apply NullSeg_EqPs in BeqA'.
    contradict nA'eqB...
  }
  { destruct (DrawExtensionLinePP O O' nOeqO')
      as [ x [ Oox O'ox ]].
    destruct (DrawPointApartLine x) as [ P nPox ].
    assert (nColOO'P : ~ [ O, O', P ]); ncolps.
    destruct (DrawIntersectionPointCC A O B A' O' B' P)
      as [ Y [ H5 [ H6 H7 ]]]...
    { split... split... apply BetPs_c_trans... }
    exists Y, O, O'.
    split.
    { apply SHb_sym in H5. apply SH_nColPs in H5; ncolperps. }
    { repeat split. rewrite SegPs_sym. rewrite H6...
      rewrite SegPs_sym. rewrite H7...
    }
  }
Defined.

Instance sp : Superpositions (on).
Proof with eauto.
  eapply (Build_Superpositions).
  { intros * nColDEF AB_DE.
    destruct (DrawPointOfEqualTriangle A B C D E F)
      as [ F' [ H1 [ H2 H3 ]]]...
    exists F'.
    assert (nColDEF' : ~ [D, E, F']); geo.
    exists nColDEF'.
    split...
    apply SSS'...
    rewrite SegPs_sym. rewrite <- H3. apply SegPs_sym.
  }
Qed.

End CONGRUENCE.

(*****************************************************************************)
(* 17 *) Section ANGLE_TRANSFER.
Context `{ cc : Concentricals }.
Context  { an : Angles on }.
Context  { sp : Superpositions on }.
(*****************************************************************************)

(** Problem #37 *)
(** Euclid, Book I : Proposition 23. *)
(* To construct a rectilinear angle equal to a given rectilinear angle
 on a given straight line and at a point on it. *)
Definition DrawAngleOnGivenHalfplane :
  forall (A O B A' O' B' : Point)(nColAOB : ~ [ A, O, B ])
         (nColA'O'B' : ~ [ A', O', B' ]),
  { P : Point | exists (nColAOP : ~ [ A, O, P ]), [ O # A | B, P ]
    /\ [| A # O # P | nColAOP |] = [| A' # O' # B' | nColA'O'B' |] }.
Proof with eauto.
  intros A O B A' O' B' nColAOB nColA'O'B'.
  assert (nColO'A'B' : ~ [O', A', B']); ncolperps.
  destruct (DrawEqualTriangle O' A' B' O A B nColO'A'B')
    as [ A'' [ P H ]]; ncolperps.
  exists P.
  destruct H as [ nColOA''P [ O_AA'' [ OA_BP EqTr ]]].
  assert (nColAOP : ~ [A, O, P]).
  { apply (SH_nColPs A O P B). apply SHa_sym; ord. }
  exists nColAOP.
  split...
  destruct EqTr as [ _ [ _ [ _ [ _ [ _ AOP ]]]]]; simpl in *.
  erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
  rewrite AOP.
  erewrite (ConvexAngPs_inv P O A'' P A); try apply SR_refl; dips.
  apply SR_sym...
  Unshelve.
  ncolperps.
Defined.
Definition DrawAngleFromRayOnGivenSide :
  forall (a b c d : Ray)(diab : ![ a # b ])(dicd : ![ c # d ]),
  { b' : Ray | exists (diab' : ![ a # b' ]),
    ![ a # b, b' ] /\ [| a # b' | diab' |] = [| c # d | dicd |] }.
Proof with eauto.
  intros [ O A nOeqA ][ O'' B nOeqB ][ O' A' nO'eqA' ][ O''' B' nO'eqB' ].
  intros [ roab diab ][ rocd dicd ]; simpl in *; subst O''' O''.
  edestruct (DrawAngleOnGivenHalfplane A O B A' O' B') as [ P H ]...
  assert (nColAOP : ~ [A, O, P]). { destruct H... }
  assert (nOeqP : O <> P); dips.
  exists ({{ O # P | nOeqP }}), (conj eq_refl nColAOP).
  destruct H as [ nColAOP' [ H1 H2 ]]... pir nColAOP' => nColAOP.
  split.
  { split; split; simpl... }
  { erewrite (EqConvexAngRsPs A O P nOeqA nOeqP).
    erewrite (EqConvexAngRsPs A' O' B' nO'eqA' nO'eqB'). apply H2.
  }
Defined.

(** Theorem #62 *)
(** Hilbert, Chapter 1 : Theorem 25. *)
Theorem AAS :
  forall (A B C D E F : Point)
    (nColABC : ~ [ A, B, C ])(nColDEF : ~ [ D, E, F ]),
  [| A, C |] = [| D, F |]
    -> [| A # B # C | nColABC |] = [| D # E # F | nColDEF |]
    -> [| A # C # B | nColPerPs_4 A B C nColABC |]
         = [| D # F # E | nColPerPs_4 D E F nColDEF |]
    -> {{ A # B # C | nColABC }} :=: {{ D # E # F | nColDEF }}.
Proof with eauto.
  intros A C B D F E nColABC nColDEF.
  intros ACeqDF ABCeqDEF BCAeqEFD.
  destruct (nColPs_3DiPs A C B nColABC)
  as [ nBeqA [ nBeqC nAeqC ]].
  destruct (nColPs_3DiPs D F E nColDEF)
  as [ nEeqD [ nEeqF nDeqF ]].
  destruct (LtS_trichotomy ([|E, F|])([|B, C|])) as [ H1 |[ H2 | H3 ]].
  { destruct (DrawSegmentOnRay B C E F) as [ G [ B_CG H ]]...
    assert (BGC : [B # G # C]).
    { apply LtS_SR_BetPs. rewrite H... apply SR_sym.
      destruct B_CG as [ B_CG |[ BeqC | H2 ]]; subst; try contradiction...
      symmetry in H. apply EqSgs_EqPs in H. contradict nEeqF...
    }
    destruct (BetPs_3DiPs B G C) as [ nBeqG [ nGeqC _ ]]...
    assert (nColABG : ~ [A, B, G]).
    { clear BCAeqEFD ABCeqDEF.
      contradict nColABC.
      destruct nColABC as [ x [ G1 [ G2 G3 ]]].
      exists x; repeat split; incpt 2.
    }
    eassert (EqTr : {{ A # B # G | _ }} :=: {{ D # E # F | _ }}).
    { apply SAS...
      rewrite <- BCAeqEFD.
      apply (SH_EqConvexAs_SR A B G C); betps.
      apply SR_SH; ncolperps; betps.
    }
    assert (nAGB : ~ [A, G, B]); ncolperps.
    assert (nBCA : ~ [B, C, A]); ncolperps.
    assert (nBGA : ~ [B, G, A]); ncolperps.
    destruct EqTr as [ _ [ _ [ _ [ _ [ G2 _ ]]]]]; simpl in *.
    erewrite ConvexAngPs_sym in G2. symmetry in G2...
    erewrite ConvexAngPs_sym in G2. rewrite <- ABCeqDEF in G2.
    erewrite ConvexAngPs_sym in G2. symmetry in G2.
    erewrite ConvexAngPs_sym in G2.
    assert (nColACG : ~ [ A, C, G ]).
    { clear ABCeqDEF BCAeqEFD.
      contradict nColABC.
      apply BetPs_ColPs in BGC.
      destruct nColABC as [ x [ G1 [ G4 G3 ]]].
      exists x; repeat split; incpt 2.
    }
    edestruct (DrawPointOfEqConvexAngPs A C G B)
      as [ X [ H2 [ H4 H5 ]]]; betps.
    destruct (BetPs_3DiPs A X B H2)
      as [ nXeqA [ nXeqB nAeqB ]].
    assert (nBGX : ~ [B, G, X]).
    { contradict nBGA.
      apply BetPs_ColPs in H2.
      destruct nBGA as [ x [ G1 [ G4 G3 ]]].
      exists x; repeat split; incpt 2.
    }
    erewrite (ConvexAngPs_sym X G B) in H5.
    erewrite (ConvexAngPs_sym B C A) in G2.
    eassert ([|A # C # B | _ |] = [|A # C # G | _ |]).
    { apply ConvexAngPs_inv; betps. }
    assert (G_AX : [G # A, X]).
    { eapply (SH_EqConvexAs_SR B G A X).
      apply SHa_sym. apply SR_SH; betps.
      rewrite G2. rewrite H0. apply H5.
    }
    contradict H4.
    apply BetPs_ColPs in H2.
    destruct G_AX as [ nGeqA [ nGeqX [ AGX _ ]]]; colperps.
  }
  { apply SAS in BCAeqEFD...
    apply EqPerTr_4 in BCAeqEFD.
    pir (nColPerPs_4 A B C (nColPerPs_4 A C B nColABC)) => nColABC.
    pir (nColPerPs_4 D E F (nColPerPs_4 D F E nColDEF)) => nColDEF.
  }
  { destruct (DrawSegmentOnRay E F B C) as [ G [ E_FG H ]]...
    assert (EGF : [E # G # F]).
    { apply LtS_SR_BetPs. rewrite H... apply SR_sym.
      destruct E_FG as [ E_FG |[ EeqF | H2 ]]; subst; try contradiction...
      symmetry in H. apply EqSgs_EqPs in H. contradict nBeqC...
    }
    destruct (BetPs_3DiPs E G F) as [ nEeqG [ nGeqF _ ]]...
    assert (nColDGE : ~ [D, G, E]).
    { clear BCAeqEFD ABCeqDEF.
      apply BetPs_ColPs in EGF.
      contradict nColDEF.
      destruct nColDEF as [ x [ G1 [ G2 G3 ]]].
      exists x; repeat split; incpt 2.
    }
    eassert (EqTr : {{ D # E # G | _ }} :=: {{ A # B # C | _ }}).
    { apply SAS...
      rewrite BCAeqEFD.
      apply (SH_EqConvexAs_SR D E G F); betps.
      apply SR_SH; ncolperps; betps.
    }
    assert (nDGE : ~ [D, G, E]); ncolperps.
    assert (nEFD : ~ [E, F, D]); ncolperps.
    assert (nEGD : ~ [E, G, D]); ncolperps.
    destruct EqTr as [ _ [ _ [ _ [ _ [ G2 _ ]]]]]; simpl in *.
    erewrite ConvexAngPs_sym in G2. symmetry in G2.
    erewrite ConvexAngPs_sym in G2. rewrite ABCeqDEF in G2.
    erewrite ConvexAngPs_sym in G2. symmetry in G2.
    erewrite ConvexAngPs_sym in G2.
    assert (nColDFG : ~ [ D, F, G ]).
    { clear ABCeqDEF BCAeqEFD.
      apply BetPs_ColPs in EGF.
      contradict nColDEF.
      destruct nColDEF as [ x [ G1 [ G4 G3 ]]].
      exists x; repeat split; incpt 2.
    }
    edestruct (DrawPointOfEqConvexAngPs D F G E)
      as [ X [ H2 [ H4 H5 ]]]; betps.
    destruct (BetPs_3DiPs D X E H2)
      as [ nXeqD [ nXeqE nDeqE ]]...
    assert (nEGX : ~ [E, G, X]).
    { contradict nEGD.
      apply BetPs_ColPs in H2.
      destruct nEGD as [ x [ G1 [ G4 G3 ]]].
      exists x; repeat split; incpt 2.
    }
    erewrite (ConvexAngPs_sym X G E) in H5.
    erewrite (ConvexAngPs_sym E F D) in G2.
    eassert ([|D # F # E | _ |] = [|D # F # G | _ |]).
    { apply ConvexAngPs_inv; betps. }
    assert (G_DX : [G # D, X]).
    { eapply (SH_EqConvexAs_SR E G D X).
      apply SHa_sym. apply SR_SH; betps.
      rewrite G2. rewrite H0. apply H5.
    }
    contradict H4.
    apply BetPs_ColPs in H2.
    destruct G_DX as [ nGeqD [ nGeqX [ DGX _ ]]]; colperps.
  }
  Unshelve.
  simpl; ncolperps. ncolps. ncolps. ncolperps. ncolps. ncolps. ncolps.
  simpl; ncolperps. ncolps. ncolps. ncolperps. ncolps. ncolps. ncolps.
Qed.

(** Problem #38 *)
(** Hilbert, Chapter 1 : Theorem 16. *)
Definition DrawAngleCutPs :
  forall (O A B C O' A' C' : Point)(nColAOB : ~ [ A, O, B ])
    (nColAOC : ~ [ A, O, C ])(nColA'O'C' : ~ [ A', O', C' ]),
  [ O | A; B; C ]
    -> [| A # O # C | nColAOC |] = [| A' # O' # C' | nColA'O'C' |]
    -> { B' : Point | exists (nColA'O'B' : ~ [ A', O', B' ]),
         [ O' | A'; B'; C' ]
         /\ [| A # O # B | nColAOB |] = [| A' # O' # B' | nColA'O'B' |] }.
Proof with eauto.
  intros * O_ABC AOCeqAOC.
  assert (nAeqO : A <> O); dips.
  assert (nCeqO : C <> O); dips.
  destruct (DrawPointCrossBar O A B C)
    as [ B'' [ BetABC OsrBB'' ]]...
  assert (nColAOB'' : ~ [ A, O, B'' ]).
  { apply (nColPs_SR_inv O A B A B''); betps. }
  assert (OoAB''C : [O | A; B''; C ]).
  { apply (BR_inv O A B C A B'' C); betps. }
  eassert (AOB : [| A # O # B | _ |] = [| A # O # B'' | _ |]).
  { apply (ConvexAngPs_inv A O B A B''); betps. }
  rewrite AOB.
  clear dependent B.
  rename B'' into B. rename nColAOB'' into nColAOB.
  assert (nColOAC : ~ [ O, A, C ]); ncolperps.
  assert (nColO'A'C' : ~ [ O', A', C' ]); ncolperps.
  destruct (DrawEqualTriangle O A C O' A' C' nColOAC)
    as [ A'' [ C'' H ]]...
  assert (O'srC'C'' : [O' # C', C'']).
  { destruct H as [ nColO'A''C'' [ O'srA'A'' [ O'A'sfC'C'' trOAC ]]].
    assert (nColA''O'C'' : ~ [ A'', O', C'' ]); ncolperps.
    assert (nColA'O'C'' : ~ [ A', O', C'' ]).
    { destruct O'A'sfC'C''
        as [ nO'eqA' [ x [ O'ox [ A'ox [ _ [ nC''ox _ ]]]]]].
      contradict nC''ox. apply (ColPs_IncPt A' O' C''); try split...
    }
    apply (SH_EqConvexAs_SR A' O' C' C'' nColA'O'C' nColA'O'C'')...
    rewrite <- AOCeqAOC...
    unfold EqTriangle in trOAC; simpl in *.
    erewrite (ConvexAngPs_sym A O C nColAOC).
    pir (nColPerPs_5 A O C nColAOC)
      => (nColPerPs_2 O A C nColOAC).
    symmetry.
    rewrite (ConvexAngPs_inv A' O' C'' A'' C'' nColA'O'C'' nColA''O'C'')...
    { erewrite (ConvexAngPs_sym A'' O' C'' nColA''O'C'').
      pir (nColPerPs_5 A'' O' C'' nColA''O'C'')
        => (nColPerPs_2 O' A'' C'' nColO'A''C'').
      destruct trOAC as [ _ [ _ [ _ [ _ [ _ H ]]]]]...
    }
    apply SR_refl; dips.
  }
  assert (nColA''O'C'' : ~ [ A'', O', C'' ]).
  { destruct H as [ nColO'A''C'' [ O'srA'A'' [ O'A'sfC'C'' trOAC ]]].
    apply (nColPs_SR_inv O' A' C' A'' C'')...
  }
  eassert (AOCeqA'O'C' : [| A # O # C | _ |] = [| A'' # O' # C'' | _ |]).
  { destruct H as [ nColO'A''C'' [ O'srA'A'' [ O'A'sfC'C'' trOAC ]]].
    rewrite AOCeqAOC.
    apply (ConvexAngPs_inv A' O' C' A'' C'')...
  }
  assert (ACeqA''C'' : [| A, C |] = [| A'', C'' |]).
  { destruct H as [ nColO'A''C'' [ O'srA'A'' [ O'A'sfC'C'' trOAC ]]].
    unfold EqTriangle in trOAC; simpl in *.
    destruct trOAC as [ _ [ H1 _ ]]...
  }
  destruct (DrawSegmentCut A B C A'' C'' BetABC ACeqA''C'')
    as [ B'' [ BetA'B'C' [ AB BC ]]].
  assert (nColO'A''B'' : ~ [O', A'', B'']).
  { destruct H as [ nColO'A''C'' [ O'srA'A'' [ O'A'sfC'C'' trOAC ]]].
    apply (nColPs_SR_inv A'' O' C'' O' B''); try apply SR_refl; dips.
    apply SR_sym. apply -> (BetPs_SR A'' B'' C'')...
  }
  assert (nColA''O'B'' : ~ [A'', O', B'']); ncolperps.
  assert (nColA'O'B'' : ~ [A', O', B'']).
  { destruct H as [ nColO'A''C'' [ O'srA'A'' [ O'A'sfC'C'' trOAC ]]].
    apply (nColPs_SR_inv O' A'' B'' A' B'')...
    apply SR_sym... apply SR_refl; dips.
  }
  exists B'', nColA'O'B'' .
  destruct H as [ nColO'A''C'' [ O'srA'A'' [ O'A'sfC'C'' trOAC ]]].
  assert (O'oA'B'C' : [ O' | A''; B''; C'' ]).
  { apply (nColPs_BetPs_BR O' A'' B'' C'' nColO'A''C'' BetA'B'C'). }
  split.
  { apply (BR_inv O' A'' B'' C'' A' B'' C'); try apply SR_sym...
    apply SR_refl; dips.
  }
  rewrite (ConvexAngPs_inv A' O' B'' A'' B'' nColA'O'B'' nColA''O'B'');
  try apply SR_refl; dips.
  clear dependent A'. clear dependent C'.
  rename A'' into A'. rename B'' into B'. rename C'' into C'.
  assert (nColOAB : ~ [ O, A, B ]); ncolperps.
  assert (nColO'A'B' : ~ [ O', A', B' ]); ncolperps.
  eassert (trOAB : {{ O # A # B | _ }} :=: {{ O' # A' # B' | _ }}).
  { apply (SAS O A B O' A' B')...
    unfold EqTriangle in trOAC; simpl in *.
    destruct trOAC as [ H1 _ ]...
    erewrite (ConvexAngPs_inv O A B O C); betps; dips.
    erewrite (ConvexAngPs_inv O' A' B' O' C').
    { symmetry.
      unfold EqTriangle in trOAC; simpl in *.
      destruct trOAC as [ _ [ _ [ _ [ H1 _ ]]]]...
    }
    { apply SR_refl; dips. }
    { apply -> (BetPs_SR A' B' C')... }
  }
  unfold EqTriangle in trOAB; simpl in *.
  destruct trOAB as [ _ [ _ [ _ [ _ [ _ H1 ]]]]].
  erewrite (ConvexAngPs_sym A O B nColAOB).
  pir (nColPerPs_5 A O B nColAOB)
    => (nColPerPs_2 O A B nColOAB).
  erewrite (ConvexAngPs_sym A' O' B' nColA''O'B'').
  pir (nColPerPs_5 A' O' B' nColA''O'B'')
    => (nColPerPs_2 O' A' B' nColO'A'B').
  apply H1.
  Unshelve.
  ncolps.
  simpl; ncolps.
  simpl; ncolps.
Defined.
Definition DrawAngleCutRs :
  forall (a b c a' c' : Ray)(diab : ![ a # b ])(diac : ![ a # c ])
                            (dia'c' : ![ a' # c' ]),
  ![ a # b # c ]
  -> [| a # c | diac |] = [| a' # c' | dia'c' |]
  -> { b' : Ray | exists (dia'b' : ![ a' # b' ]), ![ a' # b' # c' ]
                /\ [| a # b | diab |] = [| a' # b' | dia'b' |] }.
Proof with eauto.
  intros a b c a' c' [ roab diab ][ roac diac ][ roa'c' dia'c' ].
  intros [ _ [ robc BetRabc ]] ac.
  erewrite (ConvexAngRs_ConvexAngPs a c) in ac.
  erewrite (ConvexAngRs_ConvexAngPs a' c') in ac.
  edestruct (DrawAngleCutPs
    (da a)(db a)(db b)(db c)(da a')(db a')(db c'))
    as [ B' H ]...
  assert (nO'eqB' : da a' <> B').
  { destruct H as [ nColA'O'B' [ BetRa'b'c' a'b' ]]; dips. }
  assert (Exb' : { b' : Ray | {{ da a' # B' | nO'eqB' }} = b' }).
  { exists ({{ da a' # B' | nO'eqB' }})... }
  destruct Exb' as [ b' b'eqO'B' ].
  exists b'.
  assert (roa'b' : da a' = da b'). { destruct b'eqO'B'. simpl... }
  assert (nColA'O'B'' : ~ [db a', da a', db b']).
  { destruct H as [ nColA'O'B' [ BetRa'b'c' a'b' ]].
    apply (nColPs_SR_inv (da a')(db a') B' (db a')(db b'))...
    { apply SR_refl. apply (dp a'). }
    rewrite <- b'eqO'B'. simpl.
    assert (BetRa'b'c'' : [ da a' | db a'; db b'; db c']).
    { apply (BR_inv (da a')(db a') B' (db c')(db a')(db b')(db c'))...
      { apply SR_refl. apply (dp a'). }
      { rewrite <- b'eqO'B'. simpl. apply SR_refl... }
      { apply SR_refl. rewrite roa'c'. apply (dp c'). }
    }
    apply SR_refl...
  }
  eassert (a'b'' : [|db a # da a # db b | _ |]
    = [|db a' # da a' # db b' | _ |]).
  { destruct H as [ nColA'O'B' [ BetRa'b'c' a'b' ]].
    rewrite a'b'.
    apply ConvexAngPs_inv...
    { apply SR_refl. apply (dp a'). }
    { rewrite <- b'eqO'B'. simpl. apply SR_refl... }
  }
  assert (dia'b' : ![ a' # b' ]). { split... }
  exists dia'b'.
  destruct H as [ nColA'O'B' [ BetRa'b'c' a'b' ]].
  split.
  { do 2 try split...
    { rewrite <- roa'b'... }
    { rewrite <- b'eqO'B'. simpl... }
  }
  erewrite (ConvexAngRs_ConvexAngPs a b).
  rewrite (ConvexAngRs_ConvexAngPs a' b' dia'b' nColA'O'B'')...
  Unshelve. ncolps. ncolps. ncolps.
Defined.

(** Theorem #63 *)
(** Hilbert, Chapter 1 : Theorem 21. *)
Theorem UniqueAltitude :
  forall (O A B C D : Point)
         (nColAOC : ~ [ A, O, C ])(nColCOB : ~ [ C, O, B ])
         (nColAOD : ~ [ A, O, D ])(nColDOB : ~ [ D, O, B ]),
  [ A # O # B ]
    -> [ O # A | C, D ]
    -> [| A # O # C | nColAOC |] = [| C # O # B | nColCOB |]
    -> [| A # O # D | nColAOD |] = [| D # O # B | nColDOB |]
    -> [ O # C, D ].
Proof with eauto.
  intros * AOB OA_CD AOC_COB AOD_DOB.
  destruct(classic ([ O # C, D ])) as [ SR | nSR ]...
  assert (nColOCD : ~ [ O, C, D ]).
  { contradict nSR. repeat split; dips. colperps.
    destruct OA_CD as [ nAeqB [ x [ Oox [ Aox [ nCox [ nDox H ]]]]]].
    contradict H. exists O. split...
  }
  destruct (SH_nColPs_BR O A C D) as [ H1 | H2 ]...
  { edestruct (DrawAngleCutPs O A C D O B D)
      as [ C' [ nColBOC' [ O_BC'D AOC_BOC' ]]]...
    { erewrite (ConvexAngPs_sym B O D). apply AOD_DOB. }
    { erewrite (ConvexAngPs_sym C O B) in AOC_COB.
      rewrite AOC_COB in AOC_BOC'.
      assert (O_CC' : [O # C, C']).
      { eapply (SH_EqConvexAs_SR B O C C')...
        destruct H1 as [[ nOeqA [ x' [ Oox' [ Aox SSxCD ]]]] _ ].
        destruct O_BC'D as [[ nBeqO [ x [ Oox [ Box SSxC'D ]]]] _ ].
        destruct (DrawLineThroughOrderedPoints A O B AOB)
          as [ x'' [ Aox' [ Oox'' Box' ]]].
        assert (xeqx : x = x''); eqls. subst x''.
        assert (xeqx : x = x'); eqls. subst x'.
        repeat split...
        exists x; do 2 try split...
        apply SS_trans with D... apply SS_sym...
      }
      assert (OS_AB : [A | O # D | B]).
      { repeat split; dips.
        destruct (DrawExtensionLinePP O D) as [ x [ Oox Dox ]]; dips.
        exists x; repeat split; ncolps.
      }
      assert (OS : [C | O # D | C']).
      { destruct H1 as [ _ H1 ]. destruct O_BC'D as [ _ H2 ].
        eapply (OHO_trans O D C B C'). apply OHb_sym.
        eapply (OHO_trans O D B A C). apply OHb_sym...
        apply SHb_sym... apply SHb_sym...
      }
      assert (SS : [O # D | C, C']). { apply SR_SH; ncolps. }
      exfalso.
      apply (OH_DiPs_2 O D C C)...
      apply (OHO_trans O D C C' C)...
      apply SHb_sym...
    }
  }
  { edestruct (DrawAngleCutPs O A D C O B C)
      as [ D' [ nColBOD' [ O_BD'C AOD_BOD' ]]]...
    { erewrite (ConvexAngPs_sym B O C). apply AOC_COB. }
    { erewrite (ConvexAngPs_sym D O B) in AOD_DOB.
      rewrite AOD_DOB in AOD_BOD'.
      assert (O_DD' : [O # D, D']).
      { eapply (SH_EqConvexAs_SR B O D D')...
        destruct H2 as [[ nOeqA [ x' [ Oox' [ Aox SSxDC ]]]] _ ].
        destruct O_BD'C as [[ nBeqO [ x [ Oox [ Box SSxD'C ]]]] _ ].
        destruct (DrawLineThroughOrderedPoints A O B AOB)
          as [ x'' [ Aox' [ Oox'' Box' ]]].
        assert (xeqx : x = x''); eqls. subst x''.
        assert (xeqx : x = x'); eqls. subst x'.
        repeat split...
        exists x; do 2 try split...
        apply SS_trans with C... apply SS_sym...
      }
      assert (OS_AB : [A | O # C | B]).
      { repeat split; dips.
        destruct (DrawExtensionLinePP O C) as [ x [ Oox Cox ]]; dips.
        exists x; repeat split; ncolps.
      }
      assert (OS : [D | O # C | D']).
      { destruct H2 as [ _ H1 ]. destruct O_BD'C as [ _ H2 ].
        eapply (OHO_trans O C D B D'). apply OHb_sym.
        eapply (OHO_trans O C B A D). apply OHb_sym...
        apply SHb_sym... apply SHb_sym...
      }
      assert (SS : [O # C | D, D']). { apply SR_SH; ncolps. }
      exfalso.
      apply (OH_DiPs_2 O C D D)...
      apply (OHO_trans O C D D' D)...
      apply SHb_sym...
    }
  }
  Unshelve. ncolperps. ncolperps. ncolperps. ncolperps.
Qed.

(** Theorem #64 *)
Theorem IsoscelesMedianBissectrice :
  forall (A B C D : Point)(nColBAD : ~ [ B, A, D ])(nColCAD : ~ [ C, A, D ]),
  [| A, B |] = [| A, C |]
    -> [ B # D # C ]
    -> [| B, D |] = [| C, D |]
    <-> [| B # A # D | nColBAD |] = [| C # A # D | nColCAD |].
Proof with eauto.
  intros * ABeqAC BetBDC.
  split.
  { intros BDeqCD.
    assert (nColABD : ~ [ A, B, D ]); ncolperps.
    assert (nColACD : ~ [ A, C, D ]); ncolperps.
    assert (ColBDC : [B, D, C]); colps.
    destruct (BetPs_3DiPs B D C BetBDC)
      as [ nBeqD [ nDeqC nBeqC ]].
    destruct (nColPs_3DiPs A B D nColABD)
      as [ nAeqB [ _ nAeqD ]].
    destruct (nColPs_3DiPs A C D nColACD)
      as [ nAeqC [ nCeqD _ ]].
    eassert (EqTr : {{ A # B # D | _ }} :=: {{ A # C # D | _ }}).
    { apply (SAS A B D A C D nColABD)...
      erewrite (ConvexAngPs_inv A B D A C); betps; dips.
      erewrite (ConvexAngPs_inv A C D A B); betps; dips.
      eapply (IsoscelesTr_EqConvexAs A B C); eauto;
      apply BetPs_SR...
    }
    destruct EqTr as [ _ [ _ [ _ [ _ [ _ H ]]]]]; simpl in *...
    erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
    symmetry. apply H.
  }
  { intros BADeqCAD.
    eassert (EqTr : {{ B # A # D | _ }} :=: {{ C # A # D | _ }}).
    { apply (SAS B A D C A D)...
      rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
    }
    destruct EqTr as [ _ [ _ [ H1 _ ]]]; simpl in *.
    rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
  }
  Unshelve.
  ncolperps.
  { contradict nColBAD.
    destruct nColBAD as [ x [ H1 [ H2 H3 ]]].
    exists x; repeat split; incpt 2.
  }
  { contradict nColCAD.
    destruct nColCAD as [ x [ H1 [ H2 H3 ]]].
    exists x; repeat split; incpt 2.
  }
Qed.

(** Theorem #65 *)
Theorem IsoscelesMedianAltitude :
  forall (A B C D : Point)
    (nColADB : ~ [ A, D, B ])(nColADC : ~ [ A, D, C ]),
  [| A, B |] = [| A, C |]
    -> [ B # D # C ]
    -> [| B, D |] = [| C, D |]
    <-> [| A # D # B | nColADB |] = [| A # D # C | nColADC |].
Proof with eauto.
  intros * ABeqAC BetBDC.
  split.
  { intros BDeqCD.
    assert (nColABD : ~ [ A, B, D ]); ncolperps.
    assert (nColACD : ~ [ A, C, D ]); ncolperps.
    assert (ColBDC : [B, D, C]); colps.
    destruct (BetPs_3DiPs B D C BetBDC)
      as [ nBeqD [ nDeqC nBeqC ]].
    destruct (nColPs_3DiPs A B D nColABD)
      as [ nAeqB [ _ nAeqD ]].
    destruct (nColPs_3DiPs A C D nColACD)
      as [ nAeqC [ nCeqD _ ]].
    eassert (EqTr : {{ A # B # D | _ }} :=: {{ A # C # D | _ }}).
    { apply (SAS A B D A C D nColABD)...
      erewrite (ConvexAngPs_inv A B D A C); betps; dips.
      erewrite (ConvexAngPs_inv A C D A B); betps; dips.
      eapply (IsoscelesTr_EqConvexAs A B C); eauto;
      apply BetPs_SR...
    }
    destruct EqTr as [ _ [ _ [ _ [ _ [ H _ ]]]]]; simpl in *...
    erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
    symmetry. apply H.
  }
  { intros BADeqCAD.
    destruct (BetPs_3DiPs B D C BetBDC)
      as [ nBeqD [ nDeqC nBeqC ]].
    assert (nColABC : ~ [A, B, C]).
    { apply BetPs_ColPs in BetBDC.
      clear BADeqCAD. contradict nColADC; colperps.
    }
    eassert (ABC_ACB : [| A # B # C | _ |] = [| A # C # B | _ |]).
    { apply IsoscelesTr_EqConvexAs... }
    eassert (ABD_ACD : [| A # B # D | _ |] = [| A # C # D | _ |]).
    { erewrite (ConvexAngPs_inv A B D A C); try apply SR_refl; dips; betps.
      erewrite (ConvexAngPs_inv A C D A B); try apply SR_refl; dips; betps.
    }
    eassert (EqTr : {{ A # D # B | _ }} :=: {{ A # D # C | _ }}).
    { apply (AAS A D B)... }
    destruct EqTr as[ H1 [ H2 [ H3 _ ]]]; simpl in *.
    rewrite SegPs_sym. rewrite H2. apply SegPs_sym.
  }
  Unshelve.
  simpl; ncolps.
  { contradict nColADB.
    destruct nColADB as [ x [ H1 [ H2 H3 ]]].
    exists x; repeat split; incpt 2.
  }
  { contradict nColADC.
    destruct nColADC as [ x [ H1 [ H2 H3 ]]].
    exists x; repeat split; incpt 2.
  }
  ncolps. ncolperps.
Qed.

(** Theorem #66 *)
(** Hilbert, Chapter 1 : Theorem 23. *)
(** Euclid, Book I : Proposition 19. *)
(* In any triangle the side opposite the greater angle is greater. *)
Theorem GreaterAngle_GreaterLength :
  forall (A B C D : Point)(nColABC : ~ [ A, B, C ])(nColBCD : ~ [ B, C, D ]),
  [ A # D # B ]
    -> [| A # B # C | nColABC |] = [| B # C # D | nColBCD |]
    -> [| A, C |] << [| A, B |].
Proof with eauto.
  intros A B C D nColABC nColBCD ADB ABC_BCD.
  destruct (LtS_trichotomy ([|A, B|])([|A, C|]))
    as [ H1 |[ H2 | H3 ]]...
  { edestruct (DrawSmallerAngInsideBigger A C B)
      as [ E [ AEC [ nColCBA ACB_CBE ]]]...
    destruct (DrawMiddlePoint B C) as [ F [ H2 H3 ]]; dips.
    eassert (DFB_CFD : [| D # F # B | _ |] = [| D # F # C | _ |]).
    { apply -> (IsoscelesMedianAltitude D B C F)...
      { rewrite SegPs_sym. rewrite H3. apply SegPs_sym. }
      eapply EqConvexAs_IsoscelesTr.
      symmetry. erewrite ConvexAngPs_sym.
      rewrite <- ABC_BCD. erewrite ConvexAngPs_sym.
      symmetry. erewrite ConvexAngPs_sym.
      apply ConvexAngPs_inv.
      { apply SR_refl; dips. }
      apply BetPs_SR in ADB. destruct ADB...
    }
    eassert(EFB_CFE : [|E # F # C | _ |] = [|E # F # B | _ |]).
    { apply -> (IsoscelesMedianAltitude E C B F)...
      rewrite SegPs_sym. rewrite <- H3.
      apply SegPs_sym. apply BetPs_sym...
      eapply EqConvexAs_IsoscelesTr. symmetry.
      erewrite ConvexAngPs_sym. erewrite <- ACB_CBE.
      erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym.
      apply ConvexAngPs_inv.
      { apply SR_refl; dips. }
      { apply BetPs_SR in AEC. destruct AEC... }
    }
    assert (F_DE : [ F # D, E ]).
    { eapply (UniqueAltitude F B C D E)...
      { destruct (DrawExtensionLinePP F B) as [ x [ Fox Box ]]; dips.
        clear ABC_BCD ACB_CBE DFB_CFD EFB_CFE.
        split; dips.
        exists x; do 2 try split...
        apply (SS_trans D A E x).
        { apply (SR_SS B D A x)...
          contradict nColBCD.
          exists x.
          repeat split; incpt.
          apply BetPs_SR in ADB. destruct ADB...
        }
        { apply SS_sym.
          apply (SR_SS C E A x); incpt.
          contradict nColCBA.
          exists x.
          repeat split; incpt.
          apply BetPs_SR in AEC. destruct AEC...
        }
      }
      { rewrite <- DFB_CFD. apply ConvexAngPs_sym... }
      { rewrite EFB_CFE. apply ConvexAngPs_sym... }
    }
    clear ABC_BCD ACB_CBE DFB_CFD EFB_CFE.
    destruct F_DE as [ nFeqD [ nFeqE [ FDE nDEF ]]].
    destruct FDE as [ x [ Fox [ Dox Eox ]]].
    assert (nAox : ~ [ A @ x ]).
    { contradict nColABC. exists x; repeat split; incpt 2. }
    assert (nBox : ~ [ B @ x ]).
    { contradict nColABC. exists x; repeat split; incpt 2. }
    assert (nCox : ~ [ C @ x ]).
    { contradict nColABC. exists x; repeat split; incpt 2. }
      exfalso.
      apply (PaschAuxiliary A B C x); repeat split...
  }
  { eassert (ABC_ACB : [|A # B # C | _|] = [|A # C # B | _|]).
    { apply IsoscelesTr_EqConvexAs... }
    rewrite ABC_BCD in ABC_ACB.
    erewrite (ConvexAngPs_sym A C B) in ABC_ACB.
    assert (C_AD : [C # A, D]).
    { eapply SH_EqConvexAs_SR... apply SHa_sym.
      apply (SR_SH B C A D); ncolperps.
      apply BetPs_SR in ADB. apply SR_sym.
      destruct ADB...
    }
    clear ABC_BCD ABC_ACB H2 nColBCD.
    contradict nColABC.
    destruct C_AD as [ nCeqA [ nCeqD [ CAD nACD ]]].
    destruct CAD as [ x [ Aox [ Cox Dox ]]].
    exists x; repeat split; incpt 2.
  }
  Unshelve.
  ncolperps. ncolperps. ncolperps. ncolperps. ncolperps.
  { clear ABC_BCD ACB_CBE DFB_CFD H1 H3.
    contradict nColABC.
    destruct nColABC as [ x [ Eox [ Fox Box ]]].
    exists x; repeat split; incpt 3.
  }
  ncolperps. ncolps. ncolperps. ncolperps. ncolperps.
  { clear ABC_BCD ACB_CBE H1 H3.
    contradict nColABC.
    destruct nColABC as [ x [ Eox [ Fox Box ]]].
    exists x; repeat split; incpt 2.
  }
  { clear ABC_BCD ACB_CBE DFB_CFD EFB_CFE H1 H3.
    contradict nColABC.
    destruct nColABC as [ x [ Eox [ Fox Box ]]].
    exists x; repeat split; incpt 2.
  }
  { clear ABC_BCD ACB_CBE DFB_CFD EFB_CFE H1 H3.
    contradict nColABC.
    destruct nColABC as [ x [ Eox [ Fox Box ]]].
    exists x; repeat split; incpt 3.
  }
  { clear ABC_BCD ACB_CBE H1 H3.
    contradict nColABC.
    destruct nColABC as [ x [ Eox [ Fox Box ]]].
    exists x; repeat split; incpt 3.
  }
  { clear ABC_BCD ACB_CBE DFB_CFD H1 H3.
    contradict nColABC.
    destruct nColABC as [ x [ Eox [ Fox Box ]]].
    exists x; repeat split; incpt 2.
  }
  ncolperps. ncolperps.
Qed.

Lemma EqAs_EqPs :
  forall (O O' A B : Point)
    (nColAOB : ~ [ A, O, B ])(nColAO'B : ~ [ A, O', B ]),
  [ A # O, O' ]
    -> [| A # O # B | nColAOB |] = [| A # O' # B | nColAO'B |]
    -> O = O'.
Proof with eauto.
  intros * AsrOO' AOC_AO'C.
  assert (nColBOA : ~ [ B, O, A ]); ncolperps.
  assert (nColBO'A : ~ [ B, O', A ]); ncolperps.
  rewrite (ConvexAngPs_sym A O B nColAOB nColBOA) in AOC_AO'C...
  rewrite (ConvexAngPs_sym A O' B nColAO'B nColBO'A) in AOC_AO'C...
  destruct(classic (O = O')) as [ OeqO' | nOeqO' ]...
  exfalso.
  destruct (DecidePointsOrderOnRay A O O') as [ H1 | H1 ]...
  { assert (nColBOO' : ~ [B, O, O']). { contradict nColAOB; colperps. }
    destruct (DrawPointOfEqConvexAngPs B O O' A nColBOO')
      as [ E [ H2 [ H3 H4 ]]]...
    { apply BetPs_sym... }
    { rewrite (ConvexAngPs_inv B O O' B A nColBOO' nColBOA) in H4...
      { rewrite AOC_AO'C in H4.
        assert (O'srBE : [ O' # B, E ]).
        { assert (nColAO'E : ~ [A, O', E]); ncolperps.
          apply (SH_EqConvexAs_SR A O' B E nColAO'B nColAO'E)...
          { apply SHa_sym. eapply SR_SH; ncolperps.
            apply SR_sym. apply BetPs_SR in H2; tauto.
          }
          erewrite ConvexAngPs_sym... symmetry.
          erewrite ConvexAngPs_sym...
        }
        destruct (DrawLineThroughOrderedPoints B E A)
          as [ x [ Box [ Eox Aox ]]]...
        contradict nColAO'B.
        exists x; repeat split...
        destruct (BetPs_3DiPs B E A) as [ nBeqE _ ]...
        destruct O'srBE as [ G1 [ G2 [ G3 G4 ]]]; incpt 2.
      }
      apply SR_refl; dips.
      apply BetPs_SR in H1; tauto.
    }
  }
  { assert (nColBO'O : ~ [B, O', O]). { contradict nColAOB; colperps. }
    destruct (DrawPointOfEqConvexAngPs B O' O A nColBO'O)
      as [ E [ H2 [ H3 H4 ]]]...
    { apply BetPs_sym... }
    { rewrite (ConvexAngPs_inv B O' O B A nColBO'O nColBO'A) in H4...
      { rewrite <- AOC_AO'C in H4.
        assert (OsrBE : [ O # B, E ]).
        { assert (nColAOE : ~ [A, O, E]); ncolperps.
          apply (SH_EqConvexAs_SR A O B E nColAOB nColAOE)...
          { apply SHa_sym. eapply SR_SH; ncolperps.
            apply SR_sym. apply BetPs_SR in H2; tauto.
          }
          erewrite ConvexAngPs_sym... symmetry.
          erewrite ConvexAngPs_sym...
        }
        destruct (DrawLineThroughOrderedPoints B E A)
          as [ x [ Box [ Eox Aox ]]]...
        contradict nColAOB.
        exists x; repeat split...
        destruct (BetPs_3DiPs B E A) as [ nBeqE _ ]...
        destruct OsrBE as [ G1 [ G2 [ G3 G4 ]]]; incpt 2.
      }
      apply SR_refl; dips.
      apply BetPs_SR in H1; tauto.
    }
  }
Qed.

Lemma ColPs_EqSgs_ColPs :
  forall A B C A' B' C' : Point,
  [ A, B, C ]
    -> [| A, B |] = [| A', B' |]
    -> [| B, C |] = [| B', C' |]
    -> [| A, C |] = [| A', C' |]
    -> [ A', B', C' ].
Proof with eauto.
  intros A' B' C' A B C ColA'B'C' AB BC AC.
  destruct (classic (A' = B')) as [ A'eqB' | nA'eqB' ].
  { subst B'. symmetry in AB. apply EqSgs_EqPs in AB. subst B.
    destruct (ExistLineThroughTwoPoints A C) as [ x [ Aox Cox ]].
    exists x...
  }
  { destruct (classic (A' = C')) as [ A'eqC' | nA'eqC' ].
    { subst C'. symmetry in AC. apply EqSgs_EqPs in AC. subst C.
      destruct (ExistLineThroughTwoPoints A B) as [ x [ Aox Box ]].
      exists x...
    }
    { destruct (classic (B' = C')) as [ B'eqC' | nB'eqC' ].
      { subst C'. symmetry in BC. apply EqSgs_EqPs in BC. subst C.
        destruct (ExistLineThroughTwoPoints A B) as [ x [ Aox Box ]].
        exists x...
      }
      { destruct (classic ([A, B, C])) as [ ColABC | nABC ]...
        destruct (DecidePointsBetweenness A' B' C')
          as [[ ABC | BAC ]| ACB ]...
        { rewrite <- (BetPs_PlusS A' B' C') in AC.
          rewrite AB in AC. rewrite BC in AC.
          apply TriangleInequality in nABC. rewrite AC in nABC.
          apply LtS_irrefl in nABC. contradiction. left...
        }
        { rewrite <- (SegPs_sym B' A') in AB.
          rewrite <- (BetPs_PlusS B' C' A') in AB.
          rewrite (SegPs_sym C' A') in AB.
          rewrite BC in AB. rewrite AC in AB.
          rewrite (SegPs_sym A C) in AB.
          rewrite (SegPs_sym A B) in AB.
          assert (nColBCA : ~ [ B, C, A ]); ncolperps.
          apply (TriangleInequality B C A) in nColBCA.
          rewrite AB in nColBCA. apply LtS_irrefl in nColBCA.
          contradiction. left...
        }
        { rewrite <- (BetPs_PlusS B' A' C') in BC.
          rewrite AC in BC. rewrite (SegPs_sym B' A') in BC.
          rewrite AB in BC.
          assert (nColBAC : ~ [ B, A, C ]); ncolperps.
          apply TriangleInequality in nColBAC.
          rewrite (SegPs_sym B A) in nColBAC.
          rewrite BC in nColBAC.
          apply LtS_irrefl in nColBAC. contradiction. left...
        }
      }
    }
  }
Qed.
Lemma nColPs_EqSgs_nColPs :
  forall A B C A' B' C' : Point,
  ~ [ A, B, C ]
    -> [| A, B |] = [| A', B' |]
    -> [| B, C |] = [| B', C' |]
    -> [| A, C |] = [| A', C' |]
    -> ~ [ A', B', C' ].
Proof with eauto.
  intros A B C A' B' C' nColABC AB BC AC.
  contradict nColABC.
  apply (ColPs_EqSgs_ColPs A' B' C' A B C)...
Qed.

Lemma BetPs_EqSgs_BetPs :
  forall (A B C D E F : Point),
  [ A # B # C ]
    -> [| A, B |] = [| D, E |]
    -> [| B, C |] = [| E, F |]
    -> [| C, A |] = [| F, D |]
    -> [ D # E # F ].
Proof with eauto.
  intros A B C D E F BetABC AB BC CA.
  destruct (BetPs_3DiPs A B C BetABC) as [ nAeqB [ nBeqC nAeqC ]].
  assert (H : [|A, B|] ++ [|B, C|] = [|A, C|]).
  { apply BetPs_PlusS... }
  destruct (PlusS_BetPs D E F); dips.
  { rewrite AB in *. rewrite BC in *. rewrite SegPs_sym in CA.
    symmetry in CA. rewrite SegPs_sym in CA. rewrite CA in *...
  }
  destruct H0; subst.
  { apply EqSgs_EqPs in AB. contradiction. }
  { apply EqSgs_EqPs in BC. contradiction. }
Qed.

Lemma OrdRs_nColRs :
  forall (a b c d : Ray)
    (roab : da a = da b)(robc : da b = da c)(rocd : da c = da d),
  ![ a # b # c # d ]
    -> ![ a # b ] /\ ![ b # c ] /\ ![ c # d ]
    /\ ![ a # c ] /\ ![ b # d ] /\ ![ a # d ].
Proof with eauto.
  intros a b c d roab robc rocd [ abc [ abd [ acd bcd ]]].
  destruct (BetRs_nColRs a b c abc) as [ diab [ dibc diac ]].
  destruct (BetRs_nColRs a b d abd) as [ _ [ dibd diad ]].
  destruct (BetRs_nColRs a c d acd) as [ _ [ dicd _ ]].
  split...
Qed.

Lemma OpRs_EqSupAngRs :
  forall (a b c a' b' c' : Ray)
    (roab : da a = da b)(robc : da b = da c)
    (roa'b' : da a' = da b')(rob'c' : da b' = da c'),
  a == !c
    -> a' == !c'
    -> [| a, b | roab |] = [| a', b' | roa'b' |]
    -> [| b, c | robc |] = [| b', c' | rob'c' |].
Proof with eauto.
  intros a b c a' b' c' roab robc roa'b' rob'c' aopc a'opc' ab.
  destruct (classic (a == b)) as [ aeqb | naeqb ].
  { assert (a'eqb' : a' == b'). { eapply (EqAs_EqRs_EqRs a b a' b')... }
    rewrite aeqb in *. rewrite a'eqb' in a'opc'.
    apply OpRs_OpRs in aopc. apply OpRs_OpRs in a'opc'.
    eapply EqAs_OpRs_OpRs...
  }
  { destruct (classic (a <==> b)) as [ aopb | naopb ].
    { assert (a'opb' : a' <==> b').
      { eapply (EqAs_OpRs_OpRs a b a' b')... }
      apply OpRs_OpRs in aopb. apply OpRs_OpRs in a'opb'.
      assert (beqc : b == c).
      { apply OpRs_sym in aopb. eapply OpRs_trans... }
      assert (b'eqc' : b' == c').
      { apply OpRs_sym in a'opb'. eapply OpRs_trans... }
      eapply (EqAs_EqRs_EqRs b c b' c')...
    }
    { assert (diab : ![ a # b ]).
      { apply nColRs_nColPs; do 2 try split...
        contradict naopb. apply OpRs_OpRs...
      }
      assert (dibc : ![ b # c ]).
      { apply (nColRs_OpRs_nColRs a b c diab aopc). }
      assert (dia'b' : ![ a' # b' ]).
      { apply (EqAngRs_nColRs_nColRs a b a' b' roab roa'b' ab diab). }
      assert (dib'c' : ![ b' # c' ]).
      { apply (nColRs_OpRs_nColRs a' b' c' dia'b' a'opc'). }
      assert (tab' : %[a # b | diab] = %[a' # b' | dia'b']).
      { apply (EqAs_EqTs a b a' b' roab roa'b' diab dia'b' ab). }
      assert (tac : exists T : bool, %[a' # b' | dia'b'] = T).
      { exists (%[a' # b' | dia'b'])... }
      destruct tac as [ T tab ]. rewrite tab in tab'.
      induction T.
      { assert (iab : [| a, b | roab |] = [| a # b | diab |]).
        { apply (LeftOrientation_EqAs a b roab diab)... }
        assert (ia'b' : [| a', b' | roa'b' |] = [| a' # b' | dia'b' |]).
        { apply (LeftOrientation_EqAs a' b' roa'b' dia'b')... }
        assert (iaib : [| a # b | diab |] = [| a' # b' | dia'b' |]).
        { rewrite <- iab. rewrite <- ia'b'... }
        assert (bc : [| b # c | dibc |] = [| b' # c' | dib'c' |]).
        { apply (EqSupConvexAngRs a b c a' b' c' diab dibc dia'b' dib'c')... }
        assert (abc : %[ a # b | diab ] = %[ b # c | dibc ]).
        { apply (OpRs_EqOs_Left a b c diab dibc)... }
        assert (abc' : %[ a' # b' | dia'b' ] = %[ b' # c' | dib'c' ]).
        { apply (OpRs_EqOs_Left a' b' c' dia'b' dib'c')... }
        assert (tbc : %[b # c | dibc] = true). { rewrite <- abc... }
        assert (tbc' : %[b' # c' | dib'c'] = true). { rewrite <- abc'... }
        apply (LeftOrientation_EqAs b c robc dibc)in tbc...
        apply (LeftOrientation_EqAs b' c' rob'c' dib'c') in tbc'...
        rewrite tbc. rewrite tbc'...
      }
      { assert (iab : [| b, a | eq_sym roab |] = [|a # b | diab|]).
        { apply (RightOrientation_EqAs a b roab diab)... }
        assert (ia'b' : [| b', a' | eq_sym roa'b' |] = [|a' # b' | dia'b'|]).
        { apply (RightOrientation_EqAs a' b' roa'b' dia'b')... }
        assert (iaib : [| a # b | diab |] = [| a' # b' | dia'b' |]).
        { rewrite <- iab. rewrite <- ia'b'. apply EqAs_EqExpAs... }
        assert (bc : [| b # c | dibc |] = [| b' # c' | dib'c' |]).
        { apply (EqSupConvexAngRs a b c a' b' c' diab dibc dia'b' dib'c')... }
        assert (abc : %[ a # b | diab ] = %[ b # c | dibc ]).
        { apply (OpRs_EqOs_Left a b c diab dibc)... }
        assert (abc' : %[ a' # b' | dia'b' ] = %[ b' # c' | dib'c' ]).
        { apply (OpRs_EqOs_Left a' b' c' dia'b' dib'c')... }
        assert (tbc : %[b # c | dibc] = false). { rewrite <- abc... }
        assert (tbc' : %[b' # c' | dib'c'] = false). { rewrite <- abc'... }
        apply (RightOrientation_EqAs b c robc dibc)in tbc...
        apply (RightOrientation_EqAs b' c' rob'c' dib'c') in tbc'...
        pir robc => (eq_sym (eq_sym robc)).
        pir rob'c' => (eq_sym (eq_sym rob'c')).
        apply (EqAs_EqExpAs c b c' b' (eq_sym robc)(eq_sym rob'c'))...
        pir (eq_sym (eq_sym (eq_sym robc))) => (eq_sym robc).
        pir (eq_sym (eq_sym (eq_sym rob'c'))) => (eq_sym rob'c').
        rewrite tbc. rewrite tbc'...
      }
    }
  }
Qed.

Lemma OpRs_EqAngRs_OpRs :
  forall (a b c a' b' c' : Ray)
    (roab : da a = da b)(robc : da b = da c)
    (roa'b' : da a' = da b')(rob'c' : da b' = da c'),
  a == !c
    -> [| a, b | roab |] = [| a', b' | roa'b' |]
    -> [| b, c | robc |] = [| b', c' | rob'c' |]
    -> a' == !c' .
Proof with eauto.
  intros a b c a' b' c' roab robc roa'b' rob'c' aopc ab bc.
  destruct (DrawOpRay a') as [ c'' a'opc'' ].
  assert (rob'c'' : da b' = da c'').
  { destruct a'opc'' as [ roa'c'' _ ]... rewrite <- roa'b'... }
  assert (bc' : [| b, c | robc |] = [| b', c'' | rob'c'' |]).
  { apply (OpRs_EqSupAngRs a b c a' b' c'' roab robc roa'b' rob'c'')...
    apply OpRs_OpRs in a'opc''. rewrite a'opc''; reflexivity.
  }
  assert (c'eqc'' : c' == c'').
  { rewrite bc in bc'. apply -> (EqAs_EqRs b' c' c'' rob'c' rob'c'')... }
  rewrite c'eqc''. apply OpRs_OpRs...
Qed.

Lemma EqSupAs :
  forall (a b a' b' : Ray)(roab : da a = da b)(roa'b' : da a' = da b'),
  [| a, b | roab |] = [| a', b' | roa'b' |]
    <-> [| a, !b | eq_trans roab (OpRays_0 b) |]
      = [| a', !b' | eq_trans roa'b' (OpRays_0 b') |].
Proof with eauto.
  intros a b a' b' roab roa'b'.
  destruct (DrawOpRay b) as [ d bopd ].
  assert (road : da a = da d).
  { rewrite roab. destruct bopd. rewrite <- H... }
  assert (roab' : da a = da (!b)).
  { destruct bopd.
    rewrite road. rewrite <- H. apply OpRays_0.
  }
  pir (eq_trans roab (OpRays_0 b)) => roab'.
  apply OpRs_OpRs in bopd. apply OpRs_sym in bopd.
  rewrite <- (proj2 (EqAs_EqRs a d (!b) road roab'))...
  destruct (DrawOpRay b') as [ d' b'opd' ].
  assert (roa'd' : da a' = da d').
  { rewrite roa'b'. destruct b'opd'... }
  assert (roa'b'' : da a' = da (!b')).
  { destruct b'opd'.
    rewrite roa'd'. rewrite <- H. apply OpRays_0.
  }
  pir (eq_trans roa'b' (OpRays_0 b')) => roa'b''.
  apply OpRs_OpRs in b'opd'. apply OpRs_sym in b'opd'.
  rewrite <- (proj2 (EqAs_EqRs a' d' (!b') roa'd' roa'b''))...
  split.
  { intro ab.
    eapply (OpRs_EqSupAngRs b a d b' a' d'); try apply OpRs_sym...
    apply EqAs_EqExpAs...
  }
  { intro ab'.
    eapply (OpRs_EqSupAngRs d a b d' a' b' )...
    apply EqAs_EqExpAs...
  }
Qed.

Lemma EqOppVertAs :
  forall (a b : Ray)(roab' : da a = da (!b))(roa'b : da (!a) = da b),
  [| a, !b | roab' |] = [| !a, b | roa'b |].
Proof with eauto.
  intros a b roab' roa'b.
  destruct (classic (![ a # b ])) as [ diab | ndiab ].
  { assert (diab' : ![ a # !b ]). { apply (nColOpRs_2 a b diab)... }
    assert (dia'b : ![ !a # b ]). { apply (nColOpRs_1 a b diab)... }
    assert (dia'b' : ![ !a # !b ]).
    { apply (nColOpRs_2 (!a) b dia'b)... }
    eapply (EqConvexAs_EqOs_EqAs a (!b)(!a) b roab' roa'b diab' dia'b)...
    { rewrite (ConvexAngRs_sym (!a) b dia'b (nColRs_sym (!a) b dia'b))...
      eapply (EqSupConvexAngRs b a (!b) a b (!a)(nColRs_sym a b diab))...
      apply OpOpRs... apply OpOpRs... symmetry.
      apply (ConvexAngRs_sym a b diab).
    }
    { rewrite <- (OpRs_EqOs_Left b a (!b)(nColRs_sym a b diab)).
      rewrite <- (OpRs_EqOs_Right b a (!a)(nColRs_sym a b diab))...
      apply OpOpRs. apply OpOpRs.
    }
  }
  { destruct (DecideCollinearRays a b) as [ H1 | H2 ]...
    { rewrite roab'. symmetry. apply OpRays_0. }
    { assert (ab' : [| a, !b | roab' |] = A180).
      { apply (EqStraightAng a (!b) roab').
        apply OpRs_OpRs. rewrite H1. apply OpOpRs.
      }
      assert (a'b : [| !a, b | roa'b |] = A180).
      { apply (EqStraightAng (!a) b roa'b).
        apply OpRs_OpRs. rewrite H1. reflexivity.
      }
      { rewrite ab'... }
    }
    assert (ab' : [| a, !b | roab' |] = A0).
    { apply (EqNullAng a (!b) roab'). rewrite H2. reflexivity. }
    assert (a'b : [| !a, b | roa'b |] = A0).
    { apply (EqNullAng (!a) b roa'b). rewrite H2. symmetry.
      apply OpOpRs.
    }
    rewrite ab'...
  }
Qed.

Lemma EqVertAs :
  forall (a b : Ray)(roab : da a = da b)(roa'b' : da (!a) = da (!b)),
  [| a, b | roab |] = [| !a, !b | roa'b' |].
Proof with eauto.
  intros a b roab roa'b'.
  assert (roab' : da a = da (!(!b))).
  { apply (eq_trans roab (eq_trans (OpRays_0 b)(OpRays_0 (!b)))). }
  assert (ab : [| a, b | roab |] = [| a, !(!b) | roab' |]).
  { apply EqAs_EqRs. apply OpOpRs. }
  rewrite ab.
  rewrite <- (EqOppVertAs a (!b) roab')...
Qed.

Lemma OpOpRs_EqVertAs :
  forall (a b c d : Ray)(roab : da a = da b)(rocd : da c = da d),
  a == !c
    -> b == !d
    -> [| a, b | roab |] = [| c, d | rocd |].
Proof with eauto.
  intros a b c d roab rocd aopc bopd.
  erewrite (EqVertAs a b).
  apply EqAngRs_inv.
  { apply OpRs_sym in aopc. symmetry... }
  { apply OpRs_sym in bopd. symmetry... }
  Unshelve.
  rewrite <- OpRays_0. rewrite <- OpRays_0...
Qed.

Definition DrawDistinctCongruentAngle_ccw :
  forall (a b c : Ray)(roab : da a = da b),
  ![ a # b ]
    -> { d : Ray | exists (rocd : da c = da d),
          ![ c # d ] /\ [| a, b | roab |] = [| c, d | rocd |] }.
Proof with eauto.
  intros a b c roab diab.
  destruct a as [ O A nAeqO ].
  destruct b as [ O' B nBeqO ].
  destruct c as [ Q D nDeqQ ].
  simpl in *. subst O'.
  cut ( { T | T = %[{{ O # A | nAeqO}} # {{O # B | nBeqO}} | diab] }).
  { intros H.
    destruct H as [ T H0 ].
    destruct (DrawPointOnGivenSide D Q T) as [ P H ]...
    assert (nColDQP : ~ [D, Q, P]). { destruct H... }
    assert (nColAOB : ~ [ A, O, B ]).
    { eapply (OsRs_OsPs A O B)... }
    assert (nColOAB : ~ [ O, A, B ]); ncolperps.
    eassert (AOB : %[ A # O # B | _ ]
      = %[{{ O # A | _ }}#{{ O # B | _ }}| _ ]).
    { destruct (OsRs_OsPs A O B nAeqO nBeqO diab) as [ H1 H2 ].
      pir H1 => nColAOB. symmetry. apply H2.
    }
    eassert (DQP : %[D # Q # P | _ ]
      = %[{{ O # A | _ }} # {{ O # B | _ }} | _ ]).
    { destruct H... pir x => nColDQP. rewrite H0 in *... }
    clear H.
    destruct (DrawEqualTriangle O A B Q D P nColOAB)
      as [ E' [ F' H ]]; ncolperps.
    assert (nColDE'F' : ~ [Q, E', F']). { destruct H... }
    assert (QsrDE' : [Q # D, E']).
    { destruct H as [ _ [ H _ ]]... }
    assert (QDsfPF' : [Q # D | P, F']).
    { destruct H as [ _ [ _ [ H _ ]]]... }
    eassert (EqTr : {{O # A # B | _ }} :=: {{Q # E' # F' | _ }}).
    { destruct H as [ H1 [ H2 [ H3 H ]]].
      pir H1 => nColDE'F'. apply H.
    }
    clear H.
    assert (QE'sfPF' : [Q # E' | P, F']).
    { apply (SHa_inv Q D P F' E' P F');
      try apply SR_refl; dips; colperps.
    }
    apply (EqPerTr_3 O A B Q E' F') in EqTr.
    unfold EqTriangle in *; simpl in *.
    destruct EqTr as [ _ [ _ [ _ [ AOBeqE'QF' _ ]]]].
    assert (nQeqF' : Q <> F'); dips.
    exists ({{ Q # F' | nQeqF' }}), eq_refl.
    split.
    { split; simpl...
      apply SHa_sym in QDsfPF'. apply SHb_sym in QDsfPF'.
      apply (SH_nColPs D Q F' P)...
    }
    { assert (nQeqE' : Q <> E'); dips.
      assert (nColE'QF' : ~ [E', Q, F']); ncolperps.
      pir (nColPerPs_3 O A B nColOAB) => nColAOB.
      pir (nColPerPs_3 Q E' F' nColDE'F') => nColE'QF'.
      eassert ([|D, Q, F' | _ , _ |] = [|E', Q, F' | _ , _ |]).
      { eapply (AngPs_inv D Q F' E' F')... try (apply SR_refl)... }
      eassert ([|A, O, B | _ , _ |] = [|E', Q, F' | _ , _ |]).
      { eapply (EqConvexAs_EqOs_EqAs' A O B E' Q F')...
        rewrite AOB. rewrite <- DQP. apply SHa_sym in QE'sfPF'.
        assert (nColE'QP : ~ [E', Q, P]).
        { apply (SH_nColPs E' Q P F')... }
        rewrite (Orientation_inv Q D P E' P nColDQP nColE'QP)...
        apply SH_SameOrientation... apply SR_refl...
        apply (nColPs_3DiPs D Q P nColDQP).
      }
      rewrite <- H in H1...
    }
  }
  { exists (%[ {{ O # A | nAeqO }} # {{ O # B | nBeqO }} | diab])... }
  Unshelve.
  simpl... simpl...
Defined.

Lemma BetRs_SubtEqAs_BetRs :
  forall (a b c a' b' c' : Ray)
    (roab : da a = da b)(roac : da a = da c)
    (roa'b' : da a' = da b')(roa'c' : da a' = da c'),
  ![ a # b # c ]
    -> [| a, b | roab |] = [| a', b' | roa'b' |]
    -> [| a, c | roac |] = [| a', c' | roa'c' |]
    -> ![ a' # b' # c' ].
Proof with eauto.
  intros a b c a' b' c' roab roac roa'b' roa'c' abc ab ac.
  assert (robc : da b = da c). { apply (eq_trans (eq_sym roab) roac). }
  assert (rob'c' : da b' = da c'). { apply (eq_trans (eq_sym roa'b') roa'c'). }
  destruct (BetRs_nColRs a b c abc) as [ diab [ dibc diac ]].
  destruct (proj1 (BetRs_EqOs a b c diab dibc diac) abc)
    as [ abTac bcTac ].
  assert (dia'b' : ![ a' # b' ]).
  { apply (EqAngRs_nColRs_nColRs a b a' b' roab roa'b' ab diab). }
  assert (dia'c' : ![ a' # c' ]).
  { apply (EqAngRs_nColRs_nColRs a c a' c' roac roa'c' ac diac). }
  assert (abTa'b' : %[a # b | diab] = %[a' # b' | dia'b']).
  { apply (EqAs_EqTs a b a' b' roab roa'b')... }
  assert (acTa'c' : %[a # c | diac] = %[a' # c' | dia'c']).
  { apply (EqAs_EqTs a c a' c' roac roa'c')... }
  destruct (DrawAngleCutRs a b c a' c' diab diac dia'c' abc)
    as [ b'' [ dia'b'' [ a'b''c' ab'' ]]].
  { apply (EqAs_EqConvexAs a c a' c' roac roa'c')... }
  assert (roa'b'' : da a' = da b''). { destruct dia'b'' as [ roa'b'' H ]... }
  assert (ab' : [| a, b | roab |] = [| a', b'' | roa'b'' |]).
  { apply (EqConvexAs_EqOs_EqAs a b a' b'' roab roa'b'' diab dia'b''); auto.
    destruct (BetRs_EqOs a b c diab dibc diac) as [ H _ ].
    destruct (H abc) as [ tab tbc ]. clear H.
    assert (dib''c' : ![ b'' # c' ]).
    { apply (BetRs_nColRs a' b'' c' a'b''c'). }
    destruct (BetRs_EqOs a' b'' c' dia'b'' dib''c' dia'c') as [ H _ ].
    destruct (H a'b''c') as [ ta'b'' tb'c' ]. clear H.
    rewrite ta'b''. rewrite tab...
  }
  rewrite ab in ab'.
  assert (b'eqb'' : b' == b'').
  { apply (EqAs_EqRs a' b' b'' roa'b' roa'b'')... }
  apply (BetRs_inv a' b'' c' a' b' c'); try reflexivity; try symmetry...
Qed.

(** Theorem #67a *)
(** Hilbert, Chapter 1 : Theorem 15. *)
Theorem BetRs_SubtConvexAngRs :
  forall (a b c a' b' c' : Ray)
    (diab : ![ a # b ])(dibc : ![ b # c ])(diac : ![ a # c ])
    (dia'b' : ![ a' # b' ])(dib'c' : ![ b' # c' ])(dia'c' : ![ a' # c' ]),
  ![ a # b # c ]
    -> ![ a' # b' # c' ]
    -> [| a # b | diab |] = [| a' # b' | dia'b' |]
    -> [| a # c | diac |] = [| a' # c' | dia'c' |]
    -> [| b # c | dibc |] = [| b' # c' | dib'c' |].
Proof with eauto.
  intros * [ roab [ robc BetRabc ]][ roa'b' [ rob'c' BetRa'b'c' ]] ab ac.
  assert (nColAOB : ~ [ db a, da a, db b ]). { destruct diab... }
  assert (nColA'O'B' : ~ [ db a', da a', db b' ]). { destruct dia'b'... }
  rewrite (ConvexAngRs_ConvexAngPs a b diab nColAOB) in ab.
  rewrite (ConvexAngRs_ConvexAngPs a' b' dia'b' nColA'O'B') in ab.
  assert (nColAOC : ~ [ db a, da a, db c ]). { destruct diac... }
  assert (nColA'O'C' : ~ [ db a', da a', db c' ]). { destruct dia'c'... }
  rewrite (ConvexAngRs_ConvexAngPs a c diac nColAOC) in ac.
  rewrite (ConvexAngRs_ConvexAngPs a' c' dia'c' nColA'O'C') in ac.
  assert (nColBOC : ~ [ db b, da b, db c ]). { destruct dibc... }
  assert (nColB'O'C' : ~ [ db b', da b', db c' ]). { destruct dib'c'... }
  rewrite (ConvexAngRs_ConvexAngPs b c dibc nColBOC).
  rewrite (ConvexAngRs_ConvexAngPs b' c' dib'c' nColB'O'C').
  destruct robc, roab, rob'c', roa'b'.
  eapply BR_SubtConvexAngPs...
Qed.

Lemma BetRs_SubtAngRs :
  forall (a b c a' b' c' : Ray)
    (roab : da a = da b)(robc : da b = da c)(roac : da a = da c)
    (roa'b' : da a' = da b')(rob'c' : da b' = da c')(roa'c' : da a' = da c'),
  ![ a # b # c ]
    -> [| a, b | roab |] = [| a', b' | roa'b' |]
    -> [| a, c | roac |] = [| a', c' | roa'c' |]
    -> [| b, c | robc |] = [| b', c' | rob'c' |].
Proof with eauto.
  intros a b c a' b' c' roab robc roac roa'b' rob'c' roa'c' abc ab ac.
  assert (a'b'c' : ![ a' # b' # c' ]).
  { eapply (BetRs_SubtEqAs_BetRs a b c a' b' c')... }
  destruct (BetRs_nColRs a b c abc) as [ diab [ dibc diac ]].
  destruct (BetRs_nColRs a' b' c' a'b'c') as [ dia'b' [ dib'c' dia'c' ]].
  destruct (proj1 (BetRs_EqOs a b c diab dibc diac) abc)
    as [ abTac bcTac ].
  destruct (proj1 (BetRs_EqOs a' b' c' dia'b' dib'c' dia'c') a'b'c')
    as [ a'b'Ta'c' b'c'Ta'c' ].
  assert (abTa'b' : %[a # b | diab] = %[a' # b' | dia'b']).
  { apply (EqAs_EqTs a b a' b' roab roa'b')... }
  assert (acTa'c' : %[a # c | diac] = %[a' # c' | dia'c']).
  { apply (EqAs_EqTs a c a' c' roac roa'c')... }
  apply (EqConvexAs_EqOs_EqAs b c b' c' robc rob'c' dibc dib'c').
  { assert (iab : [| a # b | diab |] = [| a' # b' | dia'b' |]).
    { apply (EqAs_EqConvexAs a b a' b' roab roa'b' diab dia'b' ab). }
    assert (iac : [| a # c | diac |] = [| a' # c' | dia'c' |]).
    { apply (EqAs_EqConvexAs a c a' c' roac roa'c' diac dia'c' ac). }
    eapply (BetRs_SubtConvexAngRs a b c a' b' c')...
  }
  { rewrite b'c'Ta'c'... }
Qed.

Lemma BetRs_SubtInvEqAs_BetRs :
  forall (a b c a' b' c' : Ray)
    (roab : da a = da b)(roac : da a = da c)
    (roa'b' : da a' = da b')(roa'c' : da a' = da c'),
  ![ a # b # c ]
    -> [| a, b | roab |] = [| b', a' | eq_sym roa'b' |]
    -> [| a, c | roac |] = [| c', a' | eq_sym roa'c' |]
    -> ![ a' # b' # c' ].
Proof with eauto.
  intros a b c a' b' c' roab roac roa'b' roa'c' abc ab ac.
  assert (robc : da b = da c). { apply (eq_trans (eq_sym roab) roac). }
  assert (rob'c' : da b' = da c'). { apply (eq_trans (eq_sym roa'b') roa'c'). }
  destruct (BetRs_nColRs a b c abc) as [ diab [ dibc diac ]].
  destruct (proj1 (BetRs_EqOs a b c diab dibc diac) abc)
    as [ abTac bcTac ].
  assert (dib'a' : ![ b' # a' ]).
  { apply (EqAngRs_nColRs_nColRs a b b' a' roab (eq_sym roa'b') ab diab). }
  assert (dic'a' : ![ c' # a' ]).
  { apply (EqAngRs_nColRs_nColRs a c c' a' roac (eq_sym roa'c') ac diac). }
  assert (abTa'b' : %[a # b | diab] = %[b' # a' | dib'a']).
  { apply (EqAs_EqTs a b b' a' roab (eq_sym roa'b'))... }
  assert (acTa'c' : %[a # c | diac] = %[c' # a' | dic'a']).
  { apply (EqAs_EqTs a c c' a' roac (eq_sym roa'c'))... }
  destruct (DrawAngleCutRs a b c a' c' diab diac (nColRs_sym c' a' dic'a') abc)
    as [ b'' [ dia'b'' [ a'b''c' ab'' ]]].
  { rewrite (ConvexAngRs_sym a' c' (nColRs_sym c' a' dic'a') dic'a').
    apply (EqAs_EqConvexAs a c c' a' roac (eq_sym roa'c'))...
  }
  assert (roa'b'' : da a' = da b''). { destruct dia'b'' as [ roa'b'' H ]... }
  assert (ab' : [| a, b | roab |] = [| b'', a' | eq_sym roa'b'' |]).
  { apply (EqConvexAs_EqOs_EqAs a b b'' a' roab (eq_sym roa'b'') diab
      (nColRs_sym a' b'' dia'b'')); auto. rewrite ab''.
    apply ConvexAngRs_sym.
    destruct (BetRs_EqOs a b c diab dibc diac) as [ H _ ].
    destruct (H abc) as [ tab tbc ]. clear H.
    apply BetRs_sym in a'b''c'.
    assert (dic'b'' : ![ c' # b'' ]).
    { apply (BetRs_nColRs c' b'' a' a'b''c'). }
    destruct (BetRs_EqOs c' b'' a' dic'b'' (nColRs_sym a' b'' dia'b'') dic'a')
      as [ H _ ].
    destruct (H a'b''c') as [ ta'b'' tb'c' ]. clear H.
    rewrite tb'c'. rewrite tab...
  }
  rewrite ab in ab'.
  assert (b'eqb'' : b' == b'').
  { apply (EqAs_EqRs a' b' b'' roa'b' roa'b'')...
    apply EqAs_EqExpAs in ab'...
    pir (eq_sym (eq_sym roa'b')) => roa'b'.
    pir (eq_sym (eq_sym roa'b'')) => roa'b''...
  }
  apply (BetRs_inv a' b'' c' a' b' c'); try reflexivity; try symmetry...
Qed.

(** Theorem #67b *)
(** Hilbert, Chapter 1 : Theorem 20. *)
Lemma BetRs_SubtAs_SR_BetRs :
  forall (a b c a' b' c' : Ray)
    (diab : ![ a # b ])(diac : ![ a # c ])
    (dia'b' : ![ a' # b' ])(dia'c' : ![ a' # c' ]),
  ![ a # b # c ]
    -> ![ a' # b', c' ]
    -> [| a # b | diab |] = [| a' # b' | dia'b' |]
    -> [| a # c | diac |] = [| a' # c' | dia'c' |]
    -> ![ a' # b' # c' ].
Proof with eauto.
  intros a b c a' b' c' diab diac dia'b' dia'c' abc a'_b'c' ab ac.
  assert (roab : da a = da b). { destruct diab... }
  assert (roac : da a = da c). { destruct diac... }
  assert (roa'b' : da a' = da b'). { destruct dia'b'... }
  assert (roa'c' : da a' = da c'). { destruct dia'c'... }
  destruct (BetRs_nColRs a b c abc) as [ _ [ dibc _ ]]...
  destruct (proj1 (BetRs_EqOs a b c diab dibc diac) abc) as [ H1 H2 ].
  destruct (SameSideRs_nColRs a' b' c' a'_b'c') as [ _ [ dib'c' _ ]]...
  assert (H3 : %[ a' # b' | dia'b'] = %[ a' # c' | dia'c']).
  { apply (SameSideRs_EqOs a' b' c' dia'b' dia'c')... }
  destruct (DecideOrientationsRs a b a' b' diab dia'b') as [ H4 | H4 ]...
  { apply (BetRs_SubtEqAs_BetRs a b c a' b' c' roab roac roa'b' roa'c')...
    { eapply EqConvexAs_EqOs_EqAs. apply ab. apply H4. }
    { eapply EqConvexAs_EqOs_EqAs. apply ac.
      rewrite <- H1. rewrite <- H3. apply H4.
    }
  }
  { eapply (BetRs_SubtInvEqAs_BetRs a b c a' b' c' roab roac roa'b' roa'c')...
    { eapply EqConvexAs_EqOs_EqAs.
      erewrite (ConvexAngRs_sym b' a')...
      rewrite H4. symmetry. apply DiOsRs.
    }
    { eapply EqConvexAs_EqOs_EqAs. rewrite ac. apply ConvexAngRs_sym...
      rewrite <- H1. rewrite H4. symmetry. rewrite H3.
      apply DiOsRs...
    }
  }
  Unshelve.
    apply nColRs_sym...
    apply nColRs_sym...
Qed.

Lemma BetRs_SubtInvEqAs :
  forall (a b c a' b' c' : Ray)
    (roab : da a = da b)(robc : da b = da c)(roac : da a = da c)
    (roa'b' : da a' = da b')(rob'c' : da b' = da c')(roa'c' : da a' = da c'),
  ![ a # b # c ]
    -> [| a, b | roab |] = [| b', a' | eq_sym roa'b' |]
    -> [| a, c | roac |] = [| c', a' | eq_sym roa'c' |]
    -> [| b, c | robc |] = [| c', b' | eq_sym rob'c' |].
Proof with eauto.
  intros a b c a' b' c' roab robc roac roa'b' rob'c' roa'c' abc ab ac.
  assert (a'b'c' : ![ a' # b' # c' ]).
  { eapply (BetRs_SubtInvEqAs_BetRs a b c a' b' c')... }
  destruct (BetRs_nColRs a b c abc) as [ diab [ dibc diac ]].
  destruct (BetRs_nColRs a' b' c' a'b'c') as [ dia'b' [ dib'c' dia'c' ]].
  assert (aba'b' : [| a # b | diab |] = [| a' # b' | dia'b' |]).
  { rewrite (ConvexAngRs_sym a' b' dia'b' (nColRs_sym a' b' dia'b')).
    apply (EqAs_EqConvexAs a b b' a' roab (eq_sym roa'b'))...
  }
  assert (aba'c' : [| a # c | diac |] = [| a' # c' | dia'c' |]).
  { rewrite (ConvexAngRs_sym a' c' dia'c' (nColRs_sym a' c' dia'c')).
    apply (EqAs_EqConvexAs a c c' a' roac (eq_sym roa'c'))...
  }
  destruct (proj1 (BetRs_EqOs a' b' c' dia'b' dib'c' dia'c') a'b'c')
    as [ a'b'Ta'c' b'c'Ta'c' ].
  assert (abTa'b' : %[a # b | diab] = %[b' # a' | nColRs_sym a' b' dia'b']).
  { apply (EqAs_EqTs a b b' a' roab (eq_sym roa'b'))... }
  assert (acTa'c' : %[a # c | diac] = %[c' # a' | nColRs_sym a' c' dia'c']).
  { apply (EqAs_EqTs a c c' a' roac (eq_sym roa'c'))... }
  apply (EqConvexAs_EqOs_EqAs b c c' b' robc (eq_sym rob'c') dibc
    (nColRs_sym b' c' dib'c')).
  { rewrite <- (ConvexAngRs_sym b' c' dib'c' (nColRs_sym b' c' dib'c')).
    eapply (BetRs_SubtConvexAngRs a b c a' b' c')...
  }
  { apply (BetRs_EqOs a b c diab dibc diac) in abc.
    destruct abc as [ abac bcac ]. rewrite bcac. rewrite acTa'c'.
    apply SameSideRs_EqOs. apply BetRs_sym in a'b'c'.
    apply BetRs_SameSideRs in a'b'c'. destruct a'b'c'.
    apply SameSideRs_sym...
  }
Qed.

(** Problem #39 *)
(* Given an angle BAC and given a ray DE,
 there exists a unique ray DF on a given side of the line DE,
 marked by point P, such that BAC = EDF. *)
Definition DrawCongruentAngle_ccw :
  forall (a : Ray)(A : Angle),
  { b : Ray | exists (roab : da a = da b), [| a, b | roab |] = A }.
Proof with eauto.
  intros a Ang.
  destruct (DrawSector Ang) as [[ c d rocd ] cdeqAng ].
  rewrite <- cdeqAng. clear dependent Ang.
  destruct (DrawRayApart c) as [ e dice ].
  destruct (DecideRayDirection_NESW c e d rocd dice)
    as [[[ cSRed | cORed ]| eSRcd ]| eORcd ].
  { assert (dicd : ![ c # d ]). { apply (SameSideRs_nColRs c e d)... }
    destruct (DrawDistinctCongruentAngle_ccw c d a rocd dicd)
      as [ b H ].
    exists b.
    destruct H as [ roab [ diab abcd ]].
    exists roab...
  }
  { assert (dicd : ![ c # d ]).
    { apply (SameSideRs_nColRs c (!e) d)... apply SameSideRs_sym... }
    destruct (DrawDistinctCongruentAngle_ccw c d a rocd dicd)
      as [ b H ].
    exists b.
    destruct H as [ roab [ diab abcd ]].
    exists roab...
  }
  { assert (roce : da c = da e). { destruct dice... }
    destruct (DrawDistinctCongruentAngle_ccw c e a roce dice)
      as [ f H ].
    assert (roaf : da a = da f). { destruct H as [ roaf [ diaf ceaf ]]... }
    assert (diaf : ![ a # f ]). { destruct H as [ roaf' [ diaf ceaf ]]... }
    assert (ceaf : [| c, e | roce |] = [| a, f | roaf |]).
    { destruct H as [ roaf' [ diaf' ceaf ]]... pir roaf' => roaf. }
    clear H.
    assert (died : ![ e # d ]). { apply (SameSideRs_nColRs e c d eSRcd). }
    assert (roed : da e = da d). { destruct died... }
    destruct (DrawDistinctCongruentAngle_ccw e d f roed died)
      as [ b H1 ].
    exists b.
    destruct H1 as [ rofb [ difb edfb ]].
    assert (roab : da a = da b). { rewrite roaf... }
    exists roab.
    destruct (classic (c == d)) as [ ceqd | nceqd ].
    { apply (EqAs_EqExpAs c e a f roce roaf) in ceaf.
      assert (aeqb : a == b).
      { apply -> (EqAs_EqRs f a b (eq_sym roaf) rofb)...
        rewrite <- ceaf. rewrite <- edfb.
        apply (EqAs_EqRs e c d (eq_sym roce) roed) in ceqd...
      }
      eapply (EqAs_EqRs_EqRs a b c d)...
    }
    { edestruct (DecideRaysOrderOnSameSide e c d) as [ ecd | edc ]...
      { symmetry. eapply (BetRs_SubtAngRs e c d f a b)...
        apply (EqAs_EqExpAs c e a f roce roaf ceaf).
      }
      { pir roab => (eq_sym (eq_sym roab)).
        pir rocd => (eq_sym (eq_sym rocd)).
        eapply (EqAs_EqExpAs b a d c); eauto. symmetry.
        eapply (BetRs_SubtAngRs e d c f b a); auto. apply edfb.
        apply (EqAs_EqExpAs c e a f roce roaf); auto.
      }
    }
  }
  { assert (roce : da c = da e).
    { destruct eORcd as [ H0 [ H1 _ ]]... rewrite H1. apply OpRays_0... }
    destruct (DrawDistinctCongruentAngle_ccw c e a roce dice)
      as [ f H ].
    assert (roaf : da a = da f). { destruct H as [ roaf [ diaf ceaf ]]... }
    assert (diaf : ![ a # f ]). { destruct H as [ roaf' [ diaf ceaf ]]... }
    assert (ceaf : [| c, e | roce |] = [| a, f | roaf |]).
    { destruct H as [ roaf' [ diaf' ceaf ]]... pir roaf' => roaf. }
    clear H.
    assert (died : ![ e # d ]).
    { apply (SameSideRs_nColRs e (!c) d)... apply SameSideRs_sym... }
    assert (roed : da e = da d). { destruct died... }
    destruct (DrawDistinctCongruentAngle_ccw e d f roed died)
      as [ b H1 ].
    exists b.
    destruct H1 as [ rofb [ difb edfb ]].
    assert (roab : da a = da b). { rewrite roaf... }
    exists roab.
    destruct (classic (!c == d)) as [ copd | ncopd ].
    { symmetry. symmetry in copd. apply OpRs_sym in copd.
      assert (aopb : a == !b).
      { apply (OpRs_EqAngRs_OpRs c e d a f b roce roed roaf rofb copd)... }
      apply OpRs_OpRs in copd. apply (EqStraightAng c d rocd) in copd.
      apply OpRs_OpRs in aopb. apply (EqStraightAng a b roab) in aopb.
      rewrite copd...
    }
    destruct (DecideRaysOrderOnSameSide e (!c) d) as [ ecd | edc ]...
    { apply SameSideRs_sym... }
    { pir roab => (eq_sym (eq_sym roab)).
      pir rocd => (eq_sym (eq_sym rocd)).
      apply (EqAs_EqExpAs b a d c (eq_sym roab)(eq_sym rocd)).
      apply <- (EqSupAs b a d c (eq_sym roab)).
      apply (EqAs_EqExpAs c e a f) in ceaf.
      apply (EqSupAs e c f a (eq_sym roce)) in ceaf. symmetry.
      assert (roc'd: da (!c) = da d).
      { rewrite <- rocd. symmetry. apply OpRays_0. }
      assert (roa'b: da (!a) = da b).
      { rewrite <- roab. symmetry. apply OpRays_0. }
      pir (eq_trans (eq_sym rocd)(OpRays_0 c)) => (eq_sym roc'd).
      pir (eq_trans (eq_sym roab)(OpRays_0 a)) => (eq_sym roa'b).
      apply (EqAs_EqExpAs (!c) d (!a) b roc'd roa'b).
      eapply (BetRs_SubtAngRs e (!c) d f (!a) b)...
    }
    { pir roab => (eq_sym (eq_sym roab)).
      pir rocd => (eq_sym (eq_sym rocd)).
      apply (EqAs_EqExpAs b a d c (eq_sym roab)(eq_sym rocd)).
      apply <- (EqSupAs b a d c (eq_sym roab)).
      apply (EqAs_EqExpAs c e a f) in ceaf.
      apply (EqSupAs e c f a (eq_sym roce)) in ceaf. symmetry.
      assert (roc'd: da (!c) = da d).
      { rewrite <- rocd. symmetry. apply OpRays_0. }
      assert (roa'b: da (!a) = da b).
      { rewrite <- roab. symmetry. apply OpRays_0. }
      pir (eq_trans (eq_sym rocd)(OpRays_0 c)) => (eq_sym roc'd).
      pir (eq_trans (eq_sym roab)(OpRays_0 a)) => (eq_sym roa'b).
      eapply (BetRs_SubtAngRs e d (!c) f b (!a))...
    }
  }
Defined.
Definition DrawCongruentAngle_cw :
  forall (a : Ray)(A : Angle),
  { b : Ray | exists (roba : da b = da a), [| b, a | roba |] = A }.
Proof with eauto.
  intros a Ang.
  destruct (DrawSector Ang) as [[ c d rocd ] cdeqA ].
  destruct (DrawCongruentAngle_ccw a ([| d, c | eq_sym rocd |])) as [ b H ].
  exists b.
  destruct H as [ roab abeqdc ].
  exists (eq_sym roab).
  rewrite <- cdeqA. pir rocd => (eq_sym (eq_sym rocd)).
  apply (EqAs_EqExpAs a b d c roab (eq_sym rocd)).
  pir (eq_sym (eq_sym rocd)) => rocd.
Defined.

Lemma BetRs_EqAngRs_BetRs :
  forall (a b c d : Ray)(roab : da a = da b)(rocd : da c = da d),
  ![ a # b # d ]
    -> [| a, b | roab |] = [| c, d | rocd |]
    -> ![ a # c # d ].
Proof with eauto.
  intros * abd ab_cd.
  destruct (BetRs_nColRs a b d abd) as [ diab [ dibd diad ]].
  edestruct (DrawAngleCutRs a b d d a)
    as [ e [ dide [ BetRdea H ]]]...
  { apply ConvexAngRs_sym. }
  apply BetRs_sym in BetRdea.
  rewrite (ConvexAngRs_sym d e dide (nColRs_sym d e dide)) in H.
  assert (roed : da e = da d). { destruct dide... }
  assert (ab_ed : [| a, b | roab |] = [| e, d | roed |]).
  { eapply (EqConvexAs_EqOs_EqAs a b e d)...
    apply (BetRs_EqOs a b d diab dibd diad) in abd.
    destruct abd as [ ab_ad bd_ad ].
    destruct (BetRs_nColRs a e d BetRdea) as [ diae [ died _ ]].
    apply (BetRs_EqOs a e d diae died diad) in BetRdea.
    destruct BetRdea as [ ae_ad ed_ad ].
    pir (nColRs_sym d e dide) => died.
    destruct ed_ad...
  }
  assert (ceqe : c == e).
  { rewrite ab_cd in ab_ed.
    apply -> (EqAngRs_EqRs_cw d c e rocd roed)...
  }
  apply (BetRs_inv a e d a c d); try reflexivity... symmetry...
  Unshelve. eauto. apply nColRs_sym...
Qed.

Lemma BetRs_EqAngRs_BetRs_cross :
  forall (a b c a' b' c' : Ray)(roab : da a = da b)(roac : da a = da c)
         (rob'c' : da b' = da c')(roa'c' : da a' = da c'),
  ![ a # b # c ]
    -> [| a, c | roac |] = [| a', c' | roa'c' |]
    -> [| a, b | roab |] = [| b', c' | rob'c' |]
    -> ![ a' # b' # c' ].
Proof with eauto.
  intros * abc ac ab.
  destruct (BetRs_nColRs a b c) as [ diab [ dibc diac ]]...
  assert (dia'c' : ![ a' # c' ]).
  { apply (EqAngRs_nColRs_nColRs a c a' c' roac roa'c')... }
  assert (dib'c' : ![ b' # c' ]).
  { eapply (EqAngRs_nColRs_nColRs a b b' c')... }
  destruct (DrawAngleCutRs a b c a' c' diab diac dia'c')
    as [ e [ dide [ BetRdea H ]]]...
  { apply (EqAs_EqConvexAs a c a' c' roac roa'c')... }
  assert (roa'e : da a' = da e). { destruct dide... }
  assert (ab_ae : [| a, b | roab |] = [| a', e | roa'e |]).
  { apply (EqConvexAs_EqOs_EqAs a b a' e roab roa'e diab dide)...
    apply (BetRs_EqOs a b c diab dibc diac) in abc.
    destruct abc as [ ab_ac bc_ac ].
    destruct (BetRs_nColRs a' e c' BetRdea) as [ dia'e [ diec' _ ]].
    apply (EqAs_EqTs a c a' c' roac roa'c' diac dia'c') in ac.
    apply (BetRs_EqOs a' e c' dia'e diec' dia'c') in BetRdea.
    destruct BetRdea as [ ae_ad ed_ad ].
    pir dide => dia'e. rewrite ae_ad. rewrite <- ac...
  }
  assert (roeb' : da e = da b'). { rewrite <- roa'e. rewrite roa'c'... }
  apply (BetRs_EqAngRs_BetRs a' e b' c' roa'e rob'c')... rewrite <- ab...
Qed.

Lemma BetRs_AddEqAs_BetRs :
  forall (a b c a' b' c' : Ray)(roab : da a = da b)(robc : da b = da c)
         (roa'b' : da a' = da b')(rob'c' : da b' = da c'),
  ![ a # b # c ]
    -> [| a, b | roab |] = [| a', b' | roa'b' |]
    -> [| b, c | robc |] = [| b', c' | rob'c' |]
    -> ![ a' # b' # c' ].
Proof with eauto.
  intros * abc ab bc.
  assert (roac : da a = da c). { apply (eq_trans roab robc). }
  assert (roa'c' : da a' = da c'). { apply (eq_trans roa'b' rob'c'). }
  destruct (BetRs_nColRs a b c abc) as [ diab [ dibc diac ]].
  assert (dia'b' : ![ a' # b' ]).
  { apply (EqAngRs_nColRs_nColRs a b a' b' roab roa'b' ab diab). }
  assert (dib'c' : ![ b' # c' ]).
  { apply (EqAngRs_nColRs_nColRs b c b' c' robc rob'c' bc dibc). }
  assert (dia'c' : ![ a' # c' ]).
  { apply nColRs_nColPs.
    split.
    { apply (eq_trans roa'b' rob'c'). }
    { split.
      { intros a'eqc'.
        apply EqAs_EqExpAs in ab.
        apply <- (EqAs_EqRs b' a' c' (eq_sym roa'b') rob'c') in a'eqc'.
        rewrite <- ab in a'eqc'. rewrite <- bc in a'eqc'.
        apply EqAs_EqRs in a'eqc'. apply nColRs_nColPs in diac.
        destruct diac as [ _ [ nac _ ]]. contradiction.
      }
      { intros a'opc'.
        assert (aopc : a == !c).
        { apply (OpRs_EqAngRs_OpRs a' b' c' a b c roa'b' rob'c' roab robc)... }
        apply nColRs_nColPs in diac. destruct diac as [ _ [ _ naopc ]].
        contradiction.
      }
    }
  }
  destruct (DrawCongruentAngle_ccw a' ([| a, c | eq_trans roab robc |]))
    as [ c'' [ roa'c'' ac'' ]].
  symmetry in ac''. pir (eq_trans roab robc) => roac.
  assert (dia'c'' : ![ a' # c'' ]).
  { apply (EqAngRs_nColRs_nColRs a c a' c'' roac roa'c'' ac'' diac). }
  destruct (DrawAngleCutRs a b c a' c'' diab diac dia'c'' abc)
    as [ b'' [ dia'b'' [ a'b''c'' ab'' ]]].
  { apply (EqAs_EqConvexAs a c a' c'' roac roa'c'')... }
  assert (roa'b'' : da a' = da b''). { destruct dia'b'' as [ roa'b'' H ]... }
  assert (ab' : [| a, b | roab |] = [| a', b'' | roa'b'' |]).
  { apply (EqConvexAs_EqOs_EqAs a b a' b'' roab roa'b'' diab dia'b'')...
    destruct (BetRs_EqOs a b c diab dibc diac) as [ H _ ].
    destruct (H abc) as [ tab tbc ]. clear H.
    assert (dib''c'' : ![b'' # c'']).
    { apply (BetRs_nColRs a' b'' c'' a'b''c''). }
    destruct (BetRs_EqOs a' b'' c'' dia'b'' dib''c'' dia'c'') as [ H _ ].
    destruct (H a'b''c'') as [ ta'b'' tb'c'' ]. clear H.
    rewrite tab. rewrite ta'b''.
    apply (EqAs_EqTs a c a' c'' roac roa'c'' diac dia'c'' ac'').
  }
  rewrite ab in ab'.
  assert (b'eqb'' : b' == b'').
  { apply -> (EqAs_EqRs a' b' b'' roa'b' roa'b'')... }
  clear ab'.
  assert (rob'c'' : da b' = da c''). { rewrite <- roa'c''... }
  assert (bc' : [| b, c | robc |] = [| b', c'' | rob'c'' |]).
  { eapply (BetRs_SubtAngRs a b c a' b' c'')... }
  apply (BetRs_inv a' b'' c'' a' b' c'); try reflexivity; try symmetry...
  apply (EqAs_EqRs b' c' c'' rob'c' rob'c'')... rewrite <- bc'...
Qed.

Lemma BetRs_AddAngRs :
  forall (a b c a' b' c' : Ray)(roab : da a = da b)(robc : da b = da c)
         (roa'b' : da a' = da b')(rob'c' : da b' = da c'),
  ![ a # b # c ]
    -> ![ a' # b' # c' ]
    -> [| a, b | roab |] = [| a', b' | roa'b' |]
    -> [| b, c | robc |] = [| b', c' | rob'c' |]
    -> [| a, c | eq_trans roab robc |]
     = [| a', c' | eq_trans roa'b' rob'c' |].
Proof with eauto.
  intros * abc a'b'c' ab bc.
  destruct (BetRs_nColRs a b c abc) as [ diab [ dibc diac ]].
  destruct (BetRs_nColRs a' b' c' a'b'c') as [ dia'b' [ dib'c' dia'c' ]].
  assert (iab : [|a # b | diab|] = [|a' # b' | dia'b'|]).
  { apply (EqAs_EqConvexAs a b a' b' roab roa'b' diab dia'b' ab). }
  assert (ibc : [|b # c | dibc|] = [|b' # c' | dib'c'|]).
  { apply (EqAs_EqConvexAs b c b' c' robc rob'c' dibc dib'c' bc). }
  assert (iac : [|a # c | diac|] = [|a' # c' | dia'c'|]).
  { eapply (BetRs_AddConvexAngRs a b c a' b' c')... }
  apply (BetRs_EqOs a b c diab dibc diac) in abc.
  destruct abc as [ tab tbc ].
  apply (BetRs_EqOs a' b' c' dia'b' dib'c' dia'c') in a'b'c'.
  destruct a'b'c' as [ ta'b' tb'c' ].
  eapply (EqConvexAs_EqOs_EqAs a c a' c'). apply iac.
  rewrite <- tab. rewrite <- ta'b'.
  apply (EqAs_EqTs a b a' b' roab roa'b')...
Qed.

Lemma AddAngRs :
  forall (a b c a' b' c' : Ray)(roab : da a = da b)(robc : da b = da c)
         (roa'b' : da a' = da b')(rob'c' : da b' = da c'),
  [| a, b | roab |] = [| a', b' | roa'b' |]
    -> [| b, c | robc |] = [| b', c' | rob'c' |]
    -> [| a, c | eq_trans roab robc |] = [| a', c' | eq_trans roa'b' rob'c' |].
Proof with eauto.
  intros * ab bc.
  destruct (classic (a == b)) as [ aeqb | naeqb ].
  { apply (EqNullAng a b roab) in aeqb. rewrite aeqb in ab.
    symmetry in ab. apply EqNullAng in ab. apply EqNullAng in aeqb.
    erewrite (EqAngRs_inv a c b c); try reflexivity...
    erewrite (EqAngRs_inv a' c' b' c'); try reflexivity...
  }
  { destruct (classic (a == (!b))) as [ aopb | naopb ].
    { apply OpRs_OpRs in aopb.
      apply (EqStraightAng a b roab) in aopb.
      rewrite aopb in ab. symmetry in ab.
      apply EqStraightAng in ab. apply EqStraightAng in aopb.
      apply OpRs_OpRs in ab. apply OpRs_sym in ab.
      apply OpRs_OpRs in aopb. apply OpRs_sym in aopb.
      pir (eq_trans roab robc)
        => (eq_sym (eq_sym (eq_trans roab robc))).
      pir (eq_trans roa'b' rob'c')
        => (eq_sym (eq_sym (eq_trans roa'b' rob'c'))).
      eapply (EqAs_EqExpAs c a c' a')...
      eapply (OpRs_EqSupAngRs b c a b' c' a')...
    }
    assert (diab : ![ a # b ]). { apply nColRs_nColPs. split... }
    destruct (classic (a == c)) as [ aeqc | naeqc ].
    { apply (EqNullAng a c (eq_trans roab robc)) in aeqc.
      rewrite aeqc. symmetry.
      apply EqNullAng. apply EqNullAng in aeqc.
      apply (EqAs_EqExpAs a b a' b' roab roa'b') in ab...
      apply -> (EqAs_EqRs b' a' c' (eq_sym roa'b') rob'c')...
      rewrite <- ab. rewrite <- bc.
      apply (EqAs_EqRs b a c (eq_sym roab) robc)...
    }
    { destruct (classic (a == (!c))) as [ aopc | naopc ].
      { apply OpRs_OpRs in aopc.
        apply (EqStraightAng a c (eq_trans roab robc)) in aopc.
        rewrite aopc. symmetry. apply EqStraightAng.
        apply EqStraightAng in aopc. apply OpRs_OpRs.
        apply (OpRs_EqAngRs_OpRs a b c a' b' c' roab robc roa'b' rob'c')...
        apply OpRs_OpRs...
      }
      { assert (diac : ![ a # c ]).
        { apply nColRs_nColPs. split... apply (eq_trans roab robc). }
        destruct (classic (b == c)) as [ beqc | nbeqc ].
        { apply (EqNullAng b c robc) in beqc.
          rewrite beqc in bc. symmetry in bc.
          apply EqNullAng in bc. apply EqNullAng in beqc.
          rewrite (EqAngRs_inv a c a b (eq_trans roab robc) roab);
          try reflexivity...
          { erewrite (EqAngRs_inv a' c' a' b'); try reflexivity...
            symmetry...
          }
          symmetry...
        }
        { destruct (classic (b == (!c))) as [ bopc | nbopc ].
          { apply OpRs_OpRs in bopc.
            apply (EqStraightAng b c robc) in bopc.
            rewrite bopc in bc. symmetry in bc.
            apply EqStraightAng in bc.
            apply EqStraightAng in bopc.
            apply (EqAs_EqExpAs a b a' b' roab roa'b') in ab...
            apply OpRs_OpRs in bopc.
            eapply (OpRs_EqSupAngRs b a c b' a' c')...
            apply OpRs_OpRs...
          }
          { assert (dibc : ![ b # c ]). { apply nColRs_nColPs. split... }
            destruct (DrawOpRay c) as [ d copd ].
            destruct (DrawOpRay c') as [ d' c'opd' ].
            assert (rocd : da c = da d). { destruct copd... }
            assert (roc'd' : da c' = da d'). { destruct c'opd'... }
            edestruct (DecideOneRayBetweenTwoOthers a b c )
              as [[[ abc | acb ]| abd ]| adb ]...
            { assert (a'b'c' : ![a' # b' # c']).
              { eapply (BetRs_AddEqAs_BetRs a b c a' b' c' )... }
              apply (BetRs_AddAngRs a b c a' b' c')...
            }
            { apply BetRs_sym in acb.
              eassert (ba : [| b, a | _ |] = [| b', a' | _ |]).
              { apply EqAs_EqExpAs... }
              assert (b'c'a' : ![b' # c' # a']).
              { eapply (BetRs_SubtEqAs_BetRs b c a b' c' a')... }
              pir (eq_trans roab robc)
                => (eq_sym (eq_sym (eq_trans roab robc))).
              pir (eq_trans roa'b' rob'c')
                => (eq_sym (eq_sym (eq_trans roa'b' rob'c'))).
              eapply (EqAs_EqExpAs c a c' a')...
              eapply (BetRs_SubtAngRs b c a b' c' a')...
            }
            { pir (eq_trans robc (eq_sym (eq_trans roab robc)))
                => (eq_sym roab).
              pir (eq_trans rob'c' (eq_sym (eq_trans roa'b' rob'c')))
                => (eq_sym roa'b').
              assert (robd : da b = da d).
              { rewrite <- robc in rocd... }
              assert (rob'd' : da b' = da d').
              { rewrite <- rob'c' in roc'd'... }
              assert (bd : [| b, d | robd |] = [| b', d' | rob'd' |]).
              { apply OpRs_OpRs in copd. apply OpRs_OpRs in c'opd'.
                eapply (OpRs_EqSupAngRs c b d c' b' d')...
                apply (EqAs_EqExpAs b c b' c' robc rob'c')...
              }
              assert (a'b'd' : ![a' # b' # d']).
              { eapply (BetRs_AddEqAs_BetRs a b d a' b' d' )...
                apply (BetRs_inv a b (!c) a b d); try reflexivity...
                symmetry; apply (OpRs_sym c d)... apply OpRs_OpRs...
              }
              eassert (ad : [| a, d | _ |] = [| a', d' | _ |]).
              { apply (BetRs_AddAngRs a b d a' b' d')...
                eapply (BetRs_AddEqAs_BetRs a' b' d' a b d)...
              }
              apply (EqAs_EqExpAs a d a' d') in ad.
              eapply (OpRs_EqSupAngRs d a c d' a' c')...
              apply OpRs_sym. apply OpRs_OpRs...
              apply OpRs_sym. apply OpRs_OpRs...
            }
            assert (robd : da b = da d).
            { rewrite <- robc in rocd... }
            assert (rob'd' : da b' = da d').
            { rewrite <- rob'c' in roc'd'... }
            assert (bd : [| b, d | robd |] = [| b', d' | rob'd' |]).
            { eapply (OpRs_EqSupAngRs c b d c' b' d')...
              apply OpRs_OpRs... apply OpRs_OpRs...
              apply (EqAs_EqExpAs b c b' c' robc rob'c')...
            }
            eassert (ba : [| b, a | _ |] = [| b', a' | _ |]).
            { apply (EqAs_EqExpAs a b a' b' roab roa'b')... }
            apply BetRs_sym in adb.
            assert (bda : ![b # d # a]).
            { apply (BetRs_inv b (!c) a b d a); try reflexivity... symmetry.
              apply (OpRs_sym c d)... apply OpRs_OpRs...
            }
            assert (b'd'a' : ![b' # d' # a']).
            { eapply (BetRs_SubtEqAs_BetRs b d a b' d' a')... }
            eassert (da : [| d, a | _ |] = [| d', a' | _ |]).
            { eapply (BetRs_SubtAngRs b d a b' d' a')... }
            pir (eq_trans robd (eq_sym (eq_trans roab robd)))
              => (eq_sym roab).
            pir (eq_trans rob'd' (eq_sym (eq_trans roa'b' rob'd')))
              => (eq_sym roa'b').
            eapply (OpRs_EqSupAngRs d a c d' a' c')...
            apply OpRs_sym. apply OpRs_OpRs...
            apply OpRs_sym. apply OpRs_OpRs...
          }
        }
      }
    }
  }
  Unshelve.
  rewrite <- robd... rewrite <- rob'd'...
Qed.

Lemma SubtAngRs :
  forall (a b c a' b' c' : Ray)(roab : da a = da b)(roac : da a = da c)
         (roa'b' : da a' = da b')(roa'c' : da a' = da c'),
  [| a, b | roab |] = [| a', b' | roa'b' |]
  -> [| a, c | roac |] = [| a', c' | roa'c' |]
  -> [| b, c | eq_trans (eq_sym roab) roac |]
   = [| b', c' | eq_trans (eq_sym roa'b') roa'c' |].
Proof with eauto.
  intros * ab ac.
  apply EqAs_EqExpAs in ab.
  apply AddAngRs...
Qed.

Lemma OrdRs_EqAs_EqAs_1 :
  forall (a b c d : Ray)(roab : da a = da b)
         (robc : da b = da c)(rocd : da c = da d),
  ![ a # b # c # d ]
    -> [| a, b | roab |] = [| c, d | rocd |]
    -> [| a, c | eq_trans roab robc |] = [| b, d | eq_trans robc rocd |].
Proof with eauto.
  intros a b c d roab robc rocd [ abc [ _ [ _ bcd ]]] ab.
  destruct (BetRs_nColRs a b c abc) as [ diab [ dibc diac ]].
  destruct (BetRs_nColRs b c d bcd) as [ _ [ dicd dibd ]].
  assert (iab : [|a # b | diab|] = [|c # d | dicd|]).
  { apply (EqAs_EqConvexAs a b c d roab rocd diab dicd ab). }
  assert (Tab : %[a # b | diab] = %[c # d | dicd]).
  { apply (EqAs_EqTs a b c d roab rocd diab dicd ab). }
  rewrite (ConvexAngRs_sym c d dicd (nColRs_sym c d dicd)) in iab.
  eapply (EqConvexAs_EqOs_EqAs a c b d).
  { eassert (ibc : [|b # c | _ |] = [|c # b | _ |]).
    { apply (ConvexAngRs_sym b c dibc). }
    rewrite (ConvexAngRs_sym b d dibd (nColRs_sym b d dibd)).
    apply BetRs_sym in bcd.
    eapply (BetRs_AddConvexAngRs a b c d c b)...
  }
  destruct (proj1 (BetRs_EqOs a b c diab dibc diac) abc)
    as [ abac bcac ].
  destruct (proj1 (BetRs_EqOs b c d dibc dicd dibd) bcd)
    as [ bcbd cdbd ].
  rewrite <- cdbd. rewrite <- Tab. rewrite <- abac...
  Unshelve. apply nColRs_sym...
Qed.

Lemma OrdRs_EqAs_EqAs_2 :
  forall (a b c d : Ray)(roab : da a = da b)
         (robc : da b = da c)(rocd : da c = da d),
  ![ a # c # b # d ]
    -> [| a, b | roab |] = [| c, d | rocd |]
    -> [| a, c | eq_trans roab robc |] = [| b, d | eq_trans robc rocd |].
Proof with eauto.
  intros * [ acb [ _ [ _ cbd ]]] ab.
  destruct (BetRs_nColRs a c b acb) as [ diac [ dicb diab ]].
  destruct (BetRs_nColRs c b d cbd) as [ _ [ dibd dicd ]].
  assert (iba : [|b # a | nColRs_sym a b diab|] = [|c # d | dicd|]).
  { rewrite <- (ConvexAngRs_sym a b diab).
    apply (EqAs_EqConvexAs a b c d roab rocd diab dicd ab).
  }
  assert (Tab : %[a # b | diab] = %[c # d | dicd]).
  { apply (EqAs_EqTs a b c d roab rocd diab dicd ab). }
  eapply (EqConvexAs_EqOs_EqAs a c b d)...
  { assert (ibc : [|c # b | dicb|] = [|b # c | nColRs_sym c b dicb|]).
    { apply (ConvexAngRs_sym c b dicb). }
    apply BetRs_sym in acb.
    rewrite (ConvexAngRs_sym a c diac (nColRs_sym a c diac)).
    eapply (BetRs_SubtConvexAngRs b c a c b d)...
  }
  destruct (proj1 (BetRs_EqOs a c b diac dicb diab) acb)
    as [ acab cbab ].
  destruct (proj1 (BetRs_EqOs c b d dicb dibd dicd) cbd)
    as [ cbcd bdcd ].
  rewrite bdcd. rewrite <- cbcd. rewrite acab...
Qed.

Lemma OrdRs_EqAs_EqAs_3 :
  forall (a b c d : Ray)(roab : da a = da b)
         (robc : da b = da c)(rocd : da c = da d),
  ![ a # !b # !c # d ]
    -> [| a, b | roab |] = [| c, d | rocd |]
    -> [| a, c | eq_trans roab robc |] = [| b, d | eq_trans robc rocd |].
Proof with eauto.
  intros * abcd ab.
  assert (roab' : da a = da (!b)).
  { rewrite roab. apply OpRays_0. }
  assert (roc'd : da (!c) = da d).
  { rewrite <- rocd. symmetry. apply OpRays_0. }
  assert (abAcd : [| a, !b | roab' |] = [| !c, d | roc'd |]).
  { apply <- EqSupAs. symmetry. erewrite EqOppVertAs...
    eassert (ab' : [| a, b | _ |] = [| a, !(!b) | _ |]).
    { apply (EqAs_EqRs a b (!(!b))). apply (OpOpRs b). }
    rewrite <- ab'. rewrite ab. symmetry.
    apply (EqAngRs_EqRs_cw d c (!(!c))). apply (OpOpRs c).
  }
  assert (rob'c' : da (!b) = da (!c)).
  { rewrite <- roab'. rewrite roc'd. rewrite roab. rewrite robc... }
  eassert (acAbd : [| a, !c | _ |] = [| !b, d | _ |]).
  { apply (OrdRs_EqAs_EqAs_1 a (!b)(!c) d)... }
  apply <- EqSupAs.
  pir (eq_trans (eq_trans roab robc)(OpRays_0 c))
    => (eq_trans roab' rob'c'). rewrite acAbd. symmetry.
  pir (eq_trans (eq_trans robc rocd)(OpRays_0 d))
    => (eq_trans (eq_trans robc rocd)(OpRays_0 d)).
  pir (eq_trans rob'c' roc'd)
    => (eq_trans (eq_sym (OpRays_0 b))(eq_trans robc rocd)).
  apply (EqOppVertAs b d).
  Unshelve. rewrite <- roc'd. symmetry. apply OpRays_0.
Qed.

Lemma OrdRs_EqAs_EqAs_4 :
  forall (a b c d : Ray)(roab : da a = da b)
         (robc : da b = da c)(rocd : da c = da d),
  ![ !a # c # b # !d ]
    -> [| a, b | roab |] = [| c, d | rocd |]
    -> [| a, c | eq_trans roab robc |] = [| b, d | eq_trans robc rocd |].
Proof with eauto.
  intros * acbd ab.
  assert (roa'b : da (!a) = da b).
  { rewrite <- roab. symmetry. apply OpRays_0. }
  assert (rocd' : da c = da (!d)). { rewrite rocd. apply OpRays_0. }
  assert (acAbd : [| !a, c | eq_trans roa'b robc |]
    = [| b, !d | eq_trans robc rocd' |]).
  { apply (OrdRs_EqAs_EqAs_2 (!a) b c (!d))...
    pir roa'b => (eq_sym (eq_sym roa'b)).
    pir rocd' => (eq_sym (eq_sym rocd')).
    apply (EqAs_EqExpAs b (!a)(!d) c).
    pir (eq_sym rocd')
      => (eq_trans (eq_sym (OpRays_0 d))(eq_sym rocd)).
    erewrite <- (EqOppVertAs d c).
    apply <- (EqSupAs b (!a) d (!c)).
    apply (EqAs_EqExpAs a b c d roab rocd) in ab.
    eassert (ba : [| b, a | _ |] = [| b, !(!a) | _ |]).
    { apply (EqAs_EqRs b a (!(!a))). apply (OpOpRs a). }
    assert (rodc' : da d = da (!(!c))).
    { apply (eq_trans (eq_trans (eq_sym rocd)
        (OpRays_0 c))(OpRays_0 (!c))).
    }
    eassert (dc' : [| d, c | _ |] = [| d, !(!c) | _ |]).
    { apply (EqAs_EqRs d c (!(!c))). apply (OpOpRs c). }
    rewrite <- ba.
    pir (eq_trans (eq_trans (eq_sym rocd)(OpRays_0 c))(OpRays_0 (!c)))
      => rodc'. rewrite <- dc'...
  }
  assert ( roa'c : da (!a) = da c).
  { apply (eq_trans (eq_sym (OpRays_0 a))(eq_trans roab robc)). }
  assert ( roac' : da a = da (!c)).
  { apply (eq_trans (eq_trans roab robc)(OpRays_0 c)). }
  assert (acAac : [| !a, c | roa'c |] = [| a, !c | roac' |]).
  { symmetry.
    pir roa'c => (eq_trans (eq_sym (OpRays_0 a))(eq_trans roab robc)).
    pir roac' => (eq_trans (eq_trans roab robc)(OpRays_0 c)).
    apply (EqOppVertAs a c).
  }
  pir (eq_trans (eq_sym (OpRays_0 a))(eq_trans roab robc))
    => (eq_trans roa'b robc).
  apply <- (EqSupAs a c b d).
  pir (eq_trans robc rocd')
    => (eq_trans (eq_trans robc rocd)(OpRays_0 d)).
  rewrite <- acAbd.
  pir (eq_trans roa'b robc) => roa'c.
  pir (eq_trans (eq_trans roab robc)(OpRays_0 c)) => roac'.
Qed.

Lemma OrdRs_EqAs_EqAs_5 :
  forall (a b c d : Ray)(roab : da a = da b)
         (robc : da b = da c)(rocd : da c = da d),
  ![ b # !d # !a # c ]
    -> [| a, b | roab |] = [| c, d | rocd |]
    -> [| a, c | eq_trans roab robc |] = [| b, d | eq_trans robc rocd |].
Proof with eauto.
  intros * bdac ab.
  assert (roba' : da b = da (!a)). { rewrite <- roab. apply OpRays_0. }
  assert (roa'd' : da (!a) = da (!d)).
  { rewrite <- (OpRays_0 a).
    rewrite <- (OpRays_0 d).
    rewrite roab. rewrite robc...
  }
  assert (rod'c : da (!d) = da c). { rewrite <- roa'd'. rewrite <- roba'... }
  assert (acAbd : [| b, !d | eq_trans roba' roa'd' |]
    = [| !a, c | eq_trans roa'd' rod'c |]).
  { apply (OrdRs_EqAs_EqAs_2 b (!a)(!d) c)...
    pir roba' => (eq_sym (eq_sym roba')).
    pir rod'c => (eq_trans (eq_sym (OpRays_0 d))(eq_sym rocd)).
    erewrite <- (EqOppVertAs d c).
    apply <- (EqSupAs b (!a) d (!c)).
    eassert (ba : [| b, a | _ |] = [| b, !(!a) | _ |]).
    { apply (EqAs_EqRs b a (!(!a))). apply (OpOpRs a). }
    assert ( rodc'' : da d = da (!(!c))).
    { apply (eq_trans (eq_trans
        (eq_sym rocd)(OpRays_0 c))(OpRays_0 (!c))).
    }
    assert (dc' : [| d, c | eq_sym rocd |] = [| d, !(!c) | rodc'' |]).
    { apply (EqAs_EqRs d c (!(!c))). apply (OpOpRs c). }
    rewrite <- ba.
    pir ( eq_trans (eq_trans (eq_sym rocd)(OpRays_0 c))(OpRays_0 (!c)))
      => rodc''. rewrite <- dc'...
    apply (EqAs_EqExpAs a b c d)...
  }
  assert ( roa'c : da (!a) = da c).
  { apply (eq_trans (eq_sym (OpRays_0 a))(eq_trans roab robc)). }
  assert ( roac' : da a = da (!c)).
  { apply (eq_trans (eq_trans roab robc)(OpRays_0 c)). }
  assert (acAac : [| !a, c | roa'c |] = [| a, !c | roac' |]).
  { symmetry.
    pir roa'c => (eq_trans (eq_sym (OpRays_0 a))(eq_trans roab robc)).
    pir roac' => (eq_trans (eq_trans roab robc)(OpRays_0 c)).
    apply (EqOppVertAs a c).
  }
  pir (eq_trans (eq_sym (OpRays_0 a))(eq_trans roab robc))
    => (eq_trans roa'd' rod'c).
  apply <- (EqSupAs a c b d).
  pir (eq_trans roba' roa'd')
    => (eq_trans (eq_trans robc rocd)(OpRays_0 d)).
  pir (eq_trans (eq_trans roab robc)(OpRays_0 c)) => roac'.
  pir (eq_trans roa'd' rod'c) => roa'c.
  rewrite acAac in acAbd...
Qed.

Lemma OrdRs_EqAs_EqAs_6 :
  forall (a b c d : Ray)(roab : da a = da b)
         (robc : da b = da c)(rocd : da c = da d),
  ![ b # !a # !d # c ]
    -> [| a, b | roab |] = [| c, d | rocd |]
    -> [| a, c | eq_trans roab robc |] = [| b, d | eq_trans robc rocd |].
Proof with eauto.
  intros * badc ab.
  assert (roba' : da b = da (!a)).
  { rewrite <- roab. apply OpRays_0. }
  assert (roa'd' : da (!a) = da (!d)).
  { rewrite <- (OpRays_0 a). rewrite <- (OpRays_0 d).
    rewrite roab. rewrite robc...
  }
  assert (rod'c : da (!d) = da c).
  { rewrite <- roa'd'. rewrite <- roba'... }
  assert (acAbd : [| b, !a |roba' |] = [| !d, c | rod'c |]).
  { apply <- EqSupAs. symmetry. erewrite EqOppVertAs.
    apply EqAs_EqExpAs in ab.
    eassert (ba : [| b, a | _ |] = [| b, (!(!a)) | _ |]).
    { apply (EqAs_EqRs b a (!(!a))). apply (OpOpRs a). }
    rewrite <- ba. rewrite ab. symmetry.
    apply (EqAngRs_EqRs_cw c d (!(!d))). apply (OpOpRs d).
  }
  eassert (bdAac : [| b, !d | _ |] = [| !a, c | _ |]).
  { apply (OrdRs_EqAs_EqAs_1 b (!a)(!d) c)... }
  symmetry.
  apply <- EqSupAs.
  pir (eq_trans (eq_trans robc rocd)(OpRays_0 d))
    => (eq_trans roba' roa'd'). rewrite bdAac. symmetry.
  pir (eq_trans roa'd' rod'c)
   => (eq_trans (eq_sym (OpRays_0 a))(eq_trans roab robc)).
  apply (EqOppVertAs a c).
  Unshelve. rewrite <- rod'c. symmetry. apply OpRays_0.
Qed.

Lemma OrdRs_EqAs_EqAs_7 :
  forall (a b c d : Ray)(roab : da a = da b)
         (robc : da b = da c)(rocd : da c = da d),
  ![ b # a # d # c ]
    -> [| a, b | roab |] = [| c, d | rocd |]
    -> [| a, c | eq_trans roab robc |] = [| b, d | eq_trans robc rocd |].
Proof with eauto.
  intros a b c d roab robc rocd badc ab.
  assert (road : da a = da d).
  { rewrite roab; rewrite robc... }
  apply (EqAs_EqExpAs a b c d) in ab... symmetry.
  pir (eq_trans robc rocd) => (eq_trans (eq_sym roab) road).
  pir (eq_trans roab robc) => (eq_trans road (eq_sym rocd)).
  apply (OrdRs_EqAs_EqAs_1 b a d c)...
Qed.

Lemma OrdRs_EqAs_EqAs_8 :
  forall (a b c d : Ray)(roab : da a = da b)
         (robc : da b = da c)(rocd : da c = da d),
  ![ b # d # a # c ]
    -> [| a, b | roab |] = [| c, d | rocd |]
    -> [| a, c | eq_trans roab robc |] = [| b, d | eq_trans robc rocd |].
Proof with eauto.
  intros * bdac ab.
  apply (EqAs_EqExpAs a b c d) in ab; auto. symmetry.
  assert (roba : da b = da a). { rewrite <- roab... }
  assert (road : da a = da d). { rewrite roab; rewrite robc... }
  assert (rodc : da d = da c). { rewrite rocd... }
  pir (eq_trans robc rocd) => (eq_trans (eq_sym roab) road).
  pir (eq_trans roab robc) => (eq_trans road (eq_sym rocd)).
  apply (OrdRs_EqAs_EqAs_2 b a d c)...
Qed.

Lemma OrdRs_EqOs :
  forall (a b c d : Ray)
         (diab : ![ a # b ])(dibc : ![ b # c ])(dicd : ![ c # d ])
         (diac : ![ a # c ])(dibd : ![ b # d ])(diad : ![ a # d ]),
  ![ a # b # c # d ]
    <-> (%[ a # b | diab ] = %[ a # d | diad ])
     /\ (%[ b # c | dibc ] = %[ a # d | diad ])
     /\ (%[ c # d | dicd ] = %[ a # d | diad ])
     /\ (%[ a # c | diac ] = %[ a # d | diad ])
     /\ (%[ b # d | dibd ] = %[ a # d | diad ]).
Proof with eauto.
  intros *.
  split.
  { intros [ abc [ abd [ acd bcd ]]].
    apply (BetRs_EqOs a b c diab dibc diac) in abc.
    apply (BetRs_EqOs a b d diab dibd diad) in abd.
    apply (BetRs_EqOs a c d diac dicd diad) in acd.
    apply (BetRs_EqOs b c d dibc dicd dibd) in bcd.
    destruct abc as [ abc1 abc2 ].
    destruct abd as [ abd1 abd2 ].
    destruct acd as [ acd1 acd2 ].
    destruct bcd as [ bcd1 bcd2 ].
    destruct abc1, abc2, abd1, abd2, acd1, acd2, bcd1, bcd2...
  }
  { intros [ abad [ bcad [ cdad [ acad bdad ]]]].
    split.
    { apply (BetRs_EqOs a b c diab dibc diac).
      split.
      { rewrite abad... }
      { rewrite bcad... }
    }
    { split.
      { apply (BetRs_EqOs a b d diab dibd diad); split... }
      { split.
        { apply (BetRs_EqOs a c d diac dicd diad); split... }
        { apply (BetRs_EqOs b c d dibc dicd dibd); split.
          rewrite bcad... rewrite cdad...
        }
      }
    }
  }
Qed.

End ANGLE_TRANSFER.

(*****************************************************************************)
(* 18 *) Section ANGLE_ORDER.
Context `{ cc : Concentricals }.
Context  { an : Angles on }.
Context  { sp : Superpositions on }.
(*****************************************************************************)

Definition LtA (A B : Angle) : Prop
  := ((A = A0) /\ (B <> A0))
  \/ ((Convex A) /\ (B = A180 \/ (Reflex B)))
  \/ ((A = A180) /\ (Reflex B))
  \/ ((Convex A) /\ (Convex B) /\
     let (RsB, H) := (DrawSector B) in
     match RsB with
     | {| da := c; db := d; dp := rocd |} =>
       exists (e : Ray)(roce : da c = da e),
         (![ c # e # d ] /\ [| c, e | roce |] = A)
     end)
  \/ ((Reflex A) /\ (Reflex B) /\
     let (RsA, H) := (DrawSector A) in
     match RsA with
     | {| da := a; db := b; dp := roab |} =>
       exists (e : Ray)(roae : da a = da e),
         (![ a # e # b ] /\ [| a, e | roae |] = B)
     end).
Notation " A <<< B "
  := (LtA A B)
  (at level 70).

(** Theorem #68 *)
Theorem iAs_iAs_LtAs_BetRs :
  forall (a b c : Ray)(roab : da a = da b)(roac : da a = da c),
  Convex ([| a, b | roab |])
    -> Convex ([| a, c | roac |])
    -> ([| a, b | roab |] <<< [| a, c | roac |] <-> ![ a # b # c ]).
Proof with eauto.
  intros a b c roab roac iab iac.
  split.
  { intro abLTac.
    destruct abLTac
      as [[ AeqA0 nBeqA0 ]
       |[[ iA [BeqA180 | xB ]]
       |[[ AeqA180 xB ]
       |[[ iA [ iB H1 ]]
       |[ xA [ xB H2 ]]]]]].
    { apply ConvexAng_nAs in iab.
      destruct iab as [ nabeqA0 _ ].
      contradiction.
    }
    { apply ConvexAng_nAs in iac.
      destruct iac as [ _ [ naceqA180 _ ]].
      contradiction.
    }
    { apply ConvexAng_nAs in iac.
      destruct iac as [ _ [ _ nxB ]].
      contradiction.
    }
    { apply ConvexAng_nAs in iac.
      destruct iac as [ _ [ _ nxB ]].
      contradiction.
    }
    { destruct (DrawSector ([| a, c | roac |]))
        as [[ a' c' roa'c' ] H2 ]; simpl in *.
      destruct H1 as [ b' [ roa'b' [ Betab'c ab'eqab ]]].
      apply (BetRs_SubtEqAs_BetRs a' b' c' a b c roa'b' roa'c' roab roac)...
    }
    { destruct (DrawSector ([| a, c | roac |]))
        as [[ a' c' roa'c' ] H3 ]; simpl in *.
      apply ConvexAng_nAs in iab.
      destruct iab as [ _ [ _ nxE ]].
      contradiction.
    }
  }
  { intros BetRabc; unfold LtA.
    do 3 right; left.
    repeat split...
    destruct (DrawSector ([| a, c | roac |]))
      as [[ a' c' roa'c' ] H3 ]; simpl in *.
    destruct (BetRs_nColRs a b c BetRabc) as [ diab [ dibc diac ]].
    assert (dia'c' : ![ a' # c' ]).
    { apply (EqAngRs_nColRs_nColRs a c a' c' roac roa'c')... }
    destruct (DrawAngleCutRs a b c a' c' diab diac dia'c')
      as [ b' [ dia'b' [ BetRa'b'c' H ]]]...
    { apply (EqAs_EqConvexAs a c a' c' roac roa'c')... }
    assert (roa'b' : da a' = da b'). { destruct dia'b'... }
    exists b', roa'b'.
    split...
    symmetry.
    apply (EqConvexAs_EqOs_EqAs a b a' b' roab roa'b' diab dia'b')...
    apply -> (ConvexAngRs_Left a b roab diab) in iab.
    rewrite iab. symmetry.
    rewrite <- H3 in iac.
    apply -> (ConvexAngRs_Left a' c' roa'c' dia'c') in iac.
    destruct (BetRs_nColRs a' b' c' BetRa'b'c') as [ _ [ dib'c' _ ]].
    destruct (BetRs_EqOs a' b' c' dia'b' dib'c' dia'c') as [ H1 _ ].
    apply H1 in BetRa'b'c'.
    destruct BetRa'b'c' as [ a'b' b'c' ]. rewrite a'b'...
  }
Qed.
Lemma xA_xA_LtAs_BetRs :
  forall (a b c : Ray)(roab : da a = da b)(roac : da a = da c),
  Reflex ([| a, b | roab |])
    -> Reflex ([| a, c | roac |])
    -> ([| a, c | roac |] <<< [| a, b | roab |] <-> ![ a # b # c ]).
Proof with eauto.
  intros * iab iac.
  split.
  { intros abLTac.
    destruct abLTac
      as [[ AeqA0 nBeqA0 ]
       |[[ iA [BeqA180 | xB ]]
       |[[ AeqA180 xB ]
       |[[ iA [ iB H1 ]]
       |[ xA [ xB H2 ]]]]]].
    { apply ReflexAng_nAs in iac.
      destruct iac as [ nabeqA0 _ ].
      contradiction.
    }
    { apply ReflexAng_nAs in iab.
      destruct iab as [ _ [ naceqA180 _ ]].
      contradiction.
    }
    { apply ReflexAng_nAs in iac.
      destruct iac as [ _ [ _ nxB ]].
      contradiction.
    }
    { apply ReflexAng_nAs in iac.
      destruct iac as [ _ [ naceqA180 _ ]].
      contradiction.
    }
    { apply ReflexAng_nAs in iab.
      destruct iab as [ _ [ _ nxE ]].
      contradiction.
    }
    { destruct (DrawSector ([| a, c | roac |]))
        as [[ a' c' roa'c' ] H3 ]; simpl in *.
      destruct H2 as [ d' [ roa'd' [ Betabc' ac'eqac ]]].
      eapply (BetRs_SubtEqAs_BetRs a' d' c' a b c)...
    }
  }
  { intros BetRabc; unfold LtA.
    do 4 right; repeat split...
    destruct (DrawSector ([| a, c | roac |]))
      as [[ a' c' roa'c' ] H3 ]; simpl in *.
    destruct (DrawCongruentAngle_ccw a' ([| a, b | roab |]))
      as [ b' [ roa'b' H ]].
    exists b', roa'b'.
    split...
    apply (BetRs_SubtEqAs_BetRs a b c a' b' c' roab roac roa'b' roa'c')...
  }
Qed.

(** Theorem #69 *)
Lemma NonNegativeAngles :
  forall A : Angle,
  ~ (A <<< A0).
Proof with eauto.
  intros A AltA0.
  unfold LtA in *.
  destruct AltA0
   as [[ AeqA0 nA0eqA0 ]|[[ iA [ A0eqA180 | xA0 ]]|[[ AeqA180 xA0 ]
    |[[ iA [ iA0 H1 ]]|[ xA [ xA0 H2 ]]]]]];
  try apply (ReflexAng_nAs A0) in xA0; try destruct xA0 as [ nA0eqA0 _ ];
  try apply (ConvexAng_nAs A0) in iA0; try destruct iA0 as [ nA0eqA0 _ ];
  eauto; try apply nA0eqA180...
Qed.
Lemma PositiveAngles :
  forall A : Angle,
  A0 <<< A
    <-> A <> A0.
Proof with eauto.
  intros A.
  split.
  { intros AltA0 AeqA0.
    subst. eapply NonNegativeAngles...
  }
  { intros nAeqA0; unfold LtA in *.
    left. split...
  }
Qed.

Lemma AngleDichotomy :
  forall A : Angle,
  A = A0 \/ A0 <<< A.
Proof with eauto.
  intros A.
  destruct (classic (A = A0)) as [ AeqA0 | nAeqA0 ]...
  right. apply PositiveAngles...
Qed.

(** Theorem #70 *)
Lemma AngTrichotomy :
  forall A B : Angle,
  A <<< B \/ A = B \/ B <<< A.
Proof with eauto.
  intros A B.
  destruct (classic (A = B)) as [ AeqB | nAeqB ]; subst...
  destruct (AngleDichotomy B) as [ BeqA0 | BgtA0 ];
  destruct (AngleDichotomy A) as [ AeqA0 | AgtA0 ]; subst...
  destruct (classic (Convex A)) as [ iA | niA ];
  destruct (classic (Convex B)) as [ iB | niB ].
  { destruct (DrawSector A) as [[ a b roab ] H ].
    destruct H.
    destruct (DrawCongruentAngle_ccw a B) as [ c [ roac aceqB ]].
    assert (aSFbc : ![ a # b, c ]).
    { unfold Convex in *; subst.
      destruct iA as [[ nabeqA0 nabeqA180 ] abeqL ].
      destruct iB as [[ ncdeqA0 ncdeqA180 ] cdeqL ].
      assert (diab : ![ a # b ]). { apply (nColRs_nColAs a b roab); split... }
      assert (diac : ![ a # c ]). { apply (nColRs_nColAs a c roac); split... }
      apply <- (SameSideRs_EqOs a b c diab diac)...
      rewrite <- (OsRs_OsAs a b roab diab (conj nabeqA0 nabeqA180))
        in abeqL.
      rewrite <- (OsRs_OsAs a c roac diac (conj ncdeqA0 ncdeqA180))
        in cdeqL.
      rewrite abeqL...
    }
    destruct (classic (b == c)) as [ beqc | nbeqc ].
    { contradict nAeqB. rewrite <- aceqB. apply EqAs_EqRs... }
    { apply DecideRaysOrderOnSameSide in aSFbc...
      destruct aSFbc as [ BetRabc | BetRacb ].
      { left.
        unfold LtA; do 3 right; left; repeat split; subst...
        destruct (DrawSector ([| a, c | roac |]))
          as [[ a' c' roa'c' ] H ]; simpl in *.
        destruct (BetRs_nColRs a b c BetRabc)
          as [ diab [ dibc diac ]].
        assert (dia'c' : ![ a' # c' ]).
        { apply (EqAngRs_nColRs_nColRs a c a' c' roac roa'c')... }
        destruct (DrawAngleCutRs a b c a' c' diab diac dia'c')
          as [ b' [ dia'b' [ BetRa'b'c' H1 ]]]...
        { apply (EqAs_EqConvexAs a c a' c' roac roa'c')... }
        assert (roa'b' : da a' = da b'). { destruct dia'b'... }
        exists b', roa'b'.
        split... symmetry.
        apply (EqConvexAs_EqOs_EqAs a b a' b' roab roa'b' diab dia'b')...
        apply -> (ConvexAngRs_Left a b roab diab) in iA.
        rewrite iA. symmetry. rewrite <- H in iB.
        apply -> (ConvexAngRs_Left a' c' roa'c' dia'c') in iB.
        destruct (BetRs_nColRs a' b' c' BetRa'b'c') as [ _ [ dib'c' _ ]].
        destruct (BetRs_EqOs a' b' c' dia'b' dib'c' dia'c') as [ H2 _ ].
        apply H2 in BetRa'b'c'.
        destruct BetRa'b'c' as [ a'b' b'c' ]. rewrite a'b'...
      }
      { do 5 right; left; repeat split...
        destruct (DrawSector ([| a, b | roab |]))
          as [[ a' b' roa'b' ] H3 ]; simpl in *.
        destruct (DrawCongruentAngle_ccw a' ([| a, c | roac |]))
          as [ c' [ roa'c' H ]].
        exists c', roa'c'.
        split; subst...
        eapply (BetRs_SubtEqAs_BetRs a c b a' c' b' )...
      }
    }
  }
  { left; right; left.
    split...
    destruct (classic (B = A180)) as [ BeqA180 | nBeqA180 ]...
    right.
    apply (ReflexAng_nAs B); split...
    apply PositiveAngles...
  }
  { do 3 right; left.
    split...
    destruct (classic (A = A180)) as [ AeqA180 | nAeqA180 ]...
    right. apply (ReflexAng_nAs A). split...
    apply PositiveAngles...
  }
  { destruct (classic (A = A180)) as [ AeqA180 | nAeqA180 ];
    destruct (classic (B = A180)) as [ BeqA180 | nBeqA180 ]; subst...
    { left; do 2 right; left.
      split... apply (ReflexAng_nAs B). split...
      apply PositiveAngles...
    }
    { do 4 right; left. split...
      apply (ReflexAng_nAs A). split; try apply PositiveAngles...
    }
    assert (xA : Reflex A).
    { apply (ReflexAng_nAs A). repeat split... apply PositiveAngles... }
    assert (xB : Reflex B).
    { apply (ReflexAng_nAs B). repeat split... apply PositiveAngles... }
    destruct (DrawSector A) as [[ a b roab ] H ];
    destruct (DrawCongruentAngle_ccw a B) as [ c [ roac aceqB ]]; subst.
    assert (aSFbc : ![ a # b, c ]).
    { unfold Reflex in *.
      destruct xA as [[ nabeqA0 nabeqA180 ] abeqL ].
      destruct xB as [[ ncdeqA0 ncdeqA180 ] cdeqL ].
      assert (diab : ![ a # b ]). { apply (nColRs_nColAs a b roab); split... }
      assert (diac : ![ a # c ]). { apply (nColRs_nColAs a c roac); split... }
      apply <- (SameSideRs_EqOs a b c diab diac)...
      rewrite <- (OsRs_OsAs a b roab diab (conj nabeqA0 nabeqA180))
        in abeqL.
      rewrite <- (OsRs_OsAs a c roac diac (conj ncdeqA0 ncdeqA180))
        in cdeqL.
      rewrite abeqL...
    }
    destruct (classic (b == c)) as [ beqc | nbeqc ].
    { contradict nAeqB. apply EqAs_EqRs... }
    { apply DecideRaysOrderOnSameSide in aSFbc...
      destruct aSFbc as [ BetRabc | BetRacb ].
      { do 6 right; repeat split...
        destruct (DrawSector ([| a, c | roac |]))
          as [[ a' c' roa'c' ] H3 ]; simpl in *.
        destruct (DrawCongruentAngle_ccw a' ([| a, b | roab |]))
          as [ b' [ roa'b' H ]].
        exists b', roa'b'.
        split...
        eapply (BetRs_SubtEqAs_BetRs a b c a' b' c')...
      }
      { left; do 4 right; repeat split...
        destruct (DrawSector ([| a, b | roab |]))
          as [[ a' b' roa'b' ] H3 ]; simpl in *.
        destruct (DrawCongruentAngle_ccw a' ([| a, c | roac |]))
          as [ c' [ roa'c' H ]].
        exists c', roa'c'.
        split...
        eapply (BetRs_SubtEqAs_BetRs a c b a' c' b')...
      }
    }
  }
Qed.

(** Theorem #71 *)
Theorem LtA_irrefl :
  forall A : Angle,
  ~ (A <<< A).
Proof with eauto.
  intros A AltA.
  destruct AltA
    as [[ H1 nA0eqA0 ]|[[ iA [ AeqA180 | xA ]]
       |[[ AeqA180 xA ]|[[ iA [ H2 H1 ]]| AltB ]]]]; subst...
  { apply (ConvexAng_nAs A180) in iA.
    destruct iA as [ _ [ nAeqA180 nxA ]]...
  }
  { apply (ConvexAng_nAs A) in iA.
    destruct iA as [ _ [ nAeqA180 nxA ]]...
  }
  { apply (ReflexAng_nAs A180) in xA.
    destruct xA as [ nAeqA0 [ nAeqA180 niA ]]...
  }
  { destruct (DrawSector A) as [[ a b roab ] H ]; subst...
    destruct H1 as [ e [ roce [ aeb aeab ]]].
    assert (eeqb : e == b). { apply -> (EqAs_EqRs a e b roce roab)... }
    destruct (BetRs_nColRs a e b aeb) as [ _ [ eb _ ]].
    apply nColRs_nColPs in eb. destruct eb as [ _ [ neeqb _ ]].
    contradiction.
  }
  { destruct (DrawSector A) as [[ a b roab ] H ]; subst.
    destruct AltB as [ _ [ xA [ e [ roae [ aeb aeab ]]]]].
    assert (eeqb : e == b). { apply -> (EqAs_EqRs a e b roae roab)... }
    destruct (BetRs_nColRs a e b aeb) as [ _ [ eb _ ]].
    apply nColRs_nColPs in eb. destruct eb as [ _ [ neeqb _ ]].
    contradiction.
  }
Qed.
Theorem LtA_asymm :
  forall A B : Angle,
  (A <<< B)
    -> ~ (B <<< A).
Proof with tauto.
  intros A B AltB AgtB.
  destruct AltB
    as [[ AeqA0 nBeqA0 ]|[[ iA [BeqA180 | xB ]]
     |[[ AeqA180 xB ]|[[ iA [ iB H1 ]]|[ xA [ xB H2 ]]]]]];
  destruct AgtB
    as [[ BeqA0 nAeqA0 ]|[[ iB' [AeqA180' | xA' ]]
     |[[ BeqA180' xA' ]|[[ iB' [ iA' H3 ]]|[ xB' [ xA' H4 ]]]]]];
  subst.
  { tauto. }
  { apply nA0eqA180... }
  { apply (ReflexAng_nAs A0) in xA'... }
  { apply (ReflexAng_nAs A0) in xA'... }
  { apply (ConvexAng_nAs A0) in iA'... }
  { apply (ReflexAng_nAs A0) in xA'... }
  { symmetry in BeqA0. apply nA0eqA180 in BeqA0... }
  { apply (ConvexAng_nAs A180) in iA... }
  { apply (ConvexAng_nAs A180) in iB'... }
  { apply (ConvexAng_nAs A) in iA... }
  { apply (ConvexAng_nAs A180) in iB'... }
  { apply (ReflexAng_nAs A180) in xB'... }
  { apply (ReflexAng_nAs A0) in xB... }
  { apply (ConvexAng_nAs A180) in iA... }
  { apply (ConvexAng_nAs A) in iA... }
  { apply (ConvexAng_nAs A) in iA... }
  { apply (ConvexAng_nAs B) in iB'... }
  { apply (ConvexAng_nAs A) in iA... }
  { apply (ReflexAng_nAs A0) in xB... }
  { apply (ConvexAng_nAs B) in iB'... }
  { apply (ConvexAng_nAs B) in iB'... }
  { apply (ReflexAng_nAs A180) in xA'... }
  { apply (ConvexAng_nAs A180) in iA'... }
  { apply (ReflexAng_nAs A180) in xA'... }
  { apply (ConvexAng_nAs A0) in iB... }
  { apply (ConvexAng_nAs A180) in iA... }
  { apply (ConvexAng_nAs A) in iA... }
  { apply (ConvexAng_nAs A) in iA... }
  { destruct (DrawSector A) as [[ a b roab ] H ]; simpl in *; subst.
    destruct H3 as [ e [ roae [ BetRaeb aeeqB ]]].
    destruct (DrawSector B) as [[ c d rocd ] H ]; simpl in *; subst.
    destruct H1 as [ f [ rocf [ BetRcfd cfeqA ]]].
    destruct (BetRs_nColRs a e b BetRaeb) as [ diae [ dieb diab ]].
    destruct (BetRs_nColRs c f d BetRcfd) as [ dicf [ difd dicd ]].
    destruct (DrawAngleCutRs a e b c f diae diab dicf)
      as [ d' [ dicd' [ Betcd'f aeeqcd' ]]]; eauto.
    apply (EqAs_EqConvexAs a b c f roab rocf); eauto.
    destruct (BetRs_a_trans c d' f d) as [ _ [ BetRcd'd _ ]]; eauto.
    assert (did'd : ![ d' # d ]).
    { apply (BetRs_nColRs c d' d BetRcd'd). }
    apply nColRs_nColPs in did'd.
    destruct did'd as [ rod'd [ ndeqd' _ ]].
    assert (d'eqd : d' == d).
    { apply (SameSideRs_EqConvexAs_EqRs c d' d dicd' dicd).
      apply (BetRs_SameSideRs c d' d)...
      apply (EqAs_EqConvexAs a e c d roae rocd diae dicd) in aeeqB.
      rewrite <- aeeqB; eauto.
    }
    contradiction.
  }
  { apply (ConvexAng_nAs A) in iA... }
  { apply (ReflexAng_nAs A0) in xB... }
  { apply (ReflexAng_nAs B) in xB... }
  { apply (ReflexAng_nAs B) in xB... }
  { apply (ReflexAng_nAs A180) in xB... }
  { apply (ReflexAng_nAs B) in xB... }
  { destruct (DrawSector B)
      as [[ a b roab ] H ]; simpl in *; subst.
    destruct H4 as [ e [ roae [ BetRaeb aeeqA ]]].
    destruct (DrawSector A) as [[ c d rocd ] H ]; simpl in *; subst.
    destruct H2 as [ f [ rocf [ BetRcfd cfeqA ]]].
    destruct (BetRs_nColRs a e b BetRaeb) as [ diae [ dieb diab ]].
    destruct (BetRs_nColRs c f d BetRcfd) as [ dicf [ difd dicd ]].
    destruct (DrawAngleCutRs a e b c f diae diab dicf)
      as [ f' [ dicf' [ BetRcf'f abeqcf' ]]]; eauto.
    apply (EqAs_EqConvexAs a b c f roab rocf); eauto.
    destruct (BetRs_a_trans c f' f d) as [ _ [ BetRcf'd _ ]]; eauto.
    assert (dif'd : ![ f' # d ]). { apply (BetRs_nColRs c f' d BetRcf'd). }
    apply nColRs_nColPs in dif'd.
    destruct dif'd as [ rof'd [ nfeqd' _ ]].
    assert (f'eqd : f' == d).
    { apply (SameSideRs_EqConvexAs_EqRs c f' d dicf' dicd).
      apply (BetRs_SameSideRs c f' d)...
      apply (EqAs_EqConvexAs a e c d roae rocd diae dicd) in aeeqA.
      apply (EqAs_EqConvexAs c f a b rocf roab dicf diab) in cfeqA.
      rewrite <- abeqcf'; eauto.
    }
    contradiction.
  }
Qed.
Theorem LtA_trans :
  forall A B C : Angle,
  A <<< B
    -> B <<< C
    -> A <<< C.
Proof with eauto.
  intros A B C AltB BltC.
  destruct (AngTrichotomy A C) as [ AltC |[ AeqC | AgtC ]]; subst...
  { apply LtA_asymm in AltB; tauto. }
  { destruct (classic (C = A0)) as [ CeqA0 | nCeqA0 ]; subst...
    { apply (NonNegativeAngles B) in BltC; tauto. }
    { destruct (classic (B = A0)) as [ BeqA0 | nBeqA0 ]; subst...
      { apply (NonNegativeAngles A) in AltB; tauto. }
      { destruct (classic (A = A0)) as [ AeqA0 | nAeqA0 ]; subst...
        { apply (NonNegativeAngles C) in AgtC; tauto. }
        { destruct (classic (Convex C)) as [ iC | niC ];
          destruct (classic (Convex B)) as [ iB | niB ];
          destruct (classic (Convex A)) as [ iA | niA ].
          { do 3 right; left; repeat split...
            destruct (DrawSector A)
              as [[ a b roab ] H ]; subst...
            destruct (DrawCongruentAngle_ccw a B)
              as [ c [ roac aceqB ]]; subst...
            destruct (DrawCongruentAngle_ccw a C)
              as [ d [ road adeqC ]]; subst...
            assert (BetRabc : ![ a # b # c ]).
            { apply (iAs_iAs_LtAs_BetRs a b c roab roac)... }
            assert (BetRacd : ![ a # c # d ]).
            { apply (iAs_iAs_LtAs_BetRs a c d roac road)... }
            apply (BetRs_a_trans a b c d BetRabc) in BetRacd.
            destruct BetRacd as [ _ [ BetRabd _ ]]...
            destruct (DrawSector ([| a, d | road |]))
              as [[ a' d' roa'd' ] H ]; simpl in *.
            destruct (BetRs_nColRs a b d BetRabd)
              as [ diab [ dibd diad ]].
            assert (dia'd' : ![ a' # d' ]).
            { rewrite <- H in iC. apply ConvexAng_nAs in iC.
              destruct iC as [ _ [ nCeqA180 _ ]].
              apply -> (nColRs_nColAs a' d' roa'd'); split...
              rewrite <- H in nCeqA0...
            }
            destruct (DrawAngleCutRs a b d a' d' diab diad dia'd')
              as [ b' [ dia'b' [ BetRa'b'd' H1 ]]]...
            apply (EqAs_EqConvexAs a d a' d' road roa'd')...
            assert (roa'b' : da a' = da b'). { destruct dia'b'... }
            exists b', roa'b'; split; auto.
            symmetry.
            apply (EqConvexAs_EqOs_EqAs a b a' b' roab roa'b' diab dia'b')...
            apply -> (ConvexAngRs_Left a b roab diab) in iA.
            rewrite iA. symmetry. rewrite <- H in iC.
            apply -> (ConvexAngRs_Left a' d' roa'd' dia'd') in iC.
            destruct (BetRs_nColRs a' b' d' BetRa'b'd') as [ _ [ dib'd' _ ]].
            destruct (BetRs_EqOs a' b' d' dia'b' dib'd' dia'd') as [ H2 _ ].
            apply H2 in BetRa'b'd'.
            destruct BetRa'b'd' as [ a'b' b'd' ]. rewrite a'b'...
          }
          { contradict niA.
            destruct AltB
              as [[ H1 H1' ]|[[ H2 H2' ]|[[ H3 H3' ]
               |[[ H4 H4' ]|[ H5' [ H5 H6 ]]]]]];
            try contradiction; subst...
            { apply ConvexAng_nAs in iB; tauto. }
            { apply ConvexAng_nAs in iB; tauto. }
          }
          { contradict niB.
            destruct BltC
              as [[ H1 H1' ]|[[ H2 H2' ]|[[ H3 H3' ]
               |[[ H4 H4' ]|[ H5' [ H5 H6 ]]]]]];
            try contradiction; subst...
            { apply ConvexAng_nAs in iC; tauto. }
            { apply ConvexAng_nAs in iC; tauto. }
          }
          { contradict niB.
            destruct BltC
              as [[ H1 H1' ]|[[ H2 H2' ]|[[ H3 H3' ]
               |[[ H4 H4' ]|[ H5' [ H5 H6 ]]]]]];
            try contradiction; subst...
            { apply ConvexAng_nAs in iC; tauto. }
            { apply ConvexAng_nAs in iC; tauto. }
          }
          { contradict niC.
            destruct AgtC
              as [[ H1 H1' ]|[[ H2 H2' ]|[[ H3 H3' ]
               |[[ H4 H4' ]|[ H5' [ H5 H6 ]]]]]];
            try contradiction; subst...
            { apply ConvexAng_nAs in iA; tauto. }
            { apply ConvexAng_nAs in iA; tauto. }
          }
          { contradict niA.
            destruct AltB
              as [[ H1 H1' ]|[[ H2 H2' ]|[[ H3 H3' ]
               |[[ H4 H4' ]|[ H5' [ H5 H6 ]]]]]];
            try contradiction; subst...
            { apply ConvexAng_nAs in iB; tauto. }
            { apply ConvexAng_nAs in iB; tauto. }
          }
          { contradict niC.
            destruct AgtC
              as [[ H1 H1' ]|[[ H2 H2' ]|[[ H3 H3' ]
               |[[ H4 H4' ]|[ H5' [ H5 H6 ]]]]]];
            try contradiction; subst...
            { apply ConvexAng_nAs in iA; tauto. }
            { apply ConvexAng_nAs in iA; tauto. }
          }
          { destruct (classic (C = A180)) as [ xC180 | nC180 ]; subst...
            destruct BltC
              as [[ H1 H1' ]|[[ H2 H2' ]|[[ H3 H3' ]
               |[[ H4 H4' ]|[ H5' [ H5 H6 ]]]]]];
            try contradiction; subst...
            { destruct H5 as [[ H1 H2 ] _ ]; tauto. }
            destruct (classic (B = A180)) as [ xB180 | nB180 ]; subst...
            destruct AltB
              as [[ H1 H1' ]|[[ H2 H2' ]|[[ H3 H3' ]
               |[[ H4 H4' ]|[ H5' [ H5 H6 ]]]]]];
            try contradiction; subst...
            { destruct H5 as [[ H1 H2 ] _ ]; tauto. }
            destruct (classic (A = A180)) as [ xA180 | nA180 ]; subst...
              destruct AgtC
              as [[ H1 H1' ]|[[ H2 H2' ]|[[ H3 H3' ]
               |[[ H4 H4' ]|[ H5' [ H5 H6 ]]]]]];
            try contradiction; subst...
            { destruct H5 as [[ H1 H2 ] _ ]; tauto. }
            assert (xA : Reflex A). { apply (ReflexAng_nAs A)... }
            assert (xB : Reflex B). { apply (ReflexAng_nAs B)... }
            assert (xC : Reflex C). { apply (ReflexAng_nAs C)... }
            destruct (DrawSector A)
              as [[ a b roab ] H ]; subst.
            destruct (DrawCongruentAngle_ccw a B)
              as [ c [ roac aceqB ]]; subst.
            destruct (DrawCongruentAngle_ccw a C)
              as [ d [ robd bdeqC ]]; subst.
            assert (BetRadc : ![ a # d # c ]).
            { apply (xA_xA_LtAs_BetRs a d c robd roac)... }
            assert (BetRabd : ![ a # b # d ]).
            { apply (xA_xA_LtAs_BetRs a b d roab robd)... }
            apply xA_xA_LtAs_BetRs in AltB...
            apply (BetRs_a_trans a b d c BetRabd) in BetRadc.
            assert (BetRabc : ![a # b # c]).
            { destruct BetRadc as [ _ [ H1 _ ]]... }
            apply BetRs_sym in AltB.
            apply BetRs_nPerBetRs in AltB.
            apply BetRs_sym in BetRabc.
            contradiction.
          }
        }
      }
    }
  }
Qed.
Instance LtA_strorder : StrictOrder LtA.
Proof.
  split.
  exact LtA_irrefl.
  exact LtA_trans.
Qed.

Lemma A0_A180 :
  A0 <<< A180.
Proof with eauto.
  left; split...
  apply not_eq_sym.
  apply nA0eqA180.
Qed.

(** Theorem #72 *)
Lemma A0_iA_A180 :
  forall (A : Angle),
  Convex A
    <-> (A0 <<< A) /\ (A <<< A180).
Proof with tauto.
  intros A; split.
  { intros iA; split.
    { apply PositiveAngles. apply ConvexAng_nAs in iA... }
    { right; left; split; eauto. }
  }
  { intros [ AgtA0 AltA180 ].
    apply PositiveAngles in AgtA0. apply ConvexAng_nAs.
    do 2 try split; eauto.
    { intros AeqA180; subst. apply (LtA_irrefl A180); auto. }
    { intros xA.
      destruct AltA180
        as [[ H1 _ ]|[[ H2 _ ]|[[ H3 _ ]|[[ H4 _ ]|[ _ [ H5 _ ]]]]]];
      try contradiction.
      { apply ReflexAng_nAs in xA... }
      { apply ReflexAng_nAs in xA... }
      { apply ReflexAng_nAs in xA... }
      { apply ReflexAng_nAs in H5... }
    }
  }
Qed.
Lemma A180_xA :
  forall (A : Angle),
  Reflex A
    <-> (A180 <<< A).
Proof with eauto.
  intros A; split.
  { intros xA.
    do 2 right; left; split...
  }
  { intros AgtA180.
    apply ReflexAng_nAs.
    repeat split.
    { intros AeqA0; subst.
      apply NonNegativeAngles in AgtA180...
    }
    { intros AeqA180; subst. apply (LtA_irrefl A180)... }
    { intros iA.
      apply (LtA_asymm A A180)...
      apply A0_iA_A180 in iA; tauto.
    }
  }
Qed.

Lemma LtA_LtExpA :
  forall (a b c d : Ray)(roab : da a = da b)(rocd : da c = da d),
  a =/= b
    -> [| a, b | roab |] <<< [| c, d | rocd |]
    -> [| d, c | eq_sym rocd |] <<< [| b, a | eq_sym roab |].
Proof with eauto.
  intros a b c d roab rocd nab0 ab_cd.
  destruct ab_cd as [[ ab cd ]| H ].
  { apply EqNullAng in ab. contradiction. }
  { destruct H as [[ iab [ cd180 | xcd ]]| H ].
    { do 2 right; left; split.
      { apply EqStraightAng in cd180. apply OpRs_OpRs in cd180.
        apply OpRs_sym in cd180. apply EqStraightAng.
        apply OpRs_OpRs in cd180...
      }
      { apply ConvexAngRs_ReflexAngRs... }
    }
    { right; left; split...
      apply ConvexAngRs_ReflexAngRs...
      pir (eq_sym (eq_sym rocd)) => rocd.
      right. apply ConvexAngRs_ReflexAngRs...
    }
    { destruct H as [[ ab180 xcd ]| H ].
      { right; left; split.
        apply ConvexAngRs_ReflexAngRs...
        pir (eq_sym (eq_sym rocd)) => rocd.
        left. apply EqStraightAng in ab180.
        apply EqStraightAng. apply OpRs_OpRs in ab180.
        apply OpRs_sym in ab180. apply OpRs_OpRs...
      }
      { destruct H as [[ iab [ icd G ]]| H ].
        { do 4 right; split.
          { apply ConvexAngRs_ReflexAngRs... }
          split.
          { apply ConvexAngRs_ReflexAngRs... }
          { destruct (DrawSector ([| c, d | rocd |]))
              as [[ c' d' roc'd' ] H ].
            destruct G as [ e' [ roc'e' [ BetRc'e'd' c'e'eqab ]]].
            destruct (DrawSector ([| d, c | eq_sym rocd |]))
              as [[ d'' c'' rod''c'' ] H1 ].
            destruct (BetRs_nColRs c' e' d' BetRc'e'd')
              as [ dic'e' [ die'd' dic'd' ]].
            assert (dic''d'' : ![c'' # d'']).
            { eapply (EqAngRs_nColRs_nColRs c' d' c'' d'' )...
              apply EqAs_EqExpAs in H1.
              pir (eq_sym (eq_sym rocd)) => rocd.
              rewrite H1...
            }
            apply EqAs_EqExpAs in H1.
            pir (eq_sym (eq_sym rocd)) => rocd.
            rewrite <- c'e'eqab in *. rewrite <- H in *.
            destruct (DrawCongruentAngle_cw d''([| c', e' | roc'e' |]))
              as [ e'' [ roe''d'' e''d'' ]].
            rewrite c'e'eqab in e''d''. apply EqAs_EqExpAs in e''d''.
            exists e'', (eq_sym roe''d''); split...
            apply EqAs_EqExpAs in e''d''.
            pir (eq_sym (eq_sym roe''d'')) => roe''d''.
            pir (eq_sym (eq_sym roab)) => roab.
            rewrite <- c'e'eqab in e''d''.
            apply BetRs_sym.
            eapply (BetRs_EqAngRs_BetRs_cross c' e' d' c'' e'' d'')...
          }
        }
        { destruct H as [ xab [ xcd G ]].
          do 3 right; left; split.
          { apply ConvexAngRs_ReflexAngRs...
            pir (eq_sym (eq_sym rocd)) => rocd.
          }
          split.
          { apply ConvexAngRs_ReflexAngRs...
            pir (eq_sym (eq_sym roab)) => roab.
          }
          destruct (DrawSector ([| a, b | roab |]))
            as [[ a' b' roa'b' ] H ]; simpl in H.
          destruct G as [ e' [ roa'e' [ BetRa'e'b' a'e'eqcd ]]].
          destruct (DrawSector ([| b, a | eq_sym roab |]))
            as [[ b'' a'' rob''a'' ] H1 ]; simpl in *.
          destruct (BetRs_nColRs a' e' b' BetRa'e'b')
            as [ dia'e' [ die'b' dia'b' ]].
          assert (dia''d'' : ![a'' # b'']).
          { eapply (EqAngRs_nColRs_nColRs a' b' a'' b'' )...
            apply EqAs_EqExpAs in H1.
            pir (eq_sym (eq_sym roab)) => roab.
            rewrite H1...
          }
          apply EqAs_EqExpAs in H1.
          pir (eq_sym (eq_sym roab)) => roab.
          rewrite <- a'e'eqcd in *. rewrite <- H in *.
          destruct (DrawCongruentAngle_cw b''([| a', e' | roa'e' |]))
            as [ e'' [ roe''b'' e''b'' ]].
          rewrite a'e'eqcd in e''b''.
          apply EqAs_EqExpAs in e''b''.
          exists e'', (eq_sym roe''b''); split...
          apply EqAs_EqExpAs in e''b''.
          pir (eq_sym (eq_sym roe''b'')) => roe''b''.
          pir (eq_sym (eq_sym rocd)) => rocd.
          rewrite <- a'e'eqcd in e''b''.
          apply BetRs_sym.
          eapply (BetRs_EqAngRs_BetRs_cross a' e' b' a'' e'' b'')...
        }
      }
    }
  }
Qed.

Lemma BetRs_LtA :
  forall (a b c : Ray)(diab : ![ a # b ])(diac : ![ a # c ]),
  ![ a # b # c ]
    -> [| a # b | diab |] <<< [| a # c | diac |].
Proof with eauto.
  intros * BetRabc.
  assert (roab : da a = da b). { destruct diab as [ roab H ]... }
  assert (dibc : ![ b # c ]). { apply (BetRs_nColRs a b c BetRabc). }
  assert (robc : da b = da c). { destruct dibc as [ robc H ]... }
  assert (roca : da c = da a). { apply (eq_sym (eq_trans roab robc)). }
  destruct (BetRs_EqOs a b c diab dibc diac) as [ H1 _ ].
  destruct (H1 BetRabc) as [ H2 H3 ]. clear H1.
  symmetry in H3. rewrite H3 in H2.
  assert (ExT : { T | %[b # c | dibc] = T }). { exists (%[b # c | dibc])... }
  destruct ExT as [ T Ts ]. rewrite Ts in *.
  induction T.
  { assert (iab : Convex ([| a, b | roab |])).
    { apply (ConvexAngRs_Left a b roab diab)... }
    assert (iac : Convex ([| a, c | trans_eq roab robc |])).
    { apply (ConvexAngRs_Left a c (eq_trans roab robc) diac)... }
    destruct (iAs_iAs_LtAs_BetRs a b c roab (trans_eq roab robc))...
    rewrite (LeftOrientation_EqAs a b roab) in H2. rewrite <- H2.
    rewrite (LeftOrientation_EqAs a c (trans_eq roab robc)) in H3.
    rewrite <- H3. apply H0...
  }
  { assert (xab : Reflex ([| a, b | roab |])).
    { apply (ReflexAngRs_Right a b roab diab)... }
    assert (xac : Reflex ([| a, c | trans_eq roab robc |])).
    { apply (ReflexAngRs_Right a c (eq_trans roab robc) diac)... }
    assert (acab : [| a, c | eq_trans roab robc |] <<< [| a, b | roab |]).
    { apply (xA_xA_LtAs_BetRs a b c roab (trans_eq roab robc))... }
    rewrite (RightOrientation_EqAs a b roab) in H2. rewrite <- H2.
    rewrite (RightOrientation_EqAs a c (trans_eq roab robc)) in H3.
    rewrite <- H3.
    destruct (AngTrichotomy ([| b, a | eq_sym roab |])([| c, a | roca |]))
      as [ G1 |[ G2 | G3 ]]...
    { pir (eq_sym (eq_trans roab robc)) => roca. }
    { apply EqAs_EqExpAs in G2. pir (eq_sym (eq_sym roab)) => roab.
      pir (eq_sym (eq_sym (eq_trans roab robc))) => (eq_trans roab robc).
      rewrite G2 in acab. pir (eq_sym roca) => (eq_trans roab robc).
      apply (LtA_irrefl ([| a, c | eq_trans roab robc |])) in acab.
      contradiction.
    }
    { assert (caac : [| c, a | roca |] <<< [| a, c | eq_trans roab robc |]).
      { right; left; split... apply ConvexAngRs_ReflexAngRs...
        pir (eq_sym (eq_sym (eq_trans roab robc)))
          => (eq_trans roab robc).
        pir (eq_sym roca)
          => (eq_trans roab robc).
      }
      assert (caab : [| c, a | roca |] <<< [| a, b | roab |]).
      { eapply LtA_trans. apply caac. apply acab. }
      apply (LtA_LtExpA a c a b)...
      intros ac0. apply -> EqNullAng in ac0. rewrite ac0 in xac.
      destruct xac as [[ G1 G2 ] _ ].
      contradict G1...
    }
  }
Qed.

Lemma OrdRs_DiAs :
  forall (a b c d : Ray)(road : da a = da d)(robc : da b = da c),
  ![ a # b # c # d ]
    -> [| a, d | road |] <> [| b, c | robc |].
Proof with eauto.
  intros a b c d road robc [ abc [ abd [ acd bcd ]]] abAcd.
  destruct (BetRs_nColRs a b c abc) as [ diab [ dibc diac ]].
  destruct (BetRs_nColRs a b d abd) as [ _ [ dibd diad ]].
  destruct (BetRs_nColRs a c d acd) as [ _ [ dicd _ ]].
  apply (EqAs_EqConvexAs a d b c road robc diad dibc) in abAcd.
  assert (bc : [|b # c | dibc|] <<< [|b # d | dibd|]).
  { apply (BetRs_LtA b c d dibc dibd bcd). }
  assert (bd : [|b # d | dibd|] <<< [|a # d | diad|]).
  { rewrite (ConvexAngRs_sym b d dibd (nColRs_sym b d dibd)).
    rewrite (ConvexAngRs_sym a d diad (nColRs_sym a d diad)).
    apply BetRs_sym in abd.
    eapply (BetRs_LtA d b a). apply abd.
  }
  assert (bcad : [|b # c | dibc|] <<< [|a # d | diad|]).
  { apply (LtA_trans
      ([|b # c | dibc|])([|b # d | dibd|])([|a # d | diad|]))...
  }
  rewrite abAcd in bcad.
  apply (LtA_irrefl ([|b # c | dibc|]))...
Qed.

End ANGLE_ORDER.

Notation " A <<< B "
  := (LtA A B)
  (at level 70).

(*****************************************************************************)
(* 19 *) Section ANGLE_ADDITION.
Context `{ cc : Concentricals }.
Context  { an : Angles on }.
Context  { sp : Superpositions on }.
(*****************************************************************************)

(** Problem #40 *)
Definition PlusAngleDef (A B : Angle) :
  { C : Angle | forall (a b c : Ray)(roab : da a = da b)(robc : da b = da c),
    [| a, b | roab |] = A
      -> [| b, c | robc |] = B
      -> [| a, c | eq_trans roab robc |] = C }.
Proof with eauto.
  destruct (DrawSector A) as [[ a b roab ] Hab ].
  destruct (DrawCongruentAngle_ccw b B) as [ c Hbc ].
  assert (robc : da b = da c). { destruct Hbc... }
  exists ([| a, c | eq_trans roab robc |]).
  intros a' b' c' roa'b' rob'c' a'b'A b'c'B.
  destruct Hbc; subst. pir x => robc.
  apply AddAngRs...
Defined.

Definition PlusA : Angle -> Angle -> Angle
  := fun A B : Angle => proj1_sig (PlusAngleDef A B).
Notation " A +++ B "
  := (PlusA A B)
  (at level 65).

(** Theorem #73 *)
Lemma PlusAngRs :
  forall (a b c : Ray)(roab : da a = da b)(robc : da b = da c),
  [| a, b | roab |] +++ [| b, c | robc |] = [| a, c | eq_trans roab robc |].
Proof with eauto.
  intros a b c roab robc.
  unfold PlusA.
  destruct (DrawSector ([| a, b | roab |])) as [[ a' b' roa'b' ] Hab ].
  rewrite (proj2_sig (PlusAngleDef ([|a, b | roab|]) ([|b, c | robc|])))...
Qed.

Lemma EqAngRs_EqCrossAngRs :
  forall (a b c d : Ray)(roab : da a = da b)
         (robc : da b = da c)(rocd : da c = da d),
  [| a, b | roab |] = [| c, d | rocd |]
    -> [| a, c | eq_trans roab robc |] = [| b, d | eq_trans robc rocd |].
Proof with eauto.
  intros a b c d roab robc rocd abAcd.
  assert (roac : da a = da c). { apply (eq_trans roab robc). }
  assert (robd : da b = da d). { apply (eq_trans robc rocd). }
  assert (roc'd' : da (!c) = da (!d)).
  { eapply (eq_trans (eq_sym (OpRays_0 c)) (eq_trans rocd (OpRays_0 d))). }
  assert (roba' : da b = da (!a)).
  { apply (eq_trans (eq_sym roab)(OpRays_0 a))... }
  assert (roab' : da a = da (!b)). { rewrite <- OpRays_0... }
  assert (rod'c : da (!d) = da c).
  { apply (eq_trans (eq_sym (OpRays_0 d))(eq_sym rocd))... }
  assert (rod'a : da (!d) = da a).
  { rewrite <- OpRays_0. rewrite roab; rewrite robc... }
  assert (roc'b : da (!c) = da b).
  { apply (eq_trans (eq_sym (OpRays_0 c))(eq_sym robc))... }
  assert (roc'd : da (!c) = da d). { rewrite <- OpRays_0... }
  assert (roda' : da d = da (!a)).
  { rewrite <- OpRays_0. rewrite roab; rewrite robc... }
  assert (rocd'' : da c = da (!(!d))).
  { rewrite rocd. rewrite <- OpRays_0... rewrite <- OpRays_0... }
  assert (rodc' : da d = da (!c)).
  { rewrite <- OpRays_0. rewrite <- robd... }
  destruct (classic (![ a # b ])) as [ diab | ndiab ].
  { destruct (classic (![ c # d ])) as [ dicd | ndicd ].
    { destruct (classic (![ b # c ])) as [ dibc | ndibc ].
      { destruct (classic (![ a # c ])) as [ diac | ndiac ].
        { destruct (classic (![ a # d ])) as [ diad | ndiad ].
          { destruct (classic (![ b # d ])) as [ dibd | ndibd ].
            { assert (didc : ![ d # c ]). { apply (nColRs_sym c d dicd). }
              assert (dicb : ![ c # b ]). { apply (nColRs_sym b c dibc). }
              assert (didb : ![ d # b ]). { apply (nColRs_sym b d dibd). }
              assert (dida : ![ d # a ]). { apply (nColRs_sym a d diad). }
              assert (dica : ![ c # a ]). { apply (nColRs_sym a c diac). }
              assert (diac' : ![ a # !c ]). { apply nColOpRs_2... }
              assert (dibc' : ![ b # !c ]). { apply nColOpRs_2... }
              assert (dic'd : ![ !c # d ]). { apply nColOpRs_1... }
              assert (dic'd' : ![ !c # !d ]). { apply nColOpRs_2... }
              assert (abTcd : %[a # b | diab] = %[c # d | dicd]).
              { apply (EqAs_EqTs a b c d roab rocd diab dicd abAcd). }
              destruct (DecideFourRays a b c d) as [ H | G ]...
              { repeat destruct H as [ H | G ]...
                { apply OrdRs_EqAs_EqAs_1... }
                { apply (OrdRs_EqOs a b d c diab dibd didc diad dibc diac)
                    in G...
                  destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]]...
                  rewrite <- T1 in T3. rewrite abTcd in T3. symmetry in T3.
                  rewrite (DiOsRs c d dicd didc) in T3...
                  induction (%[ d # c | didc]); try discriminate...
                }
                { apply (OrdRs_EqOs a d b c diad didb dibc diab didc diac)
                    in G...
                  destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                  rewrite <- T4 in T5. rewrite abTcd in T5. symmetry in T5.
                  rewrite (DiOsRs c d dicd didc) in T5...
                  induction (%[ d # c | didc]); try discriminate...
                }
                { apply OrdRs_PerOrdRs in G...
                  { apply (OrdRs_EqOs d a b c dida diab dibc didb diac didc)
                      in G...
                    destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                    rewrite abTcd in T2.
                    rewrite (DiOsRs c d dicd didc) in T2...
                    induction (%[ d # c | didc]); try discriminate...
                  }
                  { rewrite roab. rewrite robc... }
                }
                { assert (G1 : ![!c # a # b # !d]).
                  { apply OrdRs_PerOrdRs...
                    { rewrite roab. rewrite robc.
                      symmetry. apply OpRays_0...
                    }
                    { rewrite robc. rewrite rocd. apply OpRays_0... }
                    { destruct G as [ abd [ abc [ adc bdc ]]].
                      split... split.
                      { apply (BetRs_inv a b c a b (!(!c)));
                        try reflexivity...
                        apply OpOpRs.
                      }
                      { split.
                        { apply (BetRs_inv a (!d) c a (!d)(!(!c)));
                          try reflexivity...
                          apply OpOpRs.
                        }
                        { apply (BetRs_inv b (!d) c b (!d)(!(!c)));
                          try reflexivity...
                          apply OpOpRs.
                        }
                      }
                    }
                  }
                  assert (cdAcd : [| c, d | rocd |] = [| !c, !d | roc'd' |]).
                  { erewrite <- (EqOppVertAs c (!d))...
                    apply (EqAs_EqRs c d (!(!d))). apply OpOpRs.
                  }
                  assert (nabAcd : [| a, b | roab |] <> [| !c, !d | roc'd' |]).
                  { apply not_eq_sym. apply OrdRs_DiAs... }
                  rewrite <- cdAcd in nabAcd.
                  contradiction.
                }
                { apply OrdRs_PerOrdRs in G...
                  { apply OrdRs_sym in G...
                    { apply OrdRs_EqAs_EqAs_4... }
                    { rewrite robc. rewrite rocd. symmetry.
                      apply OpRays_0.
                    }
                    rewrite <- robc. rewrite <- roab.
                    apply OpRays_0.
                  }
                  rewrite robc. rewrite rocd. symmetry.
                  apply OpRays_0.
                }
                { eapply (OrdRs_EqOs a b (!c) d diab dibc' dic'd) in G...
                  destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                  rewrite <- T1 in T3. rewrite abTcd in T3.
                  rewrite <- (OpRs_EqOs_Right d c (!c) didc dic'd) in T3.
                  { rewrite (DiOsRs c d dicd didc) in T3...
                    induction (%[ d # c | didc]); try discriminate...
                  }
                  apply OpOpRs.
                }
                { assert (G1 : ![c # a # b # d]). { apply OrdRs_PerOrdRs... }
                  assert (nabAcd : [| a, b | roab |] <> [| c, d | rocd |]).
                  { apply not_eq_sym. apply OrdRs_DiAs... }
                  contradiction.
                }
                { assert (G1 : ![c # a # d # b]).
                  { apply OrdRs_PerOrdRs... rewrite roab... }
                  apply OrdRs_sym in G1. apply OrdRs_EqAs_EqAs_8...
                  rewrite roab... rewrite roab.
                  rewrite robc... rewrite robc...
                }
                { assert (G1 : ![c # d # a # b]).
                  { apply OrdRs_PerOrdRs... rewrite roab. rewrite robc...
                    apply OrdRs_PerOrdRs... rewrite roab. rewrite robc...
                  }
                  apply OrdRs_sym in G1... apply OrdRs_EqAs_EqAs_7...
                  rewrite roab; rewrite robc...
                }
                { assert (G1 : ![d # c # a # b]).
                  { apply OrdRs_PerOrdRs... apply OrdRs_PerOrdRs...
                    rewrite robc. rewrite rocd. apply OpRays_0.
                  }
                  eapply (OrdRs_EqOs d c a b didc dica diab dida) in G1...
                  destruct G1 as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                  rewrite <- T1 in T3. rewrite abTcd in T3.
                  rewrite (DiOsRs c d dicd didc) in T3...
                  induction (%[ d # c | didc]); try discriminate...
                }
                { destruct (OrdRs_nColRs a (!d) b (!c))
                    as [ diad' [ did'b [ _ [ _ [ did'c' _ ]]]]]...
                  { symmetry. rewrite robc.
                    rewrite rocd. apply OpRays_0.
                  }
                  eapply
                    (OrdRs_EqOs a (!d) b (!c) diad' did'b dibc' diab did'c')
                    in G...
                  destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                  rewrite <- T5 in T4. rewrite abTcd in T4.
                  assert (cdAcd : [| c, d | rocd |] = [| !c, !d | roc'd' |]).
                  { pir roc'd' => (eq_trans (eq_sym (OpRays_0 c))
                      (eq_trans rocd (OpRays_0 d))).
                    erewrite <- (EqOppVertAs c (!d))...
                    apply (EqAs_EqRs c d (!(!d))). apply OpOpRs.
                  }
                  eapply (EqAs_EqTs c d (!c)(!d)) in cdAcd...
                  rewrite cdAcd in T4.
                  rewrite (DiOsRs (!c) (!d) dic'd' did'c') in T4...
                  induction (%[ !d # !c | did'c']); try discriminate...
                }
                { destruct (OrdRs_nColRs a (!c) b d) as [ _ [ dic'b _ ]]...
                  { rewrite roab. rewrite robc. apply OpRays_0. }
                  { eapply (OrdRs_EqOs a (!c) b d diac' dic'b dibd) in G...
                    destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                    rewrite <- T4 in T5. rewrite abTcd in T5.
                    erewrite <- (OpRs_EqOs_Right d c (!c)) in T5.
                    erewrite (DiOsRs d c didc dicd) in T5.
                    induction ( %[ c # d | dicd]); try discriminate...
                    apply OpOpRs.
                  }
                }
                { destruct (OrdRs_nColRs a (!c) d b)
                    as [ _ [ _ [ _ [ _ [ dic'b _ ]]]]]...
                  { rewrite roab. rewrite robc. apply OpRays_0. }
                  symmetry.
                  eapply (OrdRs_EqOs a (!c) d b) in G...
                  destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                  rewrite abTcd in T2.
                  erewrite <- (OpRs_EqOs_Right d c (!c)) in T2.
                  { rewrite (DiOsRs d c (nColRs_sym c d dicd) dicd) in T2.
                    induction ( %[ c # d | dicd]); try discriminate...
                  }
                  apply OpOpRs.
                }
                { apply OrdRs_PerOrdRs in G...
                  { apply -> OrdRs_PerOrdRs in G...
                    apply -> OrdRs_PerOrdRs in G...
                    { assert (G1 : ![b # !a # !d # c]).
                      { destruct G as [ abd [ abc [ adc bdc ]]].
                        split... split...
                        { apply (BetRs_inv b (!a)(!(!c)) b (!a) c);
                          try reflexivity...
                          symmetry. apply OpOpRs.
                        }
                        split...
                        { apply (BetRs_inv b (!d)(!(!c)) b (!d) c);
                          try reflexivity...
                          symmetry. apply OpOpRs.
                        }
                        apply (BetRs_inv (!a)(!d)(!(!c))(!a)(!d) c);
                        try reflexivity...
                        symmetry. apply OpOpRs.
                      }
                      apply OrdRs_EqAs_EqAs_6...
                    }
                    rewrite <- (OpRays_0 a). rewrite <- (OpRays_0 d).
                    rewrite roab. rewrite robc...
                  }
                  rewrite roab. rewrite robc...
                }
                { apply -> OrdRs_PerOrdRs in G...
                  { apply -> OrdRs_PerOrdRs in G...
                    { assert (G1 : ![b # !d # !a # c]).
                      { destruct G as [ abd [ abc [ adc bdc ]]].
                        split... split.
                        { apply (BetRs_inv b (!d)(!(!c)) b (!d) c);
                          try reflexivity...
                          symmetry. apply OpOpRs.
                        }
                        { split.
                          { apply (BetRs_inv b (!a)(!(!c)) b (!a) c);
                            try reflexivity...
                            symmetry. apply OpOpRs.
                          }
                          { apply (BetRs_inv (!d)(!a)(!(!c))(!d)(!a) c);
                            try reflexivity...
                            symmetry. apply OpOpRs.
                          }
                        }
                      }
                      apply OrdRs_EqAs_EqAs_5...
                    }
                    rewrite <- OpRays_0. rewrite <- OpRays_0.
                    rewrite roab. rewrite robc... rewrite robc.
                    rewrite rocd. apply OpRays_0.
                  }
                  rewrite robc. rewrite rocd. apply OpRays_0.
                  rewrite roab. rewrite robc. apply OpRays_0.
                }
                { assert (cdAcd : [| c, d | rocd |] = [| !c, !d | roc'd' |]).
                  { erewrite <- (EqOppVertAs c (!d)).
                    apply (EqAs_EqRs c d (!(!d))). apply OpOpRs.
                  }
                  assert (nabAcd : [| a, b | roab |] <> [| !c, !d | roc'd' |]).
                  { apply OrdRs_DiAs... }
                  rewrite <- cdAcd in nabAcd.
                  contradiction.
                }
                { destruct (OrdRs_nColRs a (!d)(!c) b)
                    as [ diad' [ did'c' [ dic'b [ _ [ did'b _ ]]]]]...
                  eapply (OrdRs_EqOs a (!d)(!c) b diad' did'c' dic'b) in G.
                  destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                  assert (cdAcd : [| c, d | rocd |] = [| !c, !d | roc'd' |]).
                  { erewrite <- (EqOppVertAs c (!d)).
                    apply (EqAs_EqRs c d (!(!d))). apply OpOpRs.
                  }
                  eapply (EqAs_EqTs c d (!c)(!d) rocd roc'd' dicd dic'd')
                    in cdAcd...
                  rewrite abTcd in T2. rewrite <- T2 in cdAcd.
                  rewrite (DiOsRs (!d)(!c) did'c' dic'd') in cdAcd.
                  induction (%[ ! c # ! d | dic'd']); try discriminate...
                }
                { apply OrdRs_EqAs_EqAs_2... }
                { destruct (OrdRs_DiAs a c d b roab rocd G abAcd). }
                { eapply (OrdRs_EqOs a d c b diad didc dicb diac didb) in G...
                  destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                  rewrite abTcd in T2. symmetry in T2.
                  rewrite (DiOsRs c d dicd didc) in T2.
                  induction (%[ d # c | didc]); try discriminate...
                }
                { apply OrdRs_PerOrdRs in G...
                  { eapply (OrdRs_EqOs d a c b dida diac dicb didc) in G...
                    destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                    destruct T5. rewrite abTcd in T4.
                    rewrite (DiOsRs c d dicd didc) in T4.
                    induction (%[ d # c | didc]); try discriminate...
                  }
                  rewrite roab. rewrite robc...
                }
                { apply OrdRs_PerOrdRs in G...
                  { eapply (OpRs_EqSupAngRs a b (!a) c d (!c)) in abAcd;
                    try apply OpOpRs...
                    erewrite (EqOppVertAs d c) in abAcd.
                    destruct (OrdRs_nColRs c (!d) b (!a))
                      as [ dicd' [ did'b [ diba' [ _ [ did'a' dica' ]]]]]...
                    { rewrite robc. rewrite rocd. symmetry.
                      apply OpRays_0.
                    }
                    eassert (baTdc : %[b # !a | diba' ] = %[!d # c | _ ]).
                    { apply (EqAs_EqTs b (!a)(!d) c roba' rod'c)... }
                    eapply (OrdRs_EqOs c (!d) b (!a) dicd' did'b diba') in G.
                    destruct G as [ T1 [ T2 [ T3 [ T4 T5 ]]]].
                    rewrite baTdc in T3. rewrite <- T1 in T3.
                    erewrite (DiOsRs (!d) c _ dicd') in T3.
                    induction (%[ c # ! d | dicd']); try discriminate...
                  }
                  rewrite <- OpRays_0. rewrite robc...
                }
              }
              { assert (G1 : ![a # !b # !c # d]).
                { apply OrdRs_sym...
                  { rewrite <- OpRays_0... rewrite <- OpRays_0... }
                  apply <- OrdRs_PerOrdRs...
                  { apply <- OrdRs_PerOrdRs...
                    { apply <- OrdRs_PerOrdRs...
                      { destruct G as [ abd [ abc [ adc bdc ]]].
                        split...
                        { apply (BetRs_inv a (!d) c a (!d)(!(!c)));
                          try reflexivity...
                          apply OpOpRs.
                        }
                        { split.
                          { apply (BetRs_inv a (!d) b a (!d)(!(!b)));
                            try reflexivity...
                            apply OpOpRs.
                          }
                          { split.
                            { apply (BetRs_inv a c b a (!(!c))(!(!b)));
                              try reflexivity...
                              apply OpOpRs. apply OpOpRs.
                            }
                            { apply (BetRs_inv (!d) c b (!d)(!(!c))(!(!b)));
                              try reflexivity...
                              { apply OpOpRs. }
                              apply OpOpRs.
                            }
                          }
                        }
                      }
                      rewrite <- OpRays_0.
                      rewrite <- OpRays_0.
                      rewrite <- OpRays_0...
                    }
                    rewrite <- OpRays_0.
                    rewrite <- OpRays_0...
                  }
                  rewrite <- OpRays_0...
                  rewrite <- OpRays_0...
                }
                apply OrdRs_EqAs_EqAs_3...
              }
            }
            { destruct (DecideCollinearRays b d) as [ beqd | bopd ]...
              { assert (beqd' := beqd).
                { apply -> (EqNullAng b d (eq_trans robc rocd)) in beqd'.
                  rewrite beqd'. apply EqNullAng.
                  apply -> (EqAngRs_EqRs_cw b a c roab (eq_sym robc)).
                  rewrite abAcd. apply EqAs_EqRs. symmetry...
                }
              }
              { assert (bopd' := bopd).
                { apply OpRs_OpRs in bopd'.
                  apply -> (EqStraightAng b d (eq_trans robc rocd)) in bopd'.
                  rewrite bopd'. apply EqStraightAng. apply OpRs_OpRs.
                  apply (EqAngRs_EqRs_cw b a (!c) roab roc'b).
                  rewrite abAcd.
                  assert (cd : [| !c, b | roc'b |] = [| !c, !d |roc'd' |]).
                  { apply (EqAs_EqRs (!c) b (!d))... }
                  rewrite cd.
                  pir roc'd' => (eq_trans (eq_sym (OpRays_0 c))
                    (eq_trans rocd (OpRays_0 d))).
                  apply (EqVertAs c d rocd).
                }
              }
            }
          }
          { destruct (DecideCollinearRays a d) as [ aeqd | aopd ]...
            { rewrite roab; rewrite robc... }
            { apply EqAs_EqExpAs in abAcd.
              eassert (da : [| d, c | _ |] = [| a, c | _ |]).
              { apply (EqAngRs_EqRs_cw c d a). symmetry... }
              rewrite <- da. rewrite <- abAcd.
              apply (EqAs_EqRs b a d)...
            }
            { apply EqAs_EqExpAs in abAcd.
              apply EqSupAs in abAcd.
              eassert (bd : [| b, d | _ |] = [| b, !a | roba' |]).
              { apply (EqAs_EqRs b d (!a)). rewrite aopd.
                apply OpOpRs.
              }
              rewrite bd.
              pir roba' => (eq_trans (eq_sym roab)(OpRays_0 a)).
              rewrite abAcd.
              eassert (ac : [| a, c | _ |] = [| !d, c | rod'c |]).
              { apply (EqAngRs_EqRs_cw c a (!d))... }
              rewrite ac. symmetry.
              pir rod'c => (eq_trans (eq_sym (OpRays_0 d))(eq_sym rocd)).
              apply EqOppVertAs.
            }
          }
        }
        { destruct (DecideCollinearRays a c) as [ aeqc | aopc ]...
          { assert (aeqc' := aeqc).
            apply -> (EqNullAng a c (eq_trans roab robc)) in aeqc'.
            rewrite aeqc'. symmetry. apply EqNullAng.
            eapply (EqAngRs_EqRs_cw a b d).
            apply EqAs_EqExpAs. rewrite abAcd.
            apply <- EqAngRs_EqRs_cw. symmetry...
          }
          { assert (aopc' := aopc).
            apply OpRs_OpRs in aopc'.
            apply -> (EqStraightAng a c (eq_trans roab robc)) in aopc'.
            rewrite aopc'. symmetry. apply EqStraightAng.
            apply OpRs_OpRs.
            eapply (EqAngRs_EqRs_cw a b (!d)).
            apply EqAs_EqExpAs in abAcd.
            rewrite abAcd.
            assert (cd : [| d, c | eq_sym rocd |] = [| d, !a | roda' |]).
            { apply <- (EqAs_EqRs d c (!a))...
              rewrite aopc. apply OpOpRs.
            }
            rewrite cd.
            eapply (EqOppVertAs d a).
          }
        }
      }
      { destruct (DecideCollinearRays b c) as [ beqc | bopc ]...
        { assert (ab : [| a, b | roab |] = [| a, c | eq_trans roab robc |]).
          { apply (EqAs_EqRs a b c)... }
          rewrite <- ab. rewrite abAcd.
          apply (EqAngRs_EqRs_cw d c b)... symmetry...
        }
        { apply EqSupAs in abAcd.
          eassert (ac : [| a, c | roac |] = [| a, !b | _ |]).
          { apply (EqAs_EqRs a c (!b)). rewrite bopc.
            apply OpOpRs.
          }
          eassert (bd : [| b, d | robd |] = [| !c, d | _ |]).
          { apply (EqAngRs_EqRs_cw d b (!c))... }
          pir (eq_trans roab robc) => roac.
          pir (eq_trans robc rocd) => robd.
          rewrite bd. rewrite ac. rewrite abAcd.
          apply EqOppVertAs.
        }
      }
    }
    { destruct (DecideCollinearRays c d) as [ ceqd | copd ]...
      { apply (EqNullAng c d rocd) in ceqd. rewrite ceqd in abAcd.
        apply EqNullAng in abAcd. apply EqNullAng in ceqd.
        eapply (EqAngRs_inv a c b d)...
      }
      { apply OpRs_OpRs in copd.
        apply (EqStraightAng c d rocd) in copd. rewrite copd in abAcd.
        apply EqStraightAng in abAcd. apply EqStraightAng in copd.
        erewrite (EqAngRs_inv a c (!b)(!d))... symmetry. apply EqVertAs.
        apply OpRs_OpRs. auto. apply OpRs_OpRs...
      }
    }
  }
  destruct (DecideCollinearRays a b) as [ aeqb | aopb ]...
  { apply (EqNullAng a b roab) in aeqb. rewrite aeqb in abAcd.
    symmetry in abAcd. apply EqNullAng in abAcd.
    apply EqNullAng in aeqb.
    apply (EqAngRs_inv a c b d (eq_trans roab robc)(eq_trans robc rocd))...
  }
  { apply OpRs_OpRs in aopb.
    apply (EqStraightAng a b roab) in aopb. rewrite aopb in abAcd.
    symmetry in abAcd. apply EqStraightAng in abAcd.
    apply EqStraightAng in aopb.
    erewrite (EqAngRs_inv a c (!b)(!d))...
    { symmetry. apply (EqVertAs b d (eq_trans robc rocd)). }
    { apply OpRs_OpRs... }
    apply OpRs_OpRs...
  }
  Unshelve.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto.
  simpl. apply nColRs_sym; auto. rewrite roab... auto.
  simpl. rewrite rodc'. auto.
  rewrite <- roab'... rewrite rod'c. rewrite <- roab'...
Qed.

(** Theorem #74 *)
Theorem PlusAs_0_r :
  forall A : Angle,
  A +++ A0 = A.
Proof with eauto.
  intros A; unfold PlusA, PlusAngleDef.
  destruct (DrawSector A) as [[ a b roab ] abeqA ].
  destruct (DrawCongruentAngle_ccw b A0) as [ c [ roac bceqA0 ]].
  simpl.
  apply EqNullAng in bceqA0. rewrite <- abeqA. symmetry.
  apply (EqAs_EqRs a b c)...
Qed.
Theorem PlusAs_0_l :
  forall A : Angle,
  A0 +++ A = A.
Proof with eauto.
  intros A; unfold PlusA, PlusAngleDef.
  destruct (DrawSector A0) as [[ a b roab ] abeqA0 ].
  destruct (DrawCongruentAngle_ccw b A) as [ c [ roac bceqA ]]. simpl.
  apply EqNullAng in abeqA0. rewrite <- bceqA.
  apply (EqAngRs_EqRs_cw c a b)...
Qed.
Theorem PlusAng_comm :
  forall A B : Angle,
  A +++ B = B +++ A.
Proof with eauto.
  intros A B.
  unfold PlusA, PlusAngleDef.
  destruct (DrawSector A) as [[ a b roab ] Aeqab ].
  destruct (DrawCongruentAngle_ccw b B) as [ c [ robc bceqB ]].
  destruct (DrawSector B) as [[ a' b' roa'b' ] Beqa'b' ].
  destruct (DrawCongruentAngle_ccw b' A) as [ c' [ rob'c' b'c'eqab ]].
  simpl; subst.
  destruct (DrawCongruentAngle_ccw c ([| a, b | roab |]))
    as [ d [ rocd cdeqA ]].
  destruct (DrawCongruentAngle_ccw c' ([| a', b' | roa'b' |]))
    as [ d' [ roc'd' c'd'eqB ]].
  assert (bdeqa'c' :[| b, d | eq_trans robc rocd |]
    = [| a', c' | eq_trans roa'b' rob'c' |]).
  { rewrite <- (PlusAngRs b c d robc rocd).
    rewrite <- (PlusAngRs a' b' c' roa'b' rob'c').
    symmetry in b'c'eqab.
    destruct Beqa'b', b'c'eqab, cdeqA...
  }
  assert (aceqbd : [| a, c | eq_trans roab robc |]
    = [| b, d | eq_trans robc rocd |]).
  { apply (EqAngRs_EqCrossAngRs a b c d); subst.
    rewrite <- cdeqA. reflexivity.
  }
  rewrite <- bdeqa'c'. rewrite <- aceqbd. reflexivity.
Qed.
Theorem PlusAs_assoc :
  forall A B C : Angle,
  A +++ (B +++ C) = (A +++ B) +++ C.
Proof with eauto.
  intros A B C.
  assert (ExAB : exists AB : Angle, AB = A +++ B).
  { exists (A +++ B)... }
  destruct ExAB as [ AB ABeqApB ].
  rewrite <- ABeqApB.
  assert (ExBC : exists BC : Angle, BC = B +++ C).
  { exists (B +++ C)... }
  destruct ExBC as [ BC BCeqBpC ].
  rewrite <- BCeqBpC.
  assert (ExABC : exists ABC : Angle, ABC = AB +++ C).
  { exists (AB +++ C)... }
  destruct ExABC as [ ABC ABCeqABpC ].
  rewrite <- ABCeqABpC.
  assert (ExABC' : exists ABC' : Angle, ABC' = A +++ BC).
  { exists (A +++ BC)... }
  destruct ExABC' as [ ABC' ABCeqApBC ].
  rewrite <- ABCeqApBC.
  destruct (DrawSector A) as [[ a b roab ] Hab ]; simpl.
  destruct Hab.
  destruct (DrawCongruentAngle_ccw b B) as [ c [ robc Hbc ]].
  destruct Hbc.
  rewrite (PlusAngRs a b c roab robc) in ABeqApB.
  symmetry in ABeqApB. destruct ABeqApB.
  destruct (DrawCongruentAngle_ccw c C) as [ d [ rocd Hcd ]].
  destruct Hcd.
  rewrite (PlusAngRs a c d (eq_trans roab robc) rocd) in ABCeqABpC.
  symmetry in ABCeqABpC. destruct ABCeqABpC.
  rewrite (PlusAngRs b c d robc rocd) in BCeqBpC.
  symmetry in BCeqBpC. destruct BCeqBpC.
  rewrite (PlusAngRs a b d roab (eq_trans robc rocd)) in ABCeqApBC.
  symmetry in ABCeqApBC. destruct ABCeqApBC.
  pir (eq_trans (eq_trans roab robc) rocd)
    => (eq_trans roab (eq_trans robc rocd)).
Qed.
Theorem PlusAs_cancel_l :
  forall A B C : Angle,
  A +++ B = A +++ C
    -> B = C.
Proof with eauto.
  intros A B C ApBeqApC.
  destruct (DrawSector A) as [[ o a rooa ] H ].
  destruct (DrawCongruentAngle_ccw a B) as [ b [ roab abeqB ]].
  rewrite <- abeqB in ApBeqApC.
  rewrite <- H in ApBeqApC.
  rewrite (PlusAngRs o a b) in ApBeqApC.
  destruct (DrawCongruentAngle_ccw a C) as [ c [ roac aceqC ]].
  rewrite <- aceqC in ApBeqApC.
  rewrite (PlusAngRs o a c) in ApBeqApC.
  assert (beqc : b == c).
  { apply (EqAs_EqRs o b c (eq_trans rooa roab)(eq_trans rooa roac))... }
  rewrite <- abeqB. rewrite <- aceqC.
  apply (EqAs_EqRs a b c roab roac)...
Qed.
Theorem PlusA_cancel_r :
  forall A B C : Angle,
  A +++ C = B +++ C
    -> A = B.
Proof with eauto.
  intros AB BC CD.
  rewrite (PlusAng_comm AB CD).
  rewrite (PlusAng_comm BC CD).
  apply PlusAs_cancel_l.
Qed.

(** Problem #41 *)
Definition DrawSubtractionOfTwoAngles :
  forall A C : Angle,
  A <<< C
    -> { B : Angle | A +++ B = C }.
Proof with eauto.
  intros A C AltC.
  assert (nCeqA0 : C <> A0).
  { intros CeqA0; subst. eapply NonNegativeAngles... }
  destruct (DrawSector A) as [[ a b roab ] H ].
  subst.
  destruct (DrawCongruentAngle_ccw a C) as [ c H ].
  assert (robc : da b = da c).
  { destruct H as [ roac _ ]. rewrite <- roab... }
  exists ([| b, c | robc |]).
  destruct H as [ roac aceqC ].
  rewrite PlusAngRs. pir (eq_trans roab robc) => roac.
Defined.

Lemma ExpA_ColA :
  forall A : Angle,
  A +++ A = A0
    -> A = A0 \/ A = A180.
Proof with eauto.
  intros A AexpA.
  destruct (DrawSector A) as [[ a b roab ] abeqA ].
  destruct abeqA.
  assert (AeqA : [| a, b | roab |] +++ [| b, a | sym_eq roab |] = A0).
  { rewrite PlusAngRs.
    pir (eq_trans roab (eq_sym roab)) => (eq_refl (da a)).
    apply (proj2_sig NullAng).
  }
  assert (AA : [| a, b | roab |] = [| b, a | sym_eq roab |]).
  { apply (PlusAs_cancel_l
      ([| a, b | roab |])([| a, b | roab |])([| b, a | eq_sym roab |])).
    rewrite AexpA. rewrite AeqA...
  }
  destruct (classic (a == b)) as [ aeqb | naeqb ].
  { left. apply (EqNullAng a b)... }
  { destruct (classic (a == (!b))) as [ aopb | naopb ].
    { right. apply EqStraightAng... apply OpRs_OpRs... }
    { assert (diab : ![ a # b ]). { apply nColRs_nColPs. repeat split... }
      assert (diba : ![ b # a ]).
      { apply nColRs_nColPs.
        repeat split...
        { contradict naopb. symmetry in naopb. contradiction. }
        { contradict naopb. rewrite naopb. apply OpOpRs... }
      }
      assert (eqts : %[ a # b | diab ] = %[ b # a | diba ]).
      { apply (EqAs_EqTs a b b a roab (eq_sym roab) diab diba AA). }
      rewrite (DiOsRs b a diba diab) in eqts...
      induction (%[ a # b | diab]); try discriminate...
    }
  }
Qed.

(** Theorem #75 *)
Theorem BetRs_PlusAngRs :
  forall (a b c : Ray)(diab : ![ a # b ])(dibc : ![ b # c ])(diac : ![ a # c ]),
  ![ a # b # c ]
    <-> [| a # b | diab |] +++ [| b # c | dibc |] = [| a # c | diac |].
Proof with eauto.
  intros a b c diab dibc diac.
  split.
  { intros BetRabc.
    destruct (BetRs_EqOs a b c diab dibc diac) as [ H _ ].
    destruct (H BetRabc) as [ abeqT bceqT ]. clear H.
    assert (ExTac : { Tac | %[ a # c | diac ] = Tac }).
    { exists (%[ a # c | diac ])... }
    destruct ExTac as [ Tac aceqT ].
    induction Tac.
    { rewrite aceqT in *.
      assert (ccwab : [| a, b | proj1 diab |] = [| a # b | diab |]).
      { apply -> (LeftOrientation_EqAs a b (proj1 diab) diab)... }
      rewrite <- ccwab.
      assert (ccwbc : [| b, c | proj1 dibc |] = [| b # c | dibc |]).
      { apply -> (LeftOrientation_EqAs b c (proj1 dibc) dibc)... }
      rewrite <- ccwbc.
      eassert (ccwac : [| a, c | _ |] = [| a # c | diac |]).
      { apply ->
          (LeftOrientation_EqAs a c (eq_trans (proj1 diab)(proj1 dibc)) diac)...
      }
      rewrite <- ccwac.
      apply (PlusAngRs a b c (proj1 diab)(proj1 dibc)).
    }
    rewrite aceqT in *.
    assert (diba : ![ b # a ]). { apply nColRs_sym... }
    assert (dicb : ![ c # b ]). { apply nColRs_sym... }
    assert (dica : ![ c # a ]). { apply nColRs_sym... }
    assert (nbaeqab : %[ a # b | diab] = negb (%[ b # a | diba])).
    { apply (DiOsRs a b diab diba)... }
    assert (ncbeqbc : %[ b # c | dibc] = negb (%[ c # b | dicb])).
    { apply (DiOsRs b c dibc dicb)... }
    assert (ncaeqac : %[ a # c | diac] = negb (%[ c # a | dica])).
    { apply (DiOsRs a c diac dica)... }
    assert (baeqT : %[b # a | diba] = true).
    { apply (OrientationRs_RL a b diab)... }
    assert (caeqT : %[c # a | dica] = true).
    { apply (OrientationRs_RL a c diac)... }
    assert (cbeqT : %[c # b | dicb] = true).
    { apply (OrientationRs_RL b c dibc)... }
    assert (ccwcb : [| c, b | eq_sym (proj1 dibc) |] = [| c # b | dicb |]).
    { apply -> (LeftOrientation_EqAs c b (eq_sym (proj1 dibc)) dicb)... }
    assert (cbbc : [| c # b | dicb |] = [| b # c | dibc |]).
    { apply (ConvexAngRs_sym c b dicb dibc). }
    rewrite cbbc in *. rewrite <- ccwcb.
    assert (ccwca : [| c, a | eq_sym (proj1 diac) |] = [| c # a | dica |]).
    { apply -> (LeftOrientation_EqAs c a (eq_sym (proj1 diac)) dica)... }
    assert (caac : [| c # a | dica |] = [| a # c | diac |]).
    { apply (ConvexAngRs_sym c a dica). }
    rewrite caac in *. rewrite <- ccwca.
    assert (ccwba : [| b, a | eq_sym (proj1 diab) |] = [| b # a | diba |]).
    { apply -> (LeftOrientation_EqAs b a (eq_sym (proj1 diab)) diba)... }
    assert (baab : [| b # a | diba |] = [| a # b | diab |]).
    { apply (ConvexAngRs_sym b a diba). }
    rewrite baab in *. rewrite <- ccwba.
    rewrite PlusAng_comm.
    pir (eq_sym (proj1 diac))
      => (eq_trans (eq_sym (proj1 dibc))(eq_sym (proj1 diab))).
    apply (PlusAngRs c b a (eq_sym (proj1 dibc))(eq_sym (proj1 diab))).
  }
  { intros abplbceqac.
    assert (Exab : exists (d e : Ray)(rode : da d = da e),
      [| a # b | diab |] = [| d, e | rode |]).
    { destruct (DrawSector ([| a # b | diab |])) as [ P H ].
      destruct P as [ d e rode ]. simpl in *.
      exists d, e, rode...
    }
    destruct Exab as [ d [ e [ rode abeqde ]]].
    destruct (DrawCongruentAngle_ccw e ([| b # c | dibc |]))
      as [ f [ roef efeqbc ]].
    symmetry in abeqde.
    rewrite <- abeqde in abplbceqac.
    rewrite <- efeqbc in abplbceqac.
    rewrite (PlusAngRs d e f) in abplbceqac.
    unfold ConvexAngleRs in *.
    apply <- (BetRs_EqOs a b c diab dibc diac).
    induction (%[a # c | diac]);
    induction (%[a # b | diab]);
    induction (%[b # c | dibc]); simpl in *; split...
    { assert (ApBeqC : [| d, e | rode |] +++ [| e, f | roef |]
        = [| d, f | eq_trans rode roef |]). { apply PlusAngRs. }
      assert (CpBeqA : [| d, f | eq_trans rode roef |] +++ [| e, f | roef |]
        = [| d, e | rode |]).
      { rewrite abplbceqac. rewrite abeqde. rewrite efeqbc.
        pir (proj1 diab) => (eq_trans (proj1 diac)(eq_sym (proj1 dibc))).
        apply (PlusAngRs a c b (proj1 diac)(eq_sym (proj1 dibc))).
      }
      rewrite <- CpBeqA in ApBeqC.
      rewrite <- PlusAs_assoc in ApBeqC.
      assert (ExH : [| d, f | eq_trans rode roef |]
        +++ ([| e, f | roef |] +++ [| e, f | roef |])
          = [| d, f | eq_trans rode roef |] +++ A0).
      { rewrite ApBeqC. symmetry. rewrite <- PlusAs_0_r... }
      apply PlusAs_cancel_l in ExH. apply ExpA_ColA in ExH.
      destruct ExH as [ efeqA0 | efeqA180 ].
      { rewrite efeqA0 in *. symmetry in efeqbc.
        apply EqNullAng in efeqbc. symmetry in efeqbc.
        apply nColRs_nColPs in dibc.
        destruct dibc as [ _ [ nbeqc _ ]]. contradiction.
      }
      rewrite efeqA180 in *. symmetry in efeqbc.
      apply EqStraightAng in efeqbc.
      apply OpRs_OpRs in efeqbc.
      apply OpRs_sym in efeqbc.
      apply nColRs_nColPs in dibc.
      destruct dibc as [ _ [ _ nbeqc ]].
      contradiction.
    }
    { assert (ApBeqC : [| d, e | rode |] +++ [| e, f | roef |]
        = [| d, f | eq_trans rode roef |]).
      { apply PlusAngRs. }
      assert (CpBeqA : [| d, e | rode |] +++ [| d, f | eq_trans rode roef |]
        = [| e, f | roef |]).
      { rewrite abplbceqac. rewrite abeqde. rewrite efeqbc.
        pir (proj1 dibc) => (eq_trans (eq_sym (proj1 diab))(proj1 diac)).
        apply (PlusAngRs b a c (eq_sym (proj1 diab))(proj1 diac)).
      }
      rewrite <- CpBeqA in ApBeqC.
      rewrite (PlusAs_assoc ([| d, e | rode |])([| d, e | rode |])
        ([| d, f | eq_trans rode roef |])) in ApBeqC.
      rewrite (PlusAng_comm ([| d, e | rode |] +++ [| d, e | rode |])
        ([| d, f | eq_trans rode roef |])) in ApBeqC.
      assert (ExH :
        [| d, f | eq_trans rode roef |]
        +++ ([| d, e | rode |] +++ [| d, e | rode |])
        = [| d, f | eq_trans rode roef |] +++ A0).
      { rewrite ApBeqC. symmetry. apply PlusAs_0_r. }
      apply PlusAs_cancel_l in ExH. apply ExpA_ColA in ExH.
      destruct ExH as [ efeqA0 | efeqA180 ].
      { rewrite efeqA0 in *. symmetry in abeqde.
        apply EqNullAng in abeqde. symmetry in abeqde.
        apply nColRs_nColPs in diab.
        destruct diab as [ _ [ nbeqc _ ]]. contradiction.
      }
      rewrite efeqA180 in *. symmetry in abeqde.
      apply EqStraightAng in abeqde. apply OpRs_OpRs in abeqde.
      apply OpRs_sym in abeqde. apply nColRs_nColPs in diab.
      destruct diab as [ _ [ _ nbeqc ]].
      contradiction.
    }
    { assert (ApBeqC : [| d, e | rode |] +++ [| e, f | roef |]
        = [| d, f | eq_trans rode roef |]).
      { apply PlusAngRs. }
      assert (CpBeqA : [| d, e | rode |]
        +++ [| d, f | eq_trans rode roef |] +++ [| e, f | roef |] = A0).
      { rewrite abeqde. rewrite efeqbc. rewrite abplbceqac.
        rewrite (PlusAngRs b a c). rewrite (PlusAngRs b c b).
        apply EqNullAng. reflexivity.
      }
      rewrite <- PlusAs_assoc in CpBeqA.
      rewrite (PlusAng_comm ([| d, f | eq_trans rode roef |])
        ([| e, f | roef |])) in CpBeqA.
      rewrite PlusAs_assoc in CpBeqA.
      rewrite ApBeqC in CpBeqA.
      apply ExpA_ColA in CpBeqA.
      destruct CpBeqA as [ dfeqA0 | dfeqA180 ].
      { rewrite dfeqA0 in *. symmetry in abplbceqac.
        apply EqNullAng in abplbceqac.
        apply nColRs_nColPs in diac.
        destruct diac as [ _ [ nbeqc _ ]].
        contradiction.
      }
      { rewrite dfeqA180 in *. symmetry in abplbceqac.
        apply EqStraightAng in abplbceqac.
        apply nColRs_nColPs in diac.
        destruct diac as [ _ [ _ nbeqc ]].
        apply OpRs_OpRs in abplbceqac.
        contradiction.
      }
    }
    { assert (ApBeqC : [| d, e | rode |] +++ [| e, f | roef |]
        = [| d, f | eq_trans rode roef |]).
      { apply PlusAngRs. }
      assert (CpBeqA : [| d, e | rode |]
        +++ [| d, f | eq_trans rode roef |] +++ [| e, f | roef |] = A0).
      { rewrite abeqde. rewrite efeqbc. rewrite abplbceqac.
        rewrite (PlusAngRs b a c). rewrite (PlusAngRs b c b ).
        apply EqNullAng. reflexivity.
      }
      rewrite <- PlusAs_assoc in CpBeqA.
      rewrite (PlusAng_comm ([| d, f | eq_trans rode roef |])
        ([| e, f | roef |])) in CpBeqA.
      rewrite PlusAs_assoc in CpBeqA.
      rewrite ApBeqC in CpBeqA.
      apply ExpA_ColA in CpBeqA.
      destruct CpBeqA as [ dfeqA0 | dfeqA180 ].
      { rewrite dfeqA0 in *. symmetry in abplbceqac.
        apply EqNullAng in abplbceqac.
        apply nColRs_nColPs in diac.
        destruct diac as [ _ [ nbeqc _ ]].
        contradiction.
      }
      { rewrite dfeqA180 in *. symmetry in abplbceqac.
        apply EqStraightAng in abplbceqac.
        apply OpRs_OpRs in abplbceqac.
        apply nColRs_nColPs in diac.
        destruct diac as [ _ [ _ nbeqc ]].
        contradiction.
      }
    }
    { assert (ApBeqC : [| d, e | rode |] +++ [| e, f | roef |]
        = [| d, f | eq_trans rode roef |]).
      { apply PlusAngRs. }
      assert (CpBeqA : [| d, e | rode |]
        +++ [| e, f | roef |] +++ [| d, f | eq_trans rode roef |] = A0).
      { rewrite abeqde. rewrite efeqbc. rewrite abplbceqac.
        rewrite (PlusAngRs a b c). rewrite (PlusAngRs a c a).
        apply EqNullAng. reflexivity.
      }
      rewrite ApBeqC in CpBeqA.
      apply ExpA_ColA in CpBeqA.
      destruct CpBeqA as [ dfeqA0 | dfeqA180 ].
      { rewrite dfeqA0 in *. symmetry in abplbceqac.
        apply EqNullAng in abplbceqac. apply nColRs_nColPs in diac.
        destruct diac as [ _ [ nbeqc _ ]]. symmetry in abplbceqac.
        contradiction.
      }
      { rewrite dfeqA180 in *. symmetry in abplbceqac.
        apply EqStraightAng in abplbceqac.
        apply OpRs_OpRs in abplbceqac.
        apply nColRs_nColPs in diac.
        destruct diac as [ _ [ _ nbeqc ]].
        apply OpRs_sym in abplbceqac.
        contradiction.
      }
    }
    { assert (ApBeqC : [| d, e | rode |] +++ [| e, f | roef |]
        = [| d, f | eq_trans rode roef |]).
      { apply PlusAngRs. }
      assert (CpBeqA : [| d, e | rode |]
        +++ [| e, f | roef |] +++ [| d, f | eq_trans rode roef |] = A0).
      { rewrite abeqde. rewrite efeqbc. rewrite abplbceqac.
        rewrite (PlusAngRs a b c). rewrite (PlusAngRs a c a).
        apply EqNullAng. reflexivity.
      }
      rewrite ApBeqC in CpBeqA.
      apply ExpA_ColA in CpBeqA.
      destruct CpBeqA as [ dfeqA0 | dfeqA180 ].
      { rewrite dfeqA0 in *. symmetry in abplbceqac.
        apply EqNullAng in abplbceqac.
        apply nColRs_nColPs in diac.
        destruct diac as [ _ [ nbeqc _ ]].
        symmetry in abplbceqac.
        contradiction.
      }
      { rewrite dfeqA180 in *. symmetry in abplbceqac.
        apply EqStraightAng in abplbceqac.
        apply nColRs_nColPs in diac.
        destruct diac as [ _ [ _ nbeqc ]].
        apply OpRs_OpRs in abplbceqac.
        apply OpRs_sym in abplbceqac.
        contradiction.
      }
    }
    { assert (ApBeqC : [| d, e | rode |] +++ [| e, f | roef |]
        = [| d, f | eq_trans rode roef |]).
      { apply PlusAngRs. }
      assert (CpBeqA : [| d, f | eq_trans rode roef |] +++ [| d, e | rode |]
        = [| e, f | roef |]).
      { rewrite abeqde. rewrite efeqbc. rewrite abplbceqac.
        rewrite (PlusAngRs c a b).
        pir (eq_trans (eq_sym (proj1 diac))(proj1 diab))
          => (eq_sym (proj1 dibc)).
      }
      rewrite (PlusAng_comm ([| d, f | eq_trans rode roef |])
        ([| d, e | rode |])) in CpBeqA.
      rewrite <- ApBeqC in CpBeqA. rewrite PlusAs_assoc in CpBeqA.
      rewrite (PlusAng_comm ([| d, e | rode |] +++ [| d, e | rode |])
        ([| e, f | roef |])) in CpBeqA.
      assert (ExH : [| e, f | roef |]
        +++ ([| d, e | rode |] +++ [| d, e | rode |])
        = [| e, f | roef |] +++ A0).
      { rewrite CpBeqA. symmetry. apply PlusAs_0_r. }
      apply PlusAs_cancel_l in ExH. apply ExpA_ColA in ExH.
      destruct ExH as [ dfeqA0 | dfeqA180 ].
      { rewrite dfeqA0 in *. symmetry in abeqde.
        apply EqNullAng in abeqde.
        apply nColRs_nColPs in diab.
        destruct diab as [ _ [ nbeqc _ ]].
        contradiction.
      }
      { rewrite dfeqA180 in *. symmetry in abeqde.
        apply EqStraightAng in abeqde.
        apply nColRs_nColPs in diab.
        destruct diab as [ _ [ _ nbeqc ]].
        apply OpRs_OpRs in abeqde.
        contradiction.
      }
    }
    { assert (ApBeqC : [| d, e | rode |] +++ [| e, f | roef |]
        = [| d, f | eq_trans rode roef |]).
      { apply PlusAngRs. }
      assert (CpBeqA : [| e, f | roef |] +++ [| d, f | eq_trans rode roef |]
        = [| d, e | rode |]).
      { rewrite abeqde. rewrite efeqbc. rewrite abplbceqac.
        rewrite (PlusAngRs b c a).
        pir (eq_trans (proj1 dibc)(eq_sym (proj1 diac)))
          => (eq_sym (proj1 diab)).
      }
      { rewrite (PlusAng_comm ([| e, f | roef |])
          ([| d, f | eq_trans rode roef |])) in CpBeqA.
        rewrite <- ApBeqC in CpBeqA.
        rewrite <- PlusAs_assoc in CpBeqA.
        assert (ExH : [| d, e | rode |]
          +++ ([| e, f | roef |] +++ [| e, f | roef |])
          = [| d, e | rode |] +++ A0).
        { rewrite CpBeqA. symmetry. apply PlusAs_0_r. }
        apply PlusAs_cancel_l in ExH. apply ExpA_ColA in ExH.
        destruct ExH as [ dfeqA0 | dfeqA180 ].
        { rewrite dfeqA0 in *. symmetry in efeqbc.
          apply EqNullAng in efeqbc.
          apply nColRs_nColPs in dibc.
          destruct dibc as [ _ [ nbeqc _ ]].
          contradiction.
        }
        { rewrite dfeqA180 in *. symmetry in efeqbc.
          apply EqStraightAng in efeqbc.
          apply nColRs_nColPs in dibc.
          destruct dibc as [ _ [ _ nbeqc ]].
          apply OpRs_OpRs in efeqbc.
          contradiction.
        }
      }
    }
  }
Qed.
Theorem BetPs_PlusConvexAngPs :
  forall (O A B C : Point)(nColAOB : ~ [ A, O, B ])
         (nColBOC : ~ [ B, O, C ])(nColAOC : ~ [ A, O, C ]),
  [ A # B # C ]
    -> [| A # O # B | nColAOB |] +++ [| B # O # C | nColBOC |]
     = [| A # O # C | nColAOC |].
Proof with eauto.
  intros O A B C nColAOB nColBOC nColAOC BetABC.
  assert (nOeqA : O <> A); dips.
  assert (nOeqB : O <> B); dips.
  assert (nOeqC : O <> C); dips.
  assert (exOA : exists a : Ray, {{ O # A | nOeqA }} = a).
  { exists ({{ O # A | nOeqA }})... }
  destruct exOA as [ a OAeqa ].
  assert (exOB : exists b : Ray, {{ O # B | nOeqB }} = b).
  { exists ({{ O # B | nOeqB }})... }
  destruct exOB as [ b OBeqb ].
  assert (exOC : exists c : Ray, {{ O # C | nOeqC }} = c).
  { exists ({{ O # C | nOeqC }})... }
  destruct exOC as [ c OCeqc ].
  assert (roab : da a = da b).
  { rewrite <- OAeqa. rewrite <- OBeqb. simpl... }
  assert (robc : da b = da c).
  { rewrite <- OBeqb. rewrite <- OCeqc. simpl... }
  assert (roac : da a = da c). { rewrite roab... }
  assert (diAB : ![{{ O # A | nOeqA }} # {{ O # B | nOeqB }}]); try split...
  assert (diBC : ![{{ O # B | nOeqB }} # {{ O # C | nOeqC }}]); try split...
  assert (diAC : ![{{ O # A | nOeqA }} # {{ O # C | nOeqC }}]); try split...
  assert (abAOB : [| {{ O # A | nOeqA }} # {{ O # B | nOeqB}} | diAB |]
    = [| A # O # B | nColAOB|]).
  { apply ConvexAngRs_ConvexAngPs. }
  rewrite <- abAOB.
  assert (bcBOC : [| {{ O # B | nOeqB }} # {{ O # C | nOeqC }} | diBC |]
    = [| B # O # C | nColBOC |]).
  { apply ConvexAngRs_ConvexAngPs. }
  rewrite <- bcBOC.
  assert (acAOC : [| {{ O # A | nOeqA }} # {{ O # C | nOeqC }} | diAC |]
    = [| A # O # C | nColAOC|]).
  { apply ConvexAngRs_ConvexAngPs. }
  rewrite <- acAOC.
  apply BetRs_PlusAngRs. do 2 split; simpl...
  apply nColPs_BetPs_BR; auto.
  ncolperps.
Qed.

End ANGLE_ADDITION.

Notation " A +++ B "
  := (PlusA A B)
  (at level 65).

(*****************************************************************************)
(* 20 *) Section SUPPLEMENTARY.
Context `{ cc : Concentricals }.
Context  { an : Angles on }.
Context  { sp : Superpositions on }.
(*****************************************************************************)

(** Problem #42 *)
Definition DrawExplementaryAngle :
  forall (A : Angle),
  { B : Angle | A +++ B = A0 }.
Proof with eauto.
  intros A.
  destruct (DrawSector A) as [[ a b roab ] Hab ].
  exists ([| b, a | sym_eq roab |]); subst.
  rewrite PlusAngRs.
  pir (eq_trans roab (eq_sym roab)) => (eq_refl (da a)).
  apply (proj2_sig NullAng).
Defined.

Definition Exp (A : Angle)
  := proj1_sig (DrawExplementaryAngle A).
Definition ExpDef (A : Angle)
  := proj2_sig (DrawExplementaryAngle A).

(** Theorem #76 *)
Theorem PlusExpAngRs :
  forall (a b : Ray)(roab : da a = da b),
  [| a, b | roab |] +++ [| b, a | eq_sym roab |] = A0.
Proof.
  intros a b roab.
  rewrite PlusAngRs.
  apply EqNullAng.
  reflexivity.
Qed.

(** Theorem #77 *)
Theorem UniqueExpAng :
  forall (A B C : Angle),
  A +++ B = A0
    -> A +++ C = A0
    -> B = C.
Proof.
  intros A B C AB AC.
  destruct (DrawSector A) as [[ a b roab ] abA ]; subst.
  rewrite <- (PlusExpAngRs a b roab) in AB.
  rewrite <- (PlusExpAngRs a b roab) in AC.
  apply (PlusAs_cancel_l ([| a, b | roab |]) B ([| b, a | eq_sym roab |]))
    in AB... rewrite AB.
  apply (PlusAs_cancel_l ([| a, b | roab |]) C ([| b, a | eq_sym roab |]))
    in AC... rewrite AC.
  reflexivity.
Qed.
Lemma PlusAngRs_ExpAs :
  forall (a b : Ray)(A : Angle)(roab : da a = da b),
  [| a, b | roab |] +++ A = A0
    -> A = [| b, a | eq_sym roab |].
Proof with eauto.
  intros a b A roab abpA.
  rewrite <- (PlusExpAngRs a b roab) in abpA.
  apply (PlusAs_cancel_l ([| a, b | roab |]) A ([| b, a | eq_sym roab |]))...
Qed.

Lemma PlusStraightAngEqNullAng :
  A180 +++ A180 = A0.
Proof with eauto.
  unfold PlusA, PlusAngleDef.
  destruct (DrawSector A180) as [[ a b roab ] abeqA180 ].
  destruct (DrawCongruentAngle_ccw b A180)
    as [ c [ robc bceqA180 ]]. simpl.
  apply (EqStraightAng a b roab) in abeqA180.
  apply OpRs_OpRs in abeqA180.
  apply (EqStraightAng b c robc) in bceqA180.
  apply OpRs_OpRs in bceqA180.
  assert (aeqc : a == c). { apply (OpRs_trans a b c)... }
  apply (EqNullAng a c(eq_trans roab robc)) in aeqc...
Qed.

Example ExpExpEqA :
  forall (A : Angle),
  Exp (Exp A) = A.
Proof.
  intros A.
  unfold Exp, DrawExplementaryAngle.
  destruct (DrawSector A) as [[ a b roab ] abA ]; simpl.
  destruct (DrawSector ([| b, a | eq_sym roab |]))
    as [[ c d rocd ] cdA ]; simpl.
  rewrite <- abA in *. clear abA.
  pir roab => (eq_sym (eq_sym roab)).
  apply (EqAs_EqExpAs c d b a); auto.
  pir (eq_sym (eq_sym (eq_sym roab))) => (eq_sym roab).
Qed.

Lemma ExpAs_iA_xA :
  forall A B : Angle,
  A +++ B = A0
    -> (Convex A <-> Reflex B).
Proof with eauto.
  intros A B ApB; unfold PlusA, PlusAngleDef in *.
  split.
  { intros iA.
    destruct (DrawSector A) as [[ a b roab ] abA ].
    destruct (DrawCongruentAngle_ccw b B) as [ c [ robc bcB ]].
    apply EqNullAng in ApB; subst.
    rewrite <- (EqAs_EqRs b a c (eq_sym roab) robc) in ApB.
    rewrite <- ApB. unfold Convex in *. destruct iA as [[ H1 H2 ] H3 ].
    assert (diab : ![ a # b ]). { destruct (nColRs_nColAs a b roab)... }
    assert (diba : ![ b # a ]). { apply (nColRs_sym a b diab). }
    assert (H7 : %[ a # b | diab] = negb (%[ b # a | diba])).
    { eapply (DiOsRs a b diab diba). }
    unfold Reflex.
    destruct (nColRs_nColAs b a (eq_sym roab)) as [ H8 H9 ]...
    destruct (H9 diba) as [ G1 G2 ].
    exists (conj G1 G2).
    destruct (nColRs_nColAs b a (eq_sym roab)) as [ G3 G4 ]...
    assert (abTs : %[a # b | diab] = true).
    { rewrite (OsRs_OsAs a b roab diab (conj H1 H2))... }
    assert (baTs : %[b # a | diba] = false).
    { induction (%[a # b | diab]), (%[b # a | diba])... }
    rewrite (OsRs_OsAs b a (eq_sym roab) diba (conj G1 G2)) in baTs...
  }
  { intros xB.
    destruct (DrawSector A) as [[ a b roab ] abA ].
    destruct (DrawCongruentAngle_ccw b B) as [ c [ robc bcB ]].
    apply EqNullAng in ApB; subst.
    rewrite <- (EqAs_EqRs b a c (eq_sym roab) robc) in ApB.
    rewrite <- ApB in xB.
    unfold Convex in *.
    destruct xB as [[ H1 H2 ] H3 ].
    assert (diba : ![ b # a ]).
    { destruct (nColRs_nColAs b a (eq_sym roab))... }
    assert (diab : ![ a # b ]). { apply (nColRs_sym b a diba). }
    assert (H7 : %[ b # a | diba] = negb (%[ a # b | diab])).
    { apply (DiOsRs b a diba diab). }
    destruct (nColRs_nColAs a b roab) as [ H8 H9 ]...
    destruct (H9 diab) as [ G1 G2 ].
    exists (conj G1 G2).
    destruct (nColRs_nColAs a b roab) as [ G3 G4 ]...
    assert (baTs : %[b # a | diba] = false).
    { rewrite (OsRs_OsAs b a (eq_sym roab) diba (conj H1 H2))... }
    assert (abTs : %[a # b | diab] = true).
    { induction (%[a # b | diab]), (%[b # a | diba])... }
    rewrite <- (OsRs_OsAs a b roab diab (conj G1 G2))...
  }
Qed.

Definition ConvexAng_ConvexSupAng :
  forall (A B : Angle),
  Convex A
    -> A +++ B = A180
    -> Convex B.
Proof with eauto.
  intros A B iA AB180.
  destruct (DrawSector A) as [[ a b roab ] abA ]; simpl.
  destruct abA.
  destruct (DrawCongruentAngle_ccw b B) as [ c [ robc bcB ]].
  destruct bcB. rewrite PlusAngRs in AB180.
  apply EqStraightAng in AB180.
  assert (diab : ![ a # b ]). { apply (ConvexAngRs_nColRs a b roab)... }
  apply (ConvexAngRs_Left a b roab diab) in iA.
  apply OpRs_OpRs in AB180.
  assert (dibc : ![ b # c ]). { apply (nColRs_OpRs_nColRs a b c)... }
  eapply (OpRs_EqOs_Left a b c diab dibc) in AB180.
  apply (ConvexAngRs_Left b c robc dibc). rewrite <- AB180...
Qed.

(** Problem #43 *)
Definition DrawSupplementaryAngle :
  forall (A : Angle),
  Convex A
    -> { B : Angle | A +++ B = A180 }.
Proof with eauto.
  intros A iab.
  destruct (DrawSector A) as [[ a b roab ] abA ].
  destruct (DrawOpRay a) as [ c copa ].
  assert (roca : da c = da a). { destruct copa... }
  assert (robc : da b = da c). { rewrite <- roab... }
  exists ([| b, c | robc |]).
  rewrite <- abA. rewrite PlusAngRs.
  rewrite <- abA in *. clear dependent A.
  apply OpRs_OpRs in copa.
  assert (diab : ![ a # b ]). { apply (ConvexAngRs_nColRs a b roab iab). }
  assert (dibc : ![ b # c ]). { apply (nColRs_OpRs_nColRs a b c diab)... }
  apply EqStraightAng... apply OpRs_OpRs...
Defined.

Definition Sup (A : Angle)(iA : Convex A)
  := proj1_sig (DrawSupplementaryAngle A iA).
Definition SupDef (A : Angle)(iA : Convex A)
  := proj2_sig (DrawSupplementaryAngle A iA).

(** Theorem #78 *)
(** Euclid, Book I : Proposition 13. *)
(* If a straight line stands on a straight line, then it makes either
  two right angles or angles whose sum equals two right angles. *)
Proposition OpRs_SupConvexAngRs :
  forall (a b : Ray)(diab : ![ a # b ])(diba : ![ b # !a ]),
  [| a # b | diab |] +++ [| b # !a | diba |] = A180.
Proof with eauto.
  intros a b diab diba.
  assert (roab : da a = da b). { destruct diab... }
  assert (roba : da b = da (!a)). { destruct diba... }
  assert (abeqba : %[ a # b | diab ] = %[ b # !a | diba ]).
  { apply (OpRs_EqOs_Left a b (!a) diab diba).
    apply OpOpRs...
  }
  assert (ExT: exists T, %[ b # !a | diba ] = T).
  { exists (%[ b # !a | diba ])... }
  destruct ExT as [ T baT ]. rewrite baT in *.
  induction T.
  { apply (LeftOrientation_EqAs a b roab diab) in abeqba.
    apply (LeftOrientation_EqAs b (!a) roba diba) in baT.
    rewrite <- abeqba. rewrite <- baT. rewrite PlusAngRs.
    apply EqStraightAng... apply OpRs_OpRs... apply OpOpRs...
  }
  { apply (RightOrientation_EqAs a b roab diab) in abeqba.
    apply (RightOrientation_EqAs b (!a) roba diba) in baT.
    rewrite <- abeqba. rewrite <- baT. rewrite PlusAng_comm.
    rewrite PlusAngRs. apply EqStraightAng.
    apply OpRs_OpRs; reflexivity...
  }
Qed.
Theorem BetPs_SupAngPs :
  forall (O A B C : Point)(nColAOB : ~ [ A, O, B ])(nColBOC : ~ [ B, O, C ]),
  [ A # O # C ]
    -> [| A # O # B | nColAOB |] +++ [| B # O # C | nColBOC |] = A180.
Proof with eauto.
  intros O A B C nColAOB nColBOC BetAOC.
  assert (nOeqA : O <> A); dips.
  assert (nOeqB : O <> B); dips.
  assert (nOeqC : O <> C); dips.
  assert (exOA : exists a : Ray, {{ O # A | nOeqA }} = a).
  { exists ({{ O # A | nOeqA }})... }
  destruct exOA as [ a OAeqa ].
  assert (exOB : exists b : Ray, {{ O # B | nOeqB }} = b).
  { exists ({{ O # B | nOeqB }})... }
  destruct exOB as [ b OBeqb ].
  assert (exOC : exists c : Ray, {{ O # C | nOeqC }} = c).
  { exists ({{ O # C | nOeqC }})... }
  destruct exOC as [ c OCeqc ].
  assert (roab : da a = da b).
  { rewrite <- OAeqa. rewrite <- OBeqb. simpl... }
  assert (robc : da b = da c).
  { rewrite <- OBeqb. rewrite <- OCeqc. simpl... }
  apply <- (OpRs_BetPs A O C nOeqA nOeqC) in BetAOC.
  assert (diba : ![ ({{ O # B | nOeqB }}) # !({{ O # A | nOeqA }}) ]).
  { apply (nColOpRs_2 ({{ O # B | nOeqB }})({{ O # A | nOeqA }})).
    apply nColRs_sym. repeat split...
  }
  assert (dibc : ![ ({{ O # B | nOeqB }}) # ({{ O # C | nOeqC }}) ]).
  { repeat split... }
  rewrite <- (OpRs_SupConvexAngRs ({{ O # A | nOeqA }})({{ O # B | nOeqB }})
    (conj eq_refl nColAOB) diba).
  rewrite (EqConvexAngRsPs A O B nOeqA nOeqB nColAOB).
  assert (H : [|{{O # B | nOeqB}} # ! ({{O # A | nOeqA}}) | diba|] =
    [|{{O # B | nOeqB}} # ({{O # C | nOeqC}}) | dibc|]).
  { apply (EqConvexAs_inv ({{O # B | nOeqB}}) (! {{O # A | nOeqA}})
    ({{O # B | nOeqB}}) ({{O # C | nOeqC}})); try reflexivity.
    rewrite BetAOC. symmetry. apply OpOpRs.
  }
  rewrite H. pir dibc => (conj (eq_refl O) nColBOC)...
  rewrite (EqConvexAngRsPs B O C nOeqB nOeqC).
  reflexivity.
Qed.

(** Theorem #79 *)
Theorem UniqueSupAng :
  forall (A B C : Angle),
  Convex A
    -> A +++ B = A180
    -> A +++ C = A180
    -> B = C.
Proof with eauto.
  intros A B C iA AB AC.
  destruct (DrawSector A) as [[ a b roab ] abA ]; subst.
  assert (diab : ![a # b]). { apply (ConvexAngRs_nColRs a b roab)... }
  apply (ConvexAngRs_Left a b roab diab) in iA.
  apply (LeftOrientation_EqAs a b roab diab) in iA. rewrite iA in *.
  rewrite <- (OpRs_SupConvexAngRs a b diab (nColOpRs_4 a b diab)) in AB.
  rewrite <- (OpRs_SupConvexAngRs a b diab (nColOpRs_4 a b diab)) in AC.
  apply (PlusAs_cancel_l ([|a # b | diab|]) B
    ([|b # ! a | nColOpRs_4 a b diab|])) in AB... rewrite AB.
  apply (PlusAs_cancel_l ([|a # b | diab|]) C
    ([|b # ! a | nColOpRs_4 a b diab|])) in AC... 
Qed.

Definition ExpPlusAs_PlusSupAs :
  forall (A B : Angle)(iA : Convex A)(iB : Convex B),
  Exp (A +++ B) = (Sup A iA) +++ (Sup B iB).
Proof with eauto.
  intros *.
  unfold Sup, DrawSupplementaryAngle.
  destruct (DrawSector A) as [[ a b roab ] abA ]; simpl.
  destruct (DrawOpRay a ) as [ a' aopa' ]; simpl.
  destruct (DrawSector B) as [[ c d rocd ] cdB ]; simpl.
  destruct (DrawOpRay c ) as [ c' copc' ]; simpl.
  assert (roaa' : da a = da a'). { destruct aopa' as [ H1 H2 ]... }
  assert (rocc' : da c = da c'). { destruct copc' as [ H3 H4 ]... }
  assert (roba' : da b = da a'). { rewrite <- roab... }
  pir (eq_ind (da a)(fun p : Point => p = da a')
    (eq_sym (eq_sym roaa'))(da b) roab)
    => roba'. rewrite <- abA.
  assert (rodc' : da d = da c'). { rewrite <- rocd... }
  pir (eq_ind (da c)(fun p : Point => p = da c')
    (eq_sym (eq_sym rocc'))(da d) rocd)
    => rodc'. rewrite <- cdB.
  unfold Exp, DrawExplementaryAngle.
  destruct (DrawSector ([| a, b | roab |] +++ [| c, d | rocd |]))
    as [[ e f roef ] efC ]; simpl.
  clear dependent A. clear dependent B.
  destruct (DrawCongruentAngle_cw a ([| c, d | rocd |]))
    as [ x [ roxa H ]].
  rewrite <- H in efC at 1. rewrite PlusAng_comm in efC.
  rewrite (PlusAngRs x a b) in efC.
  rewrite (EqAs_EqExpAs e f x b roef (eq_trans roxa roab))...
  assert (robx : da b = da x). { apply (eq_sym (eq_trans roxa roab)). }
  pir (eq_sym (eq_trans roxa roab)) => robx.
  assert (roa'x : da a' = da x). { rewrite <- roba'... }
  assert (baax : [| d, c' | rodc' |] = [| a', x | roa'x |]).
  { destruct (DrawOpRay x ) as [ x' xopx ]; simpl.
    assert (roax' : da a = da x'). { destruct xopx... rewrite <- H0... }
    rewrite (OpOpRs_EqVertAs a' x a x' roa'x roax')...
    { symmetry in H. eapply (OpRs_EqSupAngRs c d c' x a x')...
      apply OpRs_OpRs... apply OpRs_OpRs...
    }
    { apply OpRs_OpRs in aopa'. apply OpRs_sym in aopa'... }
    apply OpRs_OpRs...
  }
  destruct aopa' as [ H1 H2 ]. destruct copc' as [ H3 H4 ].
  pir (eq_ind (da a)(fun p : Point => p = da a')
    (eq_sym (eq_sym H1))(da b) roab) => roba'.
  pir (eq_ind (da c)(fun p : Point => p = da c')
    (eq_sym (eq_sym H3))(da d) rocd) => rodc'.
  rewrite baax. rewrite PlusAngRs.
  pir(eq_trans roba' roa'x) => robx.
Qed.

(** Problem #44 *)
Definition DrawRightAngle :
  { A : Angle | Convex A /\ A +++ A = A180 }.
Proof with eauto.
  destruct (DrawPoint) as [ A _ ].
  destruct (DrawDistinctPoint A) as [ B nAeqB ].
  destruct (DrawNonCollinearPoint A B nAeqB) as [ P nColABP ].
  destruct (DrawEquilateralTriangleSS A B P nColABP)
    as [ C [ AB_PC [ BC_AB AC_AB ]]].
  assert (nColABC : ~ [ A, B, C ]). { eapply SH_nColPs. apply SHb_sym... }
  clear dependent P.
  destruct (DrawMiddlePoint A B nAeqB) as [ O [ BetAOB OA_OB ]].
  assert (nColAOC : ~ [ A, O, C ]).
  { contradict nColABC.
    destruct nColABC as [ x [ Aox [ Box Cox ]]].
    exists x; repeat split; incpt 2.
  }
  assert (nColBOC : ~ [ B, O, C ]).
  { contradict nColABC.
    destruct nColABC as [ x [ Aox [ Box Cox ]]].
    exists x; repeat split; incpt 2.
  }
  exists ([| A # O # C | nColAOC |]).
  split.
  { apply ConvexAngPs. }
  { assert (EqTr : {{ A # O # C | nColAOC }} :=: {{ B # O # C | nColBOC }}).
  { apply (SSS A O C B O C nColAOC)... rewrite SegPs_sym.
    rewrite OA_OB. apply SegPs_sym.
    rewrite SegPs_sym. rewrite AC_AB.
    rewrite <- BC_AB. apply SegPs_sym.
  }
  assert (AOC_BOC : [| A # O # C | nColAOC |] = [| B # O # C | nColBOC |]).
  { destruct EqTr as [ _ [ _ [ _ [ AOC_BOC _ ]]]]; tauto. }
    rewrite AOC_BOC at 2. erewrite (ConvexAngPs_sym B O C).
    apply BetPs_SupAngPs; auto.
  }
  Unshelve. ncolperps.
Defined.

Definition A90 : Angle
  := proj1_sig DrawRightAngle.
Definition DefA90
  := proj2_sig DrawRightAngle.

(** Theorem #80 *)
Theorem UniqueRightAngle :
  forall A : Angle,
  Convex A
    -> A +++ A = A180
    -> A = A90.
Proof with eauto.
  intros A iab AsupA.
  destruct (DrawSector A) as [[ a b roab ] abA ]; simpl in *.
  rewrite <- abA in iab.
  destruct (DrawCongruentAngle_ccw b A) as [ c [ robc bcA ]].
  assert (acA180 : [| a, c | eq_trans roab robc |] = A180).
  { rewrite <- (PlusAngRs a b c roab robc).
    rewrite bcA. rewrite abA...
  }
  apply EqStraightAng in acA180.
  assert (ibc : Convex ([| b, c | robc |])). { rewrite bcA. rewrite <- abA... }
  destruct (DrawCongruentAngle_ccw a A90) as [ b' [ roab' ab'A90 ]].
  destruct (DrawCongruentAngle_ccw b' A90) as [ c' [ rob'c' b'c'A90 ]].
  assert (DefA90 : Convex A90 /\ A90 +++ A90 = A180).
  { exact (proj2_sig DrawRightAngle). }
  destruct DefA90 as [ IntA90 A9090 ].
  assert (iab' : Convex ([| a, b' | roab' |])). { rewrite ab'A90... }
  assert (ac'A180 : ([| a, c' | eq_trans roab' rob'c' |]) = A180).
  { rewrite <- (PlusAngRs a b' c' roab' rob'c').
    rewrite b'c'A90. rewrite ab'A90...
  }
  apply EqStraightAng in ac'A180.
  assert (ceqc' : c == c').
  { apply (OpRs_trans c a c')... apply OpRs_OpRs in acA180.
    apply OpRs_sym in acA180... apply OpRs_OpRs in ac'A180...
  }
  assert (rob'c : da b' = da c). { rewrite <- roab'. rewrite roab... }
  assert (b'cA90 : ([| b', c | rob'c |]) = A90).
  { rewrite <- b'c'A90.
    apply (EqAngRs_inv b' c b' c' rob'c rob'c'); try reflexivity...
  }
  clear dependent c'. rewrite <- ab'A90. rewrite <- abA.
  assert (ib'c : Convex ([| b', c | rob'c |])). { rewrite b'cA90... }
  cut (b == b'). { intros beqb'. apply (EqAs_EqRs a b b')... }
  destruct (classic (b == b')) as [ beqb' | nbeqb' ]...
  assert (diab : ![ a # b ]). { apply (ConvexAngRs_nColRs a b roab iab). }
  assert (diab' : ![ a # b' ]). { apply (ConvexAngRs_nColRs a b' roab' iab'). }
  assert (dibc : ![ b # c ]). { apply (ConvexAngRs_nColRs b c robc ibc). }
  assert (dib'c : ![ b' # c ]). { apply (ConvexAngRs_nColRs b' c rob'c ib'c). }
  assert (abc : ![ a # b, b' ]).
  { apply <- (SameSideRs_EqOs a b b' diab diab').
    apply -> ConvexAngRs_Left in iab'. rewrite iab'.
    apply -> ConvexAngRs_Left...
  }
  apply -> (ConvexAngRs_Left a b' roab' diab') in iab'.
  apply -> (LeftOrientation_EqAs a b' roab' diab') in iab'.
  apply -> (ConvexAngRs_Left a b roab diab) in iab.
  apply -> (LeftOrientation_EqAs a b roab diab) in iab.
  apply -> (ConvexAngRs_Left b' c rob'c dib'c) in ib'c.
  apply -> (LeftOrientation_EqAs b' c rob'c dib'c) in ib'c.
  apply -> (ConvexAngRs_Left b c robc dibc) in ibc.
  apply -> (LeftOrientation_EqAs b c robc dibc) in ibc.
  destruct (DecideRaysOrderOnSameSide a b b' nbeqb' abc) as [ abb' | ab'b ]...
  { assert (cb'b : ![ c # b' # b]).
    { apply (BetRs_inv (!a) b' b c b' b ); try reflexivity...
      { apply OpRs_OpRs in acA180.
        apply OpRs_sym in acA180.
        rewrite acA180. reflexivity.
      }
      apply BetRs_PerBetRs. apply BetRs_sym.
      apply (BetRs_inv a b b' (!(!a)) b b'); try reflexivity...
      apply OpOpRs.
    }
    { destruct (BetRs_nColRs a b b' abb') as [ ab [ bb' ab' ]].
      destruct (BetRs_nColRs c b' b cb'b) as [ cb' [ b'b cb ]].
      assert (b'a : ![ b' # a ]). { apply (nColRs_sym a b' ab'). }
      assert (ba : ![ b # a ]). { apply (nColRs_sym a b ab). }
      assert (ab_ab' : [| a # b | ab |] <<< [| a # b' | ab' |]).
      { apply (BetRs_LtA a b b')... }
      assert (cb'_cb : [| c # b' | cb' |] <<< [| c # b | cb |]).
      { apply (BetRs_LtA c b' b)... }
      pir diab => ab. pir diab' => ab'.
      rewrite <- iab' in ab_ab'. rewrite <- iab in ab_ab'.
      rewrite (ConvexAngRs_sym c b' cb' dib'c) in cb'_cb.
      rewrite <- ib'c in cb'_cb.
      rewrite (ConvexAngRs_sym c b cb dibc) in cb'_cb.
      rewrite <- ibc in cb'_cb. rewrite abA in ab_ab'.
      rewrite ab'A90 in ab_ab'. rewrite bcA in cb'_cb.
      rewrite b'cA90 in cb'_cb.
      apply LtA_asymm in cb'_cb.
      contradiction.
    }
  }
  { assert (cbb' : ![ c # b # b']).
    { apply (BetRs_inv (!a) b b' c b b' ); try reflexivity...
      { apply OpRs_OpRs in acA180. apply OpRs_sym in acA180.
        rewrite acA180; reflexivity.
      }
      apply BetRs_PerBetRs. apply BetRs_sym.
      apply (BetRs_inv a b' b (!(!a)) b' b); try reflexivity; auto.
      apply OpOpRs.
    }
    destruct (BetRs_nColRs a b' b ab'b) as [ ab' [ b'b ab ]].
    destruct (BetRs_nColRs c b b' cbb') as [ cb [ bb' cb' ]].
    assert (ba : ![ b # a ]). { apply (nColRs_sym a b ab). }
    assert (b'a : ![ b' # a ]). { apply (nColRs_sym a b' ab'). }
    assert (ab'_ab : [| a # b' | ab' |] <<< [| a # b | ab |]).
    { apply (BetRs_LtA a b' b)... }
    assert (cb_cb' : [| c # b | cb |] <<< [| c # b' | cb'|]).
    { apply (BetRs_LtA c b b')... }
    pir diab => ab. pir diab' => ab'.
    rewrite <- iab' in ab'_ab. rewrite <- iab in ab'_ab.
    rewrite (ConvexAngRs_sym c b' cb' dib'c) in cb_cb'.
    rewrite <- ib'c in cb_cb'.
    rewrite (ConvexAngRs_sym c b cb dibc) in cb_cb'.
    rewrite <- ibc in cb_cb'.
    rewrite abA in ab'_ab. rewrite ab'A90 in ab'_ab.
    rewrite bcA in cb_cb'. rewrite b'cA90 in cb_cb'.
    apply LtA_asymm in cb_cb'.
    contradiction.
  }
Qed.
Theorem EqSupAngPs_RightAngPs :
  forall (O A B C : Point)
    (nColAOC : ~ [ A, O, C ])(nColCOB : ~ [ C, O, B ]),
  [ A # O # B ]
    -> [| A # O # C | nColAOC |] = [| C # O # B | nColCOB |]
    -> [| A # O # C | nColAOC |] = A90.
Proof with eauto.
  intros * BetAOB AOC_COB.
  apply UniqueRightAngle.
  { apply ConvexAngPs. }
  { rewrite AOC_COB at 2. apply BetPs_SupAngPs... }
Qed.

Lemma SupA90_EqA90 :
  forall A : Angle,
  A90 +++ A = A180
    -> A = A90.
Proof with eauto.
  intros A SupA90.
  assert (DefA90 : Convex A90 /\ A90 +++ A90 = A180).
  { exact (proj2_sig DrawRightAngle). }
  destruct DefA90 as [ IntA90 A9090 ].
  apply (PlusAs_cancel_l A90 A).
  rewrite SupA90...
Qed.

Lemma RightAngPs_RightSupAngPs :
  forall (O A B C : Point)
    (AOB : ~ [ A, O, B ])(BOC : ~ [ B, O, C ]),
  [ A # O # C ]
    -> [| A # O # B | AOB |] = A90
    -> [| B # O # C | BOC |] = A90.
Proof with eauto.
  intros * BetAOC AOB90.
  apply SupA90_EqA90.
  rewrite <- AOB90.
  apply BetPs_SupAngPs...
Qed.

Definition DecideAngleClassification :
  forall (A : Angle),
  A <> A0
    -> { Convex A } + { Reflex A } + { B : Angle | A = A90 +++ B /\ Convex B }.
Proof with eauto.
  intros A nAeqA0.
  destruct (DrawSector A) as [[ a c roac ] acA ]; simpl in *.
  rewrite <- acA in *. clear dependent A.
  assert (naeqc : a =/= c). { contradict nAeqA0. apply EqNullAng... }
  destruct (DrawCongruentAngle_ccw a A90) as [ b H ].
  assert (roab : da a = da b). { destruct H as [ roab abeqdc ]... }
  assert (abA90 : [| a, b | roab |] = A90).
  { destruct H as [ x abeqdc ]... pir x => roab. }
  clear H.
  assert (diab : ![ a # b ]).
  { apply (ConvexAngRs_nColRs a b roab). rewrite abA90.
    apply (proj2_sig DrawRightAngle).
  }
  destruct (DecideRayDirection_NES a b c roac naeqc diab)
    as [[ H1 | H2 ]| H3 ].
  { do 2 left.
    assert (diac : ![ a # c ]).
    { destruct (SameSideRs_nColRs a b c)... }
    apply (ConvexAngRs_Left a c roac diac).
    rewrite <- ((proj1 (SameSideRs_EqOs a b c diab diac)) H1).
    apply (ConvexAngRs_Left a b roab diab). rewrite abA90.
    apply (proj2_sig DrawRightAngle).
  }
  { left; right.
    destruct (OppositeSideRs_nColRs a b c) as [ _ diac ]...
    apply (ReflexAngRs_Right a c roac diac).
    assert (abLeft : %[ a # b | diab] = true).
    { apply (ConvexAngRs_Left a b roab diab). rewrite abA90.
      apply (proj2_sig DrawRightAngle).
    }
    apply (proj1 (OppositeSideRs_DiOs a b c diab diac)) in H2.
    rewrite abLeft in H2.
    induction (%[ a # c | diac])...
  }
  { right.
    destruct (OppositeSideRs_nColRs b a c) as [ _ dibc ]...
    assert (abLeft : %[ a # b | diab] = true).
    { apply (ConvexAngRs_Left a b roab diab). rewrite abA90.
      apply (proj2_sig DrawRightAngle).
    }
    assert (diba : ![ b # a ]). { apply nColRs_sym... }
    assert (H : %[ a # b | diab ] = negb (%[ b # a | diba ])).
    { eapply (DiOsRs a b diab)... }
    assert (bcLeft : %[ b # c | dibc] = true).
    { apply (proj1 (OppositeSideRs_DiOs b a c diba dibc)) in H3.
      rewrite abLeft in *.
      induction (%[ b # c | dibc]), (%[ b # a | diba])...
    }
    assert (robc : da b = da c).
    { apply (eq_trans (eq_sym roab) roac). }
    apply (ConvexAngRs_Left b c robc) in bcLeft.
    exists ([| b, c | robc |]); split...
    rewrite <- abA90. symmetry. pir roac => (eq_trans roab robc).
    apply (PlusAngRs a b c)...
  }
Defined.

Definition ConvexAs_nNullSumAs :
  forall (A B : Angle),
  Convex A
    -> Convex B
    -> A +++ B <> A0.
Proof with eauto.
  intros A B iA iB.
  destruct (DrawSector A) as [[ a b roab ] abA ].
  destruct (DrawCongruentAngle_cw a B) as [ c [ roca caB ]].
  subst. rewrite PlusAng_comm. rewrite PlusAngRs.
  apply ConvexAngRs_ReflexAngRs in iA. apply ReflexAng_nAs in iA.
  destruct iA as [ _ [ _ iA ]].
  contradict iA. apply EqNullAng in iA.
  rewrite <- (EqAngRs_inv c a b a roca)...
  try reflexivity.
Qed.

Lemma ConvexAs_LtSumAs :
  forall (A B : Angle),
  Convex A
    -> Convex B
    -> A <<< A +++ B.
Proof with eauto.
  intros A B iA iB.
  destruct (AngleClassification (A +++ B))
    as [ AB0 |[ AB180 |[ iAB | xAB ]]]...
  { apply -> (ExpAs_iA_xA A B) in iA...
    assert (B = Exp A).
    { rewrite <- (ExpDef A) in AB0.
      apply (PlusAs_cancel_l A B (Exp A))...
    }
    apply ConvexAng_nAs in iB.
    destruct iB as [ _ [ _ iB ]]; contradiction.
  }
  { rewrite AB180. apply (A0_iA_A180 A) in iA. destruct iA... }
  { destruct (DrawSector A) as [[ a b roab ] abA ].
    destruct abA.
    destruct (DrawCongruentAngle_ccw b B) as [ c [ robc bcB ]].
    destruct bcB.
    rewrite PlusAngRs in *.
    apply iAs_iAs_LtAs_BetRs...
    assert (diab : ![ a # b ]). { apply (ConvexAngRs_nColRs a b roab iA). }
    assert (dibc : ![ b # c ]). { apply (ConvexAngRs_nColRs b c robc iB). }
    assert (diac : ![ a # c ]).
    { apply (ConvexAngRs_nColRs a c (eq_trans roab robc) iAB). }
    eapply (BetRs_EqOs a b c diab dibc diac).
    apply -> (ConvexAngRs_Left a b roab diab) in iA.
    apply -> (ConvexAngRs_Left b c robc dibc) in iB.
    apply -> (ConvexAngRs_Left a c (eq_trans roab robc) diac) in iAB.
    rewrite iA. rewrite iB. rewrite iAB...
  }
  { unfold LtA. right. left. split... }
Qed.

Lemma ConvexAs_LtA_BetRs :
  forall (a b c : Ray)(robc : da b = da c)(roac : da a = da c),
  Convex ([| b, c | robc |])
    -> Convex ([| a, c | roac |])
    -> ([| b, c | robc |] <<< [| a, c | roac |] <-> ![ a # b # c ]).
Proof with eauto.
  intros a b c roab roac ibc iac.
  split.
  { intro bcLTac.
    apply BetRs_sym.
    eapply (xA_xA_LtAs_BetRs c b a).
    { apply (ConvexAngRs_ReflexAngRs b c roab)... }
    { apply (ConvexAngRs_ReflexAngRs a c roac)... }
    apply (LtA_LtExpA b c a c roab roac)...
    destruct ( proj1 (ConvexAng_nAs ([| b, c | roab |])) ibc) as [ H1 H2 ]...
    contradict H1. apply EqNullAng...
  }
  { intros abc.
    pir roab => (eq_sym (eq_sym roab)).
    pir roac => (eq_sym (eq_sym roac)).
    apply (LtA_LtExpA c a c b (eq_sym roac)(eq_sym roab))...
    { destruct ( proj1 (ConvexAng_nAs ([| a, c | eq_sym (eq_sym roac) |])) iac)
        as [ H1 H2 ]...
      contradict H1. apply EqNullAng.
      symmetry...
    }
    eapply (xA_xA_LtAs_BetRs c b a).
    { apply (ConvexAngRs_ReflexAngRs b c roab)...
      pir (eq_sym (eq_sym roab)) => roab.
    }
    { apply (ConvexAngRs_ReflexAngRs a c roac)...
      pir (eq_sym (eq_sym roac)) => roac.
    }
    apply BetRs_sym...
  }
Qed.

Definition DrawSubtractionOfTwoConvexAngles :
  forall A C : Angle,
  Convex A
    -> Convex C \/ C = A180
    -> A <<< C
    -> { B : Angle | A +++ B = C /\ B <<< C /\ Convex B }.
Proof with eauto.
  intros A C iA iC AltC.
  assert (nCeqA0 : C <> A0).
  { intros CeqA0. rewrite_all CeqA0.
    apply (NonNegativeAngles A) in AltC...
  }
  destruct (DrawSector A) as [[ a b roab ] H ]; subst.
  destruct (DrawCongruentAngle_ccw a C) as [ c H ].
  assert (robc : da b = da c).
  { destruct H as [ roac _ ]. rewrite <- roab... }
  exists ([| b, c | robc |]).
  destruct H as [ roac aceqC ].
  rewrite PlusAngRs. pir (eq_trans roab robc) => roac.
  split; subst...
  destruct iC as [ iC | C180 ].
  { apply (iAs_iAs_LtAs_BetRs a b c roab roac) in AltC...
    destruct (BetRs_nColRs a b c AltC) as [ diab [ dibc diac ]].
    destruct ((proj1 (BetRs_EqOs a b c diab dibc diac)) AltC)
      as [ abac bcac ].
    assert (ibc : Convex ([| b, c | robc |])).
    { apply (ConvexAngRs_Left b c robc dibc).
      apply (ConvexAngRs_Left a c roac diac) in iC.
      rewrite bcac...
    }
    split...
    apply <- (ConvexAs_LtA_BetRs a b c robc roac)...
  }
  { rewrite C180 in *.
    apply EqStraightAng in C180.
    assert (ibc : Convex ([| b, c | robc |])).
    { eapply ConvexAng_ConvexSupAng. apply iA.
      rewrite PlusAngRs. apply EqStraightAng...
    }
    split...
    apply A0_iA_A180 in ibc. destruct ibc...
  }
Defined.

Definition ConvexAng_ReflexPlusStaightAng :
  forall (A : Angle),
  Convex A
    <-> Reflex (A180 +++ A).
Proof with eauto.
  intros A; unfold PlusA, PlusAngleDef.
  destruct (DrawSector A180) as [[ a c roac ] acA180 ]; simpl.
  destruct (DrawCongruentAngle_ccw c A) as [ b [ rocb cbH ]]; simpl.
  apply EqStraightAng in acA180. subst.
  split.
  { intros iA.
    assert (dicb : ![ c # b ]). { apply (ConvexAngRs_nColRs c b rocb iA). }
    rewrite (ConvexAngRs_Left c b rocb dicb) in iA.
    assert (diab : ![ a # b ]).
    { apply nColRs_sym.
      apply (nColRs_OpRs_nColRs c b a)... apply OpRs_OpRs in acA180.
      rewrite acA180. apply OpOpRs.
    }
    rewrite (ReflexAngRs_Right a b (eq_trans roac rocb) diab).
    assert (dibc : ![ b # c ]). { apply nColRs_sym... }
    assert (H : %[ a # b | diab ] = %[ b # c | dibc ]).
    { apply OpRs_OpRs in acA180.
      apply (OpRs_EqOs_Left a b c diab)...
    }
    rewrite H.
    assert (bccb : %[ b # c | dibc ] = negb (%[ c # b | dicb ])).
    { apply (DiOsRs b c dibc)... }
    rewrite iA in *.
    induction (%[ b # c | dibc])...
  }
  { intros xA.
    pir (eq_trans roac rocb) => (eq_sym (eq_sym (eq_trans roac rocb))).
    apply (ConvexAngRs_ReflexAngRs b a) in xA.
    assert (diab : ![ a # b ]).
    { apply nColRs_sym.
      apply (ConvexAngRs_nColRs b a (eq_sym (eq_trans roac rocb)))...
    }
    assert (dicb : ![ c # b ]).
    { apply nColRs_sym.
      apply (nColRs_OpRs_nColRs a b c)... apply OpRs_OpRs in acA180...
    }
    assert (diba : ![ b # a ]). { apply nColRs_sym... }
    rewrite (ConvexAngRs_Left b a (eq_sym (eq_trans roac rocb)) diba) in xA.
    rewrite (ConvexAngRs_Left c b rocb dicb).
    assert (dibc : ![ b # c ]). { apply nColRs_sym... }
    assert (H : %[ a # b | diab ] = %[ b # c | dibc ]).
    { apply OpRs_OpRs in acA180.
      apply (OpRs_EqOs_Left a b c diab)...
    }
    apply EqOs_EqOpOs in H.
    pir (nColRs_sym a b diab) => diba. pir (nColRs_sym b c dibc) => dicb.
    rewrite <- H...
  }
Qed.

Definition DrawConvexAngle :
  forall (A : Angle),
  Reflex A
    -> { B : Angle | A = A180 +++ B /\ Convex B }.
Proof with eauto.
  intros A xA.
  apply (A180_xA A) in xA.
  destruct (DrawSubtractionOfTwoAngles A180 A xA) as [ B H1 ].
  exists B; split...
  apply ConvexAng_ReflexPlusStaightAng.
  rewrite H1. apply (A180_xA A) in xA...
Defined.

Definition Convex_LtAs_LtSumAs :
  forall (A B C : Angle),
  Convex A
    -> Convex B
    -> Convex C
    -> B <<< C
    -> A +++ B <<< A +++ C.
Proof with eauto.
  intros A B C iA iB iC B_C.
  destruct (DrawSubtractionOfTwoConvexAngles B C)
    as [ X [ BX_C [ X_C iX ]]]...
  rewrite <- BX_C. destruct BX_C. clear B_C. clear X_C.
  rewrite (PlusAs_assoc A B X).
  destruct (AngleClassification (A +++ B)) as [ AB0 |[ AB180 | ixAB ]]...
  { left.
    apply (ConvexAs_nNullSumAs A B iA iB) in AB0.
    contradiction.
  }
  { do 2 right; left; split...
    rewrite AB180 in *.
    apply ConvexAng_ReflexPlusStaightAng...
  }
  destruct (AngleClassification ((A +++ B) +++ X))
    as [ ABX0 |[ ABX180 |[ iABX | xABX ]]]...
  { rewrite <- (PlusAs_assoc A B X) in ABX0.
    apply (ConvexAs_nNullSumAs A (B +++ X) iA iC) in ABX0.
    contradiction.
  }
  { destruct ixAB as [ iAB | xAB ].
    { right; left; split... }
    { apply ReflexAng_nAs in xAB.
      destruct xAB as [ _ [ _ xAB ]].
      rewrite PlusAng_comm in ABX180.
      apply ConvexAng_ConvexSupAng in ABX180; auto.
      contradiction.
    }
  }
  { destruct ixAB as [ iAB | xAB ].
    { apply (ConvexAs_LtSumAs (A +++ B) X iAB iX). }
    { destruct (DrawSector A) as [[ a b roab ] abA ].
      destruct abA.
      destruct (DrawCongruentAngle_ccw b B) as [ c [ robc bcB ]].
      destruct bcB. rewrite PlusAngRs in *.
      destruct (DrawCongruentAngle_ccw c X) as [ d [ rocd cdC ]].
      destruct cdC. rewrite PlusAngRs in *.
      assert (diab : ![ a # b ]). { apply (ConvexAngRs_nColRs a b roab iA). }
      assert (dibc : ![ b # c ]). { apply (ConvexAngRs_nColRs b c robc iB). }
      assert (dibd : ![ b # d ]). { eapply (ConvexAngRs_nColRs b d)... }
      assert (dicd : ![ c # d ]). { apply (ConvexAngRs_nColRs c d rocd iX). }
      assert (diad : ![ a # d ]). { eapply (ConvexAngRs_nColRs a d)... }
      assert (diac : ![ a # c ]).
      { pir (eq_trans roab robc)
          => (eq_sym (eq_sym (eq_trans roab robc))).
        eapply (ConvexAngRs_ReflexAngRs c a) in xAB. apply nColRs_sym.
        apply (ConvexAngRs_nColRs c a (eq_sym (eq_trans roab robc)))...
      }
      apply (ConvexAngRs_Left a b roab diab) in iA.
      apply (ConvexAngRs_Left b c robc dibc) in iB.
      apply (ConvexAngRs_Left b d (eq_trans robc rocd) dibd) in iC.
      apply (ConvexAngRs_Left c d rocd dicd) in iX.
      apply (ConvexAngRs_Left a d (eq_trans (eq_trans roab robc) rocd) diad)
        in iABX.
      apply (ReflexAngRs_Right a c (eq_trans roab robc) diac) in xAB.
      assert (bcd : ![ b # c # d ]).
      { apply <- BetRs_EqOs; split. rewrite iB. rewrite iC...
        rewrite iX. rewrite iC...
      }
      assert (abd : ![ a # b # d ]).
      { apply <- BetRs_EqOs; split. rewrite iA. rewrite iABX...
        rewrite iC. rewrite iABX...
      }
      assert (dcba : ![ d # c # b # a ]).
      { apply BetRs_a_trans; apply BetRs_sym... }
      destruct dcba as [ _ [ H2 [ _ _ ]]].
      apply BetRs_sym in H2...
      apply (BetRs_EqOs a c d diac dicd diad) in H2.
      destruct H2 as [ H1 H2 ]. rewrite xAB in H1.
      rewrite iABX in H1.
      discriminate.
    }
  }
  { destruct ixAB as [ iAB | xAB ].
    { right; left; split; auto. }
    { do 4 right.
      destruct (DrawSector (A +++ B))
        as [[ a b roab ] Hab ]; simpl in *.
      repeat split... destruct Hab.
      destruct (DrawCongruentAngle_ccw b X) as [ c [ robc bcX ]].
      destruct bcX. rewrite PlusAngRs in *.
      exists c, (eq_trans roab robc).
      split...
      assert (diac : ![ a # c ]).
      { pir (eq_trans roab robc)
          => (eq_sym (eq_sym (eq_trans roab robc))).
        eapply (ConvexAngRs_ReflexAngRs) in xABX. apply nColRs_sym.
        apply (ConvexAngRs_nColRs c a (eq_sym (eq_trans roab robc)))...
      }
      assert (diab : ![ a # b ]).
      { pir roab => (eq_sym (eq_sym roab)).
        eapply (ConvexAngRs_ReflexAngRs) in xAB. apply nColRs_sym.
        apply (ConvexAngRs_nColRs b a (eq_sym roab))...
      }
      assert (dibc : ![ b # c ]). { apply (ConvexAngRs_nColRs b c robc iX). }
      apply (ReflexAngRs_Right a b roab diab) in xAB.
      apply (ConvexAngRs_Left b c robc dibc) in iX.
      apply (ReflexAngRs_Right a c (eq_trans roab robc) diac) in xABX.
      apply <- (BetRs_EqOs a c b diac (nColRs_sym b c dibc) diab).
      rewrite xAB. rewrite xABX. split...
      eapply OrientationRs_LR. apply iX.
    }
  }
Qed.

Lemma LtA_LtA_LtPlusAs :
  forall A B C D : Angle,
  Convex A
    -> Convex B
    -> Convex C
    -> Convex D
    -> A <<< B
    -> C <<< D
    -> A +++ C <<< B +++ D.
Proof with eauto.
  intros A B C D iA iB iC iD AB CD.
  assert (BCD : B +++ C <<< B +++ D). { apply Convex_LtAs_LtSumAs... }
  assert (CAB : C +++ A <<< C +++ B). { apply Convex_LtAs_LtSumAs... }
  rewrite (PlusAng_comm C A) in CAB.
  rewrite (PlusAng_comm C B) in CAB.
  apply (LtA_trans (A +++ C)(B +++ C)(B +++ D))...
Qed.

Definition ConvexAs_ConvexDoubleAs_ConvexSumAs :
  forall (A B : Angle),
  Convex A
    -> Convex B
    -> Convex (A +++ A)
    -> Convex (B +++ B)
    -> Convex (A +++ B).
Proof with eauto.
  intros A B iA iB iAA iBB.
  destruct (AngTrichotomy A B) as [ AltB |[ AeqB | AgtB ]].
  { assert (AB_BB : A +++ B <<< B +++ B).
    { rewrite PlusAng_comm. apply Convex_LtAs_LtSumAs... }
    assert (A0_AB : A0 <<< A +++ B).
    { apply PositiveAngles. apply ConvexAs_nNullSumAs... }
    assert (AB_180 : A +++ B <<< A180).
    { apply (LtA_trans (A +++ B)(B +++ B) A180)...
      apply A0_iA_A180 in iBB. destruct iBB...
    }
    apply A0_iA_A180; split...
  }
  { subst B... }
  { assert (AB_AA : A +++ B <<< A +++ A).
    { apply Convex_LtAs_LtSumAs... }
    assert (A0_AB : A0 <<< A +++ B).
    { apply PositiveAngles. apply ConvexAs_nNullSumAs... }
    assert (AB_180 : A +++ B <<< A180).
    { apply (LtA_trans (A +++ B)(A +++ A) A180)...
      apply A0_iA_A180 in iAA. destruct iAA...
    }
    apply A0_iA_A180; split...
  }
Qed.

Definition MidRay (a o b : Ray) : Prop
  := ![ a # o # b ] /\
    exists (dioa : ![ o # a ])(diob : ![ o # b ]),
      [| o # a | dioa |] = [| o # b | diob |].
Notation " ![ a -- o -- b ] "
  := (MidRay a o b)
  (at level 60).

Definition DrawMiddleRay :
  forall (a b : Ray),
  ![ a # b ]
    -> { o : Ray | ![ a -- o -- b ] }.
Proof with eauto.
  intros [ O A nOeqA ][ O' B' nOeqB' ][ roab diab ]; simpl in *;
  subst O'.
  destruct (DrawPointProjectionOnRay O B' A) as [ B [ H1 OA_OB ]]...
  assert (nOeqB : O <> B).
  { contradict nOeqA. subst B. symmetry in OA_OB.
    apply EqSgs_EqPs in OA_OB...
  }
  assert (OsrBB' : [O # B', B]).
  { destruct H1 as [ H1 |[ H | H ]]; subst; try contradiction... }
  clear H1.
  assert (nColAOB : ~ [ A, O, B ]).
  { apply (nColPs_SR_inv O A B' A B); betps. }
  destruct (DrawMiddlePoint A B) as [ Q [ AQB QA_QB ]]; dips.
  assert (nOeqQ : O <> Q).
  { intros OeqQ. subst Q. contradict nColAOB; colps. }
  exists ({{ O # Q | nOeqQ }}).
  assert (OAsfBQ : [ O # A | B, Q ]).
  { apply SHa_sym. apply SR_SH; betps. }
  assert (OBsfAQ : [ O # B | A, Q ]).
  { apply SHa_sym. apply SR_SH; ncolperps; betps. }
  assert (nColAOQ : ~ [A, O, Q]).
  { eapply SH_nColPs. apply SHa_sym.
    apply SHb_sym. apply OAsfBQ.
  }
  assert (nColBOQ : ~ [B, O, Q]).
  { eapply SH_nColPs. apply SHa_sym.
    apply SHb_sym. apply OBsfAQ.
  }
  assert (H : {{ A # O # Q | nColAOQ }} :=: {{ B # O # Q | nColBOQ }}).
  { apply SSS'...
    rewrite SegPs_sym. symmetry. rewrite SegPs_sym...
  }
  split.
  { split; simpl...
    split...
    apply (BR_inv O A Q B A Q B'); betps.
    split; apply SHb_sym...
  }
  { assert (nColQOA : ~ [Q, O, A]); ncolperps.
    assert (nColQOB : ~ [Q, O, B]); ncolperps.
    assert (nColQOB' : ~ [Q, O, B']).
    { destruct OsrBB' as [ _ [ _ [[ x [ H1 [ H2 H3 ]]] _ ]]].
      contradict nColQOB. exists x; repeat split... incpt 2.
    }
    exists (conj eq_refl nColQOA), (conj eq_refl nColQOB').
    erewrite (EqConvexAngRsPs Q O A nOeqQ nOeqA). symmetry.
    erewrite (EqConvexAngRsPs Q O B' nOeqQ nOeqB'). symmetry.
    apply EqPerTr_5 in H.
    destruct H as [ _ [ _ [ _ [ H _ ]]]]; simpl in *.
    erewrite <- (ConvexAngPs_inv Q O B Q B'); betps.
    pir (nColPerPs_5 A O Q nColAOQ) => nColQOA.
    apply H.
  }
Defined.

Lemma MidRs_EqRs :
  forall a o o' b : Ray,
  ![ a -- o -- b ]
    -> ![ a -- o' -- b ]
    -> o == o'.
Proof with eauto.
  intros [ O A nOeqA ][ O' B nOeqB ][ O'' C nOeqC ][ O''' D nOeqD ];
  intros [[ H1 [ H2 abd ]][[ roba ba ][[ robd bd ] ab_bd ]]];
  intros [[ H3 [ H4 acd ]][[ roca ca ][[ rocd cd ] ac_cd ]]]; simpl in *.
  subst O''' O'' O'; simpl in *.
  pir (conj roba ba) => (conj (eq_refl O) ba).
  pir (conj robd bd) => (conj (eq_refl O) bd).
  pir (conj roca ca) => (conj (eq_refl O) ca).
  pir (conj rocd cd) => (conj (eq_refl O) cd).
  repeat rewrite EqConvexAngRsPs in ab_bd.
  repeat rewrite EqConvexAngRsPs in ac_cd. clear H4 robd roba rocd roca.
  split; simpl...
  assert (ab : ~ [A, O, B]); ncolperps.
  assert (ac : ~ [A, O, C]); ncolperps.
  rewrite (ConvexAngPs_sym B O A ba ab) in ab_bd.
  rewrite (ConvexAngPs_sym C O A ca ac) in ac_cd.
  destruct (DrawSegmentOnRay O D O A nOeqD) as [ D' [ ODD' H ]].
  destruct ODD'...
  destruct (DrawPointCrossBar O A B D') as [ B' [ ABD BB' ]].
  { split...
    apply (SHa_inv O A B D A B D'); colps; try apply SR_refl...
    apply (SHa_inv O D B A D' B A); colps; try apply SR_refl...
    destruct H0 as [ H1 [ H2 [ H3 H4 ]]]... colperps.
  }
  destruct (DrawPointCrossBar O A C D') as [ C' [ ACD CC' ]].
  { split...
    apply (SHa_inv O A C D A C D'); colps; try apply SR_refl...
    apply (SHa_inv O D C A D' C A); colps; try apply SR_refl...
    destruct H0 as [ H1 [ H2 [ H3 H4 ]]]... colperps.
  }
  assert (ab' : ~ [A, O, B']).
  { apply (nColPs_SR_inv O A B A B'); try apply SR_refl... }
  assert (b'd' : ~ [B', O, D']).
  { apply (nColPs_SR_inv O B D B' D'); try apply SR_refl... }
  assert (ab'_b'd' : [|A # O # B' | ab'|] = [|B' # O # D' | b'd'|]).
  { rewrite (ConvexAngPs_inv A O B' A B ab' ab);
    try rewrite (ConvexAngPs_inv B' O D' B D b'd' bd);
    try apply SR_sym; try apply SR_refl...
  }
  assert (ac' : ~ [A, O, C']).
  { apply (nColPs_SR_inv O A C A C'); try apply SR_refl... }
  assert (c'd' : ~ [C', O, D']).
  { apply (nColPs_SR_inv O C D C' D'); try apply SR_refl... }
  assert (ac'_c'd' : [|A # O # C' | ac'|] = [|C' # O # D' | c'd'|]).
  { rewrite (ConvexAngPs_inv A O C' A C ac' ac);
    try rewrite (ConvexAngPs_inv C' O D' C D c'd' cd);
    try apply SR_sym; try apply SR_refl...
  }
  apply (SR_trans O B B' C)...
  apply (SR_trans O B' C' C); try apply SR_sym... apply SR_sym.
  apply (BR_inv O A B D A B' D') in abd; try apply SR_refl...
  apply (BR_inv O A C D A C' D') in acd; try apply SR_refl...
  eapply (SH_EqConvexAs_SR A O B' C' ab' ac').
  { destruct abd as [ H1 H2 ]. destruct acd as [ H3 H4 ].
    apply SH_trans with D'... apply SHb_sym...
  }
  assert (d'b' : ~ [D', O, B']); ncolperps.
  assert (d'c' : ~ [D', O, C']); ncolperps.
  rewrite (ConvexAngPs_sym B' O D' b'd' d'b') in ab'_b'd'.
  rewrite (ConvexAngPs_sym C' O D' c'd' d'c') in ac'_c'd'.
  assert (TrAOB : {{ A # O # B' | ab' }} :=: {{ D' # O # B' | d'b' }}).
  { apply (SAS' A O B' D' O B' ab' d'b')... rewrite SegPs_sym.
    rewrite <- H. apply SegPs_sym...
  }
  assert (B'A_B'D' : [|B', A|] = [|B', D'|]).
  { destruct TrAOB as [ H1 [ H2 [ H3 _ ]]]; simpl in *. rewrite <- H3... }
  assert (TrAOC : {{ A # O # C' | ac' }} :=: {{ D' # O # C' | d'c' }}).
  { apply (SAS' A O C' D' O C' ac' d'c')... rewrite SegPs_sym.
    rewrite <- H. apply SegPs_sym...
  }
  assert (C'A_C'D' : [|C', A|] = [|C', D'|]).
  { destruct TrAOC as [ H1 [ H2 [ H3 _ ]]]; simpl in *. rewrite <- H3... }
  assert (B'eqC' : B' = C'). { apply (UniqueMiddlePoint A B' C' D')... }
  subst C'. pir ac' => ab'.
  destruct H0 as [ OeqD | OeqD' ]; try subst D'; try subst D.
  contradict nOeqD... contradict nOeqA. symmetry in H.
  apply EqSgs_EqPs in H...
Qed.

Definition DrawHalfOfConvexAngle :
  forall (A : Angle),
  Convex A
    -> { B : Angle | Convex B /\ B +++ B = A }.
Proof with eauto.
  intros Ang iAng.
  destruct (DrawSector Ang) as [[ a b roab ] abAng' ]; simpl in *.
  rewrite <- abAng' in iAng.
  assert (diab : ![ a # b ]). { apply (ConvexAngRs_nColRs a b roab iAng). }
  assert (abLeft : %[a # b | diab] = true).
  { apply (ConvexAngRs_Left a b roab diab)... }
  apply (LeftOrientation_EqAs a b roab) in abLeft.
  destruct a as [ O A' nA'eqO ].
  destruct b as [ O' B nBeqO ]. simpl in *. subst O'.
  destruct (DrawPointProjectionOnRay O A' B nA'eqO)
    as [ A [ H1 OA_OB ]].
  assert (nOeqA : O <> A); dips.
  assert (OsrAA' : [O # A', A]).
  { destruct H1 as [ OsrAA' |[ OeqA' | OeqA ]]; try contradiction... }
  assert (abAng : [| A, O, B | nOeqA, nBeqO |] = Ang).
  { rewrite <- (AngPs_inv A' O B A B nA'eqO nBeqO nOeqA)...
    apply SR_refl...
  }
  assert (nColA'OB : ~ [ A', O, B ]). { destruct diab; simpl in *... }
  eassert (iAOB : [| A' # O # B | _ |]
    = [| {{ O # A' | _ }} # {{ O # B | _ }} |_ |]).
  { symmetry. eapply (EqConvexAngRsPs A' O B nA'eqO nBeqO). }
  destruct iAOB.
  assert (nColAOB : ~ [ A, O, B ]).
  { clear abLeft. contradict nColA'OB.
    destruct nColA'OB as [ x [ A'ox [ Oox Box ]]].
    destruct OsrAA' as [ _ [ _ [[ x' [ Oox' [ A'ox' Aox' ]]] nA'OA ]]].
    assert (xeqx' : x = x'); eqls. subst x'.
    exists x; split...
  }
  assert (AOB : [|A # O # B | nColAOB|] = [|A' # O # B | nColA'OB|]).
  { apply (ConvexAngPs_inv A O B A' B nColAOB nColA'OB)...
    apply SR_sym; auto. apply SR_refl...
  }
  pir (conj (eq_refl O) nColA'OB) => diab.
  rewrite <- abAng' in *. clear dependent Ang.
  rewrite (ConvexAngRs_ConvexAngPs ({{O # A' | nA'eqO}})({{O # B | nBeqO}})
  diab nColA'OB) in abLeft; simpl in *.
  rewrite abLeft in *. rewrite <- AOB in *.
  clear dependent A'.
  assert (nAeqB : A <> B). { apply (nColPs_3DiPs A O B)... }
  destruct (DrawMiddlePoint A B nAeqB) as [ Q [ BetAQB QA_QB ]].
  assert (nQeqO : Q <> O).
  { intros QeqO; subst Q.
    apply BetPs_ColPs in BetAQB.
    contradiction.
  }
  assert (nColQOA : ~ [ Q, O, A ]).
  { clear iAng abAng. contradict nColAOB.
    destruct nColAOB as [ x [ Oox [ Qox Aox ]]].
    assert (Box : [ B @ x ]). { apply (BetPs_IncPt A Q B)... }
    exists x; split...
  }
  assert (nColQOB : ~ [ Q, O, B ]).
  { clear iAng abAng. contradict nColAOB.
    destruct nColAOB as [ x [ Oox [ Qox Box ]]].
    assert (Aox : [ A @ x ]); incpt 2.
    repeat split...
  }
  assert (EqTr : {{ Q # O # A | nColQOA }} :=: {{ Q # O # B | nColQOB }}).
  { apply (SSS Q O A Q O B nColQOA)...
    rewrite SegPs_sym. rewrite QA_QB. apply SegPs_sym.
  }
  assert (QOA_QOB : [| Q # O # A | nColQOA |] = [| Q # O # B | nColQOB |]).
  { destruct EqTr as [ _ [ _ [ _ [ H1 _ ]]]]; simpl in *... }
  exists ([|Q # O # A | nColQOA|]).
  split.
  { apply ConvexAngPs. }
  { rewrite QOA_QOB at 2. erewrite ConvexAngPs_sym.
    apply BetPs_PlusConvexAngPs...
  }
  Unshelve.
  ncolperps. ncolperps.
Defined.

(** Problem #45 *)
(** Euclid, Book I : Proposition 9. *)
(* To bisect a given rectilineal angle. *)
Definition DrawHalfAngle :
  forall (A : Angle),
  A <> A0
    -> { B : Angle | Convex B /\ B +++ B = A }.
Proof with eauto.
  intros * nAeqA0.
  destruct (DecideAngleClassification A nAeqA0) as [[ iA | xA ]| oA ].
  { destruct (DrawHalfOfConvexAngle A iA) as [ B H ]. exists B... }
  { destruct (DrawExplementaryAngle A) as [ B H ]...
    assert (iB : Convex B).
    { apply <- ( ExpAs_iA_xA B A)... rewrite PlusAng_comm... }
    destruct (DrawHalfOfConvexAngle B iB) as [ C [ iC CC_ExpA ]].
    destruct (DrawSupplementaryAngle C iC) as [ D CD_A180 ].
    exists D; split...
    apply (ConvexAng_ConvexSupAng C D)...
    assert (BDD : (B +++ (D +++ D)) = A0).
    { rewrite <- CC_ExpA.
      rewrite <- (PlusAs_assoc C C (D +++ D)).
      rewrite PlusAng_comm. rewrite (PlusAs_assoc C D D).
      rewrite <- (PlusAs_assoc (C +++ D) D C).
      rewrite (PlusAng_comm D C). rewrite CD_A180.
      apply PlusStraightAngEqNullAng.
    }
    apply (PlusAs_cancel_l B (D +++ D) A).
    rewrite BDD. rewrite PlusAng_comm...
  }
  { destruct oA as [ C [ CA90 iC ]].
    destruct (DrawHalfOfConvexAngle C iC) as [ D [ iD CD ]].
    destruct (DrawHalfOfConvexAngle A90) as [ A45 [ iA45 A4590 ]].
    apply DefA90.
    assert (G : (D +++ A45) +++ (D +++ A45) = A).
    { rewrite (PlusAng_comm D A45) at 1.
      rewrite <- (PlusAs_assoc A45 D (D +++ A45)).
      rewrite (PlusAs_assoc D D A45). rewrite CD.
      rewrite PlusAng_comm.
      rewrite <- (PlusAs_assoc C A45 A45).
      rewrite A4590. rewrite PlusAng_comm...
    }
    exists (D +++ A45); split... apply ConvexAs_ConvexDoubleAs_ConvexSumAs...
    rewrite CD... rewrite A4590. apply DefA90.
  }
Defined.

(** Theorem #81 *)
Theorem UniqueHalfAngle :
  forall A B : Angle,
  Convex A
    -> Convex B
    -> A +++ A = B +++ B
    -> A = B.
Proof with eauto.
  intros A B iA iB AA_BB.
  destruct (AngTrichotomy A B) as [ AB |[ AeqB | BA ]]...
  assert (H : A +++ A <<< B +++ B).
  { apply (LtA_LtA_LtPlusAs A B A B iA iB iA iB)... }
  rewrite AA_BB in H. apply LtA_irrefl in H; contradiction.
  assert (H : B +++ B <<< A +++ A).
  { apply (LtA_LtA_LtPlusAs B A B A iB iA iB iA)... }
  rewrite AA_BB in H. apply LtA_irrefl in H; contradiction.
Qed.

Lemma RightAngPs_RightAngPs :
  forall (O A B A' B' : Point)(x y : Line)
         (nColAOB : ~ [ A, O, B ])(nColA'OB' : ~ [ A', O, B' ]),
  [ O @ x, y ]
    -> [ A, A' @ x ]
    -> [ B, B' @ y ]
    -> [| A # O # B | nColAOB |] = A90
    -> [| A' # O # B' | nColA'OB' |] = A90.
Proof with eauto.
  intros * [ Oox Ooy ][ Aox A'ox ][ Boy B'oy ] AOBeqA90.
  assert (iA90 : Convex A90). { apply DefA90. }
  destruct (classic ([ A # O # A' ])) as [ BetAOA' | nBetAOA' ];
  destruct (classic ([ B # O # B' ])) as [ BetBOB' | nBetBOB' ].
  { rewrite <- AOBeqA90. symmetry.
    eapply (BetPs_EqVertAngPs O A B A' B')...
  }
  { assert (OsrBB' : [ O # B, B' ]). { repeat split; dips... }
    assert (nColA'OB : ~ [A', O, B]).
    { eapply (nColPs_SR_inv O A' B' A' B); betps. }
    assert (nColBOA' : ~ [B, O, A']); ncolperps.
    rewrite (ConvexAngPs_inv A' O B' A' B nColA'OB' nColA'OB); betps.
    rewrite (ConvexAngPs_sym A' O B nColA'OB nColBOA')...
    apply SupA90_EqA90... rewrite <- AOBeqA90.
    eapply BetPs_SupAngPs...
  }
  { assert (OsrAA' : [ O # A, A' ]); repeat split; dips.
    assert (nColAOB' : ~ [A, O, B']).
    { eapply (nColPs_SR_inv O A' B' A B'); betps. }
    assert (nColBOA : ~ [B, O, A]); ncolperps.
    erewrite (ConvexAngPs_inv A' O B' A B' nColA'OB' nColAOB'); betps.
    apply SupA90_EqA90.
    rewrite <- (ConvexAngPs_sym B O A nColBOA) in AOBeqA90 ...
    rewrite <- AOBeqA90. eapply BetPs_SupAngPs...
  }
  { assert (OsrAA' : [ O # A, A' ]); repeat split; dips.
    assert (OsrBB' : [ O # B, B' ]); repeat split; dips.
    rewrite <- AOBeqA90.
    eapply (ConvexAngPs_inv A' O B' A B); betps.
  }
Qed.

End SUPPLEMENTARY.

(*****************************************************************************)
(* 21 *) Section PERPENDICULARS.
Context `{ cc : Concentricals }.
Context  { an : Angles on }.
Context  { sp : Superpositions on }.
(*****************************************************************************)

Definition Perpendicular (x y : Line) : Prop
  := exists (O A B : Point)(nColAOB : ~ [ A, O, B ]),
     [ O @ x, y ] /\ [ A @ x ] /\ [ B @ y ]
     /\ [| A # O # B | nColAOB |] = A90.
Notation " x _|_ y "
  := (Perpendicular x y)
  (at level 50).

Lemma PerpLs_ConvLs :
  forall (x y : Line),
  x _|_ y
    -> x >< y.
Proof with eauto.
  intros * [ O [ A [ B [ nColAOB [[ Oox Ooy ][ Aox [ Boy AOB ]]]]]]].
  split.
  { intros xeqy; subst... }
  { exists O... }
Qed.

Lemma PerpLs_irrefl :
  forall (x : Line),
  ~ (x _|_ x).
Proof with eauto.
  intros x xperpx.
  apply PerpLs_ConvLs in xperpx...
  destruct xperpx as [ H1 H2 ]...
Qed.

Lemma PerpLs_sym :
  forall (x y : Line),
  x _|_ y
    -> y _|_ x.
Proof with eauto.
  intros x y [ A [ C [ B [ nColCAB [[ Aox Aoy ][ Cox [ Boy CAB ]]]]]]].
  assert (nColBAC : ~ [B, A, C]); ncolperps.
  exists A, B, C, nColBAC; repeat split...
  rewrite (ConvexAngPs_sym B A C nColBAC nColCAB)...
Qed.

Lemma PerpLs_EqA90 :
  forall (O A B : Point)(x y : Line)(nColAOB : ~ [ A, O, B ]),
  x _|_ y
    -> [ O @ x, y ]
    -> [ A @ x ]
    -> [ B @ y ]
    -> [| A # O # B | nColAOB |] = A90.
Proof with eauto.
  intros O A B x y nColAOB xperpy [ Oox Ooy ] Aox Boy.
  assert (nxeqy : x >< y). { apply (PerpLs_ConvLs x y xperpy). }
  destruct nxeqy as [ nxeqy _ ].
  destruct xperpy as [ O' [ A' [ B' [ nColA'OB' H ]]]].
  destruct H as [[ O'ox O'oy ][ A'ox [ B'oy A'O'B'eqA90 ]]].
  assert (OeqO' : O = O'); eqps. subst O'.
  apply (RightAngPs_RightAngPs O A' B' A B x y nColA'OB'); try split...
Qed.

Lemma PerpLs_EqLs :
  forall (O : Point)(x y z : Line),
  [ O @ x, y, z ]
    -> x _|_ y
    -> x _|_ z
    -> y = z.
Proof with eauto.
  intros * [ Oox [ Ooy Ooz ]] xperpy xperpz.
  assert (nxeqy : x <> y). { destruct (PerpLs_ConvLs x y)... }
  assert (nxeqz : x <> z). { destruct (PerpLs_ConvLs x z)... }
  destruct xperpy
    as [ O'' [ A [ B [ AOB [[ O''ox O''oy ][ Aox [ Boy H1 ]]]]]]].
  destruct xperpz
    as [ O' [ A' [ B' [ A'OB' [[ O'ox O'oy ][ A'ox [ B'oy H2 ]]]]]]].
  assert (OeqO' : O = O'); eqps. subst O'. clear O'oy O'ox.
  assert (OeqO'' : O = O''); eqps. subst O''. clear O''oy O''ox.
  assert (nAeqO : A <> O); dips.
  assert (nA'eqO : A' <> O); dips.
  assert (AOB' : ~ [A, O, B']).
  { clear H1 H2. contradict A'OB'.
    exists x; repeat split... eapply (ColPs_IncPt A O B')...
  }
  assert (H3 : [|A # O # B' | AOB'|] = A90).
  { eapply (RightAngPs_RightAngPs O A' B' A B' x); try split... }
  assert (nBox : ~ [ B @ x ]); nincpt.
  assert (nB'ox : ~ [ B' @ x ]); nincpt.
  destruct (DecideSameSide B B' x nBox nB'ox) as [ SS | OS ].
  { assert (OsrBB' : [ O # B, B' ]).
    { eapply (SH_EqConvexAs_SR A O B B')... split... rewrite H3... }
    apply (DiPs_EqLs O B y z); dips; repeat split; incpt.
  }
  { destruct (DrawSegmentExtension B O) as [ B'' BOB'' ]; dips.
    assert (SS : [ x | B', B'']).
    { eapply (OOS_trans B' B B'' x). apply OS_sym... repeat split; incpt. }
    assert (OsrB'B'' : [ O # B', B'' ]).
    { eapply (SH_EqConvexAs_SR A O B' B'')... split... rewrite H3... symmetry.
      eapply (RightAngPs_RightAngPs O A B A B'' x y); repeat split; incpt 2.
    }
    assert (BOB' : [ B # O # B' ]); betps.
    apply (DiPs_EqLs O B y z); dips; repeat split; incpt 2.
  }
  Unshelve. contradict nBox. incpt 3.
Qed.

Definition DrawPointsOnRightAngle :
  forall (O A B : Point)(x y : Line)(AOB : ~ [ A, O, B ]),
  [ O, A @ x ]
    -> [ O, B @ y ]
    -> [| A # O # B | AOB |] = A90
    -> { C : Point & { D : Point | [ C @ x ] /\ [ D @ y ] /\
         [ A # O # C ] /\ [ B # O # D ] /\
         exists (BOC : ~ [ B, O, C ])(COD : ~ [ C, O, D ])(DOA : ~ [ D, O, A ]),
         [| B # O # C | BOC |] = A90 /\ [| C # O # D | COD |] = A90 /\
         [| D # O # A | DOA |] = A90 } }.
Proof with eauto.
  intros * [ Oox Aox ][ Ooy Boy ] AOB90.
  destruct (DrawSegmentExtension A O) as [ C AOC ]; dips.
  destruct (DrawSegmentExtension B O) as [ D BOD ]; dips.
  exists C, D. repeat split; incpt.
  assert (nxeqy : x <> y).
  { clear AOB90. contradict AOB. subst y. exists x; repeat split... }
  assert (BOC : ~ [ B, O, C ]).
  { clear AOB90. contradict AOB. exists x; repeat split...
    apply (ColPs_IncPt C O B x); dips; split...
    apply (BetPs_IncPt A O C x); dips; split...
  }
  assert (COD : ~ [ C, O, D ]).
  { contradict BOC. exists y; repeat split...
    apply (ColPs_IncPt D O C y); dips; split...
    apply (BetPs_IncPt B O D y); dips; split...
  }
  assert (DOA : ~ [ D, O, A ]).
  { contradict COD. exists x; repeat split...
    { apply (BetPs_IncPt A O C x); dips; split... }
    { apply (ColPs_IncPt A O D x); dips; split... }
  }
  assert ([|B # O # C | BOC|] = A90).
  { apply (RightAngPs_RightSupAngPs O A B C AOB)... }
  assert ([|C # O # D | COD|] = A90).
  { apply (RightAngPs_RightSupAngPs O B C D BOC)... }
  assert ([|D # O # A | DOA|] = A90).
  { apply (RightAngPs_RightSupAngPs O C D A COD)... apply BetPs_sym... }
  exists BOC, COD, DOA; repeat split...
Defined.

Example DrawMirrorPoint :
  forall (A B C : Point)(nColABC : ~ [ A, B, C ]),
  { D : Point | [| A, C |] = [| A, D |] /\ [| B, C |] = [| B, D |]
                                        /\ [ C | A # B | D ] }.
Proof with eauto.
  intros O O' P nColOO'P.
  assert (nOeqO' : O <> O'); dips.
  assert (nOeqP : O <> P); dips.
  assert (nO'eqP : O' <> P); dips.
  destruct (DrawPointProjectionOnRay O O' P nOeqO') as [ A [ H1 H2 ]].
  assert (OsrO'A : [O # O', A]).
  { destruct H1 as [ H1 |[ H | H]]; subst; try contradiction...
    contradict nOeqP. symmetry. apply (EqSgs_EqPs P A A)...
    rewrite H2. apply SegPs_sym.
  }
  clear H1.
  destruct (DrawPointProjectionOnRay O' O P) as [ A' [ H3 H4 ]]...
  assert (O'srOA : [O' # O, A']).
  { destruct H3 as [ H3 |[ H | H]]; subst; try contradiction...
    contradict nO'eqP. symmetry. apply (EqSgs_EqPs P A' A')...
    rewrite H4. apply SegPs_sym.
  }
  clear H3.
  assert (nOeqA : O <> A); dips.
  destruct (DrawOppositePoint O A) as [ B [ H5 H6 ]]...
  assert (nO'eqA' : O' <> A'); dips.
  destruct (DrawOppositePoint O' A') as [ B' [ H7 H8 ]]...
  destruct (DrawExtensionLinePP O O') as [ x [ Oox O'ox ]]...
  assert (nPox : ~ [ P @ x ]). { contradict nColOO'P. exists x... }
  destruct (DrawPointOnOppositeSide P x) as [ Q H9 ]...
  assert (Aox : [ A @ x ]); incpt 2.
  assert (A'ox : [ A' @ x ]); incpt 2.
  assert (Box : [ B @ x ]); incpt 2.
  assert (B'ox : [ B' @ x ]); incpt 2.
  assert (nColOO'Q : ~ [O, O', Q]).
  { destruct H9 as [ _ [ nQox _ ]].
    contradict nQox. apply (ColPs_IncPt O O' Q x); try split...
  }
  assert (BAAB : [ B # A' # A # B' ]).
  { apply (IntersectionOfTwoCircles B O A A' O' B' P)...
    { rewrite <- H2... }
    { do 2 try split; betps. }
    apply BetPs_b_trans.
    { apply (BetPs_SR_BetPs O B A O'). { apply BetPs_sym... }
      apply SR_sym...
    }
    apply BetPs_sym. apply (BetPs_SR_BetPs O' B' A' O).
    apply BetPs_sym... apply SR_sym...
  }
  destruct BAAB as [ BetBA'A BetA'AB' ].
  destruct (DrawIntersectionPointCC B O A A' O' B' Q)
    as [ R H10 ]...
  { do 2 try split; betps. }
  { exists R.
    destruct H10 as [ H11 [ H12 H13 ]].
    do 3 try split...
    { rewrite <- H2. rewrite H12... }
    { rewrite <- H4. rewrite H13... }
    { exists x; split...
      split...
      apply (OSO_trans P Q R x)...
      destruct H11 as [ _ [ x' [ Oox' [ O'ox' H11 ]]]].
      assert (xeqx' : x = x'); eqls.
    }
  }
Defined.

Lemma MirrorPerpendicular :
  forall (A B C D : Point)(x y : Line),
  [ C | A # B | D ]
    -> [| A, C |] = [| A, D |]
    -> [| B, C |] = [| B, D |]
    -> [ A, B @ x ]
    -> [ C, D @ y ]
    -> x _|_ y.
Proof with eauto.
  intros * [ nAeqB [ t [ Aot [ Bot CxD ]]]] AC_AD BC_BD [ Aox Box ][ Coy Doy ].
  assert (xeqt : x = t); eqls. subst t.
  destruct (DrawIntersectionOfLineAndSegment C D x)
    as [ O [ Oox COD ]]...
  assert (nColABC : ~ [ A, B, C ]).
  { destruct CxD as [ nCox _ ]. contradict nCox; incpt 2. }
  assert (nColABD : ~ [ A, B, D ]).
  { destruct CxD as [ _ [ nDox _ ]]. contradict nDox; incpt 2. }
  assert (EqTs : {{ A # B # C | nColABC }} :=: {{ A # B # D | nColABD }}).
  { apply (SSS A B C A B D)...
    rewrite SegPs_sym. rewrite AC_AD. apply SegPs_sym.
  }
  assert (nxeqy : x <> y ).
  { destruct CxD as [ nCox _ ]. contradict nCox; subst; incpt. }
  destruct EqTs as [ _ [ _ [ _ [ H1 [ H2 H3 ]]]]]; simpl in *.
  destruct (DecidePointsOrderOnLine A B O) as [ G1 | G2 ]...
  { assert(nAeqO : A <> O); dips.
    assert (nColAOC : ~ [ A, O, C ]).
    { contradict nxeqy.
      assert (Cox : [ C @ x ]); incpt 2.
      destruct CxD as [ nCox _ ]. contradiction.
    }
    assert (nColAOD : ~ [ A, O, D ]).
    { contradict nxeqy.
      assert (Dox : [ D @ x ]); incpt 2.
      destruct CxD as [ _ [ nDox _ ]]; contradiction.
    }
    exists O, A, C, nColAOC.
    repeat split; incpt 2.
    apply UniqueRightAngle.
    { apply ConvexAngPs. }
    assert (nColCAO : ~ [C, A, O]).
    { clear H1 H2 H3. contradict nColABC.
      exists x; repeat split; incpt 2.
    }
    assert (nColDAO : ~ [D, A, O]).
    { clear H1 H2 H3. contradict nColABD.
      exists x; repeat split; incpt 2.
    }
    assert (H4 : [|C # A # O | nColCAO |] = [|D # A # O | nColDAO|]).
    { erewrite (ConvexAngPs_inv C A O C B nColCAO).
      { rewrite H3.
        erewrite (ConvexAngPs_inv D A O D B nColDAO);
        try reflexivity; betps 2. apply SR_refl; dips.
      }
      apply SR_refl; dips.
      apply SR_sym; dips.
    }
    assert (EqTr : {{ C # A # O | nColCAO }} :=: {{ D # A # O | nColDAO }}).
    { apply (SAS C A O D A O)...
      rewrite SegPs_sym. rewrite AC_AD. rewrite SegPs_sym...
    }
    destruct EqTr as [ G2 [ G3 [ G4 [ G5 [ G6 G7 ]]]]];
    simpl in *...
    pir (nColPerPs_1 C A O nColCAO) => nColAOC.
    pir (nColPerPs_1 D A O nColDAO) => nColAOD.
    rewrite G6 at 1.
    erewrite (ConvexAngPs_sym A O D nColAOD).
    apply BetPs_SupAngPs. apply BetPs_sym...
  }
  { assert(nBeqO : B <> O). { destruct G2 as [ H5 [ H6 H7 ]]... }
    assert (nColBOC : ~ [ B, O, C ]).
    { contradict nxeqy. assert (Cox : [ C @ x ]); incpt 2.
      destruct CxD as [ nCox _ ]. contradiction.
    }
    assert (nColBOD : ~ [ B, O, D ]).
    { contradict nxeqy. assert (Dox : [ D @ x ]); incpt 2.
      destruct CxD as [ _ [ nDox _ ]]. contradiction.
    }
    exists O, B, C, nColBOC.
    repeat split; incpt 2.
    apply UniqueRightAngle. apply ConvexAngPs.
    assert (nColCBO : ~ [C, B, O]).
    { clear H1 H2 H3. contradict nColABC.
      exists x; repeat split; incpt 2.
    }
    assert (nColDBO : ~ [D, B, O]).
    { clear H1 H2 H3. contradict nColABD.
      exists x; repeat split; incpt 2.
    }
    assert (H4 : [|C # B # O | nColCBO |] = [|D # B # O | nColDBO|]).
    { erewrite (ConvexAngPs_inv C B O C A nColCBO).
      erewrite ConvexAngPs_sym. rewrite H1.
      erewrite (ConvexAngPs_inv D B O D A nColDBO).
      erewrite ConvexAngPs_sym. reflexivity. apply SR_refl; dips.
      apply SR_sym; dips. apply SR_refl; dips. apply SR_sym; dips.
    }
    assert (EqTr : {{ C # B # O | nColCBO }} :=: {{ D # B # O | nColDBO }}).
    { apply (SAS C B O D B O)...
      rewrite SegPs_sym. rewrite BC_BD. rewrite SegPs_sym...
    }
    destruct EqTr as [ G1 [ G3 [ G4 [ G5 [ G6 G7 ]]]]];
    simpl in *...
    pir (nColPerPs_1 C B O nColCBO) => nColBOC.
    pir (nColPerPs_1 D B O nColDBO) => nColBOD.
    rewrite G6 at 1.
    erewrite (ConvexAngPs_sym B O D nColBOD).
    apply BetPs_SupAngPs. apply BetPs_sym...
  }
  Unshelve. ncolperps. ncolperps. ncolperps. ncolperps.
Qed.

Example DrawMirrorPerpendicular : forall (A B C D : Point),
  [ C | A # B | D ]
    -> [| A, C |] = [| A, D |]
    -> [| B, C |] = [| B, D |]
    -> { O : Point | [ A, O, B ] /\ [ C # O # D ] /\ [| O, C |] = [| O, D |] }.
Proof with eauto.
  intros * [ nAeqB H ] AC_AD BC_BD.
  destruct (DrawExtensionLinePP A B nAeqB) as [ x [ Aox Box ]].
  assert (CxD : [C | x | D]).
  { destruct H as [ t [ Aot [ Bot CtD ]]].
    assert (xeqt : x = t); eqls.
  }
  clear H.
  destruct (DrawIntersectionOfLineAndSegment C D x)
    as [ O [ Oox COD ]]...
  assert (nCeqD : C <> D); dips.
  destruct (DrawExtensionLinePP C D nCeqD) as [ y [ Coy Doy ]].
  elim CxD; intros nCox [ nDox H ] .
  assert (nxeqy : x <> y ); dils.
  assert (nColABC : ~ [ A, B, C ]); ncolps.
  assert (nColABD : ~ [ A, B, D ]); ncolps.
  assert (EqTs : {{ A # B # C | nColABC }} :=: {{ A # B # D | nColABD }}).
  { apply (SSS A B C A B D)...
    rewrite SegPs_sym. rewrite AC_AD. apply SegPs_sym.
  }
  destruct EqTs as [ _ [ _ [ _ [ H1 [ H2 H3 ]]]]]; simpl in *.
  exists O; repeat split...
  destruct (DecidePointsOrderOnLine A B O) as [ G1 | G2 ]...
  { assert(nAeqO : A <> O). { destruct G1 as [ H5 [ H6 H7 ]]... }
    assert (nColAOC : ~ [ A, O, C ]); ncolps.
    assert (nColAOD : ~ [ A, O, D ]); ncolps.
    assert (nColCAO : ~ [ C, A, O ]); ncolps.
    assert (nColDAO : ~ [ D, A, O ]); ncolps.
    assert (H4 : [|C # A # O | nColCAO |] = [|D # A # O | nColDAO|]).
    { erewrite (ConvexAngPs_inv C A O C B nColCAO);
      try reflexivity; try apply SR_refl; dips; betps.
      erewrite (ConvexAngPs_inv D A O D B nColDAO);
      try reflexivity; try apply SR_refl; dips; betps.
    }
    assert (EqTr : {{ C # A # O | nColCAO }} :=: {{ D # A # O | nColDAO }}).
    { apply (SAS C A O D A O)...
      rewrite SegPs_sym. rewrite AC_AD. rewrite SegPs_sym...
    }
    destruct EqTr as [ G2 [ G3 [ G4 [ G5 [ G6 G7 ]]]]]; simpl in *...
  }
  { assert(nBeqO : B <> O). { destruct G2 as [ H5 [ H6 H7 ]]... }
    assert (nColBOC : ~ [ B, O, C ]); ncolps.
    assert (nColBOD : ~ [ B, O, D ]); ncolps.
    assert (nColCBO : ~ [ C, B, O ]); ncolps.
    assert (nColDBO : ~ [ D, B, O ]); ncolps.
    assert (H4 : [|C # B # O | nColCBO |] = [|D # B # O | nColDBO|]).
    { erewrite (ConvexAngPs_inv C B O C A nColCBO);
      try reflexivity; try apply SR_refl; dips; betps.
      erewrite (ConvexAngPs_inv D B O D A nColDBO);
      try reflexivity; try apply SR_refl; dips; betps.
      erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym...
    }
    assert (EqTr : {{ C # B # O | nColCBO }} :=: {{ D # B # O | nColDBO }}).
    { apply (SAS C B O D B O)...
      rewrite SegPs_sym. rewrite BC_BD. rewrite SegPs_sym...
    }
    destruct EqTr as [ G1 [ G3 [ G4 [ G5 [ G6 G7 ]]]]];
    simpl in *...
  }
  Unshelve. ncolps. ncolps.
Defined.

Lemma EqSgs_BetPs :
  forall A B C : Point,
  A <> C
    -> [ A, B, C ]
    -> [| A, B |] = [| B, C |]
    -> [ A # B # C ].
Proof with eauto.
  intros A B C nAeqC ColABC ABeqBC.
  assert (nAeqB : A <> B).
  { contradict nAeqC; subst.
    rewrite NullSeg_def in ABeqBC. symmetry in ABeqBC.
    apply NullSeg_EqPs...
  }
  assert (nBeqC : B <> C); dips.
  destruct (DecidePointsBetweenness A B C) as [[ ABC | BCA ]| BAC ]...
  { contradict nAeqC.
    apply (SR_EqSgs_EqPs B A C).
    { left. apply SR_sym. apply BetPs_SR; betps. }
    { rewrite <- ABeqBC. apply SegPs_sym. }
  }
  { contradict nAeqC.
    apply (SR_EqSgs_EqPs B A C).
    { left. apply BetPs_SR; betps. }
    { rewrite <- ABeqBC. apply SegPs_sym. }
  }
Qed.

Lemma DiameterPs_BetPs :
  forall A B C D E : Point,
  [ A # B # C ]
    -> [ A -- B -- D ]
    -> [ A -- C -- E ]
    -> [ A # D # E ].
Proof with eauto.
  intros A B C D E ABC [ ABD AB_BD][ ACE AC_CE ].
  destruct (BetPs_3DiPs A B C ABC) as [ nAeqB [ nBeqC nAeqC ]].
  destruct (BetPs_3DiPs A B D ABD) as [ _ [ nBeqD nAeqD ]].
  destruct (BetPs_3DiPs A C E ACE) as [ _ [ nCeqE nAeqE ]].
  assert (nDeqE : D <> E).
  { contradict nBeqC; subst. apply (UniqueMiddlePoint A B C E); split... }
  destruct (BetPs_ColPs A B C ABC) as [ x [ Aox [ Box Cox ]]].
  assert (Dox : [ D @ x ]); incpt 2.
  assert (Eox : [ E @ x ]); incpt 2.
  assert (AD : [|A, B|] ++ [|B, D|] = [|A, D|]).
  { apply (BetPs_PlusS A B D)... }
  assert (AE : [|A, C|] ++ [|C, E|] = [|A, E|]).
  { apply (BetPs_PlusS A C E)... }
  assert (ADltAE : [|A, D|] << [|A, E|]).
  { rewrite <- AD. rewrite <- AE. rewrite <- AB_BD. rewrite <- AC_CE.
    rewrite (SegPs_sym B A). rewrite (SegPs_sym C A).
    apply (LtS_LtS_PlusLtS ([|A, B|])([|A, C|])([|A, B|])([|A, C|])).
    apply (BetPs_LtS A B C ABC). apply (BetPs_LtS A B C ABC).
  }
  destruct (DrawSubtractionOfTwoSegments ([|A, D|])([|A, E|]))
    as [ DE [ H1 H2 ]]...
  apply (LtS_SR_BetPs A D E)... apply (SR_trans A D B E).
  apply SR_sym. apply (BetPs_SR A B D)...
  apply (BetPs_SR A B E). apply (BetPs_c_trans A B C E)...
Qed.

Theorem EquidistantLine :
  forall (A B C P Q : Point),
  [ P | A # B | Q ]
    -> [| A, P |] = [| A, Q |]
    -> [| B, P |] = [| B, Q |]
    -> [| C, P |] = [| C, Q |] <-> [ A, B, C ].
Proof with eauto.
  intros * AB_PQ AP_AQ BP_BQ.
  assert (ABPQ := AB_PQ).
  destruct ABPQ as [ nAeqB [ x [ Aox [ Box PxQ ]]]].
  destruct (DrawMirrorPerpendicular A B P Q)
    as [ O [ ColAOB [ POQ OP_OQ ]]]...
  assert (nPeqQ : P <> Q); dips.
  destruct (DrawExtensionLinePP P Q nPeqQ) as [ y [ Poy Qoy ]].
  assert (xperpy : x _|_ y). { apply (MirrorPerpendicular A B P Q x y)... }
  split.
  { intros CP_CQ.
    destruct (classic ([A, B, C])) as [ ColABC | nColABC ]...
    exfalso.
    assert (nCox : ~ [ C @ x ]); nincpt.
    assert (nCoy : ~ [ C @ y ]).
    { intros Coy.
      assert (PCQ : [ P # C # Q ]).
      { apply EqSgs_BetPs... rewrite SegPs_sym. rewrite CP_CQ... }
      assert (CeqO : C = O). { apply (UniqueMiddlePoint P C O Q); split... }
      subst. contradict nColABC; colperps.
    }
    assert (nOeqC : O <> C).
    { intros OeqC; subst. contradict nColABC; colperps. }
    destruct (DrawExtensionLinePP O C nOeqC) as [ z [ Ooz Coz ]].
    assert (nyeqz : y <> z). { contradict nCoy. subst... }
    assert (OC_PQ : [ P | O # C | Q ]).
    { repeat split; dips. exists z. repeat split; dips.
      { contradict nyeqz.
        apply (DiPs_EqLs O P y z); dips; repeat split; incpt 2.
      }
      { contradict nyeqz.
        apply (DiPs_EqLs O P y z); dips; repeat split; incpt 2.
      }
    }
    assert (zperpy : z _|_ y).
    { apply (MirrorPerpendicular O C P Q z y); dips. }
    assert (xeqz : x = z).
    { apply (PerpLs_EqLs O y x z); repeat split... incpt 2.
      eapply (ColPs_IncPt A B O)...
      apply PerpLs_sym... apply PerpLs_sym...
    }
    subst z. contradict nColABC.
    exists x...
  }
  { intros ColABC.
    assert (Oox : [ O @ x ]). apply (ColPs_IncPt A B O x)...
    assert (Cox : [ C @ x ]). apply (ColPs_IncPt A B C x)...
    assert (Ooy : [ O @ y ]). apply (BetPs_IncPt P Q O y)...
    destruct (classic (C = O)) as [ CeqO | nCeqO ].
    { subst... }
    { assert (nColPOC : ~ [P, O, C]).
      { apply PerpLs_ConvLs in xperpy.
        destruct xperpy as [ nxeqy _ ]. contradict nxeqy.
        apply (DiPs_EqLs O P x y); dips; repeat split; incpt 2.
      }
      assert (nColQOC : ~ [Q, O, C]).
      { apply PerpLs_ConvLs in xperpy.
        destruct xperpy as [ nxeqy _ ]. contradict nxeqy.
        apply (DiPs_EqLs O Q x y); dips; repeat split; incpt 2.
      }
      assert (EqTr : {{ P # O # C | nColPOC }} :=: {{ Q # O # C | nColQOC }}).
      { apply SAS...
        rewrite SegPs_sym. rewrite OP_OQ. apply SegPs_sym.
        rewrite (PerpLs_EqA90 O P C y x)...
        rewrite (PerpLs_EqA90 O Q C y x)...
        apply PerpLs_sym... apply PerpLs_sym...
      }
      destruct EqTr as [ H1 [ H2 [ H3 _ ]]]; simpl in *...
    }
  }
Qed.

(** Problem #46 *)
(** Euclid, Book I : Proposition 11. *)
(* To draw a straight line at right angles to a given infinite straight line
 from a given point on it. *)
Definition DrawPerpFromPointOnLine :
  forall (A : Point)(x : Line),
  [ A @ x ]
    -> { y : Line | [ A @ y ] /\ x _|_ y }.
Proof with eauto.
  intros O x Oox.
  destruct (DrawDistinctPointOnLine O x Oox) as [ A [ nOeqA Aox ]].
  destruct (DrawOppositePoint O A nOeqA) as [ B [ AOB OA_OB ]].
  destruct (BetPs_3DiPs A O B AOB) as [ _ [ nOeqB nAeqB ]].
  assert (Box : [B @ x]); incpt 2.
  destruct (DrawPointApartLine x) as [ P nPox ].
  assert (nColABP : ~ [ A, B, P ]). { contradict nPox; incpt 2. }
  destruct (DrawEquilateralTriangleSS A B P)
    as [ C [ H1 [ BC_AB AC_AB ]]]...
  assert (nColABC : ~ [ A, B, C ]).
  { apply SHb_sym in H1. eapply SH_nColPs... }
  clear dependent P.
  assert (nOeqC : O <> C). { contradict nColABC; subst... }
  assert (nColAOC : ~ [ A, O, C ]).
  { contradict nColABC. exists x; repeat split; incpt 2. }
  assert (nColCOB : ~ [ C, O, B ]).
  { contradict nColAOC. exists x; repeat split; incpt 2. }
  destruct (DrawExtensionLinePP O C nOeqC) as [ y [ Ooy Coy ]].
  exists y; split...
  assert (H : [|A # O # C | nColAOC|] = [|C # O # B | nColCOB|]).
  { erewrite ConvexAngPs_sym...
    apply -> IsoscelesMedianAltitude...
    { rewrite SegPs_sym. symmetry. rewrite SegPs_sym... }
    { rewrite SegPs_sym. rewrite AC_AB.
      rewrite <- BC_AB. apply SegPs_sym...
    }
  }
  exists O, A, C, nColAOC; repeat split...
  eapply EqSupAngPs_RightAngPs...
  Unshelve. ncolperps.
Defined.

(** Problem #47 *)
(** Euclid, Book I : Proposition 12. *)
(* To draw a straight line perpendicular to a given infinite straight line
 from a given point not on it. *)
Definition DrawPerpFromPointApartLine :
  forall (A : Point)(x : Line),
  ~ [ A @ x ]
    -> { y : Line | [ A @ y ] /\ x _|_ y }.
Proof with eauto.
  intros P x nPox .
  destruct (DrawPointOnLine x) as [ A Aox ].
  destruct (DrawDistinctPointOnLine A x Aox) as [ B [ nAeqB Box ]].
  destruct (DrawMirrorPoint A B P)
    as [ Q [ AP_AQ [ BP_BQ PxQ ]]]; ncolps.
  destruct (DrawMirrorPerpendicular A B P Q)
    as [ O [ ColAOB [ POQ OP_OQ ]]]...
  destruct (DrawLineThroughOrderedPoints P O Q)
    as [ y [ Poy [ Ooy Qoy ]]]...
  exists y; split...
  eapply (MirrorPerpendicular A B P Q x y)...
Defined.

Lemma EqAltAs_nSS :
  forall (A B C D E: Point)(x y z : Line)
         (nColBAC : ~ [ B, A, C ])(nColABD : ~ [ A, B, D ]),
  [ A, B @ x ] -> [ A, C @ y ] -> [ B, D @ z ] -> [ C | x | D ]
    -> [| B # A # C | nColBAC |] = [| A # B # D | nColABD |]
    -> [ E @ y ] -> [ E @ z ] -> ~ [ x | D, E ].
Proof with eauto.
  intros * [ Aox Box ][ Aoy Coy ][ Boz Doz ] OSxCD CABeqDBA Eoy Eoz SSxDE.
  assert (H := SSxDE); destruct H as [ nDox [ nEox _ ]]...
  assert (nxeqy : x <> y). { intros xeqy. subst y... }
  assert (nxeqz : x <> z). { intros xeqz. subst z... }
  assert (nyeqz : y <> z).
  { contradict nxeqy. subst z. apply (DiPs_EqLs A B x y); dips. }
  assert (nAeqE : A <> E). { contradict nxeqz. subst E; eqls. }
  assert (nBeqE : B <> E). { contradict nxeqy. subst E; eqls. }
  assert (OSxCE : [ C | x | E ]). apply (OSO_trans C D E x)...
  destruct (DrawSegmentOnRay A C B E)
    as [ F [[ AsrCF |[ AeqC | FeqA ]] AFeqBE ]]; dips.
  { assert (SSxCF : [ x | C, F ]).
    { apply (SR_SS A C F x Aox)...
      destruct OSxCE as [ H1 [ H2 H3 ]]...
    }
    assert (nFox : ~ [ F @ x ]). { destruct SSxCF as [ H1 [ H2 H3 ]]... }
    assert (nColBAF : ~ [ B, A, F ]).
    { contradict nFox. apply (ColPs_IncPt B A F); dips. }
    assert (nColABE : ~ [ A, B, E ]).
    { contradict nEox. apply (ColPs_IncPt A B E); dips. }
    assert (nAeqF : A <> F); dips.
    assert (nBeqF : B <> F); dips.
    assert (BAF_ABE : [|B # A # F | nColBAF|] = [|A # B # E | nColABE|]).
    { erewrite (ConvexAngPs_inv B A F B C); try apply SR_refl; dips.
      erewrite (ConvexAngPs_inv A B E A D); try apply SR_refl; dips.
      apply (SS_SR B E D x)... apply SS_sym...
      apply SR_sym; auto.
    }
    assert (EqTr : {{ B # A # F | nColBAF }} :=: {{ A # B # E | nColABE }}).
    { eapply (SAS B A F A B E); try apply SegPs_sym... }
    eassert (ABF_BAE : [|A # B # F | _ |] = [|B # A # E | _ |]).
    { destruct EqTr as [ _ [ _ [ _ [ _ [ _ H ]]]]]; simpl in *.
      erewrite ConvexAngPs_sym. symmetry. erewrite ConvexAngPs_sym. symmetry.
      apply H.
    }
    assert (BetFAE : [ F # A # E ]).
    { eapply OS_OR.
      { apply Aox. }
      { exists y; repeat split; incpt. }
      { apply OS_sym.
        eapply OSO_trans.
        { apply OS_sym. apply OSxCE. }
        { apply SSxCF. }
      }
    }
    assert (BetEBF : [ E # B # F ]).
    { eapply (EqSupAngPs_BetPs A F B E B E A F)...
      { erewrite ConvexAngPs_sym. rewrite BAF_ABE. apply ConvexAngPs_sym. }
      { repeat split; dips.
        exists x; repeat split...
        exists A; split... apply BetPs_sym...
      }
    }
    assert (Foy : [ F @ y ]). { incpt 2. }
    assert (Boy : [ B @ y ]). { incpt 2. }
    clear BAF_ABE ABF_BAE EqTr CABeqDBA.
    contradict nColBAC.
    exists y; repeat split...
  }
  { contradict AeqC; dips. }
  { subst. symmetry in AFeqBE. apply EqSgs_EqPs in AFeqBE. contradiction. }
  Unshelve. ncolperps. ncolperps. ncolperps. ncolperps.
Qed.

(** Theorem #82 *)
(** Euclid, Book I : Proposition 27. *)
(* If a straight line falling on two straight lines
 makes the alternate angles equal to one another, then the straight lines
 are parallel to one another. *)
Theorem EqAltAs_ParLs :
  forall (A B C D : Point)(x y z : Line)
         (nColABC : ~ [ A, B, C ])(nColBAD : ~ [ B, A, D ]),
  [ A, B @ x ]
    -> [ B, C @ y ]
    -> [ A, D @ z ]
    -> [ C | x | D ]
    -> [| A # B # C | nColABC |] = [| B # A # D | nColBAD |]
    -> y || z.
Proof with eauto.
  intros * [ Aox Box ][ Boy Coy ][ Aoz Doz ] CxD ABCeqBAD.
  intros [ nyeqz [ P [ Poy Poz ]]].
  assert (nxeqy : x <> y).
  { intros xeqy. subst y. destruct CxD as [ H1 [ H2 H3 ]]... }
  assert (nxeqz : x <> z).
  { intros xeqz. subst z. destruct CxD as [ H1 [ H2 H3 ]]... }
  assert (nCox : ~ [ C @ x ]); incpt.
  assert (nDox : ~ [ D @ x ]); incpt.
  assert (nPox : ~ [ P @ x ]).
  { destruct (DecidePointsDistinction A P B) as [ nAeqP | nBeqP ]; dips.
    { contradict nxeqz; eqls. }
    { contradict nxeqy; eqls. }
  }
  assert (nAeqP : A <> P); dips.
  assert (nBeqP : B <> P); dips.
  destruct (PlaneSeparation C D P x nPox CxD)
    as [[ CxP SSxDP ]|[ SSxCP DxP ]].
  { eapply (EqAltAs_nSS B A C D P x y z)... }
  { eapply (EqAltAs_nSS A B D C P x z y)...
    eapply OSO_trans...
    apply SS_sym. apply SSxCP.
  }
Qed.

(** Euclid, Book I : Proposition 28a. *)
(* If a straight line falling on two straight lines makes
 the sum of the interior angles on the same side equal to two right angles,
 then the straight lines are parallel to one another.  *)
Lemma SumAs_Eq180_ParLs :
  forall (A B C D : Point)(x y z : Line)
         (nColABC : ~ [ A, B, C ])(nColBAD : ~ [ B, A, D ]),
  [ A, B @ x ]
    -> [ B, C @ y ]
    -> [ A, D @ z ]
    -> [ x | C, D ]
    -> [| A # B # C | nColABC |] +++ [| B # A # D | nColBAD |] = A180
    -> y || z.
Proof with eauto.
  intros * [ Aox Box ][ Boy Coy ][ Aoz Doz ] xCD ABCeqBAD.
  assert (nxeqy : x <> y).
  { intros xeqy. subst y. destruct xCD as [ H1 [ H2 H3 ]]... }
  assert (nxeqz : x <> z).
  { intros xeqz. subst z. destruct xCD as [ H1 [ H2 H3 ]]... }
  assert (nCox : ~ [ C @ x ]); incpt.
  assert (nDox : ~ [ D @ x ]); incpt.
  destruct (DrawOppositePoint A D) as [ D' [ DAD' _ ]]; dips.
  eapply (EqAltAs_ParLs A B C D' x y z)... split... incpt 2.
  apply OS_sym. eapply (OSO_trans D' D C)...
  { repeat split... contradict nDox. incpt 2. exists A; repeat split...
    apply BetPs_sym... }
  { apply SS_sym... }
  { eassert ([|B # A # D | nColBAD|] +++ [|B # A # D' | _|] = A180).
    { erewrite ConvexAngPs_sym. eapply BetPs_SupAngPs...
    }
    eapply (PlusAs_cancel_l ([|B # A # D | _ |])([|A # B # C | _ |]))...
    rewrite H. rewrite PlusAng_comm...
  }
  Unshelve.
  { clear ABCeqBAD. contradict nColBAD.
    assert (nAeqB : A <> B); dips.
    assert (D'ox : [ D' @ x ]); incpt 2.
    exists x; repeat split; incpt 2.
  }
  ncolperps.
Qed.
(** Euclid, Book I : Proposition 28b. *)
(* If a straight line falling on two straight lines makes the exterior
 angle equal to the interior and opposite angle on the same side,
 then the straight lines are parallel to one another. *)
Lemma EqAs_ParLs :
  forall (A B C B' C' : Point)(x y : Line)
         (nColABC : ~ [ A, B, C ])(nColAB'C' : ~ [ A, B', C' ]),
  [ B, C @ x ]
    -> [ B', C' @ y ]
    -> [ A # B, B' ]
    -> [ A # B | C, C' ]
    -> [| A # B # C | nColABC |] = [| A # B' # C' | nColAB'C' |]
    -> x || y.
Proof with eauto.
  intros * [ Box Cox ][ B'oy C'oy ] AsrBB' AB_CC' ABC_AB'C'.
  destruct (DrawSameHalfplaneBorderLine A B C C')
    as [ t [ Aot [ Bot SStCC' ]]]...
  intros xcony.
  assert (nBeqB' : B <> B').
  { intros BeqB'; subst B'.
    assert (BsrCC' : [B # C, C']).
    { eapply SH_EqConvexAs_SR.
      apply SHa_sym. apply AB_CC'.
      apply ABC_AB'C'.
    }
    destruct xcony as [ nxeqy [ P [ Pox Poy ]]].
    assert (C'ox : [ C' @ x ]); incpt.
    assert (BeqC' : B = C'); eqps.
    subst C'. destruct BsrCC' as [ _ [ H _ ]]. contradiction.
  }
  assert (B'ot : [ B' @ t ]); incpt 2.
  assert (H := SStCC'); destruct H as [ nCot [ nC'ot _ ]]...
  destruct (DrawSegmentExtension C B) as [ D BetCBD ]; dips.
  assert (nDot : ~ [ D @ t ]). { contradict nCot; incpt 2. }
  assert (nxeqt : x <> t). { contradict nCot; subst... }
  assert (nyeqt : y <> t). { contradict nC'ot; subst... }
  contradict xcony.
  eapply (EqAltAs_ParLs B' B D C' t x y).
  { split; incpt 2. }
  { split; incpt 2. }
  { split; incpt 2. }
  { eapply (OSO_trans D C C' t)... repeat split; nincpt.
    exists B; split... apply BetPs_sym...
  }
  { destruct (DecidePointsOrderOnRay A B B') as [ H1 | H2 ]...
    { erewrite ConvexAngPs_sym in ABC_AB'C'.
      eapply (EqSupConvexAngPs B C A D B' A C' B) in ABC_AB'C'...
      symmetry. erewrite ConvexAngPs_sym. rewrite <- ABC_AB'C'.
      apply ConvexAngPs_inv.
      { apply BetPs_SR in H1... destruct H1. apply SR_sym... }
      { apply SR_refl; dips. }
    }
    { erewrite <- (BetPs_EqVertAngPs B A C B' D)...
      rewrite ABC_AB'C'. erewrite ConvexAngPs_sym.
      symmetry. erewrite ConvexAngPs_sym.
      apply ConvexAngPs_inv...
      { apply SR_refl; dips. }
      { apply BetPs_SR in H2... destruct H2... }
    }
  }
  Unshelve. ncolperps. ncolps. ncolps. contradict nDot.
  eapply (ColPs_IncPt A B D t); dips. ncolps. ncolperps. ncolps.
Qed.

Lemma PerpLs_PerpLs_ParLs :
  forall (x y z : Line),
  x _|_ y
    -> x _|_ z
    -> y || z.
Proof with eauto.
  intros x y z xperpy xperpz.
  elim xperpy.
  intros O [ A [ B [ AOB [[ Oox Ooy ][ Aox [ Boy H1 ]]]]]].
  destruct (DrawPointsOnRightAngle O A B x y AOB)
    as [ C [ D [ Cox [ Dox [ AOC [ BOD H ]]]]]];
    try split...
  destruct H
    as [ BOC [ COD [ DOA [ BOC90 [ COD90 DOA90 ]]]]].
  elim xperpz.
  intros O' [ A' [ B' [ A'O'B' [[ O'ox O'oz ][ A'ox [ B'oz H2 ]]]]]].
  destruct (DrawPointsOnRightAngle O' A' B' x z A'O'B')
    as [ C' [ D' [ C'ox [ D'ox [ A'O'C' [ B'O'D' H ]]]]]];
    try split...
  destruct H
    as [ B'O'C' [ C'O'D' [ D'O'A' [ B'O'C'90 [ C'O'D'90 D'O'A'90 ]]]]].
  assert (nOeqA : O <> A); dips.
  assert (nO'eqA' : O' <> A'); dips.
  destruct (DecideRayDirection ({{O # A | nOeqA}})({{O' # A' | nO'eqA'}}))
    as[ SD | OD ]; simpl in *.
  { repeat split... }
  { eassert ({{A # O | _ }} ~~ {{A' # O' | _ }}).
		{ apply EqDirRs_EqDirOpRs... }
		clear SD.
    destruct H as [[ H3 H4 ]|[[ H5 H6 ]|[ H7 H8 ]]]; simpl in *.
    { subst A'.
      destruct (DecideSameSide B B' x) as [ SS | OS ]; nincpt.
      { eapply (EqAs_ParLs A O B O' B')...
        { split... }
        rewrite H1...
      }
      { eapply (EqAs_ParLs A O B O' D')...
        { split...
          exists x; split... split...
          eapply OOS_trans.
          { apply OS. }
          { repeat split... destruct OS as [ _ [ H _ ]]...
            nincpt.
          }
        }
        rewrite H1... erewrite ConvexAngPs_sym...
      }
    }
    { assert (SOO' : [A # O, O']).
      { apply (SR_trans A O A' O').
        { apply SR_sym... }
        { apply BetPs_SR in H6; tauto. }
      }
      destruct (DecideSameSide B B' x) as [ SS | OS ]; nincpt.
      { eapply (EqAs_ParLs A O B O' B')...
        { split... }
        rewrite H1... erewrite ConvexAngPs_sym. rewrite <- H2.
        erewrite ConvexAngPs_sym. apply ConvexAngPs_inv. apply SR_refl; dips.
        apply BetPs_SR in H6; tauto.
      }
      { eapply (EqAs_ParLs A O B O' D')...
        { split...
          exists x; split... split...
          eapply OOS_trans.
          { apply OS. }
          { repeat split... destruct OS as [ _ [ H _ ]]...
            nincpt.
          }
        }
        rewrite H1... erewrite ConvexAngPs_sym...
        rewrite <- D'O'A'90.
        apply ConvexAngPs_inv. apply SR_refl; dips.
        apply BetPs_SR in H6; tauto.
      }
    }
    { assert (SOO' : [A' # O, O']).
      { apply (SR_trans A' O A O')...
        apply SR_sym... apply BetPs_SR in H8; tauto.
      }
      destruct (DecideSameSide B B' x) as [ SS | OS ]; nincpt.
      { eapply (EqAs_ParLs A' O B O' B')...
        { split; dips. }
        rewrite H2... erewrite ConvexAngPs_sym. rewrite <- H1.
        symmetry. erewrite ConvexAngPs_sym. apply ConvexAngPs_inv.
        apply SR_refl; dips.
        apply BetPs_SR in H8; tauto.
      }
      { eapply (EqAs_ParLs A' O B O' D')...
        { split; dips.
          exists x; split... split...
          eapply OOS_trans.
          { apply OS. }
          { repeat split... destruct OS as [ _ [ H _ ]]...
            nincpt.
          }
        }
        symmetry. erewrite ConvexAngPs_sym... rewrite D'O'A'90.
        rewrite <- H1. erewrite ConvexAngPs_sym...
        symmetry. erewrite ConvexAngPs_sym...
        apply ConvexAngPs_inv. apply SR_refl; dips.
        apply SR_sym... apply BetPs_SR in H8; tauto.
      }
    }
  }
  { apply ColRs_DiDirRs_EqDirOpRs in OD.
    eassert (SD : {{O' # C' | _ }} == !({{O' # A' | nO'eqA'}})).
		{ eapply OpRs_BetPs. apply BetPs_sym... }
		apply EqRs_EqRsDir in SD.
    eassert (H : {{ A # O | _ }} ~~ {{C' # O' | _ }}).
		{ apply EqDirRs_EqDirOpRs...
	    eapply EqRaysDir_trans. apply OD. apply EqRaysDir_sym...
	  }
		clear SD OD.	
    destruct H as [[ H3 H4 ]|[[ H5 H6 ]|[ H7 H8 ]]]; simpl in *.
    { subst C'.
      destruct (DecideSameSide B B' x) as [ SS | OS ]; nincpt.
      { eapply (EqAs_ParLs A O B O' B')...
        { split... }
        rewrite H1... erewrite ConvexAngPs_sym...
      }
      { eapply (EqAs_ParLs A O B O' D')...
        { split...
          exists x; split... split...
          eapply OOS_trans.
          { apply OS. }
          { repeat split... destruct OS as [ _ [ H _ ]]...
            nincpt.
          }
        }
        rewrite H1...
      }
    }
    { assert (SOO' : [A # O, O']).
      { apply (SR_trans A O C' O').
        { apply SR_sym... }
        { apply BetPs_SR in H6; tauto. }
      }
      destruct (DecideSameSide B B' x) as [ SS | OS ]; nincpt.
      { eapply (EqAs_ParLs A O B O' B')...
        { split... }
        rewrite H1... rewrite <- H2. symmetry. erewrite ConvexAngPs_sym.
        erewrite ConvexAngPs_inv. rewrite B'O'C'90... apply SR_refl; dips.
        apply SR_sym. apply BetPs_SR in H6; tauto.
      }
      { eapply (EqAs_ParLs A O B O' D')...
        { split...
          exists x; split... split...
          eapply OOS_trans.
          { apply OS. }
          { repeat split... destruct OS as [ _ [ H _ ]]...
            nincpt.
          }
        }
        rewrite H1... rewrite <- C'O'D'90. erewrite ConvexAngPs_sym.
        symmetry. erewrite ConvexAngPs_sym.
        apply ConvexAngPs_inv. apply SR_refl; dips.
        apply SR_sym. apply BetPs_SR in H6; tauto.
      }
    }
    { assert (SOO' : [C' # O, O']).
      { apply (SR_trans C' O A O')...
        apply SR_sym... apply BetPs_SR in H8; tauto.
      }
      destruct (DecideSameSide B B' x) as [ SS | OS ]; nincpt.
      { eapply (EqAs_ParLs C' O B O' B')...
        { split; dips. }
        symmetry. erewrite ConvexAngPs_sym. rewrite B'O'C'90.
        symmetry. erewrite ConvexAngPs_sym. erewrite ConvexAngPs_inv.
        erewrite ConvexAngPs_sym in H1. apply H1.
        apply SR_refl; dips. apply SR_sym. apply BetPs_SR in H8; tauto.
      }
      { eapply (EqAs_ParLs C' O B O' D')...
        { split; dips.
          exists x; split... split...
          eapply OOS_trans.
          { apply OS. }
          { repeat split... destruct OS as [ _ [ H _ ]]...
            nincpt.
          }
        }
        rewrite C'O'D'90.
        erewrite ConvexAngPs_sym... erewrite ConvexAngPs_sym in H1.
        rewrite <- H1. apply ConvexAngPs_inv. apply SR_refl; dips.
        apply SR_sym... apply BetPs_SR in H8; tauto.
      }
    }
    { exists x; repeat split... }
  }
  Unshelve. ncolperps.
  { clear H2. contradict A'O'B'. exists x; repeat split...
    apply (ColPs_IncPt A O' B' x); dips.
  }
  { clear H2. contradict A'O'B'. exists x; repeat split...
    apply (ColPs_IncPt A O' B' x); dips.
  }
  ncolperps.
  { clear D'O'A'90. contradict D'O'A'. exists x; repeat split...
    apply (ColPs_IncPt A O' D' x); dips.
  }
  { clear D'O'A'90. contradict D'O'A'. exists x; repeat split...
    apply (ColPs_IncPt A O' D' x); dips.
  }
  { clear H1. contradict AOB. exists x; repeat split...
    apply (ColPs_IncPt A' O B x); dips.
  }
  { clear H1. contradict AOB. exists x; repeat split...
    apply (ColPs_IncPt A' O B x); dips.
  }
  ncolperps.
  { clear H1. contradict AOB. exists x; repeat split...
    apply (ColPs_IncPt A' O B x); dips.
  }
  ncolperps. ncolperps.
  { clear H1. contradict AOB. exists x; repeat split...
    apply (ColPs_IncPt A' O B x); dips.
  }
  dips.
  { clear H2. contradict A'O'B'. exists x; repeat split...
    apply (ColPs_IncPt A O' B' x); dips.
  }
  { clear H2. contradict A'O'B'. exists x; repeat split...
    apply (ColPs_IncPt A O' B' x); dips.
  }
  { clear H2. contradict A'O'B'. exists x; repeat split...
    apply (ColPs_IncPt A O' B' x); dips.
  }
  { clear D'O'A'90. contradict D'O'A'. exists x; repeat split...
    apply (ColPs_IncPt A O' D' x); dips.
  }
  ncolperps.
  { clear D'O'A'90. contradict D'O'A'. exists x; repeat split...
    apply (ColPs_IncPt A O' D' x); dips.
  }
  { clear H1. contradict AOB. exists x; repeat split...
    apply (ColPs_IncPt C' O B x); dips.
  }
  ncolperps.
  { clear H1. contradict AOB. exists x; repeat split...
    apply (ColPs_IncPt C' O B x); dips.
  }
  ncolperps.
  { clear H1. contradict AOB. exists x; repeat split...
    apply (ColPs_IncPt C' O B x); dips.
  }
  { contradict AOB. exists x; repeat split...
    apply (ColPs_IncPt C' O B x); dips.
  }
  ncolperps.
Qed.

(** Problem #48 *)
Definition DrawParallelFromPointApartLine :
  forall (A : Point)(x : Line),
  ~ [ A @ x ]
    -> { y : Line | [ A @ y ] /\ (y || x) }.
Proof with eauto.
 intros A x nAox.
 destruct (DrawPerpFromPointApartLine A x nAox) as [ y [ Aoy xperpy ]].
 destruct (DrawPerpFromPointOnLine A y Aoy) as [ z [ Aoz yperpz ]].
 exists z; split...
 apply (PerpLs_PerpLs_ParLs y z x)...
 apply PerpLs_sym...
Defined.

Example DrawPointOnConvergentLineSameSide :
  forall (A : Point)(x y : Line),
  x >< y
    -> ~ [ A @ x ]
    -> { B : Point | [ B @ y ] /\ [ x | A, B ] }.
Proof with eauto.
  intros A x y nxpary nAox.
  destruct (DrawIntersectionPointLL x y nxpary)
    as [ O [ Oox Ooy ]].
  assert (nxeqy : x <> y). { destruct nxpary... }
  destruct (DrawDistinctPointOnLine O y Ooy) as [ B [ nBeqO Boy ]].
  destruct (DrawOppositePoint O B) as [ C [ BOC BO_OC ]]...
  assert (nBox : ~ [B @ x]). { contradict nxeqy; eqls. }
  assert (nCox : ~ [C @ x]). { contradict nBox; incpt 2. }
  assert (Coy : [C @ y]). { incpt 2. }
  destruct (DecideTwoSides B A C x) as [ AB | AC ]; repeat split...
  { exists C; split...
    apply (OOS_trans A B C x)...
    { apply OS_sym... }
    { repeat split... }
  }
  { exists B; split...
    apply (OOS_trans A C B x)...
    repeat split...
    exists O; split...
    apply BetPs_sym...
  }
Defined.

Example DrawPointOnConvergentLineOppSide :
  forall (A : Point)(x y : Line),
  x >< y
    -> ~ [ A @ x ]
    -> { B : Point | [ B @ y ] /\ [ A | x | B ] }.
Proof with eauto.
  intros A x y nxpary nAox.
  destruct (DrawIntersectionPointLL x y nxpary)
    as [ O [ Oox Ooy ]].
  destruct (DrawPointOnConvergentLineSameSide A x y nxpary nAox)
    as [ B [ Boy SSxAB ]].
  assert (nBox : ~ [ B @ x ]).
  { destruct SSxAB as [ _ [ nBox _ ]]... }
  assert (nBeqO : B <> O); dips.
  destruct (DrawSegmentExtension B O nBeqO) as [ B' BetBOB' ].
  assert (B'oy : [ B' @ y ]). { incpt 2. }
  assert (nB'eqO : B' <> O); dips.
  assert (nB'ox : ~ [ B' @ x ]).
  { contradict nBox; incpt. }
  assert (OSxBB' : [ B | x | B' ]).
  { repeat split... }
  exists B'; split...
  apply OS_sym in OSxBB'. apply SS_sym in SSxAB. apply OS_sym.
  apply (OSO_trans B' B A x)...
Defined.

End PERPENDICULARS.

Notation " x _|_ y "
  := (Perpendicular x y)
  (at level 50).

Notation " ![ a -- o -- b ] "
  := (MidRay a o b)
  (at level 60).

(*****************************************************************************)
(* 22 *) Section PARALLELS.
Context `{ cc : Concentricals }.
Context  { an : Angles on }.
Context  { sp : Superpositions on }.
Context  { pa : Parallels dc df }.
(*****************************************************************************)

Lemma Proclus :
  forall (x y z : Line),
  x >< z
    -> y || z
    -> x >< y.
Proof with eauto.
  intros * [ nxeqz [ A [ Aox Aoz ]]] yz.
  destruct (classic (x >< y)) as [ xcony | xpary ]...
  contradict nxeqz.
  apply (ParallelAxiom A x z y)...
  unfold Parallel in *. contradict yz. apply ConvLs_sym...
Qed.

(** Theorem #83 *)
(* The parallelism of lines is the equivalence relation. *)
Theorem ParLs_refl :
  forall (x : Line),
  x || x.
Proof.
  intros x [ H _ ].
  contradict H; auto.
Qed.
Theorem ParLs_sym :
  forall (x y : Line),
  x || y
    -> y || x.
Proof.
  unfold Parallel, Convergent.
  intros x y H. contradict H.
  destruct H as [ nyeqx [ A [ Aoy Aox ]]].
  split; eauto.
Qed.
(** Euclid, Book I : Proposition 30. *)
(* Straight lines parallel to the same straight line
 are also parallel to one another. *)
Theorem ParLs_trans :
  forall (x y z : Line),
  x || y
    -> y || z
    -> x || z.
Proof.
  unfold Parallel.
  intros x y z Hxy Hyz. contradict Hxy.
  apply (Proclus x y z); eauto.
Qed.
Global Instance Parallel_equiv :
  Equivalence Parallel
  := Build_Equivalence Parallel
     ParLs_refl
     ParLs_sym
     ParLs_trans.

Lemma ParLs_ConvLs_ConvLs :
  forall x y z: Line,
  y || z
    -> x >< y
    -> x >< z.
Proof with eauto.
  intros x y z yparz xconvy.
  destruct (classic (x >< z)) as [ H1 | H2 ]...
  contradict xconvy.
  apply ParLs_sym in yparz.
  apply ParLs_trans with z...
Qed.

(** Theorem #84 *)
(** Hilbert, Chapter 1 : Theorem 30. *)
(** Euclid, Book I : Proposition 29a. *)
(* A straight line falling on parallel straight lines makes the exterior
 angle equal to the interior and opposite angle on the same side. *)
Theorem ParLs_EqAs :
  forall (A B C B' C' : Point)(x y : Line)
         (nColABC : ~ [ A, B, C ])(nColAB'C' : ~ [ A, B', C' ]),
  [ B, C @ x ]
    -> [ B', C' @ y ]
    -> [ A # B, B' ]
    -> [ A # B | C, C' ]
    -> x || y
    -> [| A # B # C | nColABC |] = [| A # B' # C' | nColAB'C' |].
Proof with eauto.
  intros * [ Box Cox ][ B'oy C'oy ] AsrBB' AB_CC' xpary.
  destruct (DrawSameHalfplaneBorderLine A B C C')
    as [ t [ Aot [ Bot SStCC' ]]]...
  assert (H := SStCC'); destruct H as [ nCot [ nC'ot _ ]]...
  assert (nxeqt : x <> t). { contradict nCot; subst... }
  assert (nyeqt : y <> t). { contradict nC'ot; subst... }
  destruct (DrawAngleOnGivenHalfplane A B C A B' C' nColABC nColAB'C')
    as [ P [ nColABP [ AB_CP H ]]].
  apply SHa_sym in AB_CP.
  destruct (DrawExtensionLinePP B P) as [ z [ Boz Poz ]]; dips.
  assert (xeqz : x = z).
  { cut (x || z). { intros xparz. apply (ParLs_InsPs_EqLs B x z)... }
    apply ParLs_trans with y... apply ParLs_sym.
    apply (EqAs_ParLs A B P B' C' z y nColABP nColAB'C')...
    apply SH_trans with C... apply SHb_sym...
  }
  subst z. rewrite <- H.
  assert (B_CP : [B # C, P]).
  { apply (SS_SR B C P t); incpt.
    { destruct AB_CP as [ nAeqB [ t' [ Aot' [ Bot' tCP ]]]].
      assert (teqt' : t = t'); eqls.
    }
  }
  apply ConvexAngPs_inv... apply SR_refl; dips.
Qed.
(** Euclid, Book I : Proposition 29b. *)
(* A straight line falling on parallel straight lines makes the alternate
 interior angles equal to one another. *)
Lemma ParLs_EqAltAs :
  forall (A B C D : Point)(x y z : Line)
         (nColABC : ~ [ A, B, C ])(nColBAD : ~ [ B, A, D ]),
  [ A, B @ x ]
    -> [ B, C @ y ]
    -> [ A, D @ z ]
    -> [ C | x | D ]
    -> y || z
    -> [| A # B # C | nColABC |] = [| B # A # D | nColBAD |].
Proof with eauto.
  intros * [ Aox Box ][ Boy Coy ][ Aoz Doz ] CxD yparz.
  assert (nxeqy : x <> y).
  { intros xeqy. subst y. destruct CxD as [ H1 [ H2 H3 ]]... }
  assert (nxeqz : x <> z).
  { intros xeqz. subst z. destruct CxD as [ H1 [ H2 H3 ]]... }
  assert (nCox : ~ [ C @ x ]); incpt.
  assert (nDox : ~ [ D @ x ]); incpt.
  destruct (DrawOppositePoint A B) as [ E [ BAE _ ]]; dips.
  destruct (DrawOppositePoint A D) as [ F [ DAF _ ]]; dips.
  assert (Eox : [ E @ x ]); incpt.
  assert (nFox : ~ [ F @ x ]). { contradict nDox; incpt. }
  erewrite (BetPs_EqVertAngPs A B D E F)...
  erewrite (ConvexAngPs_inv A B C E C)...
  { eapply ParLs_EqAs...
    { split; incpt. }
    { apply SR_sym. apply BetPs_SR in BAE; tauto. }
    { split; dips.
      exists x; split; incpt. split; incpt.
      apply (OOS_trans C D F x)... repeat split...
    }
  }
  { apply BetPs_SR in BAE; tauto. }
  { apply SR_refl; dips. }
  Unshelve.
  { contradict nFox. apply (ColPs_IncPt E A F x); dips. }
  { contradict nColABC. exists x; repeat split...
    apply (ColPs_IncPt E B C x); dips.
  }
Qed.

Lemma ParLs_PerpLs_PerpLs :
  forall x y z: Line,
  y || z
    -> x _|_ y
    -> x _|_ z.
Proof with eauto.
  intros x y z yparz xperpy.
  elim xperpy.
  intros O [ A [ B [ AOB [[ Oox Ooy ][ Aox [ Boy H1 ]]]]]].
  destruct (DrawPointsOnRightAngle O A B x y AOB)
    as [ C [ D [ Cox [ Dox [ AOC [ BOD H ]]]]]];
    try split...
  destruct H
    as [ BOC [ COD [ DOA [ BOC90 [ COD90 DOA90 ]]]]].
  assert (xconvz : x >< z).
  { eapply ParLs_ConvLs_ConvLs... apply PerpLs_ConvLs... }
  destruct xconvz as [ nxeqz [ O' [ O'ox O'oz ]]].
  destruct (classic(O = O')) as [ OeqO' | nOeqO' ].
  { subst O'.
    assert(yeqz : y = z).
    { apply (ParLs_InsPs_EqLs O y z); try split... }
    subst z.
    exists O, A, B, AOB; repeat split...
  }
  { destruct (LineSeparation O A C O') as [[ O_AO' AOO' ]|[AOO' O_CO' ]]; dips.
    { destruct (DrawPointOnConvergentLineSameSide B x z)
        as [ B' [ B'oz xBB' ]]; try split...
      { clear H1. contradict AOB; incpt. }
      assert (nB'ox : ~ [ B' @ x ]). { destruct xBB'; tauto. }
      assert (nColCO'B' : ~ [C, O', B']).
      { contradict nB'ox. apply (ColPs_IncPt C O' B' x); dips. }
      exists O', C, B', nColCO'B'; repeat split...
      erewrite ConvexAngPs_sym in BOC90. rewrite <- BOC90.
      eapply ParLs_EqAs...
      { apply SR_sym. apply BetPs_SR in AOO'; tauto. }
      { split; dips. exists x; split... split... apply SS_sym... }
      { apply ParLs_sym... }
    }
    { destruct (DrawPointOnConvergentLineSameSide B x z)
        as [ B' [ B'oz xBB' ]]; try split...
      { clear H1. contradict AOB; incpt. }
      assert (nB'ox : ~ [ B' @ x ]). { destruct xBB'; tauto. }
      assert (nColAO'B' : ~ [A, O', B']).
      { contradict nB'ox. apply (ColPs_IncPt A O' B' x); dips. }
      exists O', A, B', nColAO'B'; repeat split...
      rewrite <- H1.
      eapply ParLs_EqAs...
      { apply SR_sym. apply BetPs_SR in AOO'; tauto. }
      { split; dips. exists x; split... split... apply SS_sym... }
      { apply ParLs_sym... }
    }
  }
  Unshelve. ncolperps.
Qed.

(** Theorem #85 *)
(** Hilbert, Chapter 1 : Theorem 31. *)
(** Euclid, Book I : Proposition 32. *)
(* In any triangle, if one of the sides is produced,
 then the exterior angle equals the sum of the two interior
 and opposite angles, and the sum of the three interior angles
 of the triangle equals two right angles. *)
Theorem TriangleAngleSum :
  forall (A B C : Point)(nColABC : ~ [ A, B, C ]),
    [| A # B # C | nColABC |] +++
    [| B # C # A | nCol_a A B C nColABC |] +++
    [| C # A # B | nCol_b A B C nColABC |] = A180.
Proof with eauto.
  intros A B C nColABC.
  destruct (DrawExtensionLinePP B C) as [ x [ Box Cox ]]; dips.
  destruct (DrawExtensionLinePP A B) as [ y [ Aoy Boy ]]; dips.
  destruct (DrawExtensionLinePP A C) as [ z [ Aoz Coz ]]; dips.
  destruct (DrawOppositePoint C B) as [ D [ BCD _ ]]; dips.
  assert (Dox : [ D @ x ]); incpt.
  assert (nDoy : ~ [ D @ y ]).
  { contradict nColABC. exists y; repeat split... incpt. }
  assert (nDoz : ~ [ D @ z ]).
  { contradict nColABC. exists z; repeat split... incpt. }
  destruct (DrawPointOfEqConvexAngPs A B C D nColABC BCD)
    as [ E [ AED [ nColECD H ]]].
  assert (nEox : ~ [ E @ x ]); incpt.
  assert (nEoz : ~ [ E @ z ]). { contradict nDoz; incpt. }
  assert (AED' := AED).
  assert (nColCAD : ~ [C, A, D]).
  { clear H. contradict nColABC.
    exists x; repeat split...
    apply (ColPs_IncPt C D A); dips; split...
  }
  apply (nColPs_BetPs_BR C A E D nColCAD) in AED'.
  destruct AED' as [[ nCeqA [ z' [ Coz' [ Aoz' zED ]]]] _ ].
  assert (zeqz' : z = z'); eqls.
  subst z'.
  destruct (DrawExtensionLinePP C E) as [ t [ Cot Eot ]]; dips.
  assert (ypart : y || t).
  { eapply (EqAs_ParLs D B A C E y t).
    { split... }
    { split... }
    { apply SR_sym. apply BetPs_SR... }
    { split; dips. exists x; split... split...
      eapply (SR_SS D A E x); nincpt.
      apply SR_sym. apply BetPs_SR in AED; tauto.
    }
    erewrite (ConvexAngPs_sym D C E). rewrite <- H.
    erewrite (ConvexAngPs_sym D B A). apply ConvexAngPs_inv.
    apply SR_refl; dips. apply SR_sym. apply BetPs_SR in BCD; tauto.
  }
  rewrite H.
  eassert (H1 : [|C # A # B | nCol_b A B C nColABC|] = [|A # C # E | _ |]).
  { eapply (ParLs_EqAltAs C A B E z y t)...
    { apply (nColPs_BetPs_BR C A E D) in AED.
      apply (OSO_trans B D E z).
      { repeat split...
        contradict nDoz; incpt 2.
      }
      apply SS_sym...
      clear H. contradict nColABC.
      exists x; repeat split...
      apply (ColPs_IncPt C D A); dips; split...
    }
  }
  rewrite H1.
  rewrite <- PlusAs_assoc.
  rewrite (PlusAng_comm ([|B # C # A | nCol_a A B C nColABC|])).
  rewrite PlusAs_assoc.
  eassert (H2:[|D # C # E | _ |] +++ [|E # C # A | _ |] = [|D # C # A | _ |]).
  { apply BetPs_PlusConvexAngPs... apply BetPs_sym... }
  erewrite ConvexAngPs_sym in H2. erewrite (ConvexAngPs_sym E C A) in H2.
  rewrite H2. erewrite (ConvexAngPs_sym B C A).
  apply BetPs_SupAngPs... apply BetPs_sym...
  Unshelve.
  { contradict nColCAD. exists x; repeat split...
    apply (ColPs_IncPt D B A x); dips.
  }
  ncolperps.
  { clear H. contradict nColABC. exists x; repeat split...
    apply (ColPs_IncPt D B A x); dips.
  }
  ncolps. ncolperps. ncolps. ncolperps. ncolperps.
Qed.

(** Problem #49 *)
Definition DrawPerpendicularLine :
  forall (A : Point)(x : Line),
  { y : Line | [ A @ y ] /\ x _|_ y }.
Proof with eauto.
  intros P x.
  destruct (DrawPointOnLine x) as [ A Aox ].
  destruct (DrawDistinctPointOnLine A x Aox) as [ B [ nAeqB Box ]].
  destruct (DecidePointsDistinction A P B nAeqB) as [ nAeqP | nPeqB ].
  { destruct (DrawPerpFromPointOnLine A x Aox) as [ y [ Aoy xperpy ]].
    destruct (DecidePointApartTwoLines A P x y) as [ nPox | nPoy ]...
    { apply PerpLs_ConvLs in xperpy. destruct xperpy... }
    { destruct (DrawPerpFromPointApartLine P x nPox)
        as [ t [ Pot xperpt ]].
      exists t; split...
    }
    { destruct (DrawParallelFromPointApartLine P y nPoy)
        as [ t [ Pot yperpt ]].
      exists t; split... apply (ParLs_PerpLs_PerpLs x y t)...
      apply ParLs_sym...
    }
  }
  { destruct (DrawPerpFromPointOnLine B x Box) as [ y [ Boy xperpy ]].
    destruct (DecidePointApartTwoLines B P x y) as [ nPox | nPoy ]...
    { apply PerpLs_ConvLs in xperpy. destruct xperpy... }
    { destruct (DrawPerpFromPointApartLine P x nPox)
        as [ t [ Pot xperpt ]].
      exists t; split...
    }
    { destruct (DrawParallelFromPointApartLine P y nPoy)
        as [ t [ Pot yperpt ]].
      exists t; split... apply (ParLs_PerpLs_PerpLs x y t)...
      apply ParLs_sym...
    }
  }
Defined.

(** Problem #50 *)
Definition DrawParallelLine :
  forall (A : Point)(x : Line),
  { y : Line | [ A @ y ] /\ x || y }.
Proof with eauto.
  intros A x.
  destruct (DrawPerpendicularLine A x) as [ y [ Aoy xperpy ]].
  destruct (DrawPerpendicularLine A y) as [ t [ Aot yperpt ]].
  exists t; split...
  apply (PerpLs_PerpLs_ParLs y x t)...
  apply PerpLs_sym...
Defined.

(** Problem #51 *)
Definition DecideLinesConvergence :
  forall (x y z : Line),
  x >< z
    -> { x >< y } + { y >< z }.
Proof with eauto.
  intros x a y xconvy.
  destruct (DrawIntersectionPointLL x y) as [ O [ Oox Ooy ]]...
  destruct (DrawParallelLine O a) as [ b [ Oob aparb ]].
  destruct (DrawDistinctPointOnLine O b) as [ P [ nOeqP Pob ]]...
  destruct (DecidePointApartTwoLines O P x y) as [ H1 | H2 ];
  destruct xconvy...
  { left. apply (ParLs_ConvLs_ConvLs x b a). apply ParLs_sym...
    split.
    { apply not_eq_sym. apply (nIncPt_DiLs P b x)... }
    { exists O; split... }
  }
  { right. apply ConvLs_sym.
    apply (ParLs_ConvLs_ConvLs y b a). apply ParLs_sym...
    split.
    { apply not_eq_sym. apply (nIncPt_DiLs P b y)... }
    { exists O; split... }
  }
Defined.

(** Problem #52 *)
Definition DecideLinesDistinction :
  forall (x y z : Line),
  x <> z
    -> { x <> y } + { y <> z }.
Proof with eauto.
  intros * nxeqz.
  destruct (DrawPointSeparatingTwoLines x z) as [ A [ Aox nAoz ]]...
  destruct (DrawPointSeparatingTwoLines z x) as [ B [ Boz nBox ]]...
  assert (nAeqB : A <> B); dips.
  destruct (DrawExtensionLinePP A B) as [ t [ Aot Bot ]]; dips.
  assert (nzpart : z >< t). { unfold Convergent; split; dils. }
  destruct (DecideLinesConvergence z y t nzpart) as [[ H1 H2 ]|[ H1 H2 ]].
  { right... }
  { destruct (DecideLineApartTwoPoints A B t y) as [ nAoy | nBoy ];
    dips; [left | right]; dils.
  }
Defined.

End PARALLELS.

Hint Unfold
  Convergent
  : ConLs.
Hint Unfold
  Parallel
  : ParLs.

Hint Resolve
  ParLs_InsPs_EqLs
  : EqLs.

Hint Resolve
  nIncPt_ConvLs_1 nIncPt_ConvLs_2
  : ConLs.

Tactic Notation "conls"
  := try solve
  [ congruence
  | eauto with ConLs
  | intuition eauto with ConLs ].
Tactic Notation "conls" integer(n)
  := try solve
  [ congruence
  | eauto n with ConLs
  | intuition (auto n with ConLs) ].
Tactic Notation "parls"
  := try solve
  [ congruence
  | eauto with ParLs
  | intuition eauto with ParLs ].
Tactic Notation "parls" integer(n)
  := try solve
  [ congruence
  | eauto n with ParLs
  | intuition (auto n with ParLs) ].

(*****************************************************************************)
(* 23 *) Section VONPLATO.
Context `{ cc : Concentricals }.
Context  { an : Angles on }.
Context  { sp : Superpositions on }.
Context  { pa : Parallels dc df }.
(*****************************************************************************)

Class CoTransitive { A : Type } (R : relation A) : Type
  := cotransitivity :
     forall { x y z : A }, R x z -> { R x y } + { R y z }.

Class Apartness { A : Type } (R : relation A) : Type
  := Build_Apartness {
       Apartness_Irreflexive :> Irreflexive R;
       Apartness_Symmetric :> Symmetric R;
       Apartness_CoTransitive :> CoTransitive R;
     }.

Class VonPlato :=
{
  points : Set;
  lines : Set;

  dipt : points -> points -> Prop;
  diln : lines -> lines -> Prop;
  aprt : points -> lines -> Prop;
  conv : lines -> lines -> Prop;

  eqpt (a b : points) := ~ dipt a b;
  eqln (x y : lines) := ~ diln x y;
  incd (a : points)(l : lines) := ~ aprt a l;
  parl (x y : lines) := ~ conv x y;

  twopoints := @Duple points (fun A B => dipt A B);
  drawtwopoints := @BuildDuple points (fun A B => dipt A B);

  twolines : Set := @Duple lines (fun x y => conv x y);
  drawtwolines := @BuildDuple lines (fun x y => conv x y);

  aprt_dipt : Apartness dipt;
  aprt_diln : Apartness diln;
  aprt_conv : Apartness conv;
  draw_line : forall x : twopoints,
    { l : lines | incd (da x) l /\ incd (db x) l };
  draw_point : forall x : twolines,
    { a : points | incd a (da x) /\ incd a (db x) };
  el_ax : forall (x : twopoints)(l m : lines),
    diln l m
      -> { aprt (da x) l } +
         { aprt (db x) l } +
         { aprt (da x) m } +
         { aprt (db x) m };
  cmp_aprt_dipt : forall (a b : points)(l : lines),
    aprt a l
      -> { dipt a b } + { aprt b l };
  cmp_aprt_diln : forall (a : points)(l m : lines),
    aprt a l
      -> { diln l m } + { aprt a m };
  cmp_conv_diln : forall l m n : lines,
    conv l m
      -> { diln m n } + { conv l n }
}.

Instance VP : VonPlato.
Proof with eauto.
  eapply (Build_VonPlato Point Line (fun A B => A <> B)
    (fun x y => x <> y)(fun A x => ~ [ A @ x ])(fun x y => x >< y)).
  { split.
    { intros A H. apply H; auto. }
    { intros A B H; auto. }
    { intros A B C H. apply DecidePointsDistinction; auto. }
  }
  { split.
    { intros A H. apply H; auto. }
    { intros A B H; auto. }
    { intros A B C H. apply DecideLinesDistinction; auto. }
  }
  { split.
    { intros x H. apply H; auto. }
    { intros x y H. apply ConvLs_sym; auto. }
    { intros x y z H. apply DecideLinesConvergence; auto. }
  }
  { intros [ A B nAeqB ]; unfold incd, aprt.
    destruct (DrawExtensionLinePP A B nAeqB) as [ y [ Aoy Boy ]]; simpl.
    exists y; split...
  }
  { intros [ x y H ]; unfold conv, incd, aprt.
    destruct (DrawIntersectionPointLL x y H) as [ A [ Aox Aoy ]].
    exists A; split...
  }
  { intros [ A B nAeqB ] x y nxeqy; simpl.
    destruct (DrawExtensionLinePP A B nAeqB) as [ z [ Aoz Boz ]].
    destruct (DecideLinesDistinction x z y nxeqy) as [ nxeqz | nyeqz ].
    destruct (DecideLineApartTwoPoints A B z x nAeqB)
      as [ nAox | nBox ]...
    destruct (DecideLineApartTwoPoints A B z y nAeqB)
      as [ nAoy | nBoy ]...
  }
  { unfold aprt, dipt.
    intros A B x nAox.
    destruct (DrawPointOnLine x) as [ C Cox ].
    destruct (DrawDistinctPointOnLine C x Cox) as [ D [ nDeqC Dox ]].
    assert (nAeqC : A <> C). { contradict nAox; subst... }
    assert (nAeqD : A <> D). { contradict nAox; subst... }
    destruct (DecidePointsDistinction A B C nAeqC) as [ nBeqA | nBeqC ]...
    destruct (DecidePointsDistinction A B D nAeqD) as [ nBeqA | nBeqD ]...
    destruct (DrawExtensionLinePP A C nAeqC) as [ y [ Aoy Coy ]].
    destruct (DrawExtensionLinePP A D nAeqD) as [ z [ Aoz Doz ]].
    destruct (DecidePointApartTwoLines C B x y) as [ H1 | H2 ]...
    { intros xeqy; subst. contradiction. }
    { left. contradict H2; subst... }
  }
  { unfold aprt, diln.
    intros A x y nAox.
    destruct (DrawPointOnLine x) as [ C Cox ].
    destruct (DrawDistinctPointOnLine C x Cox) as [ D [ nDeqC Dox ]].
    assert (nAeqC : A <> C). { contradict nAox; subst... }
    assert (nAeqD : A <> D). { contradict nAox; subst... }
    destruct (DrawExtensionLinePP A C nAeqC) as [ z [ Aoz Coz ]].
    destruct (DecideLinesConvergence x y z) as [ H1 | H2 ]...
    { split.
      { intros xeqz; subst; contradiction. }
      { exists C; split... }
    }
    { left. destruct H1... }
    { destruct (DrawIntersectionPointLL y z H2) as [ E [ Eoz Eoy ]]...
      destruct (DecidePointsDistinction A E C nAeqC) as [ nAeqE | nCeqE ]...
      { right. contradict nAeqE. apply (DiLs_EqPs A E y z)... destruct H2... }
      { left. contradict nCeqE. subst. apply (DiLs_EqPs E C y z); dils. }
    }
  }
  { unfold conv, diln.
    intros x y z nxpary.
    destruct (DecideLinesConvergence x z y) as [ H1 | H2 ]...
    left; destruct H2...
  }
Defined.

End VONPLATO.

(*****************************************************************************)
(* 24 *) Section HILBERT.
Context `{ cc : Concentricals }.
Context  { an : Angles on }.
Context  { sp : Superpositions on }.
Context  { pr : Parallels dc df }.
(*****************************************************************************)

Class Hilbert :=
{ point : Set;
  line : Set;

  (** Group I Incidence *)
  inc : point -> line -> Prop;
  line_existence : forall A B,
    A <> B -> exists l, inc A l /\ inc B l;
  line_uniqueness : forall A B l m,
    A <> B -> inc A l -> inc B l -> inc A m -> inc B m -> l = m;
  two_points_on_line : forall l,
    { A : point & { B | inc B l /\ inc A l /\ A <> B} };
  col := fun A B C => exists l, inc A l /\ inc B l /\ inc C l;
  ncol := fun A B C => ~ exists l, inc A l /\ inc B l /\ inc C l;
  l0 : line;
  p0 : point;
  plan : ~ inc p0 l0;

  (** Group II Order *)
  bet : point -> point -> point -> Prop;
  between_col : forall A B C,
    bet A B C -> col A B C;
  between_diff : forall A B C,
    bet A B C -> A <> C;
  between_comm : forall A B C,
    bet A B C -> bet C B A;
  between_out : forall A B,
    A <> B -> exists C, bet A B C;
  between_only_one : forall A B C,
    bet A B C -> ~ bet B C A;
  cut := fun l A B => ~ inc A l /\ ~ inc B l /\
    exists I, inc I l /\ bet A I B;
  pasch : forall A B C l,
    ~ col A B C -> ~ inc C l -> cut l A B -> cut l A C \/ cut l B C;

  (** Group IIIa Segment Congruence *)
  cong : point -> point -> point -> point -> Prop;
  cong_permr : forall A B C D,
    cong A B C D -> cong A B D C;
  cong_pseudo_transitivity : forall A B C D E F,
    cong A B C D -> cong A B E F -> cong C D E F;

  out := fun P A B => bet P A B \/ bet P B A \/ (P <> A /\ A = B);

  cong_existence : forall A B A' P l,
    A <> B -> A' <> P -> inc A' l -> inc P l ->
    exists B', inc B' l /\ out A' P B' /\ cong A' B' A B;
  disjoint := fun A B C D => ~ exists P, bet A P B /\ bet C P D;
  addition : forall A B C A' B' C',
    col A B C -> col A' B' C' ->
    disjoint A B B C -> disjoint A' B' B' C' ->
    cong A B A' B' -> cong B C B' C' -> cong A C A' C';

  (** Group IIIb Angle Congruence *)
  angle := @Triple point ncol;
  ang := BuildTriple point ncol;
  conga : angle -> angle -> Prop;
  same_side := fun A B l => exists P, cut l A P /\ cut l B P;
  same_side' := fun A B X Y =>
    X <> Y /\ forall l, inc X l -> inc Y l -> same_side A B l;

  conga_refl : forall (A B C : point)(nColABC : ncol A B C),
    conga (ang A B C nColABC)(ang A B C nColABC);
  conga_comm : forall (A B C : point)
    (nColABC : ncol A B C)(nColCBA : ncol C B A),
    conga (ang A B C nColABC)(ang C B A nColCBA);
  conga_permlr : forall (A B C D E F : point)
    (nColABC : ncol A B C)(nColDEF : ncol D E F)
    (nColCBA : ncol C B A)(nColFED : ncol F E D),
    conga (ang A B C nColABC)(ang D E F nColDEF) ->
    conga (ang C B A nColCBA)(ang F E D nColFED);
  cong_5 : forall (A B C A' B' C' : point)
    (nColBAC : ncol B A C)(nColBAC' : ncol B' A' C')
    (nColABC : ncol A B C)(nColABC' : ncol A' B' C'),
    cong A B A' B' -> cong A C A' C' ->
    conga (ang B A C nColBAC)(ang B' A' C' nColBAC') ->
    conga (ang A B C nColABC)(ang A' B' C' nColABC');
  hcong_4_existence : forall (A B C O X P : point)(nColABC : ncol A B C),
    ncol P O X -> exists (Y : point)(nColXOY : ncol X O Y),
      conga (ang A B C nColABC)(ang X O Y nColXOY)
      /\ same_side' P Y O X;
  hcong_4_uniqueness : forall (A B C O P X Y Y' : point)
    (nColABC : ncol A B C)(nColXOY : ncol X O Y)(nColXOY' : ncol X O Y'),
    ncol P O X
      -> conga (ang A B C nColABC)(ang X O Y nColXOY)
      -> conga (ang A B C nColABC)(ang X O Y' nColXOY')
      -> same_side' P Y O X -> same_side' P Y' O X
      -> out O Y Y';
  conga_out_conga : forall (A B C D E F A' C' D' F' : point)
    (nColABC : ncol A B C)(nColDEF : ncol D E F)
    (nColA'BC' : ncol A' B C')(nColD'EF' : ncol D' E F'),
    conga (ang A B C nColABC)(ang D E F nColDEF) ->
    out B A A' -> out B C C' -> out E D D' -> out E F F' ->
    conga (ang A' B C' nColA'BC')(ang D' E F' nColD'EF');

  (** Group IV Parallels *)
  par := fun l m => ~ exists X, inc X l /\ inc X m;
  euclid_uniqueness : forall l P m1 m2,
    ~ inc P l -> par l m1 -> inc P m1-> par l m2 -> inc P m2 -> m1 = m2
}.

Instance H : Hilbert.
Proof with geo.
  eapply (Build_Hilbert Point Line).
  { intros. destruct (DrawExtensionLinePP A B) as [ x [ Aox Box ]]... }
  { intros. apply (DiPs_EqLs A B l m)... }
  { intros.
    destruct (DrawPointOnLine l) as [ B Bol ].
    destruct (DrawDistinctPointOnLine B l Bol) as [ A [ nAeqB Aol ]].
    exists A, B...
  }
  { Unshelve.
    2: { destruct DrawPoint as [ A _ ].
      destruct (DrawDistinctPoint A) as [ B nAeqB ].
      destruct (DrawExtensionLinePP A B nAeqB) as [ x [ Aox Box ]].
      apply x.
    }
    2: { destruct DrawPoint as [ A _ ].
      destruct (DrawDistinctPoint A) as [ B nAeqB ].
      destruct (DrawExtensionLinePP A B nAeqB) as [ x [ Aox Box ]].
      destruct (DrawPointApartLine x) as [ C nCox ].
      apply C.
    }
    { simpl.
      destruct DrawPoint as [ A _ ].
      destruct (DrawDistinctPoint A) as [ B nAeqB ].
      destruct (DrawExtensionLinePP A B nAeqB) as [ x [ Aox Box ]].
      destruct (DrawPointApartLine x) as [ C nCox ].
      apply nCox.
    }
    { apply (fun A B C => [ A # B # C ])... }
    { apply (fun A B C D => [| A, B |] = [| C, D |])... }
    { apply (fun a b : Triangle =>
        [| ta a # tb a # tc a | tp a |] = [| ta b # tb b # tc b | tp b |])...
    }
  }
  { exact BetPs_ColPs. }
  { intros * BetABC; simpl in *. apply (BetPs_3DiPs A B C BetABC). }
  { exact BetPs_sym. }
  { intros * nAeqB.
    destruct (DrawOppositePoint B A) as [ C [ BAC _ ]]...
  }
  { intros * ABC. simpl; betps. }
  { intros A B C x nColABC nCox OSxAB; simpl in *.
    destruct (DecideTwoSides A C B x nCox OSxAB) as [ H1 | H2 ].
    { left... }
    { apply OS_sym in H2; right... }
  }
  { simpl. intros * H. rewrite H. apply SegPs_sym. }
  { simpl. intros * AB_CD AB_EF. rewrite <- AB_CD... }
  { intros * nAeqB nCeqD A'ol Pol; simpl.
    destruct (DrawSegmentOnRay A' P A B nCeqD) as [ E [ H1 H2 ]].
    exists E. split; auto.
    { destruct H1 as [ H1 |[ H1 | H1 ]].
      { incpt. }
      { subst P; contradiction. }
      { subst E; auto. }
    }
    { destruct H1 as [ H1 |[ H1 | H1 ]].
      { apply SR_BetPs in H1. destruct H1 as [ H1 |[ H4 | H3 ]]; tauto. }
      { subst P; contradiction. }
      { subst E; auto. symmetry in H2.
        apply EqSgs_EqPs in H2. contradiction.
      }
    }
  }
  { simpl in *. intros * ColABC ColA'B'C' H1 H2 H3 H4; simpl in *.
    destruct (classic (A = B)) as [ AeqB | nAeqB ].
    { subst B. symmetry in H3.
      apply EqSgs_EqPs in H3. subst B'...
    }
    destruct (classic (A = C)) as [ AeqC | nAeqC ].
    { subst C. contradict H1.
      destruct (DrawPointInsideSegment A B nAeqB) as [ Q AQB ].
      exists Q; split...
    }
    destruct (classic (B = C)) as [ BeqC | nBeqC ].
    { subst C. symmetry in H4.
      apply EqSgs_EqPs in H4. subst C'...
    }
    destruct (classic (A' = B')) as [ A'eqB' | nA'eqB' ].
    { subst B'.
      apply EqSgs_EqPs in H3. subst B...
    }
    destruct (classic (A' = C')) as [ A'eqC' | nA'eqC' ].
    { subst C'. contradict H2.
      destruct (DrawPointInsideSegment A' B' nA'eqB') as [ Q A'QB' ].
      exists Q; split...
    }
    destruct (classic (B' = C')) as [ B'eqC' | nB'eqC' ].
    { subst C'.
      apply EqSgs_EqPs in H4. subst C...
    }
    destruct (DecidePointsBetweenness A B C nAeqB) as [[ G1 | G2 ]| G3 ]...
    { destruct (DecidePointsBetweenness A' B' C' nA'eqB')
        as [[ G4 | G5 ]| G6 ]...
      { apply (BetPs_AddSgs A B C A' B' C')... }
      { contradict H2. apply BetPs_sym in G5.
        destruct (DrawPointInsideSegment B' C' nB'eqC') as [ Q B'QC' ].
        exists Q; split; eauto. apply (BetPs_a_trans A' C' Q B')...
      }
      { contradict H2.
        destruct (DrawPointInsideSegment A' B' nA'eqB') as [ Q A'QB' ].
        exists Q; split; eauto. apply (BetPs_c_trans B' Q A' C')...
      }
    }
    { destruct (DecidePointsBetweenness A' B' C' nA'eqB')
        as [[ G4 | G5 ]| G6 ]...
      { contradict H1.
        destruct (DrawPointInsideSegment B C nBeqC) as [ Q BQC ].
        exists Q; split; eauto.
        apply (BetPs_a_trans A C Q B); apply BetPs_sym...
      }
      { destruct (BetPs_SubtractSgs B C A B' C' A' G2); betps.
        rewrite SegPs_sym. symmetry.
        rewrite SegPs_sym... rewrite SegPs_sym. symmetry.
        rewrite SegPs_sym...
      }
      { contradict H1.
        destruct (DrawPointInsideSegment B C nBeqC) as [ Q BQC ].
        exists Q; split; eauto. apply (BetPs_a_trans A C Q B)...
      }
    }
    { destruct (DecidePointsBetweenness A' B' C' nA'eqB')
        as [[ G4 | G5 ]| G6 ]...
      { contradict H1.
        destruct (DrawPointInsideSegment A B nAeqB) as [ Q AQB ].
        exists Q; split; eauto. apply (BetPs_c_trans B Q A C)...
      }
      { contradict H1.
        destruct (DrawPointInsideSegment A B nAeqB) as [ Q AQB ].
        exists Q; split; eauto. apply (BetPs_c_trans B Q A C)...
      }
      { destruct (BetPs_SubtractSgs B A C B' A' C' G3); betps.
        rewrite SegPs_sym... symmetry.
        rewrite SegPs_sym...
      }
    }
  }
  { simpl in *. intros *; auto. }
  { simpl in *. intros *; auto. apply ConvexAngPs_sym... }
  { simpl in *. intros * ABC_DEF; auto.
    assert (ABC_CBA : [|A # B # C | nColABC|] = [|C # B # A | nColCBA|]).
    { apply ConvexAngPs_sym. }
    rewrite <- ABC_CBA. rewrite ABC_DEF.
    apply ConvexAngPs_sym.
  }
  { simpl in *; intros * ABA'B' ACA'C' H.
    edestruct (SAS B A C B' A' C') as [ H1 [ H2 [ H3 [ H4 [ H5 H6 ]]]]]...
    { rewrite SegPs_sym. symmetry. rewrite SegPs_sym. auto. }
    simpl in *.
    erewrite ConvexAngPs_sym... symmetry. erewrite ConvexAngPs_sym...
  }
  { simpl in *; intros * nColPOX.
    edestruct (DrawAngleOnGivenHalfplane X O P A B C)
      as [ Y [ nColXOY [[ nXeqO [ x [ Oox [ Xox SS ]]]] H3 ]]]; ncolperps.
    exists Y, nColXOY; split; auto.
    { rewrite H3; auto. }
    split...
    intros t Oot Xot.
    assert (xeqt : x = t). { apply (DiPs_EqLs X O x t)... }
    subst t.
    destruct (DrawPointOnOppositeSide P x) as [ Q OS ].
    { destruct SS; tauto. }
    exists Q. split. destruct OS; tauto. apply OS_sym in OS.
    apply (OSO_trans Q P Y x) in OS; eauto. apply OS_sym in OS.
    destruct OS; tauto.
  }
  { simpl in *; intros * nColPOX H1 H2 SL1 SS2.
    cut ([ O # Y, Y' ]).
    { intros. apply SR_BetPs in H.
      destruct H as [ H4 |[[ H5 H6 ]| H3 ]]; eauto.
    }
    rewrite H1 in H2.
    apply (SH_EqConvexAs_SR X O Y Y' nColXOY nColXOY'); eauto.
    destruct SL1 as [ nOeqX SL1].
    destruct SS2 as [ _ SS2 ].
    destruct (DrawExtensionLinePP O X) as [ t [ Oot Xot ]]; eauto.
    split; eauto.
    exists t; split; auto. split; auto.
    destruct (SL1 t Oot Xot) as [ Q [ OStQP OStQY ]]; eauto. clear SL1.
    destruct (SS2 t Oot Xot) as [ R [ OStRP OStRY' ]]; eauto. clear SS2.
    apply (SS_trans Y P Y' t).
    { apply (OOS_trans Y Q P t); eauto. apply OS_sym; eauto. }
    apply (OOS_trans P R Y' t); eauto. apply OS_sym; eauto.
  }
  { simpl in *. intros * ABC_DEF H1 H2 H3 H4.
    erewrite ConvexAngPs_inv.
    { rewrite ABC_DEF. apply ConvexAngPs_inv.
      { apply SR_BetPs. destruct H3 as [ G1 |[ G2 |[ G3 G4 ]]]; inc. }
      { apply SR_BetPs. destruct H4 as [ G1 |[ G2 |[ G3 G4 ]]]; inc. }
    }
    apply SR_BetPs.
    { destruct H1 as [ G1 |[ G2 |[ G3 G4 ]]]; inc. }
    apply SR_sym. apply SR_BetPs.
    destruct H2 as [ G1 |[ G2 |[ G3 G4 ]]]; inc.
  }
  { intros * nPol lm1 Pom1 lm2 Pom2.
    apply (ParLs_InsPs_EqLs P m1 m2)...
    apply (ParLs_trans m1 l m2).
    { unfold Parallel. contradict lm1.
      destruct (DrawIntersectionPointLL m1 l lm1) as [ Q [ H1 H2 ]].
      exists Q; split; eauto.
    }
    unfold Parallel. contradict lm2.
    destruct (DrawIntersectionPointLL l m2 lm2) as [ Q [ H1 H2 ]].
    exists Q; split; eauto.
  }
Qed.

End HILBERT.