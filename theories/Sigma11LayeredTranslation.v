From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import 
  ssreflect ssrfun finfun zmodp ssrbool ssrnat ssralg seq fintype finalg tuple eqtype
  bigop.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils CoqArith.Sigma11 CoqArith.Sigma11Layered.

Require Import Program.

Module Sigma11LayeredTranslationInternal (Params : Sigma11Parameters).
  Module S11 := Sigma11LayeredInternal Params.
  Import S11.
  Export S11.

  (* Check that no universal quantifiers appear *)
  Fixpoint NoQuantifiers 
  (f : Sigma11Formula) : bool :=
  match f with
  | Sigma11Equal r1 r2 => true
  | Sigma11LessOrEqual r1 r2 => true
  | Sigma11Not f => NoQuantifiers f
  | Sigma11And f1 f2 => NoQuantifiers f1 && NoQuantifiers f2
  | Sigma11Or f1 f2 => NoQuantifiers f1 && NoQuantifiers f2
  | Sigma11Implies f1 f2 => NoQuantifiers f2 && NoQuantifiers f2
  | Sigma11Iff f1 f2 => NoQuantifiers f1 && NoQuantifiers f2
  | Sigma11ForAll b f => false
  | Sigma11ForSome bs y f => false
  | Sigma11Top => true
  | Sigma11Bot => true
  end.

  (* Check that no universal quantifiers appear *)
  Fixpoint NoUniversalQuantifiers 
  (f : Sigma11Formula) : bool :=
  match f with
  | Sigma11Equal r1 r2 => true
  | Sigma11LessOrEqual r1 r2 => true
  (*Note: This could be changed to detect non-functional existential quantifiers*)
  | Sigma11Not f => NoQuantifiers f
  (*Note: (∃x.p(x)) /\ q <-> ∃x.p(x) /\ q*)
  | Sigma11And f1 f2 => NoUniversalQuantifiers f1 && NoUniversalQuantifiers f2
  | Sigma11Or f1 f2 => NoQuantifiers f1 && NoQuantifiers f2
  (*Note: This could be changed to detect non-functional existential quantifiers in the first argument*)
  | Sigma11Implies f1 f2 => NoQuantifiers f2 && NoQuantifiers f2
  (*Is there an alternative to this?*)
  | Sigma11Iff f1 f2 => NoQuantifiers f1 && NoQuantifiers f2
  | Sigma11ForAll b f => false
  | Sigma11ForSome bs y f => NoUniversalQuantifiers f
  | Sigma11Top => true
  | Sigma11Bot => true
  end.

  (* Check that no Existential quantifiers appear *)
  Fixpoint NoExistentialQuantifiers 
  (f : Sigma11Formula) : bool :=
  match f with
  | Sigma11Equal r1 r2 => true
  | Sigma11LessOrEqual r1 r2 => true
  (*Note: This could be changed to detect universal quantifiers*)
  | Sigma11Not f => NoQuantifiers f
  | Sigma11And f1 f2 => NoQuantifiers f1 && NoQuantifiers f2
  (*Note: (∀x.p(x)) \/ q <-> ∀x.p(x) \/ q, classically*)
  | Sigma11Or f1 f2 => NoExistentialQuantifiers f1 && NoExistentialQuantifiers f2
  (*Note: This could be changed to detect universal quantifiers in the first argument*)
  | Sigma11Implies f1 f2 => NoQuantifiers f2 && NoExistentialQuantifiers f2
  (*Is there an alternative to this?*)
  | Sigma11Iff f1 f2 => NoQuantifiers f1 && NoQuantifiers f2
  | Sigma11ForAll b f => NoExistentialQuantifiers f
  | Sigma11ForSome bs y f => false
  | Sigma11Top => true
  | Sigma11Bot => true
  end.

  (* Check that all quantifiers can be bubbled while preserving semantics *)
  Fixpoint BubblableFormula 
  (f : Sigma11Formula) : bool :=
  match f with
  | Sigma11Equal r1 r2 => true
  | Sigma11LessOrEqual r1 r2 => true
  (*Note: This could be changed to detect non-functional quantifiers, and swap them*)
  | Sigma11Not f => NoQuantifiers f
  (*Note: (∃x.p(x)) /\ q <-> ∃x.p(x) /\ q*)
  | Sigma11And f1 f2 => NoUniversalQuantifiers f1 && NoUniversalQuantifiers f2
  (*Note: (∀x.p(x)) \/ q <-> ∀x.p(x) \/ q, classically*)
  | Sigma11Or f1 f2 => NoExistentialQuantifiers f1 && NoExistentialQuantifiers f2
  (*Note: This could be changed to detect non-functional quantifiers in the first argument, and swap them*)
  | Sigma11Implies f1 f2 => NoQuantifiers f2 && NoExistentialQuantifiers f2
  (*Is there an alternative to this?*)
  | Sigma11Iff f1 f2 => NoQuantifiers f1 && NoQuantifiers f2
  | Sigma11ForAll b f => BubblableFormula f
  | Sigma11ForSome bs y f => BubblableFormula f
  | Sigma11Top => true
  | Sigma11Bot => true
  end.

  Definition Hole {A} : A. Admitted.

  Fixpoint BubbleQuantifiers
    (f : Sigma11Formula) : 
    seq (sum Sigma11Term (seq Sigma11Term * Sigma11Term)) * Sigma11LayeredZOFormula :=
  match f with
  | Sigma11Equal r1 r2 => (nil, Sigma11LayeredEqual r1 r2)
  | Sigma11LessOrEqual r1 r2 => (nil, Sigma11LayeredLessOrEqual r1 r2)
  (*Note: this could be altered to swap non-functional quantifiers prior to recursion*)
  | Sigma11Not f => 
    let p := BubbleQuantifiers f in
    (fst p, Sigma11LayeredNot (snd p))
  | Sigma11And f1 f2 => 
    let p1 := BubbleQuantifiers f1 in
    let p2 := BubbleQuantifiers f2 in
    (fst p1 ++ fst p2, Sigma11LayeredAnd (snd p1) (snd p2))
  | Sigma11Or f1 f2 => 
    let p1 := BubbleQuantifiers f1 in
    let p2 := BubbleQuantifiers f2 in
    (fst p1 ++ fst p2, Sigma11LayeredOr (snd p1) (snd p2))
  (*Note: this could be altered to swap non-functional quantifiers in the first argument prior to recursion*)
  | Sigma11Implies f1 f2 => 
    let p1 := BubbleQuantifiers f1 in
    let p2 := BubbleQuantifiers f2 in
    (fst p1 ++ fst p2, Sigma11LayeredImplies (snd p1) (snd p2))
  | Sigma11Iff f1 f2 => 
    let p1 := BubbleQuantifiers f1 in
    let p2 := BubbleQuantifiers f2 in
    (fst p1 ++ fst p2, Sigma11LayeredImplies (snd p1) (snd p2))
  | Sigma11ForAll b f => 
    let p := BubbleQuantifiers f in
    (inl b :: fst p, snd p)
  | Sigma11ForSome bs y f => 
    let p := BubbleQuantifiers f in
    (inr (bs, y) :: fst p, snd p)
  | Sigma11Top => (nil, Sigma11LayeredTop)
  | Sigma11Bot => (nil, Sigma11LayeredBottom)
  end.

  Fixpoint FoldBubbledQuantifiers
    (qs : seq (sum Sigma11Term (seq Sigma11Term * Sigma11Term)))
    (z : Sigma11LayeredZOFormula) :
    Sigma11LayeredFormula :=
  match qs with
  | nil => Sigma11LayeredZO z
  | inl b :: xs => Sigma11LayeredForAll b (FoldBubbledQuantifiers xs z)
  | inr (bs, y) :: xs => Sigma11LayeredForSome bs y (FoldBubbledQuantifiers xs z)
  end.

  Definition SeparateQuantifiers (f : Sigma11Formula) : Sigma11LayeredFormula :=
    uncurry FoldBubbledQuantifiers (BubbleQuantifiers f).

End Sigma11LayeredTranslationInternal.