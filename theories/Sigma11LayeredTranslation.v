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

  (*When quantifiers are bubbled, bound variables must be adjusted appropriately.

    When formulas with bubbled quantifiers are joined, both the left and the right must be
    adjusted in different ways.
    All bound terms must be increased to make room for the right term's quantifiers.
  *)
  Fixpoint AdjustLeftTermBounds (rightExi rightUni : nat) 
  (t : Sigma11Term) : Sigma11Term :=
  match t with
  | Sigma11Var m => Sigma11Var (m + rightUni)
  | Sigma11App i a t => Sigma11App (i + rightExi) a t
  | Sigma11Add r1 r2 => 
    let p1 := AdjustLeftTermBounds rightExi rightUni r1 in
    let p2 := AdjustLeftTermBounds rightExi rightUni r2 in
    Sigma11Add p1 p2
  | Sigma11Mul r1 r2 => 
    let p1 := AdjustLeftTermBounds rightExi rightUni r1 in
    let p2 := AdjustLeftTermBounds rightExi rightUni r2 in
    Sigma11Mul p1 p2
  | Sigma11IndLess r1 r2 => 
    let p1 := AdjustLeftTermBounds rightExi rightUni r1 in
    let p2 := AdjustLeftTermBounds rightExi rightUni r2 in
    Sigma11IndLess p1 p2
  | Sigma11Max r1 r2 => 
    let p1 := AdjustLeftTermBounds rightExi rightUni r1 in
    let p2 := AdjustLeftTermBounds rightExi rightUni r2 in
    Sigma11Max p1 p2
  | Sigma11Const n => Sigma11Const n
  end.

  (*When quantifiers are bubbled, bound variables must be adjusted appropriately.

    When formulas with bubbled quantifiers are joined, both the left and the right must be
    adjusted in different ways.
    Bound terms only need to be adjusted if they would refference a quantifier
    earlier than the left's new quantifiers.
  *)
  Fixpoint AdjustRightTermBounds (leftExi rightExi leftUni rightUni : nat) 
  (t : Sigma11Term) : Sigma11Term :=
  match t with
  | Sigma11Var m => Sigma11Var (if m >= rightUni then m+leftUni else m)
  | Sigma11App i a t => Sigma11App (if i >= rightExi then i+leftExi else i) a t
  | Sigma11Add r1 r2 => 
    let p1 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r1 in
    let p2 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r2 in
    Sigma11Add p1 p2
  | Sigma11Mul r1 r2 => 
    let p1 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r1 in
    let p2 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r2 in
    Sigma11Mul p1 p2
  | Sigma11IndLess r1 r2 => 
    let p1 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r1 in
    let p2 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r2 in
    Sigma11IndLess p1 p2
  | Sigma11Max r1 r2 => 
    let p1 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r1 in
    let p2 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r2 in
    Sigma11Max p1 p2
  | Sigma11Const n => Sigma11Const n
  end.

  Fixpoint AdjustLeftFormulaBounds (rightExi rightUni : nat) 
  (f : Sigma11LayeredZOFormula) : Sigma11LayeredZOFormula :=
  match f with
  | Sigma11LayeredEqual r1 r2 => 
    let p1 := AdjustLeftTermBounds rightExi rightUni r1 in
    let p2 := AdjustLeftTermBounds rightExi rightUni r2 in
    Sigma11LayeredEqual p1 p2
  | Sigma11LayeredLessOrEqual r1 r2 => 
    let p1 := AdjustLeftTermBounds rightExi rightUni r1 in
    let p2 := AdjustLeftTermBounds rightExi rightUni r2 in
    Sigma11LayeredLessOrEqual p1 p2
  | Sigma11LayeredNot f => 
    let p := AdjustLeftFormulaBounds rightExi rightUni f in
    Sigma11LayeredNot p
  | Sigma11LayeredAnd f1 f2 => 
    let p1 := AdjustLeftFormulaBounds rightExi rightUni f1 in
    let p2 := AdjustLeftFormulaBounds rightExi rightUni f2 in
    Sigma11LayeredAnd p1 p2
  | Sigma11LayeredOr f1 f2 => 
    let p1 := AdjustLeftFormulaBounds rightExi rightUni f1 in
    let p2 := AdjustLeftFormulaBounds rightExi rightUni f2 in
    Sigma11LayeredOr p1 p2
  | Sigma11LayeredImplies f1 f2 => 
    let p1 := AdjustLeftFormulaBounds rightExi rightUni f1 in
    let p2 := AdjustLeftFormulaBounds rightExi rightUni f2 in
    Sigma11LayeredImplies p1 p2
  | Sigma11LayeredIff f1 f2 => 
    let p1 := AdjustLeftFormulaBounds rightExi rightUni f1 in
    let p2 := AdjustLeftFormulaBounds rightExi rightUni f2 in
    Sigma11LayeredIff p1 p2
  | Sigma11LayeredTop => Sigma11LayeredTop
  | Sigma11LayeredBot => Sigma11LayeredBot
  end.

  Fixpoint AdjustRightFormulaBounds (leftExi rightExi leftUni rightUni : nat) 
  (f : Sigma11LayeredZOFormula) : Sigma11LayeredZOFormula :=
  match f with
  | Sigma11LayeredEqual r1 r2 => 
    let p1 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r1 in
    let p2 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r2 in
    Sigma11LayeredEqual p1 p2
  | Sigma11LayeredLessOrEqual r1 r2 => 
    let p1 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r1 in
    let p2 := AdjustRightTermBounds leftExi rightExi leftUni rightUni r2 in
    Sigma11LayeredLessOrEqual p1 p2
  | Sigma11LayeredNot f => 
    let p := AdjustRightFormulaBounds leftExi rightExi leftUni rightUni f in
    Sigma11LayeredNot p
  | Sigma11LayeredAnd f1 f2 => 
    let p1 := AdjustRightFormulaBounds leftExi rightExi leftUni rightUni f1 in
    let p2 := AdjustRightFormulaBounds leftExi rightExi leftUni rightUni f2 in
    Sigma11LayeredAnd p1 p2
  | Sigma11LayeredOr f1 f2 => 
    let p1 := AdjustRightFormulaBounds leftExi rightExi leftUni rightUni f1 in
    let p2 := AdjustRightFormulaBounds leftExi rightExi leftUni rightUni f2 in
    Sigma11LayeredOr p1 p2
  | Sigma11LayeredImplies f1 f2 => 
    let p1 := AdjustRightFormulaBounds leftExi rightExi leftUni rightUni f1 in
    let p2 := AdjustRightFormulaBounds leftExi rightExi leftUni rightUni f2 in
    Sigma11LayeredImplies p1 p2
  | Sigma11LayeredIff f1 f2 => 
    let p1 := AdjustRightFormulaBounds leftExi rightExi leftUni rightUni f1 in
    let p2 := AdjustRightFormulaBounds leftExi rightExi leftUni rightUni f2 in
    Sigma11LayeredIff p1 p2
  | Sigma11LayeredTop => Sigma11LayeredTop
  | Sigma11LayeredBot => Sigma11LayeredBot
  end.

  Fixpoint ExiNums (qs : seq (sum Sigma11Term (seq Sigma11Term * Sigma11Term))) : nat :=
    match qs with
    | nil => 0
    | inl _ :: xs => ExiNums xs
    | inr _ :: xs => (ExiNums xs).+1
    end.

  Fixpoint UniNums (qs : seq (sum Sigma11Term (seq Sigma11Term * Sigma11Term))) : nat :=
    match qs with
    | nil => 0
    | inl _ :: xs => (UniNums xs).+1
    | inr _ :: xs => UniNums xs
    end.

  Definition AdjustFormulaPair
    (left right : seq (sum Sigma11Term (seq Sigma11Term * Sigma11Term)) * Sigma11LayeredZOFormula) :
    Sigma11LayeredZOFormula * Sigma11LayeredZOFormula := 
    let lqs := fst left in let leqs := ExiNums lqs in let luqs := UniNums lqs in let lf := snd left in 
    let rqs := fst right in let reqs := ExiNums rqs in let ruqs := UniNums rqs in let rf := snd right in 
    (AdjustLeftFormulaBounds reqs ruqs lf, AdjustRightFormulaBounds leqs reqs luqs ruqs rf).

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
    let p12 := AdjustFormulaPair p1 p2 in
    (fst p1 ++ fst p2, uncurry Sigma11LayeredAnd p12)
  | Sigma11Or f1 f2 => 
    let p1 := BubbleQuantifiers f1 in
    let p2 := BubbleQuantifiers f2 in
    let p12 := AdjustFormulaPair p1 p2 in
    (fst p1 ++ fst p2, uncurry Sigma11LayeredOr p12)
  (*Note: this could be altered to swap non-functional quantifiers in the first argument prior to recursion*)
  | Sigma11Implies f1 f2 => 
    let p1 := BubbleQuantifiers f1 in
    let p2 := BubbleQuantifiers f2 in
    let p12 := AdjustFormulaPair p1 p2 in
    (fst p1 ++ fst p2, uncurry Sigma11LayeredImplies p12)
  | Sigma11Iff f1 f2 => 
    let p1 := BubbleQuantifiers f1 in
    let p2 := BubbleQuantifiers f2 in
    let p12 := AdjustFormulaPair p1 p2 in
    (fst p1 ++ fst p2, uncurry Sigma11LayeredIff p12)
  | Sigma11ForAll b f => 
    let p := BubbleQuantifiers f in
    (inl b :: fst p, snd p)
  | Sigma11ForSome bs y f => 
    let p := BubbleQuantifiers f in
    (inr (bs, y) :: fst p, snd p)
  | Sigma11Top => (nil, Sigma11LayeredTop)
  | Sigma11Bot => (nil, Sigma11LayeredBot)
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
