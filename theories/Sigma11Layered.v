From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import 
  ssreflect ssrfun finfun zmodp ssrbool ssrnat ssralg seq fintype finalg tuple eqtype
  bigop.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils CoqArith.Sigma11.

Require Import Program.

Module Sigma11LayeredInternal (Params : Sigma11Parameters).
  Module S11 := Sigma11Internal Params.
  Import S11.
  Export S11.

  (* Formulas with no quantifiers *)
  Inductive Sigma11LayeredZOFormula : Type :=
  | Sigma11LayeredEqual : Sigma11Term -> Sigma11Term -> Sigma11LayeredZOFormula
  | Sigma11LayeredLessOrEqual : Sigma11Term -> Sigma11Term -> Sigma11LayeredZOFormula
  (* | Sigma11LayeredPredicate : ??? -> Sigma11LayeredZOFormula *)
  | Sigma11LayeredNot : Sigma11LayeredZOFormula -> Sigma11LayeredZOFormula
  | Sigma11LayeredAnd : Sigma11LayeredZOFormula -> Sigma11LayeredZOFormula -> Sigma11LayeredZOFormula
  | Sigma11LayeredOr : Sigma11LayeredZOFormula -> Sigma11LayeredZOFormula -> Sigma11LayeredZOFormula
  | Sigma11LayeredImplies : Sigma11LayeredZOFormula -> Sigma11LayeredZOFormula -> Sigma11LayeredZOFormula
  | Sigma11LayeredIff : Sigma11LayeredZOFormula -> Sigma11LayeredZOFormula -> Sigma11LayeredZOFormula
  | Sigma11LayeredTop : Sigma11LayeredZOFormula
  | Sigma11LayeredBot : Sigma11LayeredZOFormula.

  (* Formulas with quantifiers *)
  Inductive Sigma11LayeredFormula : Type :=
  | Sigma11LayeredZO : 
    Sigma11LayeredZOFormula -> 
    Sigma11LayeredFormula
  | Sigma11LayeredForAll : 
    Sigma11Term -> 
    Sigma11LayeredFormula -> 
    Sigma11LayeredFormula
  | Sigma11LayeredForSome : 
    forall (bs : seq Sigma11Term)
           (y : Sigma11Term),
    Sigma11LayeredFormula -> 
    Sigma11LayeredFormula
  (* | Sigma11LayeredForSomeP : ??? -> Sigma11LayeredZOFormula *)
  (* | Sigma11LayeredGiven : ??? -> Sigma11LayeredZOFormula *)
  .

  Fixpoint Sigma11LayeredZOFormulaDenote (M : Sigma11Model)
  (f : Sigma11LayeredZOFormula) : option bool :=
  match f with
  | Sigma11LayeredEqual r1 r2 => 
    let d1 := Sigma11TermDenote M r1 in
    let d2 := Sigma11TermDenote M r2 in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) d2) d1
  | Sigma11LayeredLessOrEqual r1 r2 => 
    let d1 := Sigma11TermDenote M r1 in
    let d2 := Sigma11TermDenote M r2 in
    obind (fun r1 : 'F_FSize => obind (fun r2 : 'F_FSize => Some ((r1 < r2) || (r1 == r2))) d2) d1
  | Sigma11LayeredNot f =>
    let d := Sigma11LayeredZOFormulaDenote M f in
    obind (fun d => Some (~~ d)) d
  | Sigma11LayeredAnd f1 f2 =>
    let d1 := Sigma11LayeredZOFormulaDenote M f1 in
    let d2 := Sigma11LayeredZOFormulaDenote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) d2) d1
  | Sigma11LayeredOr f1 f2 => 
    let d1 := Sigma11LayeredZOFormulaDenote M f1 in
    let d2 := Sigma11LayeredZOFormulaDenote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) d2) d1
  | Sigma11LayeredImplies f1 f2 => 
    let d1 := Sigma11LayeredZOFormulaDenote M f1 in
    let d2 := Sigma11LayeredZOFormulaDenote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 ==> r2)) d2) d1
  | Sigma11LayeredIff f1 f2 => 
    let d1 := Sigma11LayeredZOFormulaDenote M f1 in
    let d2 := Sigma11LayeredZOFormulaDenote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) d2) d1
  | Sigma11LayeredTop => Some true
  | Sigma11LayeredBot => Some false
  end.

  Fixpoint Sigma11LayeredFormulaDenote (M : Sigma11Model) (f : Sigma11LayeredFormula) : option bool :=
    match f with
    | Sigma11LayeredZO z => Sigma11LayeredZOFormulaDenote M z
    | Sigma11LayeredForAll b f => 
      let d := Sigma11TermDenote M b in
      \oall (r in 'F_FSize | obind (fun p' : 'F_FSize => Some (r < p')) (Sigma11TermDenote M b) == Some true) 
        Sigma11LayeredFormulaDenote (AddModelV M r) f
    | Sigma11LayeredForSome bs y f => 
      \oexi (F in {ffun 'F_FSize ^ length bs -> option ('F_FSize)} |
        Fun_Bound_Check M (finfun_of_tuple (in_tuple bs)) y F == Some true)
        (Sigma11LayeredFormulaDenote (AddModelF M (existT _ (size bs) F)) f)
    end.

End Sigma11LayeredInternal.
