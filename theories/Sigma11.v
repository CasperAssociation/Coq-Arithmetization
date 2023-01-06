From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import 
  ssreflect ssrfun finfun zmodp ssrbool ssrnat ssralg seq fintype finalg tuple eqtype
  bigop.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

Module Type Sigma11Parameters.
  Parameter (FSize (*Size of finite field*) : nat).
End Sigma11Parameters.

Module Sigma11Internal (Params : Sigma11Parameters).
  Import Params.
  Export Params.

  Inductive Sigma11Term : Type :=
  | Sigma11Var : nat -> Sigma11Term
  | Sigma11App : nat -> forall a, (Sigma11Term ^ a) -> Sigma11Term
  (* | Sigma11AppInverse : nat -> Sigma11Term -> Sigma11Term *)
  | Sigma11Add : Sigma11Term -> Sigma11Term -> Sigma11Term
  | Sigma11Mul : Sigma11Term -> Sigma11Term -> Sigma11Term
  | Sigma11IndLess : Sigma11Term -> Sigma11Term -> Sigma11Term
  | Sigma11Max : Sigma11Term -> Sigma11Term -> Sigma11Term
  | Sigma11Const : 'F_FSize -> Sigma11Term.

  Inductive Sigma11Formula : Type :=
  | Sigma11Equal : Sigma11Term -> Sigma11Term -> Sigma11Formula
  | Sigma11LessOrEqual : Sigma11Term -> Sigma11Term -> Sigma11Formula
  (* | Sigma11Predicate : ??? -> Sigma11Formula *)
  | Sigma11Not : Sigma11Formula -> Sigma11Formula
  | Sigma11And : Sigma11Formula -> Sigma11Formula -> Sigma11Formula
  | Sigma11Or : Sigma11Formula -> Sigma11Formula -> Sigma11Formula
  | Sigma11Implies : Sigma11Formula -> Sigma11Formula -> Sigma11Formula
  | Sigma11Iff : Sigma11Formula -> Sigma11Formula -> Sigma11Formula
  | Sigma11Forall : Sigma11Term -> 
    Sigma11Formula -> 
    Sigma11Formula
  | Sigma11ForSome : 
    forall (bs : seq Sigma11Term)
            (y : Sigma11Term),
    Sigma11Formula -> 
    Sigma11Formula
  (* | Sigma11ForSomeP : ??? -> Sigma11Formula *)
  (* | Sigma11Given : ??? -> Sigma11Formula *)
  | Sigma11Top : Sigma11Formula
  | Sigma11Bottom : Sigma11Formula.

  Record Sigma11Model : Type :=
  mkSigma11Model {
      V_F : nat -> 'F_FSize;
      F_S : nat -> { a & {ffun 'F_FSize ^ a -> option 'F_FSize} };
  }.

  Definition finFldInd {p} (x y : 'F_p) : 'F_p := if (x < y) then 1%R else 0%R.
  Definition finFldMax {p} (x y : 'F_p) : 'F_p := if (x < y) then y else x.

  Program Definition ofan {A B C} (op : B -> B -> C) (a1 a2 : A) (r : A -> option B) : option C :=
    let d1 := r a1 in
    let d2 := r a2 in
    obind (fun r1 => obind (fun r2 => Some (op r1 r2)) d2) d1.

  Program Fixpoint Sigma11TermDenote (M : Sigma11Model) 
  (r : Sigma11Term) : option ('F_FSize) :=
  match r with
  | Sigma11Var m => Some (V_F M m)
  | Sigma11App i a t => 
    (if a == projT1 (F_S M i) as b return ((a == projT1 (F_S M i)) = b -> option ('F_FSize))
     then 
      fun e => (
      let ds := 
          option_ffun [ffun x : 'I_(projT1 (F_S M i)) => Sigma11TermDenote M (t x)] in
      obind (fun t => projT2 (F_S M i) t) ds)
     else fun _ => None) (erefl _)
  | Sigma11Add r1 r2 => ofan (fun a b => (a + b)%R) r1 r2 (Sigma11TermDenote M)
  | Sigma11Mul r1 r2 => ofan (fun a b => (a + b)%R) r1 r2 (Sigma11TermDenote M)
  | Sigma11IndLess r1 r2 => ofan finFldInd r1 r2 (Sigma11TermDenote M)
  | Sigma11Max r1 r2 => ofan finFldMax r1 r2 (Sigma11TermDenote M)
  | Sigma11Const n => Some n
  end.
  Next Obligation. apply EEConvert in e; qauto. Qed.
  
  Definition AddModelV (M : Sigma11Model) (r : 'F_FSize) : Sigma11Model :=
    {| V_F := ExtendAt0 r (V_F M); F_S := F_S M |}.

  Definition AddModelF  (M : Sigma11Model) (f : { newA & {ffun 'F_FSize ^ newA -> option ('F_FSize)}})  :
    Sigma11Model := {| V_F := V_F M; F_S := ExtendAt0 f (F_S M) |}.

  Program Fixpoint FunBounds 
    (M : Sigma11Model) {a}
    (ins : 'F_FSize ^ a) (out : 'F_FSize)
    (insB : Sigma11Term ^ a) (outB : Sigma11Term) : option bool :=
    match a with
    | 0 => 
      let oB := Sigma11TermDenote M outB in
      obind (fun oB : 'F_FSize => Some (out < oB)) oB
    | n.+1 => 
      let iB := Sigma11TermDenote M (insB (inord 0)) in
      let rB := 
        @FunBounds (AddModelV M (ins (inord 0))) 
                   n 
                   [ffun x : 'I_ _ => ins (inord (x.+1))] 
                   out 
                   [ffun x : 'I_ _ => insB (inord (x.+1))] 
                   outB in
      obind (fun rB => 
      obind (fun iB : 'F_FSize => 
        Some (((ins (inord 0)) < iB) && rB)) 
      iB) rB
    end.

  Program Definition andob (a1 a2 : option bool) : option bool :=
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) a2) a1.
  Program Definition orob (a1 a2 : option bool) : option bool :=
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) a2) a1.

  Import Monoid.
  Lemma andobA : associative andob.
  Proof. move=> [x|] [y|] [z|]; try destruct x; auto. Qed.
  Lemma andobFb : left_id (Some true) andob.
  Proof. move=> [x|]; auto. Qed.
  Lemma andobbF : right_id (Some true) andob.
  Proof. move=> [x|]; try destruct x; auto. Qed.

  Canonical andob_monoid := Law andobA andobFb andobbF.

  Lemma orobA : associative orob.
  Proof. move=> [x|] [y|] [z|]; try destruct x; auto. Qed.
  Lemma orobFb : left_id (Some false) orob.
  Proof. move=> [x|]; auto. Qed.
  Lemma orobbF : right_id (Some false) orob.
  Proof. move=> [x|]; try destruct x; auto. Qed.

  Canonical orob_monoid := Law orobA orobFb orobbF.

  Reserved Notation "\oall ( i 'in' r | P ) F"
    (at level 36, F at level 36, i, r at level 50,
        format "'[' \oall ( i 'in' r | P ) '/ ' F ']'").
  Notation "\oall ( i 'in' A | P ) F" := 
    (\big[andob/Some true]_(i | (i \in A) && P) F) : big_scope.
  Reserved Notation "\oall ( i 'in' A ) F"
    (at level 36, F at level 36, i, A at level 50,
        format "'[' \oall ( i 'in' A ) '/ ' F ']'").
  Notation "\oall ( i 'in' A ) F" :=
    (\big[andob/Some true]_(i | i \in A) F) : big_scope.
  Reserved Notation "\oexi ( i 'in' A ) F"
    (at level 36, F at level 36, i, A at level 50,
        format "'[' \oexi ( i 'in' A ) '/ ' F ']'").
  Notation "\oexi ( i 'in' A ) F" :=
    (\big[orob/Some false]_(i | i \in A) F) : big_scope.

  (* Definition exiob {A : finType} (B : A -> option bool) : option bool :=
    \big[orob/(Some false)]_(y <- enum A) (B y). *)

  Definition Fun_Bound_Check 
    (M : Sigma11Model)
    {n : nat}
    (bs : Sigma11Term ^ n)
    (y : Sigma11Term)
    (f : ('F_FSize ^ n) -> option ('F_FSize)) : option bool :=
  \oall (ins in ('F_FSize ^ n)%type) obind (fun out => 
    FunBounds M ins out bs y
  ) (f ins).

  Fixpoint Sigma11FormulaDenote (M : Sigma11Model)
  (f : Sigma11Formula) : option bool :=
  match f with
  | Sigma11Equal r1 r2 => 
    let d1 := Sigma11TermDenote M r1 in
    let d2 := Sigma11TermDenote M r2 in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) d2) d1
  | Sigma11LessOrEqual r1 r2 => 
    let d1 := Sigma11TermDenote M r1 in
    let d2 := Sigma11TermDenote M r2 in
    obind (fun r1 : 'F_FSize => obind (fun r2 : 'F_FSize => Some ((r1 < r2) || (r1 == r2))) d2) d1
  | Sigma11Not f =>
    let d := Sigma11FormulaDenote M f in
    obind (fun d => Some (~~ d)) d
  | Sigma11And f1 f2 =>
    let d1 := Sigma11FormulaDenote M f1 in
    let d2 := Sigma11FormulaDenote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) d2) d1
  | Sigma11Or f1 f2 => 
    let d1 := Sigma11FormulaDenote M f1 in
    let d2 := Sigma11FormulaDenote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) d2) d1
  | Sigma11Implies f1 f2 => 
    let d1 := Sigma11FormulaDenote M f1 in
    let d2 := Sigma11FormulaDenote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 ==> r2)) d2) d1
  | Sigma11Iff f1 f2 => 
    let d1 := Sigma11FormulaDenote M f1 in
    let d2 := Sigma11FormulaDenote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) d2) d1
  | Sigma11Forall b f => 
    let d := Sigma11TermDenote M b in
    obind (fun p' : 'F_FSize =>
    \oall (r in 'F_FSize | r < p') Sigma11FormulaDenote (AddModelV M r) f
    ) d
  | Sigma11ForSome bs y f => 
    \oexi (F in {ffun 'F_FSize ^ length bs -> option ('F_FSize)})
    andob
      (Fun_Bound_Check M (finfun_of_tuple (in_tuple bs)) y F)
      (Sigma11FormulaDenote (AddModelF M (existT _ (size bs) F)) f)
  | Sigma11Top => Some true
  | Sigma11Bot => Some false
  end.

End Sigma11Internal.