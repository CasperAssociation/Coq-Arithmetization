From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun zmodp ssrbool ssrnat ssralg seq fintype finalg tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.
From Coq Require Import ClassicalChoice.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1.
Require Import CoqArith.Prenex.
Require Import Program.

Section SemicircuitDef.

Variable (FSize : nat).

(* Record SemicircuitCtx {subCtx : Sigma11Ctx} := mkSemicircuitCtx
  { freeFC : |[freeF subCtx]| -> nat (*Number of free function calls*)
  ; exiFC : |[exiF subCtx]| -> nat (*Number of exi function calls*)
  ; indC : nat (*Number of ind function calls*)
  }. *)

(* <P> in the paper *)
Inductive SCPoly {IndC : nat} {ExiC FreeC : nat -> nat} : Type :=
| PolyConsZero : SCPoly
| PolyConsPlusOne : SCPoly
| PolyConsMinusOne : SCPoly
| PolyConsPlus : SCPoly -> SCPoly -> SCPoly
| PolyConsTimes : SCPoly -> SCPoly -> SCPoly
| PolyConsInd : |[IndC]| -> SCPoly
| PolyConsFreeV : nat -> SCPoly
| PolyConsUniV : nat -> SCPoly
| PolyConsFreeF : forall i, |[FreeC i]| -> SCPoly
| PolyConsExiF : forall i, |[ExiC i]| -> SCPoly.

(* <S> in the paper *)
Inductive SCProp {IndC ExiC FreeC} : Type :=
| ZOConsNot : SCProp -> SCProp
| ZOConsAnd : SCProp -> SCProp -> SCProp
| ZOConsOr : SCProp -> SCProp -> SCProp
| ZOConsImp : SCProp -> SCProp -> SCProp
| ZOConsEq : @SCPoly IndC ExiC FreeC -> @SCPoly IndC ExiC FreeC -> SCProp.

Record SemiCircuit {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} : Type :=
  mkSemiCircuit {
    (* nu : {s : |[exiV ctx]| -> { m : nat | m <= uniV ctx } | forall i j : |[exiV ctx]|, (` i) <= (` j) -> (` (s j)) <= (` (s i))}; *)
    indArgs0 : |[IndC0]| -> (@SCPoly IndC0 ExiC0 FreeC0 * @SCPoly IndC0 ExiC0 FreeC0);
    indArgsS : forall x : |[length E]|, 
               |[IndCS x]| -> 
                   (@SCPoly (IndCS x) (ExiCS x) (FreeCS x) 
                  * @SCPoly (IndCS x) (ExiCS x) (FreeCS x));
    (* w in paper *)
    freeFArgs0 : forall i a : nat, |[FreeC0 i]| -> (|[a]| -> @SCPoly IndC0 ExiC0 FreeC0);
    freeFArgsS : forall x : |[length E]|, 
                 forall i a : nat, |[FreeCS x i]| -> (|[a]| -> @SCPoly (IndCS x) (ExiCS x) (FreeCS x));
    (* omega in paper *)
    exiArgs0 : forall i, |[ExiC0 (` i)]| -> (|[lnth E i]| -> @SCPoly IndC0 ExiC0 FreeC0);
    exiArgsS : forall x : |[length E]|, 
                 forall i, |[ExiCS x (` i)]| -> (|[lnth E i]| -> @SCPoly (IndCS x) (ExiCS x) (FreeCS x));
    (* V in paper *)
    uniVBounds : seq (@SCPoly IndC0 ExiC0 FreeC0);
    (* S, G and B in paper *)
    exiFBounds : forall i, (|[lnth E i]| -> @SCPoly (IndCS i) (ExiCS i) (FreeCS i)) 
                          * @SCPoly (IndCS i) (ExiCS i) (FreeCS i);
    formula : @SCProp IndC0 ExiC0 FreeC0
  }.

(* Record SCInstance {ctx} {R : RingData} {c : @SemicircuitCtx ctx} : Type :=
  mkSCInstance { 
    (* v in paper *)
    freeVInst : |[freeV ctx]| -> T R;
    (* f in paper *)
    freeFInst : forall i : |[freeF ctx]|, (|[freeFA ctx i]| -> T R) -> option 'F_FSize;
  }. *)

Record SCAdvice {E IndC0} {ExiC0 FreeC0 : nat -> nat} 
                {IndCS : |[length E]| -> nat} {ExiCS FreeCS : |[length E]| -> nat -> nat} 
                {M : @Sigma11Model FSize} : Type :=
  mkSCAdvice { 
    (* s and g in paper *)
    exiAdv : forall i, (|[lnth E i]| -> 'F_FSize) -> option 'F_FSize;
    (* o in paper *)
    (*Arguments are: which bound, which function, which call*)
    freeFCallOut0 : forall i, |[FreeC0 i]| -> (nat -> 'F_FSize) -> option 'F_FSize;
    freeFCallOutS : forall x : |[length E]|, forall i,  |[FreeCS x i]| -> (nat -> 'F_FSize) -> option 'F_FSize;
    (* sigma in paper *)
    (*Arguments are: which bound, which function, which call*)
    exiCallOut0 : forall i, |[ExiC0 i]| -> (nat -> 'F_FSize) -> option 'F_FSize;
    exiCallOutS : forall x : |[length E]|, forall i, |[ExiCS x i]| -> (nat -> 'F_FSize) -> option 'F_FSize;
    (*Arguments are: which bound, which call*)
    indCallOut0 : |[IndC0]| -> (nat -> 'F_FSize) -> option 'F_FSize;
    indCallOutS : forall x : |[length E]|, |[IndCS x]| -> (nat -> 'F_FSize) -> option 'F_FSize;
  }.

Fixpoint SCPolyDenotation0 {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M)
  (p : @SCPoly IndC0 ExiC0 FreeC0) :
  (nat -> 'F_FSize) -> option 'F_FSize :=
  match p with
  | PolyConsZero => fun _ => Some 0%R
  | PolyConsPlusOne => fun _ => Some 1%R
  | PolyConsMinusOne => fun _ => Some (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SCPolyDenotation0 adv p1 u in
    let r2 := SCPolyDenotation0 adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SCPolyDenotation0 adv p1 u in
    let r2 := SCPolyDenotation0 adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyConsInd i => indCallOut0 adv i
  | PolyConsFreeV i => fun _ => Some (V_F _ M i)
  | PolyConsUniV i => fun u => Some (u i)
  | PolyConsFreeF i j => freeFCallOut0 adv i j
  | PolyConsExiF i j => exiCallOut0 adv i j
  end.

Fixpoint SCPolyDenotationS {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M)
  x (p : @SCPoly (IndCS x) (ExiCS x) (FreeCS x)) :
  (nat -> 'F_FSize) -> option 'F_FSize :=
  match p with
  | PolyConsZero => fun _ => Some 0%R
  | PolyConsPlusOne => fun _ => Some 1%R
  | PolyConsMinusOne => fun _ => Some (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SCPolyDenotationS adv x p1 u in
    let r2 := SCPolyDenotationS adv x p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SCPolyDenotationS adv x p1 u in
    let r2 := SCPolyDenotationS adv x p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyConsInd i => indCallOutS adv x i
  | PolyConsFreeV i => fun _ => Some (V_F _ M i)
  | PolyConsUniV i => fun u => Some (u i)
  | PolyConsFreeF i j => freeFCallOutS adv x i j
  | PolyConsExiF i j => exiCallOutS adv x i j
  end.

Fixpoint SCPropDenotation {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M)
  (p : @SCProp IndC0 ExiC0 FreeC0) :
  (nat -> 'F_FSize) -> option bool :=
  match p with
  | ZOConsNot p => fun u => 
    let r := SCPropDenotation adv p u in
    obind (fun r1 => Some (negb r)) r
  | ZOConsAnd p1 p2 => fun u => 
    let r1 := SCPropDenotation adv p1 u in
    let r2 := SCPropDenotation adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) r2) r1
  | ZOConsOr p1 p2 => fun u => 
    let r1 := SCPropDenotation adv p1 u in
    let r2 := SCPropDenotation adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) r2) r1
  | ZOConsImp p1 p2 => fun u => 
    let r1 := SCPropDenotation adv p1 u in
    let r2 := SCPropDenotation adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 ==> r2)) r2) r1
  | ZOConsEq p1 p2 => fun u => 
    let r1 := SCPolyDenotation0 adv p1 u in
    let r2 := SCPolyDenotation0 adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) r2) r1
  end.

(* Definition UProp {ctx} {R} {c}
                 (inst : @SCInstance ctx R (Ctx c)) (adv : @SCAdvice ctx R (Ctx c)) 
                 (t : |[uniV ctx]| -> T R) : Prop :=
  let ev i := SCPolyDenotation inst adv (lnth (polyConstraints c) (uniVBounds c i)) in
  forall i, 
    match (ev i t) with
    | None => false
    | Some e => lt R (t i) e
    end.

Definition U {ctx} {R} {c}
             (inst : @SCInstance ctx R (Ctx c)) (adv : @SCAdvice ctx R (Ctx c)) : Type 
  := { t : |[uniV ctx]| -> T R | UProp inst adv t }. *)


Definition SCInBound0 {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M)
  (r : 'F_FSize)
  (b : SCPoly) 
  (t : nat -> 'F_FSize) : bool :=
  match SCPolyDenotation0 adv b t with
  | None => false
  | Some e => r < e
  end.

Definition SCInBoundS {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) x
  (r : 'F_FSize)
  (b : SCPoly) 
  (t : nat -> 'F_FSize) : bool :=
  match SCPolyDenotationS adv x b t with
  | None => false
  | Some e => r < e
  end.

(*A collection of universal variables within *)
Program Definition SCU {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) 
  (f : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) : Type 
  := { u : |[length (uniVBounds f)]| -> 'F_FSize | 
       forall j : |[length (uniVBounds f)]|,
       forall v : nat -> 'F_FSize, 
       SCInBound0 adv (u j) (lnth (uniVBounds f) j) (MakeU u v)
    }.

Program Definition SCFormulaCondition {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (f : SemiCircuit) : Prop :=
  forall (u : SCU adv f), 
  SCPropDenotation adv (formula f) (MakeU u (fun _ => 0%R)) == Some true.

Program Definition SCB {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) 
  (f : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) (x : |[length E]|) : Type 
  := { u : |[lnth E x]| -> 'F_FSize | 
       forall j : |[lnth E x]|,
       forall v : nat -> 'F_FSize, 
       SCInBoundS adv x (u j) ((exiFBounds f x).1 j) (MakeU u v)
    }.

Program Definition SCIndCondition0 {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall i : |[IndC0]|,
  let (a1, a2) := indArgs0 c i in
  let b1 : option 'F_FSize := SCPolyDenotation0 adv a1 (MakeU u v) in
  let b2 : option 'F_FSize := SCPolyDenotation0 adv a2 (MakeU u v) in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOut0 adv i (MakeU u v).

Program Definition SCIndConditionS {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall x : |[length E]|, forall u : SCB adv c x, forall i : |[IndCS x]|,
  let (a1, a2) := indArgsS c x i in
  let b1 : option 'F_FSize := SCPolyDenotationS adv x a1 (MakeU u v) in
  let b2 : option 'F_FSize := SCPolyDenotationS adv x a2 (MakeU u v) in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOutS adv x i (MakeU u v).

Program Definition SCExiFCondition0 {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall (i : |[length E]|) (j : |[ExiC0 i]|),
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotation0 adv (exiArgs0 c i j a) (MakeU u v) in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOut0 adv i j (MakeU u v).

Program Definition SCExiFConditionS {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall x, forall u : SCB adv c x, forall (i : |[length E]|) (j : |[ExiCS x i]|),
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotationS adv x (exiArgsS c x i j a) (MakeU u v) in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOutS adv x i j (MakeU u v).

Program Definition SCFreeFCondition0 {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall (i : |[length E]|) (j : |[FreeC0 i]|),
  let t a : option 'F_FSize
      := SCPolyDenotation0 adv (freeFArgs0 c i (projT1 (F_S _ M i)) j a) (MakeU u v) in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOut0 adv i j (MakeU u v).

Program Definition SCFreeFConditionS {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall x, forall u : SCB adv c x, forall (i : |[length E]|) (j : |[FreeCS x i]|),
  let t a : option 'F_FSize
      := SCPolyDenotationS adv x (freeFArgsS c x i (projT1 (F_S _ M i)) j a) (MakeU u v) in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOutS adv x i j (MakeU u v).

Program Definition SCUniversalCondition {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) 
  (c : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) : Prop :=
  forall (u : nat -> 'F_FSize) (i : |[length (uniVBounds c)]|),
    (forall j : |[i]|, SCInBound0 adv (u j) (lnth (uniVBounds c) j) u) ->
    exists o, SCPolyDenotation0 adv (lnth (uniVBounds c) i) u = Some o.
Next Obligation. strivial use: ltn_trans. Qed.

Program Fixpoint SCFunBounds {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (x : |[length E]|) {a}
  (ins : |[a]| -> 'F_FSize) (out : 'F_FSize)
  (insB : |[a]| -> SCPoly) (outB : SCPoly) :
  (nat -> 'F_FSize) -> bool := fun u =>
  match a with
  | 0 => SCInBoundS adv x out outB u
  | n.+1 => SCInBoundS adv x (ins 0) (insB 0) u &&
    @SCFunBounds E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M 
      adv x n (fun x => ins (x.+1)) out (fun x => insB (x.+1)) outB u
  end.

Definition SCExiBoundCondition {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) 
  (c : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) : Prop :=
  forall u : nat -> 'F_FSize, forall i : |[length E]|,
  forall (ins : |[lnth E i]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv i ins == Some out -> 
  SCFunBounds adv i ins out 
    (fun x => (exiFBounds c i).1 x)
    (exiFBounds c i).2 (MakeU ins u) == true.

Definition SCDenotation {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (c : SemiCircuit) : Prop :=
  exists (a : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M),
    SCFormulaCondition a c /\
    SCIndCondition0 a c /\
    SCIndConditionS a c /\
    SCExiFCondition0 a c /\
    SCExiFConditionS a c /\
    SCFreeFCondition0 a c /\
    SCFreeFConditionS a c /\
    SCUniversalCondition a c /\
    SCExiBoundCondition a c.

End SemicircuitDef.

Section SemicircuitTranslation.

