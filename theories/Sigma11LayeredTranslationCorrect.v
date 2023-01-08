From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import 
  ssreflect ssrfun finfun zmodp ssrbool ssrnat ssralg seq fintype finalg tuple eqtype
  bigop.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils CoqArith.Sigma11 CoqArith.Sigma11Layered CoqArith.Sigma11LayeredTranslation.

Require Import Program.

Module Sigma11LayeredTranslationCorrectInternal (Params : Sigma11Parameters).
  Module S11 := Sigma11LayeredTranslationInternal Params.
  Import S11.
  Export S11.

  Theorem NoQuantNoQuant : forall f, NoQuantifiers f -> fst (BubbleQuantifiers f) = nil.
    induction f; try qauto;
    simpl; do 2 destruct (NoQuantifiers _); try qauto.
  Qed.

  Theorem NoUni0Count : forall f, NoUniversalQuantifiers f -> UniNums (fst (BubbleQuantifiers f)) = 0.
  Proof.
    induction f; try qauto; simpl; move=>i. 
    all: try (unfold UniNums; by rewrite big_nil).
    all: try 
      (rewrite NoQuantNoQuant;[|by destruct (NoQuantifiers _)];
       rewrite NoQuantNoQuant;[|by destruct (NoQuantifiers _)];unfold UniNums; by rewrite big_nil).
    all: try
      (transitivity (UniNums (BubbleQuantifiers f1).1 + UniNums (BubbleQuantifiers f2).1);[
        unfold UniNums; by rewrite big_cat|
        do 2 destruct (NoUniversalQuantifiers _); try qauto]).
    - rewrite NoQuantNoQuant; auto.
      unfold UniNums; by rewrite big_nil.
    transitivity (UniNums (BubbleQuantifiers f).1); try qauto.
    unfold UniNums; by rewrite big_cons.
  Qed.

  Theorem NoExi0Count : forall f, NoExistentialQuantifiers f -> ExiNums (fst (BubbleQuantifiers f)) = 0.
  Proof.
    induction f; try qauto; simpl; move=>i. 
    all: try (unfold ExiNums; by rewrite big_nil).
    all: try 
      (rewrite NoQuantNoQuant;[|by destruct (NoQuantifiers _)];
       rewrite NoQuantNoQuant;[|by destruct (NoQuantifiers _)];unfold ExiNums; by rewrite big_nil).
    - rewrite NoQuantNoQuant; auto.
      unfold ExiNums; by rewrite big_nil.
    - transitivity (ExiNums (BubbleQuantifiers f1).1 + ExiNums (BubbleQuantifiers f2).1). 
      unfold ExiNums; by rewrite big_cat.
      do 2 destruct (NoExistentialQuantifiers _); qauto.
    - rewrite NoQuantNoQuant; auto;destruct (NoExistentialQuantifiers f2), (NoQuantifiers _); qauto.
    transitivity (ExiNums (BubbleQuantifiers f).1); try qauto.
    unfold ExiNums; by rewrite big_cons.
  Qed.

End Sigma11LayeredTranslationCorrectInternal.
