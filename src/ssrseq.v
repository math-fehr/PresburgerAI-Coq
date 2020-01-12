From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Export seq eqtype ssrnat.


Theorem fold_union :
  forall (A: eqType) (l: seq A) f base P,
    (forall acc a, P (f acc a) = P acc || P a) ->
             P (foldl f base l) = P base || (has P l).
Proof.
  move => A. elim => [ f base P HP /= | ]. by rewrite orbF.
  move => a l Hind f base P HP. rewrite /= Hind => //.
  by rewrite HP orbA.
Qed.

Theorem fold_intersection :
  forall (A: eqType) (l: seq A) f base P,
    (forall acc a, P (f acc a) = P acc && P a) ->
             P (foldl f base l) = (P base && all P l).
Proof.
  move => A. elim => [ f base P HP |  ]; first by rewrite andbT.
  move => a l Hind f base P HP. rewrite /= Hind => //.
  by rewrite HP andbA.
Qed.



Theorem sub_all_in: forall (T : eqType) (a1 a2 : pred T) (s: seq T),
    subpred (T:=T) (fun x => (x \in s) ==> a1 x) (fun x => (x \in s) ==> a2 x) ->
    all a1 s -> all a2 s.
Proof.
  move => T a1 a2 s Hsubpred.
  move => /allP HIn1. apply /allP => x Hx_in.
  move => /(_ x) in Hsubpred. rewrite Hx_in in Hsubpred.
  rewrite !implyTb in Hsubpred; auto.
Qed.

Theorem zip_uniq :
  forall (A B: eqType) (a: A) (b: B) (s1: seq A) (s2: seq B), uniq s1 -> uniq (zip s1 s2).
Proof.
  move => A B a b s1 s2.
  move => /uniqP Huniq.
  apply /(uniqP (a,b)) => x y Hx Hy.
  move => /(_ a x y) in Huniq.
  rewrite /in_mem /= in Hx, Hy, Huniq.
  move: (Hx) (Hy). rewrite !size_zip !leq_min => /andP[Hx1 Hx2] /andP[Hy1 Hy2].
  move => /(_ Hx1 Hy1) in Huniq.
  rewrite !nth_zip_cond Hx Hy. move => [H1 H2].
    by auto.
Qed.
