Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas.
Require Import PG32.pg32_inductive.
Require Import List.
Require Import PG32.pg32_spreads_packings PG32.pg32_packings.

Import ListNotations.

Require Import PG32.pg32_packings_part1 PG32.pg32_packings_part2 PG32.pg32_packings_part3 PG32.pg32_packings_part4 PG32.pg32_packings_part5 PG32.pg32_packings_part6.

Lemma abcdef_bool_lr : forall x y z t u v,
    x && y && z && t && u && v -> x /\y /\ z /\ t /\ u /\ v.
Proof.
  intros x y z t u v Hv'.
  destruct  (and_bool_lr _ _ Hv') as [Hu' Hv].
  destruct (and_bool_lr _ _ Hu') as [Ht' Hu]. 
  destruct (and_bool_lr _ _ Ht') as [Hz' Ht].
  destruct (and_bool_lr _ _ Hz') as [Hy' Hz].
  destruct (and_bool_lr _ _ Hy') as [Hx Hy].
  repeat split; assumption.
Qed.

Lemma is_packing_descr_B :
  forall s1 s2 s3 s4 s5 s6 s7 : list Line,
    ltS s1 s2 && ltS s2 s3 && ltS s3 s4 && ltS s4 s5 && ltS s5 s6 && ltS s6 s7 ->
    In s1 spreads -> In s2 spreads -> In s3 spreads -> In s4 spreads ->
    In s5 spreads -> In s6 spreads -> In s7 spreads ->
    (is_packing7 s1 s2 s3 s4 s5 s6 s7) -> In [s1;s2;s3;s4;s5;s6;s7] packings.
Proof.
  intros s1 s2 s3 s4 s5 s6 s7 Hlt Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 His.
  decompose [and] (abcdef_bool_lr _ _ _ _ _ _ Hlt); clear Hlt; 
    decompose [or] (In_spreads_decomp s1 Hs1); clear Hs1; subst s1.
  apply aux_S0; assumption.
  apply aux_S1; assumption.
  apply aux_S2; assumption.
  apply aux_S3; assumption.
  apply aux_S4; assumption.
  apply aux_S5; assumption.
  apply aux_S6; assumption.
  apply aux_S7; assumption.
  apply aux_S8; assumption.
  apply aux_S9; assumption.
  apply aux_S10; assumption.
  apply aux_S11; assumption.
  apply aux_S12; assumption.
  apply aux_S13; assumption.
  apply aux_S14; assumption.
  apply aux_S15; assumption.
  apply aux_S16; assumption.
  apply aux_S17; assumption.
  apply aux_S18; assumption.
  apply aux_S19; assumption.
  apply aux_S20; assumption.
  apply aux_S21; assumption.
  apply aux_S22; assumption.
  apply aux_S23; assumption.
  apply aux_S24; assumption.
  apply aux_S25; assumption.
  apply aux_S26; assumption.
  apply aux_S27; assumption.
  apply aux_S28; assumption.
  apply aux_S29; assumption.
  apply aux_S30; assumption.
  apply aux_S31; assumption.
  apply aux_S32; assumption.
  apply aux_S33; assumption.
  apply aux_S34; assumption.
  apply aux_S35; assumption.
  apply aux_S36; assumption.
  apply aux_S37; assumption.
  apply aux_S38; assumption.
  apply aux_S39; assumption.
  apply aux_S40; assumption.
  apply aux_S41; assumption.
  apply aux_S42; assumption.
  apply aux_S43; assumption.
  apply aux_S44; assumption.
  apply aux_S45; assumption.
  apply aux_S46; assumption.
  apply aux_S47; assumption.
  apply aux_S48; assumption.
  apply aux_S49; assumption.
  apply aux_S50; assumption.
  apply aux_S51; assumption.
  apply aux_S52; assumption.
  apply aux_S53; assumption.
  apply aux_S54; assumption.
  apply aux_S55; assumption.
Qed.

(* main theorem *)
Lemma is_packing_descr : forall s1 s2 s3 s4 s5 s6 s7 : list Line,
    ltS s1 s2 && ltS s2 s3 && ltS s3 s4 && ltS s4 s5 && ltS s5 s6 && ltS s6 s7 ->
    In s1 spreads -> In s2 spreads -> In s3 spreads -> In s4 spreads ->
    In s5 spreads -> In s6 spreads -> In s7 spreads ->
    (is_packing7 s1 s2 s3 s4 s5 s6 s7) <-> In [s1;s2;s3;s4;s5;s6;s7] packings.
Proof.
  intros; split; [apply is_packing_descr_B ; assumption| apply is_packing_descr_A].
Qed.

