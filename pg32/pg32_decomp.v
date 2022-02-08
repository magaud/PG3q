Require Import ssreflect ssrfun ssrbool.

Require Import PG32.pg32_inductive PG32.pg32_proofs.
Require Import PG32.pg32_spreads.
Require Import PG32.pg32_spreads_collineations.
Require Import PG32.pg32_spreads_packings.
Require Import PG32.pg32_packings_collineations.
Require Import PG32.pg32_automorphisms.
Require Import PG32.pg32_decomp_prelude.

Require Import PG32.pg32_decomp0.
Require Import PG32.pg32_decomp1.
Require Import PG32.pg32_decomp2.
Require Import PG32.pg32_decomp3.
Require Import PG32.pg32_decomp4.
Require Import PG32.pg32_decomp5.
Require Import PG32.pg32_decomp6.
Require Import PG32.pg32_decomp7.
Require Import PG32.pg32_decomp8.
Require Import PG32.pg32_decomp9.
Require Import PG32.pg32_decomp10.
Require Import PG32.pg32_decomp11.
Require Import PG32.pg32_decomp12.
Require Import PG32.pg32_decomp13.
Require Import PG32.pg32_decomp14.

Require Import List.
Import ListNotations.
Lemma focus : forall (fp:Point->Point) (fl:Line->Line),
    forall l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 L,
      In (fp, fl) (l0++l1++l2++l3++l4++l5++l6 ++l7++l8++l9++l10++l11++l12++l13) ->
      In (fp, fl) (l0++l1++l2++l3++l4++l5++l6 ++l7++l8++l9++l10++l11++l12++l13++L)
   .
Proof.
  intros fp fl l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 L.
  repeat rewrite in_app_iff; solve [intuition].
Qed.

Lemma strip : forall (fp:Point->Point) (fl:Line->Line),
    forall l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 L,
      In (fp, fl) L ->
      In (fp, fl) (l0++l1++l2++l3++l4++l5++l6 ++l7++l8++l9++l10++l11++l12++l13++L).
Proof.
  intros fp fl l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 L.
  repeat rewrite in_app_iff; solve [intuition].
Qed.
    
Lemma is_collineations_descr_B :
  forall fp fl, is_collineation fp fl -> In (fp,fl) all_collineations.
Proof.
  intros fp fl Hfpfl.
  case_eq (fp P0); intros HP0.
  apply focus; apply is_collineations_descr_B_P0; assumption.
  do 1 apply strip; apply focus; apply is_collineations_descr_B_P1; assumption.
  do 2 apply strip; apply focus; apply is_collineations_descr_B_P2; assumption.
  do 3 apply strip; apply focus; apply is_collineations_descr_B_P3; assumption.
  do 4 apply strip; apply focus; apply is_collineations_descr_B_P4; assumption.
  do 5 apply strip; apply focus; apply is_collineations_descr_B_P5; assumption.
  do 6 apply strip; apply focus; apply is_collineations_descr_B_P6; assumption.
  do 7 apply strip; apply focus; apply is_collineations_descr_B_P7; assumption.
  do 8 apply strip; apply focus; apply is_collineations_descr_B_P8; assumption.
  do 9 apply strip; apply focus; apply is_collineations_descr_B_P9; assumption.
  do 10 apply strip; apply focus; apply is_collineations_descr_B_P10; assumption.
  do 11 apply strip; apply focus; apply is_collineations_descr_B_P11; assumption.
  do 12 apply strip; apply focus; apply is_collineations_descr_B_P12; assumption.
  do 13 apply strip; apply focus; apply is_collineations_descr_B_P13; assumption.
  do 14 apply strip; apply is_collineations_descr_B_P14; assumption.
Qed.
