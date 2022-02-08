Require Import PG32.pg32_inductive.
Require Import PG32.pg32_spreads_packings.
Require Import PG32.pg32_spreads_collineations.
Require Import PG32.pg32_packings_collineations.
Require Import PG32.pg32_automorphisms. 
Require Import PG32.pg32_collineations_tactics.
Require Import PG32.pg32_collineations PG32.pg32_decomp.

Require Import List.
Import ListNotations.

Lemma is_collineations_descr : forall fp fl, is_collineation fp fl <-> In (fp,fl) all_collineations.
Proof.
  intros; split; [apply is_collineations_descr_B; assumption| apply is_collineations_descr_A].
Qed.


