Require Import PG32.pg32_inductive.
Require Import PG32.pg32_spreads_packings.
Require Import PG32.pg32_spreads_collineations.
Require Import PG32.pg32_packings_collineations.
Require Import PG32.pg32_automorphisms. 
Require Import PG32.pg32_collineations_tactics.
Require Import PG32.pg32_collineations0 PG32.pg32_collineations1 PG32.pg32_collineations2 PG32.pg32_collineations3 PG32.pg32_collineations4 PG32.pg32_collineations5 PG32.pg32_collineations6 PG32.pg32_collineations7 PG32.pg32_collineations8 PG32.pg32_collineations9 PG32.pg32_collineations10 PG32.pg32_collineations11 PG32.pg32_collineations12 PG32.pg32_collineations13 PG32.pg32_collineations14.

Require Import List.
Import ListNotations.

Lemma decompose : forall (fp:Point->Point) (fl:Line->Line),
    forall l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 L,
      In (fp, fl)
         (l0++l1++l2++l3++l4++l5++l6 ++l7++l8++l9++l10++l11++l12++l13++L)->
      In (fp, fl) (l0++l1++l2++l3++l4++l5++l6 ++l7++l8++l9++l10++l11++l12++l13) \/ In (fp,fl) L.
Proof.
  intros fp fl l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 L.
  repeat rewrite in_app_iff; solve [intuition].
Qed.
    
Lemma is_collineations_descr_A :
  forall fp fl, In (fp, fl) all_collineations -> is_collineation fp fl.
Proof.
  unfold all_collineations.
  intros fp fl HIn_S.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c0; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c14; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c28; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c42; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c56; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c70; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c84; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c98; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c112; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c126; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c140; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c154; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c168; assumption.
  apply decompose in HIn_S; destruct HIn_S as [Hall | HIn_S].
  apply is_col_all_c182; assumption.
  apply is_col_all_c196; assumption.
Qed.
