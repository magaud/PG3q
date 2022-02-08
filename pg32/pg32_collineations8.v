Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas.
Require Import PG32.pg32_inductive PG32.pg32_spreads_collineations.
Require Import PG32.pg32_automorphisms.
Require Import PG32.pg32_automorphisms_inv.
Require Import Lists.List.
Import ListNotations.
Require Import Arith.

Lemma collineation_10752 : is_collineation fp_10752 fl_10752.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10752 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10752 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10752.

Lemma collineation_10753 : is_collineation fp_10753 fl_10753.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10753 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10753 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10753.

Lemma collineation_10754 : is_collineation fp_10754 fl_10754.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10754 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10754 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10754.

Lemma collineation_10755 : is_collineation fp_10755 fl_10755.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10755 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10755 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10755.

Lemma collineation_10756 : is_collineation fp_10756 fl_10756.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10756 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10756 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10756.

Lemma collineation_10757 : is_collineation fp_10757 fl_10757.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10757 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10757 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10757.

Lemma collineation_10758 : is_collineation fp_10758 fl_10758.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10758 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10758 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10758.

Lemma collineation_10759 : is_collineation fp_10759 fl_10759.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10759 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10759 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10759.

Lemma collineation_10760 : is_collineation fp_10760 fl_10760.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10760 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10760 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10760.

Lemma collineation_10761 : is_collineation fp_10761 fl_10761.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10761 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10761 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10761.

Lemma collineation_10762 : is_collineation fp_10762 fl_10762.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10762 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10762 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10762.

Lemma collineation_10763 : is_collineation fp_10763 fl_10763.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10763 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10763 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10763.

Lemma collineation_10764 : is_collineation fp_10764 fl_10764.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10764 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10764 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10764.

Lemma collineation_10765 : is_collineation fp_10765 fl_10765.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10765 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10765 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10765.

Lemma collineation_10766 : is_collineation fp_10766 fl_10766.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10766 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10766 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10766.

Lemma collineation_10767 : is_collineation fp_10767 fl_10767.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10767 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10767 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10767.

Lemma collineation_10768 : is_collineation fp_10768 fl_10768.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10768 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10768 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10768.

Lemma collineation_10769 : is_collineation fp_10769 fl_10769.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10769 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10769 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10769.

Lemma collineation_10770 : is_collineation fp_10770 fl_10770.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10770 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10770 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10770.

Lemma collineation_10771 : is_collineation fp_10771 fl_10771.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10771 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10771 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10771.

Lemma collineation_10772 : is_collineation fp_10772 fl_10772.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10772 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10772 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10772.

Lemma collineation_10773 : is_collineation fp_10773 fl_10773.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10773 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10773 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10773.

Lemma collineation_10774 : is_collineation fp_10774 fl_10774.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10774 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10774 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10774.

Lemma collineation_10775 : is_collineation fp_10775 fl_10775.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10775 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10775 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10775.

Lemma collineation_10776 : is_collineation fp_10776 fl_10776.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10776 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10776 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10776.

Lemma collineation_10777 : is_collineation fp_10777 fl_10777.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10777 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10777 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10777.

Lemma collineation_10778 : is_collineation fp_10778 fl_10778.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10778 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10778 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10778.

Lemma collineation_10779 : is_collineation fp_10779 fl_10779.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10779 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10779 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10779.

Lemma collineation_10780 : is_collineation fp_10780 fl_10780.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10780 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10780 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10780.

Lemma collineation_10781 : is_collineation fp_10781 fl_10781.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10781 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10781 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10781.

Lemma collineation_10782 : is_collineation fp_10782 fl_10782.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10782 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10782 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10782.

Lemma collineation_10783 : is_collineation fp_10783 fl_10783.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10783 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10783 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10783.

Lemma collineation_10784 : is_collineation fp_10784 fl_10784.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10784 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10784 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10784.

Lemma collineation_10785 : is_collineation fp_10785 fl_10785.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10785 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10785 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10785.

Lemma collineation_10786 : is_collineation fp_10786 fl_10786.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10786 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10786 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10786.

Lemma collineation_10787 : is_collineation fp_10787 fl_10787.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10787 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10787 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10787.

Lemma collineation_10788 : is_collineation fp_10788 fl_10788.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10788 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10788 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10788.

Lemma collineation_10789 : is_collineation fp_10789 fl_10789.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10789 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10789 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10789.

Lemma collineation_10790 : is_collineation fp_10790 fl_10790.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10790 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10790 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10790.

Lemma collineation_10791 : is_collineation fp_10791 fl_10791.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10791 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10791 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10791.

Lemma collineation_10792 : is_collineation fp_10792 fl_10792.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10792 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10792 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10792.

Lemma collineation_10793 : is_collineation fp_10793 fl_10793.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10793 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10793 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10793.

Lemma collineation_10794 : is_collineation fp_10794 fl_10794.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10794 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10794 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10794.

Lemma collineation_10795 : is_collineation fp_10795 fl_10795.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10795 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10795 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10795.

Lemma collineation_10796 : is_collineation fp_10796 fl_10796.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10796 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10796 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10796.

Lemma collineation_10797 : is_collineation fp_10797 fl_10797.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10797 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10797 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10797.

Lemma collineation_10798 : is_collineation fp_10798 fl_10798.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10798 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10798 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10798.

Lemma collineation_10799 : is_collineation fp_10799 fl_10799.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10799 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10799 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10799.

Lemma collineation_10800 : is_collineation fp_10800 fl_10800.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10800 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10800 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10800.

Lemma collineation_10801 : is_collineation fp_10801 fl_10801.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10801 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10801 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10801.

Lemma collineation_10802 : is_collineation fp_10802 fl_10802.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10802 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10802 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10802.

Lemma collineation_10803 : is_collineation fp_10803 fl_10803.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10803 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10803 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10803.

Lemma collineation_10804 : is_collineation fp_10804 fl_10804.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10804 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10804 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10804.

Lemma collineation_10805 : is_collineation fp_10805 fl_10805.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10805 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10805 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10805.

Lemma collineation_10806 : is_collineation fp_10806 fl_10806.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10806 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10806 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10806.

Lemma collineation_10807 : is_collineation fp_10807 fl_10807.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10807 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10807 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10807.

Lemma collineation_10808 : is_collineation fp_10808 fl_10808.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10808 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10808 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10808.

Lemma collineation_10809 : is_collineation fp_10809 fl_10809.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10809 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10809 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10809.

Lemma collineation_10810 : is_collineation fp_10810 fl_10810.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10810 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10810 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10810.

Lemma collineation_10811 : is_collineation fp_10811 fl_10811.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10811 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10811 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10811.

Lemma collineation_10812 : is_collineation fp_10812 fl_10812.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10812 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10812 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10812.

Lemma collineation_10813 : is_collineation fp_10813 fl_10813.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10813 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10813 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10813.

Lemma collineation_10814 : is_collineation fp_10814 fl_10814.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10814 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10814 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10814.

Lemma collineation_10815 : is_collineation fp_10815 fl_10815.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10815 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10815 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10815.

Lemma collineation_10816 : is_collineation fp_10816 fl_10816.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10816 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10816 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10816.

Lemma collineation_10817 : is_collineation fp_10817 fl_10817.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10817 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10817 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10817.

Lemma collineation_10818 : is_collineation fp_10818 fl_10818.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10818 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10818 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10818.

Lemma collineation_10819 : is_collineation fp_10819 fl_10819.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10819 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10819 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10819.

Lemma collineation_10820 : is_collineation fp_10820 fl_10820.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10820 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10820 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10820.

Lemma collineation_10821 : is_collineation fp_10821 fl_10821.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10821 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10821 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10821.

Lemma collineation_10822 : is_collineation fp_10822 fl_10822.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10822 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10822 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10822.

Lemma collineation_10823 : is_collineation fp_10823 fl_10823.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10823 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10823 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10823.

Lemma collineation_10824 : is_collineation fp_10824 fl_10824.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10824 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10824 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10824.

Lemma collineation_10825 : is_collineation fp_10825 fl_10825.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10825 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10825 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10825.

Lemma collineation_10826 : is_collineation fp_10826 fl_10826.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10826 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10826 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10826.

Lemma collineation_10827 : is_collineation fp_10827 fl_10827.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10827 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10827 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10827.

Lemma collineation_10828 : is_collineation fp_10828 fl_10828.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10828 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10828 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10828.

Lemma collineation_10829 : is_collineation fp_10829 fl_10829.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10829 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10829 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10829.

Lemma collineation_10830 : is_collineation fp_10830 fl_10830.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10830 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10830 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10830.

Lemma collineation_10831 : is_collineation fp_10831 fl_10831.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10831 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10831 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10831.

Lemma collineation_10832 : is_collineation fp_10832 fl_10832.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10832 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10832 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10832.

Lemma collineation_10833 : is_collineation fp_10833 fl_10833.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10833 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10833 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10833.

Lemma collineation_10834 : is_collineation fp_10834 fl_10834.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10834 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10834 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10834.

Lemma collineation_10835 : is_collineation fp_10835 fl_10835.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10835 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10835 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10835.

Lemma collineation_10836 : is_collineation fp_10836 fl_10836.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10836 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10836 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10836.

Lemma collineation_10837 : is_collineation fp_10837 fl_10837.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10837 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10837 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10837.

Lemma collineation_10838 : is_collineation fp_10838 fl_10838.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10838 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10838 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10838.

Lemma collineation_10839 : is_collineation fp_10839 fl_10839.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10839 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10839 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10839.

Lemma collineation_10840 : is_collineation fp_10840 fl_10840.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10840 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10840 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10840.

Lemma collineation_10841 : is_collineation fp_10841 fl_10841.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10841 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10841 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10841.

Lemma collineation_10842 : is_collineation fp_10842 fl_10842.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10842 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10842 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10842.

Lemma collineation_10843 : is_collineation fp_10843 fl_10843.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10843 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10843 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10843.

Lemma collineation_10844 : is_collineation fp_10844 fl_10844.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10844 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10844 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10844.

Lemma collineation_10845 : is_collineation fp_10845 fl_10845.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10845 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10845 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10845.

Lemma collineation_10846 : is_collineation fp_10846 fl_10846.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10846 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10846 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10846.

Lemma collineation_10847 : is_collineation fp_10847 fl_10847.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10847 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10847 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10847.

Lemma collineation_10848 : is_collineation fp_10848 fl_10848.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10848 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10848 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10848.

Lemma collineation_10849 : is_collineation fp_10849 fl_10849.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10849 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10849 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10849.

Lemma collineation_10850 : is_collineation fp_10850 fl_10850.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10850 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10850 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10850.

Lemma collineation_10851 : is_collineation fp_10851 fl_10851.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10851 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10851 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10851.

Lemma collineation_10852 : is_collineation fp_10852 fl_10852.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10852 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10852 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10852.

Lemma collineation_10853 : is_collineation fp_10853 fl_10853.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10853 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10853 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10853.

Lemma collineation_10854 : is_collineation fp_10854 fl_10854.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10854 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10854 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10854.

Lemma collineation_10855 : is_collineation fp_10855 fl_10855.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10855 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10855 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10855.

Lemma collineation_10856 : is_collineation fp_10856 fl_10856.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10856 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10856 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10856.

Lemma collineation_10857 : is_collineation fp_10857 fl_10857.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10857 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10857 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10857.

Lemma collineation_10858 : is_collineation fp_10858 fl_10858.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10858 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10858 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10858.

Lemma collineation_10859 : is_collineation fp_10859 fl_10859.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10859 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10859 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10859.

Lemma collineation_10860 : is_collineation fp_10860 fl_10860.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10860 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10860 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10860.

Lemma collineation_10861 : is_collineation fp_10861 fl_10861.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10861 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10861 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10861.

Lemma collineation_10862 : is_collineation fp_10862 fl_10862.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10862 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10862 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10862.

Lemma collineation_10863 : is_collineation fp_10863 fl_10863.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10863 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10863 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10863.

Lemma collineation_10864 : is_collineation fp_10864 fl_10864.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10864 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10864 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10864.

Lemma collineation_10865 : is_collineation fp_10865 fl_10865.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10865 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10865 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10865.

Lemma collineation_10866 : is_collineation fp_10866 fl_10866.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10866 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10866 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10866.

Lemma collineation_10867 : is_collineation fp_10867 fl_10867.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10867 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10867 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10867.

Lemma collineation_10868 : is_collineation fp_10868 fl_10868.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10868 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10868 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10868.

Lemma collineation_10869 : is_collineation fp_10869 fl_10869.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10869 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10869 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10869.

Lemma collineation_10870 : is_collineation fp_10870 fl_10870.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10870 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10870 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10870.

Lemma collineation_10871 : is_collineation fp_10871 fl_10871.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10871 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10871 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10871.

Lemma collineation_10872 : is_collineation fp_10872 fl_10872.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10872 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10872 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10872.

Lemma collineation_10873 : is_collineation fp_10873 fl_10873.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10873 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10873 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10873.

Lemma collineation_10874 : is_collineation fp_10874 fl_10874.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10874 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10874 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10874.

Lemma collineation_10875 : is_collineation fp_10875 fl_10875.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10875 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10875 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10875.

Lemma collineation_10876 : is_collineation fp_10876 fl_10876.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10876 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10876 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10876.

Lemma collineation_10877 : is_collineation fp_10877 fl_10877.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10877 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10877 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10877.

Lemma collineation_10878 : is_collineation fp_10878 fl_10878.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10878 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10878 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10878.

Lemma collineation_10879 : is_collineation fp_10879 fl_10879.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10879 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10879 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10879.

Lemma collineation_10880 : is_collineation fp_10880 fl_10880.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10880 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10880 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10880.

Lemma collineation_10881 : is_collineation fp_10881 fl_10881.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10881 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10881 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10881.

Lemma collineation_10882 : is_collineation fp_10882 fl_10882.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10882 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10882 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10882.

Lemma collineation_10883 : is_collineation fp_10883 fl_10883.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10883 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10883 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10883.

Lemma collineation_10884 : is_collineation fp_10884 fl_10884.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10884 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10884 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10884.

Lemma collineation_10885 : is_collineation fp_10885 fl_10885.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10885 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10885 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10885.

Lemma collineation_10886 : is_collineation fp_10886 fl_10886.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10886 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10886 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10886.

Lemma collineation_10887 : is_collineation fp_10887 fl_10887.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10887 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10887 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10887.

Lemma collineation_10888 : is_collineation fp_10888 fl_10888.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10888 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10888 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10888.

Lemma collineation_10889 : is_collineation fp_10889 fl_10889.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10889 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10889 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10889.

Lemma collineation_10890 : is_collineation fp_10890 fl_10890.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10890 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10890 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10890.

Lemma collineation_10891 : is_collineation fp_10891 fl_10891.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10891 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10891 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10891.

Lemma collineation_10892 : is_collineation fp_10892 fl_10892.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10892 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10892 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10892.

Lemma collineation_10893 : is_collineation fp_10893 fl_10893.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10893 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10893 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10893.

Lemma collineation_10894 : is_collineation fp_10894 fl_10894.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10894 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10894 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10894.

Lemma collineation_10895 : is_collineation fp_10895 fl_10895.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10895 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10895 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10895.

Lemma collineation_10896 : is_collineation fp_10896 fl_10896.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10896 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10896 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10896.

Lemma collineation_10897 : is_collineation fp_10897 fl_10897.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10897 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10897 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10897.

Lemma collineation_10898 : is_collineation fp_10898 fl_10898.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10898 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10898 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10898.

Lemma collineation_10899 : is_collineation fp_10899 fl_10899.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10899 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10899 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10899.

Lemma collineation_10900 : is_collineation fp_10900 fl_10900.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10900 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10900 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10900.

Lemma collineation_10901 : is_collineation fp_10901 fl_10901.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10901 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10901 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10901.

Lemma collineation_10902 : is_collineation fp_10902 fl_10902.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10902 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10902 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10902.

Lemma collineation_10903 : is_collineation fp_10903 fl_10903.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10903 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10903 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10903.

Lemma collineation_10904 : is_collineation fp_10904 fl_10904.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10904 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10904 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10904.

Lemma collineation_10905 : is_collineation fp_10905 fl_10905.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10905 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10905 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10905.

Lemma collineation_10906 : is_collineation fp_10906 fl_10906.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10906 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10906 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10906.

Lemma collineation_10907 : is_collineation fp_10907 fl_10907.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10907 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10907 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10907.

Lemma collineation_10908 : is_collineation fp_10908 fl_10908.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10908 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10908 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10908.

Lemma collineation_10909 : is_collineation fp_10909 fl_10909.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10909 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10909 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10909.

Lemma collineation_10910 : is_collineation fp_10910 fl_10910.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10910 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10910 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10910.

Lemma collineation_10911 : is_collineation fp_10911 fl_10911.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10911 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10911 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10911.

Lemma collineation_10912 : is_collineation fp_10912 fl_10912.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10912 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10912 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10912.

Lemma collineation_10913 : is_collineation fp_10913 fl_10913.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10913 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10913 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10913.

Lemma collineation_10914 : is_collineation fp_10914 fl_10914.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10914 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10914 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10914.

Lemma collineation_10915 : is_collineation fp_10915 fl_10915.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10915 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10915 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10915.

Lemma collineation_10916 : is_collineation fp_10916 fl_10916.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10916 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10916 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10916.

Lemma collineation_10917 : is_collineation fp_10917 fl_10917.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10917 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10917 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10917.

Lemma collineation_10918 : is_collineation fp_10918 fl_10918.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10918 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10918 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10918.

Lemma collineation_10919 : is_collineation fp_10919 fl_10919.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10919 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10919 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10919.

Lemma collineation_10920 : is_collineation fp_10920 fl_10920.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10920 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10920 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10920.

Lemma collineation_10921 : is_collineation fp_10921 fl_10921.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10921 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10921 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10921.

Lemma collineation_10922 : is_collineation fp_10922 fl_10922.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10922 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10922 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10922.

Lemma collineation_10923 : is_collineation fp_10923 fl_10923.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10923 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10923 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10923.

Lemma collineation_10924 : is_collineation fp_10924 fl_10924.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10924 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10924 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10924.

Lemma collineation_10925 : is_collineation fp_10925 fl_10925.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10925 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10925 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10925.

Lemma collineation_10926 : is_collineation fp_10926 fl_10926.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10926 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10926 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10926.

Lemma collineation_10927 : is_collineation fp_10927 fl_10927.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10927 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10927 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10927.

Lemma collineation_10928 : is_collineation fp_10928 fl_10928.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10928 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10928 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10928.

Lemma collineation_10929 : is_collineation fp_10929 fl_10929.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10929 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10929 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10929.

Lemma collineation_10930 : is_collineation fp_10930 fl_10930.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10930 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10930 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10930.

Lemma collineation_10931 : is_collineation fp_10931 fl_10931.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10931 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10931 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10931.

Lemma collineation_10932 : is_collineation fp_10932 fl_10932.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10932 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10932 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10932.

Lemma collineation_10933 : is_collineation fp_10933 fl_10933.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10933 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10933 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10933.

Lemma collineation_10934 : is_collineation fp_10934 fl_10934.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10934 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10934 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10934.

Lemma collineation_10935 : is_collineation fp_10935 fl_10935.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10935 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10935 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10935.

Lemma collineation_10936 : is_collineation fp_10936 fl_10936.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10936 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10936 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10936.

Lemma collineation_10937 : is_collineation fp_10937 fl_10937.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10937 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10937 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10937.

Lemma collineation_10938 : is_collineation fp_10938 fl_10938.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10938 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10938 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10938.

Lemma collineation_10939 : is_collineation fp_10939 fl_10939.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10939 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10939 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10939.

Lemma collineation_10940 : is_collineation fp_10940 fl_10940.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10940 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10940 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10940.

Lemma collineation_10941 : is_collineation fp_10941 fl_10941.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10941 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10941 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10941.

Lemma collineation_10942 : is_collineation fp_10942 fl_10942.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10942 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10942 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10942.

Lemma collineation_10943 : is_collineation fp_10943 fl_10943.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10943 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10943 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10943.

Lemma collineation_10944 : is_collineation fp_10944 fl_10944.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10944 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10944 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10944.

Lemma collineation_10945 : is_collineation fp_10945 fl_10945.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10945 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10945 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10945.

Lemma collineation_10946 : is_collineation fp_10946 fl_10946.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10946 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10946 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10946.

Lemma collineation_10947 : is_collineation fp_10947 fl_10947.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10947 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10947 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10947.

Lemma collineation_10948 : is_collineation fp_10948 fl_10948.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10948 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10948 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10948.

Lemma collineation_10949 : is_collineation fp_10949 fl_10949.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10949 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10949 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10949.

Lemma collineation_10950 : is_collineation fp_10950 fl_10950.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10950 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10950 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10950.

Lemma collineation_10951 : is_collineation fp_10951 fl_10951.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10951 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10951 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10951.

Lemma collineation_10952 : is_collineation fp_10952 fl_10952.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10952 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10952 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10952.

Lemma collineation_10953 : is_collineation fp_10953 fl_10953.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10953 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10953 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10953.

Lemma collineation_10954 : is_collineation fp_10954 fl_10954.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10954 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10954 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10954.

Lemma collineation_10955 : is_collineation fp_10955 fl_10955.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10955 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10955 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10955.

Lemma collineation_10956 : is_collineation fp_10956 fl_10956.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10956 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10956 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10956.

Lemma collineation_10957 : is_collineation fp_10957 fl_10957.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10957 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10957 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10957.

Lemma collineation_10958 : is_collineation fp_10958 fl_10958.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10958 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10958 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10958.

Lemma collineation_10959 : is_collineation fp_10959 fl_10959.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10959 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10959 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10959.

Lemma collineation_10960 : is_collineation fp_10960 fl_10960.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10960 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10960 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10960.

Lemma collineation_10961 : is_collineation fp_10961 fl_10961.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10961 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10961 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10961.

Lemma collineation_10962 : is_collineation fp_10962 fl_10962.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10962 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10962 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10962.

Lemma collineation_10963 : is_collineation fp_10963 fl_10963.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10963 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10963 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10963.

Lemma collineation_10964 : is_collineation fp_10964 fl_10964.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10964 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10964 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10964.

Lemma collineation_10965 : is_collineation fp_10965 fl_10965.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10965 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10965 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10965.

Lemma collineation_10966 : is_collineation fp_10966 fl_10966.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10966 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10966 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10966.

Lemma collineation_10967 : is_collineation fp_10967 fl_10967.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10967 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10967 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10967.

Lemma collineation_10968 : is_collineation fp_10968 fl_10968.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10968 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10968 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10968.

Lemma collineation_10969 : is_collineation fp_10969 fl_10969.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10969 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10969 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10969.

Lemma collineation_10970 : is_collineation fp_10970 fl_10970.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10970 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10970 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10970.

Lemma collineation_10971 : is_collineation fp_10971 fl_10971.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10971 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10971 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10971.

Lemma collineation_10972 : is_collineation fp_10972 fl_10972.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10972 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10972 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10972.

Lemma collineation_10973 : is_collineation fp_10973 fl_10973.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10973 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10973 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10973.

Lemma collineation_10974 : is_collineation fp_10974 fl_10974.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10974 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10974 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10974.

Lemma collineation_10975 : is_collineation fp_10975 fl_10975.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10975 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10975 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10975.

Lemma collineation_10976 : is_collineation fp_10976 fl_10976.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10976 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10976 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10976.

Lemma collineation_10977 : is_collineation fp_10977 fl_10977.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10977 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10977 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10977.

Lemma collineation_10978 : is_collineation fp_10978 fl_10978.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10978 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10978 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10978.

Lemma collineation_10979 : is_collineation fp_10979 fl_10979.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10979 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10979 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10979.

Lemma collineation_10980 : is_collineation fp_10980 fl_10980.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10980 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10980 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10980.

Lemma collineation_10981 : is_collineation fp_10981 fl_10981.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10981 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10981 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10981.

Lemma collineation_10982 : is_collineation fp_10982 fl_10982.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10982 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10982 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10982.

Lemma collineation_10983 : is_collineation fp_10983 fl_10983.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10983 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10983 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10983.

Lemma collineation_10984 : is_collineation fp_10984 fl_10984.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10984 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10984 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10984.

Lemma collineation_10985 : is_collineation fp_10985 fl_10985.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10985 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10985 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10985.

Lemma collineation_10986 : is_collineation fp_10986 fl_10986.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10986 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10986 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10986.

Lemma collineation_10987 : is_collineation fp_10987 fl_10987.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10987 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10987 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10987.

Lemma collineation_10988 : is_collineation fp_10988 fl_10988.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10988 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10988 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10988.

Lemma collineation_10989 : is_collineation fp_10989 fl_10989.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10989 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10989 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10989.

Lemma collineation_10990 : is_collineation fp_10990 fl_10990.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10990 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10990 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10990.

Lemma collineation_10991 : is_collineation fp_10991 fl_10991.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10991 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10991 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10991.

Lemma collineation_10992 : is_collineation fp_10992 fl_10992.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10992 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10992 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10992.

Lemma collineation_10993 : is_collineation fp_10993 fl_10993.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10993 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10993 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10993.

Lemma collineation_10994 : is_collineation fp_10994 fl_10994.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10994 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10994 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10994.

Lemma collineation_10995 : is_collineation fp_10995 fl_10995.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10995 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10995 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10995.

Lemma collineation_10996 : is_collineation fp_10996 fl_10996.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10996 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10996 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10996.

Lemma collineation_10997 : is_collineation fp_10997 fl_10997.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10997 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10997 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10997.

Lemma collineation_10998 : is_collineation fp_10998 fl_10998.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10998 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10998 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10998.

Lemma collineation_10999 : is_collineation fp_10999 fl_10999.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10999 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10999 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10999.

Lemma collineation_11000 : is_collineation fp_11000 fl_11000.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11000 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11000 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11000.

Lemma collineation_11001 : is_collineation fp_11001 fl_11001.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11001 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11001 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11001.

Lemma collineation_11002 : is_collineation fp_11002 fl_11002.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11002 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11002 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11002.

Lemma collineation_11003 : is_collineation fp_11003 fl_11003.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11003 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11003 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11003.

Lemma collineation_11004 : is_collineation fp_11004 fl_11004.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11004 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11004 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11004.

Lemma collineation_11005 : is_collineation fp_11005 fl_11005.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11005 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11005 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11005.

Lemma collineation_11006 : is_collineation fp_11006 fl_11006.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11006 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11006 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11006.

Lemma collineation_11007 : is_collineation fp_11007 fl_11007.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11007 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11007 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11007.

Lemma collineation_11008 : is_collineation fp_11008 fl_11008.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11008 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11008 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11008.

Lemma collineation_11009 : is_collineation fp_11009 fl_11009.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11009 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11009 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11009.

Lemma collineation_11010 : is_collineation fp_11010 fl_11010.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11010 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11010 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11010.

Lemma collineation_11011 : is_collineation fp_11011 fl_11011.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11011 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11011 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11011.

Lemma collineation_11012 : is_collineation fp_11012 fl_11012.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11012 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11012 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11012.

Lemma collineation_11013 : is_collineation fp_11013 fl_11013.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11013 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11013 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11013.

Lemma collineation_11014 : is_collineation fp_11014 fl_11014.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11014 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11014 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11014.

Lemma collineation_11015 : is_collineation fp_11015 fl_11015.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11015 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11015 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11015.

Lemma collineation_11016 : is_collineation fp_11016 fl_11016.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11016 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11016 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11016.

Lemma collineation_11017 : is_collineation fp_11017 fl_11017.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11017 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11017 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11017.

Lemma collineation_11018 : is_collineation fp_11018 fl_11018.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11018 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11018 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11018.

Lemma collineation_11019 : is_collineation fp_11019 fl_11019.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11019 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11019 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11019.

Lemma collineation_11020 : is_collineation fp_11020 fl_11020.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11020 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11020 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11020.

Lemma collineation_11021 : is_collineation fp_11021 fl_11021.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11021 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11021 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11021.

Lemma collineation_11022 : is_collineation fp_11022 fl_11022.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11022 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11022 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11022.

Lemma collineation_11023 : is_collineation fp_11023 fl_11023.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11023 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11023 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11023.

Lemma collineation_11024 : is_collineation fp_11024 fl_11024.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11024 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11024 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11024.

Lemma collineation_11025 : is_collineation fp_11025 fl_11025.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11025 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11025 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11025.

Lemma collineation_11026 : is_collineation fp_11026 fl_11026.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11026 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11026 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11026.

Lemma collineation_11027 : is_collineation fp_11027 fl_11027.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11027 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11027 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11027.

Lemma collineation_11028 : is_collineation fp_11028 fl_11028.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11028 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11028 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11028.

Lemma collineation_11029 : is_collineation fp_11029 fl_11029.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11029 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11029 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11029.

Lemma collineation_11030 : is_collineation fp_11030 fl_11030.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11030 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11030 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11030.

Lemma collineation_11031 : is_collineation fp_11031 fl_11031.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11031 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11031 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11031.

Lemma collineation_11032 : is_collineation fp_11032 fl_11032.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11032 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11032 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11032.

Lemma collineation_11033 : is_collineation fp_11033 fl_11033.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11033 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11033 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11033.

Lemma collineation_11034 : is_collineation fp_11034 fl_11034.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11034 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11034 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11034.

Lemma collineation_11035 : is_collineation fp_11035 fl_11035.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11035 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11035 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11035.

Lemma collineation_11036 : is_collineation fp_11036 fl_11036.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11036 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11036 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11036.

Lemma collineation_11037 : is_collineation fp_11037 fl_11037.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11037 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11037 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11037.

Lemma collineation_11038 : is_collineation fp_11038 fl_11038.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11038 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11038 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11038.

Lemma collineation_11039 : is_collineation fp_11039 fl_11039.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11039 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11039 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11039.

Lemma collineation_11040 : is_collineation fp_11040 fl_11040.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11040 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11040 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11040.

Lemma collineation_11041 : is_collineation fp_11041 fl_11041.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11041 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11041 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11041.

Lemma collineation_11042 : is_collineation fp_11042 fl_11042.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11042 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11042 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11042.

Lemma collineation_11043 : is_collineation fp_11043 fl_11043.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11043 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11043 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11043.

Lemma collineation_11044 : is_collineation fp_11044 fl_11044.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11044 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11044 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11044.

Lemma collineation_11045 : is_collineation fp_11045 fl_11045.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11045 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11045 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11045.

Lemma collineation_11046 : is_collineation fp_11046 fl_11046.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11046 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11046 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11046.

Lemma collineation_11047 : is_collineation fp_11047 fl_11047.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11047 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11047 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11047.

Lemma collineation_11048 : is_collineation fp_11048 fl_11048.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11048 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11048 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11048.

Lemma collineation_11049 : is_collineation fp_11049 fl_11049.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11049 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11049 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11049.

Lemma collineation_11050 : is_collineation fp_11050 fl_11050.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11050 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11050 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11050.

Lemma collineation_11051 : is_collineation fp_11051 fl_11051.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11051 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11051 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11051.

Lemma collineation_11052 : is_collineation fp_11052 fl_11052.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11052 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11052 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11052.

Lemma collineation_11053 : is_collineation fp_11053 fl_11053.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11053 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11053 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11053.

Lemma collineation_11054 : is_collineation fp_11054 fl_11054.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11054 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11054 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11054.

Lemma collineation_11055 : is_collineation fp_11055 fl_11055.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11055 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11055 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11055.

Lemma collineation_11056 : is_collineation fp_11056 fl_11056.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11056 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11056 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11056.

Lemma collineation_11057 : is_collineation fp_11057 fl_11057.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11057 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11057 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11057.

Lemma collineation_11058 : is_collineation fp_11058 fl_11058.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11058 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11058 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11058.

Lemma collineation_11059 : is_collineation fp_11059 fl_11059.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11059 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11059 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11059.

Lemma collineation_11060 : is_collineation fp_11060 fl_11060.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11060 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11060 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11060.

Lemma collineation_11061 : is_collineation fp_11061 fl_11061.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11061 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11061 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11061.

Lemma collineation_11062 : is_collineation fp_11062 fl_11062.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11062 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11062 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11062.

Lemma collineation_11063 : is_collineation fp_11063 fl_11063.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11063 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11063 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11063.

Lemma collineation_11064 : is_collineation fp_11064 fl_11064.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11064 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11064 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11064.

Lemma collineation_11065 : is_collineation fp_11065 fl_11065.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11065 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11065 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11065.

Lemma collineation_11066 : is_collineation fp_11066 fl_11066.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11066 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11066 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11066.

Lemma collineation_11067 : is_collineation fp_11067 fl_11067.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11067 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11067 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11067.

Lemma collineation_11068 : is_collineation fp_11068 fl_11068.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11068 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11068 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11068.

Lemma collineation_11069 : is_collineation fp_11069 fl_11069.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11069 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11069 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11069.

Lemma collineation_11070 : is_collineation fp_11070 fl_11070.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11070 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11070 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11070.

Lemma collineation_11071 : is_collineation fp_11071 fl_11071.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11071 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11071 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11071.

Lemma collineation_11072 : is_collineation fp_11072 fl_11072.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11072 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11072 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11072.

Lemma collineation_11073 : is_collineation fp_11073 fl_11073.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11073 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11073 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11073.

Lemma collineation_11074 : is_collineation fp_11074 fl_11074.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11074 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11074 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11074.

Lemma collineation_11075 : is_collineation fp_11075 fl_11075.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11075 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11075 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11075.

Lemma collineation_11076 : is_collineation fp_11076 fl_11076.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11076 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11076 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11076.

Lemma collineation_11077 : is_collineation fp_11077 fl_11077.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11077 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11077 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11077.

Lemma collineation_11078 : is_collineation fp_11078 fl_11078.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11078 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11078 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11078.

Lemma collineation_11079 : is_collineation fp_11079 fl_11079.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11079 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11079 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11079.

Lemma collineation_11080 : is_collineation fp_11080 fl_11080.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11080 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11080 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11080.

Lemma collineation_11081 : is_collineation fp_11081 fl_11081.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11081 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11081 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11081.

Lemma collineation_11082 : is_collineation fp_11082 fl_11082.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11082 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11082 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11082.

Lemma collineation_11083 : is_collineation fp_11083 fl_11083.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11083 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11083 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11083.

Lemma collineation_11084 : is_collineation fp_11084 fl_11084.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11084 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11084 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11084.

Lemma collineation_11085 : is_collineation fp_11085 fl_11085.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11085 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11085 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11085.

Lemma collineation_11086 : is_collineation fp_11086 fl_11086.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11086 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11086 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11086.

Lemma collineation_11087 : is_collineation fp_11087 fl_11087.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11087 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11087 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11087.

Lemma collineation_11088 : is_collineation fp_11088 fl_11088.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11088 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11088 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11088.

Lemma collineation_11089 : is_collineation fp_11089 fl_11089.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11089 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11089 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11089.

Lemma collineation_11090 : is_collineation fp_11090 fl_11090.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11090 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11090 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11090.

Lemma collineation_11091 : is_collineation fp_11091 fl_11091.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11091 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11091 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11091.

Lemma collineation_11092 : is_collineation fp_11092 fl_11092.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11092 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11092 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11092.

Lemma collineation_11093 : is_collineation fp_11093 fl_11093.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11093 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11093 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11093.

Lemma collineation_11094 : is_collineation fp_11094 fl_11094.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11094 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11094 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11094.

Lemma collineation_11095 : is_collineation fp_11095 fl_11095.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11095 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11095 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11095.

Lemma collineation_11096 : is_collineation fp_11096 fl_11096.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11096 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11096 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11096.

Lemma collineation_11097 : is_collineation fp_11097 fl_11097.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11097 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11097 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11097.

Lemma collineation_11098 : is_collineation fp_11098 fl_11098.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11098 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11098 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11098.

Lemma collineation_11099 : is_collineation fp_11099 fl_11099.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11099 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11099 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11099.

Lemma collineation_11100 : is_collineation fp_11100 fl_11100.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11100 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11100 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11100.

Lemma collineation_11101 : is_collineation fp_11101 fl_11101.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11101 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11101 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11101.

Lemma collineation_11102 : is_collineation fp_11102 fl_11102.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11102 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11102 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11102.

Lemma collineation_11103 : is_collineation fp_11103 fl_11103.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11103 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11103 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11103.

Lemma collineation_11104 : is_collineation fp_11104 fl_11104.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11104 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11104 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11104.

Lemma collineation_11105 : is_collineation fp_11105 fl_11105.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11105 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11105 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11105.

Lemma collineation_11106 : is_collineation fp_11106 fl_11106.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11106 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11106 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11106.

Lemma collineation_11107 : is_collineation fp_11107 fl_11107.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11107 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11107 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11107.

Lemma collineation_11108 : is_collineation fp_11108 fl_11108.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11108 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11108 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11108.

Lemma collineation_11109 : is_collineation fp_11109 fl_11109.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11109 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11109 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11109.

Lemma collineation_11110 : is_collineation fp_11110 fl_11110.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11110 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11110 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11110.

Lemma collineation_11111 : is_collineation fp_11111 fl_11111.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11111 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11111 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11111.

Lemma collineation_11112 : is_collineation fp_11112 fl_11112.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11112 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11112 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11112.

Lemma collineation_11113 : is_collineation fp_11113 fl_11113.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11113 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11113 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11113.

Lemma collineation_11114 : is_collineation fp_11114 fl_11114.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11114 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11114 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11114.

Lemma collineation_11115 : is_collineation fp_11115 fl_11115.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11115 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11115 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11115.

Lemma collineation_11116 : is_collineation fp_11116 fl_11116.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11116 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11116 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11116.

Lemma collineation_11117 : is_collineation fp_11117 fl_11117.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11117 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11117 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11117.

Lemma collineation_11118 : is_collineation fp_11118 fl_11118.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11118 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11118 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11118.

Lemma collineation_11119 : is_collineation fp_11119 fl_11119.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11119 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11119 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11119.

Lemma collineation_11120 : is_collineation fp_11120 fl_11120.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11120 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11120 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11120.

Lemma collineation_11121 : is_collineation fp_11121 fl_11121.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11121 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11121 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11121.

Lemma collineation_11122 : is_collineation fp_11122 fl_11122.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11122 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11122 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11122.

Lemma collineation_11123 : is_collineation fp_11123 fl_11123.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11123 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11123 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11123.

Lemma collineation_11124 : is_collineation fp_11124 fl_11124.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11124 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11124 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11124.

Lemma collineation_11125 : is_collineation fp_11125 fl_11125.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11125 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11125 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11125.

Lemma collineation_11126 : is_collineation fp_11126 fl_11126.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11126 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11126 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11126.

Lemma collineation_11127 : is_collineation fp_11127 fl_11127.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11127 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11127 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11127.

Lemma collineation_11128 : is_collineation fp_11128 fl_11128.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11128 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11128 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11128.

Lemma collineation_11129 : is_collineation fp_11129 fl_11129.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11129 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11129 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11129.

Lemma collineation_11130 : is_collineation fp_11130 fl_11130.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11130 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11130 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11130.

Lemma collineation_11131 : is_collineation fp_11131 fl_11131.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11131 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11131 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11131.

Lemma collineation_11132 : is_collineation fp_11132 fl_11132.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11132 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11132 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11132.

Lemma collineation_11133 : is_collineation fp_11133 fl_11133.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11133 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11133 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11133.

Lemma collineation_11134 : is_collineation fp_11134 fl_11134.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11134 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11134 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11134.

Lemma collineation_11135 : is_collineation fp_11135 fl_11135.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11135 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11135 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11135.

Lemma collineation_11136 : is_collineation fp_11136 fl_11136.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11136 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11136 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11136.

Lemma collineation_11137 : is_collineation fp_11137 fl_11137.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11137 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11137 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11137.

Lemma collineation_11138 : is_collineation fp_11138 fl_11138.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11138 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11138 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11138.

Lemma collineation_11139 : is_collineation fp_11139 fl_11139.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11139 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11139 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11139.

Lemma collineation_11140 : is_collineation fp_11140 fl_11140.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11140 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11140 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11140.

Lemma collineation_11141 : is_collineation fp_11141 fl_11141.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11141 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11141 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11141.

Lemma collineation_11142 : is_collineation fp_11142 fl_11142.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11142 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11142 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11142.

Lemma collineation_11143 : is_collineation fp_11143 fl_11143.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11143 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11143 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11143.

Lemma collineation_11144 : is_collineation fp_11144 fl_11144.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11144 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11144 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11144.

Lemma collineation_11145 : is_collineation fp_11145 fl_11145.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11145 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11145 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11145.

Lemma collineation_11146 : is_collineation fp_11146 fl_11146.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11146 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11146 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11146.

Lemma collineation_11147 : is_collineation fp_11147 fl_11147.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11147 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11147 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11147.

Lemma collineation_11148 : is_collineation fp_11148 fl_11148.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11148 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11148 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11148.

Lemma collineation_11149 : is_collineation fp_11149 fl_11149.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11149 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11149 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11149.

Lemma collineation_11150 : is_collineation fp_11150 fl_11150.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11150 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11150 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11150.

Lemma collineation_11151 : is_collineation fp_11151 fl_11151.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11151 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11151 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11151.

Lemma collineation_11152 : is_collineation fp_11152 fl_11152.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11152 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11152 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11152.

Lemma collineation_11153 : is_collineation fp_11153 fl_11153.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11153 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11153 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11153.

Lemma collineation_11154 : is_collineation fp_11154 fl_11154.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11154 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11154 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11154.

Lemma collineation_11155 : is_collineation fp_11155 fl_11155.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11155 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11155 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11155.

Lemma collineation_11156 : is_collineation fp_11156 fl_11156.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11156 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11156 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11156.

Lemma collineation_11157 : is_collineation fp_11157 fl_11157.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11157 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11157 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11157.

Lemma collineation_11158 : is_collineation fp_11158 fl_11158.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11158 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11158 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11158.

Lemma collineation_11159 : is_collineation fp_11159 fl_11159.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11159 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11159 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11159.

Lemma collineation_11160 : is_collineation fp_11160 fl_11160.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11160 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11160 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11160.

Lemma collineation_11161 : is_collineation fp_11161 fl_11161.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11161 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11161 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11161.

Lemma collineation_11162 : is_collineation fp_11162 fl_11162.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11162 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11162 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11162.

Lemma collineation_11163 : is_collineation fp_11163 fl_11163.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11163 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11163 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11163.

Lemma collineation_11164 : is_collineation fp_11164 fl_11164.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11164 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11164 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11164.

Lemma collineation_11165 : is_collineation fp_11165 fl_11165.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11165 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11165 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11165.

Lemma collineation_11166 : is_collineation fp_11166 fl_11166.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11166 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11166 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11166.

Lemma collineation_11167 : is_collineation fp_11167 fl_11167.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11167 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11167 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11167.

Lemma collineation_11168 : is_collineation fp_11168 fl_11168.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11168 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11168 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11168.

Lemma collineation_11169 : is_collineation fp_11169 fl_11169.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11169 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11169 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11169.

Lemma collineation_11170 : is_collineation fp_11170 fl_11170.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11170 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11170 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11170.

Lemma collineation_11171 : is_collineation fp_11171 fl_11171.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11171 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11171 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11171.

Lemma collineation_11172 : is_collineation fp_11172 fl_11172.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11172 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11172 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11172.

Lemma collineation_11173 : is_collineation fp_11173 fl_11173.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11173 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11173 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11173.

Lemma collineation_11174 : is_collineation fp_11174 fl_11174.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11174 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11174 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11174.

Lemma collineation_11175 : is_collineation fp_11175 fl_11175.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11175 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11175 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11175.

Lemma collineation_11176 : is_collineation fp_11176 fl_11176.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11176 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11176 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11176.

Lemma collineation_11177 : is_collineation fp_11177 fl_11177.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11177 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11177 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11177.

Lemma collineation_11178 : is_collineation fp_11178 fl_11178.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11178 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11178 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11178.

Lemma collineation_11179 : is_collineation fp_11179 fl_11179.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11179 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11179 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11179.

Lemma collineation_11180 : is_collineation fp_11180 fl_11180.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11180 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11180 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11180.

Lemma collineation_11181 : is_collineation fp_11181 fl_11181.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11181 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11181 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11181.

Lemma collineation_11182 : is_collineation fp_11182 fl_11182.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11182 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11182 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11182.

Lemma collineation_11183 : is_collineation fp_11183 fl_11183.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11183 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11183 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11183.

Lemma collineation_11184 : is_collineation fp_11184 fl_11184.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11184 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11184 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11184.

Lemma collineation_11185 : is_collineation fp_11185 fl_11185.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11185 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11185 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11185.

Lemma collineation_11186 : is_collineation fp_11186 fl_11186.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11186 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11186 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11186.

Lemma collineation_11187 : is_collineation fp_11187 fl_11187.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11187 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11187 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11187.

Lemma collineation_11188 : is_collineation fp_11188 fl_11188.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11188 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11188 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11188.

Lemma collineation_11189 : is_collineation fp_11189 fl_11189.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11189 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11189 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11189.

Lemma collineation_11190 : is_collineation fp_11190 fl_11190.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11190 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11190 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11190.

Lemma collineation_11191 : is_collineation fp_11191 fl_11191.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11191 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11191 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11191.

Lemma collineation_11192 : is_collineation fp_11192 fl_11192.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11192 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11192 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11192.

Lemma collineation_11193 : is_collineation fp_11193 fl_11193.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11193 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11193 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11193.

Lemma collineation_11194 : is_collineation fp_11194 fl_11194.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11194 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11194 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11194.

Lemma collineation_11195 : is_collineation fp_11195 fl_11195.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11195 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11195 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11195.

Lemma collineation_11196 : is_collineation fp_11196 fl_11196.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11196 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11196 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11196.

Lemma collineation_11197 : is_collineation fp_11197 fl_11197.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11197 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11197 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11197.

Lemma collineation_11198 : is_collineation fp_11198 fl_11198.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11198 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11198 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11198.

Lemma collineation_11199 : is_collineation fp_11199 fl_11199.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11199 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11199 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11199.

Lemma collineation_11200 : is_collineation fp_11200 fl_11200.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11200 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11200 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11200.

Lemma collineation_11201 : is_collineation fp_11201 fl_11201.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11201 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11201 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11201.

Lemma collineation_11202 : is_collineation fp_11202 fl_11202.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11202 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11202 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11202.

Lemma collineation_11203 : is_collineation fp_11203 fl_11203.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11203 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11203 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11203.

Lemma collineation_11204 : is_collineation fp_11204 fl_11204.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11204 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11204 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11204.

Lemma collineation_11205 : is_collineation fp_11205 fl_11205.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11205 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11205 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11205.

Lemma collineation_11206 : is_collineation fp_11206 fl_11206.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11206 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11206 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11206.

Lemma collineation_11207 : is_collineation fp_11207 fl_11207.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11207 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11207 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11207.

Lemma collineation_11208 : is_collineation fp_11208 fl_11208.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11208 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11208 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11208.

Lemma collineation_11209 : is_collineation fp_11209 fl_11209.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11209 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11209 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11209.

Lemma collineation_11210 : is_collineation fp_11210 fl_11210.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11210 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11210 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11210.

Lemma collineation_11211 : is_collineation fp_11211 fl_11211.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11211 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11211 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11211.

Lemma collineation_11212 : is_collineation fp_11212 fl_11212.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11212 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11212 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11212.

Lemma collineation_11213 : is_collineation fp_11213 fl_11213.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11213 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11213 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11213.

Lemma collineation_11214 : is_collineation fp_11214 fl_11214.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11214 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11214 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11214.

Lemma collineation_11215 : is_collineation fp_11215 fl_11215.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11215 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11215 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11215.

Lemma collineation_11216 : is_collineation fp_11216 fl_11216.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11216 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11216 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11216.

Lemma collineation_11217 : is_collineation fp_11217 fl_11217.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11217 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11217 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11217.

Lemma collineation_11218 : is_collineation fp_11218 fl_11218.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11218 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11218 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11218.

Lemma collineation_11219 : is_collineation fp_11219 fl_11219.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11219 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11219 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11219.

Lemma collineation_11220 : is_collineation fp_11220 fl_11220.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11220 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11220 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11220.

Lemma collineation_11221 : is_collineation fp_11221 fl_11221.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11221 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11221 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11221.

Lemma collineation_11222 : is_collineation fp_11222 fl_11222.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11222 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11222 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11222.

Lemma collineation_11223 : is_collineation fp_11223 fl_11223.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11223 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11223 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11223.

Lemma collineation_11224 : is_collineation fp_11224 fl_11224.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11224 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11224 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11224.

Lemma collineation_11225 : is_collineation fp_11225 fl_11225.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11225 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11225 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11225.

Lemma collineation_11226 : is_collineation fp_11226 fl_11226.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11226 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11226 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11226.

Lemma collineation_11227 : is_collineation fp_11227 fl_11227.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11227 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11227 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11227.

Lemma collineation_11228 : is_collineation fp_11228 fl_11228.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11228 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11228 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11228.

Lemma collineation_11229 : is_collineation fp_11229 fl_11229.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11229 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11229 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11229.

Lemma collineation_11230 : is_collineation fp_11230 fl_11230.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11230 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11230 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11230.

Lemma collineation_11231 : is_collineation fp_11231 fl_11231.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11231 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11231 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11231.

Lemma collineation_11232 : is_collineation fp_11232 fl_11232.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11232 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11232 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11232.

Lemma collineation_11233 : is_collineation fp_11233 fl_11233.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11233 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11233 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11233.

Lemma collineation_11234 : is_collineation fp_11234 fl_11234.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11234 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11234 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11234.

Lemma collineation_11235 : is_collineation fp_11235 fl_11235.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11235 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11235 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11235.

Lemma collineation_11236 : is_collineation fp_11236 fl_11236.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11236 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11236 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11236.

Lemma collineation_11237 : is_collineation fp_11237 fl_11237.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11237 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11237 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11237.

Lemma collineation_11238 : is_collineation fp_11238 fl_11238.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11238 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11238 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11238.

Lemma collineation_11239 : is_collineation fp_11239 fl_11239.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11239 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11239 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11239.

Lemma collineation_11240 : is_collineation fp_11240 fl_11240.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11240 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11240 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11240.

Lemma collineation_11241 : is_collineation fp_11241 fl_11241.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11241 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11241 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11241.

Lemma collineation_11242 : is_collineation fp_11242 fl_11242.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11242 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11242 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11242.

Lemma collineation_11243 : is_collineation fp_11243 fl_11243.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11243 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11243 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11243.

Lemma collineation_11244 : is_collineation fp_11244 fl_11244.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11244 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11244 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11244.

Lemma collineation_11245 : is_collineation fp_11245 fl_11245.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11245 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11245 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11245.

Lemma collineation_11246 : is_collineation fp_11246 fl_11246.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11246 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11246 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11246.

Lemma collineation_11247 : is_collineation fp_11247 fl_11247.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11247 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11247 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11247.

Lemma collineation_11248 : is_collineation fp_11248 fl_11248.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11248 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11248 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11248.

Lemma collineation_11249 : is_collineation fp_11249 fl_11249.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11249 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11249 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11249.

Lemma collineation_11250 : is_collineation fp_11250 fl_11250.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11250 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11250 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11250.

Lemma collineation_11251 : is_collineation fp_11251 fl_11251.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11251 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11251 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11251.

Lemma collineation_11252 : is_collineation fp_11252 fl_11252.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11252 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11252 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11252.

Lemma collineation_11253 : is_collineation fp_11253 fl_11253.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11253 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11253 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11253.

Lemma collineation_11254 : is_collineation fp_11254 fl_11254.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11254 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11254 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11254.

Lemma collineation_11255 : is_collineation fp_11255 fl_11255.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11255 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11255 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11255.

Lemma collineation_11256 : is_collineation fp_11256 fl_11256.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11256 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11256 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11256.

Lemma collineation_11257 : is_collineation fp_11257 fl_11257.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11257 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11257 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11257.

Lemma collineation_11258 : is_collineation fp_11258 fl_11258.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11258 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11258 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11258.

Lemma collineation_11259 : is_collineation fp_11259 fl_11259.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11259 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11259 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11259.

Lemma collineation_11260 : is_collineation fp_11260 fl_11260.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11260 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11260 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11260.

Lemma collineation_11261 : is_collineation fp_11261 fl_11261.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11261 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11261 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11261.

Lemma collineation_11262 : is_collineation fp_11262 fl_11262.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11262 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11262 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11262.

Lemma collineation_11263 : is_collineation fp_11263 fl_11263.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11263 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11263 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11263.

Lemma collineation_11264 : is_collineation fp_11264 fl_11264.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11264 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11264 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11264.

Lemma collineation_11265 : is_collineation fp_11265 fl_11265.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11265 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11265 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11265.

Lemma collineation_11266 : is_collineation fp_11266 fl_11266.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11266 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11266 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11266.

Lemma collineation_11267 : is_collineation fp_11267 fl_11267.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11267 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11267 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11267.

Lemma collineation_11268 : is_collineation fp_11268 fl_11268.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11268 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11268 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11268.

Lemma collineation_11269 : is_collineation fp_11269 fl_11269.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11269 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11269 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11269.

Lemma collineation_11270 : is_collineation fp_11270 fl_11270.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11270 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11270 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11270.

Lemma collineation_11271 : is_collineation fp_11271 fl_11271.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11271 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11271 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11271.

Lemma collineation_11272 : is_collineation fp_11272 fl_11272.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11272 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11272 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11272.

Lemma collineation_11273 : is_collineation fp_11273 fl_11273.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11273 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11273 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11273.

Lemma collineation_11274 : is_collineation fp_11274 fl_11274.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11274 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11274 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11274.

Lemma collineation_11275 : is_collineation fp_11275 fl_11275.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11275 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11275 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11275.

Lemma collineation_11276 : is_collineation fp_11276 fl_11276.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11276 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11276 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11276.

Lemma collineation_11277 : is_collineation fp_11277 fl_11277.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11277 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11277 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11277.

Lemma collineation_11278 : is_collineation fp_11278 fl_11278.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11278 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11278 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11278.

Lemma collineation_11279 : is_collineation fp_11279 fl_11279.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11279 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11279 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11279.

Lemma collineation_11280 : is_collineation fp_11280 fl_11280.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11280 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11280 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11280.

Lemma collineation_11281 : is_collineation fp_11281 fl_11281.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11281 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11281 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11281.

Lemma collineation_11282 : is_collineation fp_11282 fl_11282.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11282 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11282 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11282.

Lemma collineation_11283 : is_collineation fp_11283 fl_11283.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11283 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11283 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11283.

Lemma collineation_11284 : is_collineation fp_11284 fl_11284.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11284 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11284 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11284.

Lemma collineation_11285 : is_collineation fp_11285 fl_11285.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11285 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11285 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11285.

Lemma collineation_11286 : is_collineation fp_11286 fl_11286.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11286 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11286 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11286.

Lemma collineation_11287 : is_collineation fp_11287 fl_11287.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11287 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11287 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11287.

Lemma collineation_11288 : is_collineation fp_11288 fl_11288.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11288 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11288 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11288.

Lemma collineation_11289 : is_collineation fp_11289 fl_11289.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11289 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11289 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11289.

Lemma collineation_11290 : is_collineation fp_11290 fl_11290.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11290 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11290 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11290.

Lemma collineation_11291 : is_collineation fp_11291 fl_11291.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11291 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11291 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11291.

Lemma collineation_11292 : is_collineation fp_11292 fl_11292.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11292 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11292 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11292.

Lemma collineation_11293 : is_collineation fp_11293 fl_11293.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11293 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11293 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11293.

Lemma collineation_11294 : is_collineation fp_11294 fl_11294.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11294 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11294 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11294.

Lemma collineation_11295 : is_collineation fp_11295 fl_11295.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11295 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11295 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11295.

Lemma collineation_11296 : is_collineation fp_11296 fl_11296.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11296 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11296 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11296.

Lemma collineation_11297 : is_collineation fp_11297 fl_11297.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11297 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11297 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11297.

Lemma collineation_11298 : is_collineation fp_11298 fl_11298.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11298 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11298 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11298.

Lemma collineation_11299 : is_collineation fp_11299 fl_11299.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11299 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11299 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11299.

Lemma collineation_11300 : is_collineation fp_11300 fl_11300.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11300 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11300 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11300.

Lemma collineation_11301 : is_collineation fp_11301 fl_11301.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11301 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11301 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11301.

Lemma collineation_11302 : is_collineation fp_11302 fl_11302.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11302 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11302 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11302.

Lemma collineation_11303 : is_collineation fp_11303 fl_11303.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11303 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11303 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11303.

Lemma collineation_11304 : is_collineation fp_11304 fl_11304.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11304 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11304 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11304.

Lemma collineation_11305 : is_collineation fp_11305 fl_11305.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11305 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11305 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11305.

Lemma collineation_11306 : is_collineation fp_11306 fl_11306.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11306 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11306 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11306.

Lemma collineation_11307 : is_collineation fp_11307 fl_11307.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11307 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11307 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11307.

Lemma collineation_11308 : is_collineation fp_11308 fl_11308.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11308 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11308 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11308.

Lemma collineation_11309 : is_collineation fp_11309 fl_11309.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11309 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11309 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11309.

Lemma collineation_11310 : is_collineation fp_11310 fl_11310.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11310 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11310 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11310.

Lemma collineation_11311 : is_collineation fp_11311 fl_11311.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11311 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11311 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11311.

Lemma collineation_11312 : is_collineation fp_11312 fl_11312.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11312 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11312 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11312.

Lemma collineation_11313 : is_collineation fp_11313 fl_11313.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11313 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11313 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11313.

Lemma collineation_11314 : is_collineation fp_11314 fl_11314.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11314 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11314 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11314.

Lemma collineation_11315 : is_collineation fp_11315 fl_11315.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11315 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11315 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11315.

Lemma collineation_11316 : is_collineation fp_11316 fl_11316.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11316 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11316 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11316.

Lemma collineation_11317 : is_collineation fp_11317 fl_11317.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11317 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11317 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11317.

Lemma collineation_11318 : is_collineation fp_11318 fl_11318.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11318 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11318 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11318.

Lemma collineation_11319 : is_collineation fp_11319 fl_11319.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11319 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11319 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11319.

Lemma collineation_11320 : is_collineation fp_11320 fl_11320.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11320 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11320 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11320.

Lemma collineation_11321 : is_collineation fp_11321 fl_11321.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11321 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11321 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11321.

Lemma collineation_11322 : is_collineation fp_11322 fl_11322.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11322 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11322 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11322.

Lemma collineation_11323 : is_collineation fp_11323 fl_11323.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11323 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11323 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11323.

Lemma collineation_11324 : is_collineation fp_11324 fl_11324.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11324 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11324 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11324.

Lemma collineation_11325 : is_collineation fp_11325 fl_11325.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11325 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11325 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11325.

Lemma collineation_11326 : is_collineation fp_11326 fl_11326.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11326 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11326 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11326.

Lemma collineation_11327 : is_collineation fp_11327 fl_11327.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11327 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11327 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11327.

Lemma collineation_11328 : is_collineation fp_11328 fl_11328.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11328 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11328 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11328.

Lemma collineation_11329 : is_collineation fp_11329 fl_11329.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11329 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11329 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11329.

Lemma collineation_11330 : is_collineation fp_11330 fl_11330.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11330 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11330 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11330.

Lemma collineation_11331 : is_collineation fp_11331 fl_11331.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11331 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11331 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11331.

Lemma collineation_11332 : is_collineation fp_11332 fl_11332.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11332 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11332 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11332.

Lemma collineation_11333 : is_collineation fp_11333 fl_11333.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11333 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11333 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11333.

Lemma collineation_11334 : is_collineation fp_11334 fl_11334.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11334 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11334 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11334.

Lemma collineation_11335 : is_collineation fp_11335 fl_11335.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11335 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11335 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11335.

Lemma collineation_11336 : is_collineation fp_11336 fl_11336.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11336 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11336 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11336.

Lemma collineation_11337 : is_collineation fp_11337 fl_11337.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11337 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11337 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11337.

Lemma collineation_11338 : is_collineation fp_11338 fl_11338.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11338 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11338 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11338.

Lemma collineation_11339 : is_collineation fp_11339 fl_11339.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11339 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11339 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11339.

Lemma collineation_11340 : is_collineation fp_11340 fl_11340.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11340 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11340 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11340.

Lemma collineation_11341 : is_collineation fp_11341 fl_11341.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11341 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11341 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11341.

Lemma collineation_11342 : is_collineation fp_11342 fl_11342.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11342 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11342 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11342.

Lemma collineation_11343 : is_collineation fp_11343 fl_11343.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11343 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11343 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11343.

Lemma collineation_11344 : is_collineation fp_11344 fl_11344.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11344 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11344 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11344.

Lemma collineation_11345 : is_collineation fp_11345 fl_11345.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11345 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11345 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11345.

Lemma collineation_11346 : is_collineation fp_11346 fl_11346.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11346 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11346 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11346.

Lemma collineation_11347 : is_collineation fp_11347 fl_11347.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11347 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11347 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11347.

Lemma collineation_11348 : is_collineation fp_11348 fl_11348.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11348 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11348 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11348.

Lemma collineation_11349 : is_collineation fp_11349 fl_11349.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11349 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11349 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11349.

Lemma collineation_11350 : is_collineation fp_11350 fl_11350.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11350 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11350 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11350.

Lemma collineation_11351 : is_collineation fp_11351 fl_11351.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11351 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11351 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11351.

Lemma collineation_11352 : is_collineation fp_11352 fl_11352.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11352 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11352 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11352.

Lemma collineation_11353 : is_collineation fp_11353 fl_11353.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11353 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11353 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11353.

Lemma collineation_11354 : is_collineation fp_11354 fl_11354.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11354 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11354 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11354.

Lemma collineation_11355 : is_collineation fp_11355 fl_11355.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11355 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11355 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11355.

Lemma collineation_11356 : is_collineation fp_11356 fl_11356.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11356 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11356 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11356.

Lemma collineation_11357 : is_collineation fp_11357 fl_11357.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11357 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11357 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11357.

Lemma collineation_11358 : is_collineation fp_11358 fl_11358.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11358 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11358 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11358.

Lemma collineation_11359 : is_collineation fp_11359 fl_11359.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11359 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11359 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11359.

Lemma collineation_11360 : is_collineation fp_11360 fl_11360.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11360 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11360 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11360.

Lemma collineation_11361 : is_collineation fp_11361 fl_11361.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11361 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11361 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11361.

Lemma collineation_11362 : is_collineation fp_11362 fl_11362.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11362 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11362 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11362.

Lemma collineation_11363 : is_collineation fp_11363 fl_11363.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11363 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11363 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11363.

Lemma collineation_11364 : is_collineation fp_11364 fl_11364.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11364 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11364 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11364.

Lemma collineation_11365 : is_collineation fp_11365 fl_11365.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11365 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11365 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11365.

Lemma collineation_11366 : is_collineation fp_11366 fl_11366.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11366 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11366 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11366.

Lemma collineation_11367 : is_collineation fp_11367 fl_11367.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11367 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11367 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11367.

Lemma collineation_11368 : is_collineation fp_11368 fl_11368.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11368 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11368 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11368.

Lemma collineation_11369 : is_collineation fp_11369 fl_11369.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11369 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11369 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11369.

Lemma collineation_11370 : is_collineation fp_11370 fl_11370.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11370 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11370 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11370.

Lemma collineation_11371 : is_collineation fp_11371 fl_11371.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11371 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11371 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11371.

Lemma collineation_11372 : is_collineation fp_11372 fl_11372.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11372 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11372 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11372.

Lemma collineation_11373 : is_collineation fp_11373 fl_11373.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11373 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11373 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11373.

Lemma collineation_11374 : is_collineation fp_11374 fl_11374.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11374 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11374 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11374.

Lemma collineation_11375 : is_collineation fp_11375 fl_11375.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11375 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11375 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11375.

Lemma collineation_11376 : is_collineation fp_11376 fl_11376.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11376 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11376 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11376.

Lemma collineation_11377 : is_collineation fp_11377 fl_11377.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11377 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11377 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11377.

Lemma collineation_11378 : is_collineation fp_11378 fl_11378.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11378 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11378 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11378.

Lemma collineation_11379 : is_collineation fp_11379 fl_11379.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11379 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11379 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11379.

Lemma collineation_11380 : is_collineation fp_11380 fl_11380.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11380 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11380 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11380.

Lemma collineation_11381 : is_collineation fp_11381 fl_11381.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11381 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11381 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11381.

Lemma collineation_11382 : is_collineation fp_11382 fl_11382.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11382 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11382 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11382.

Lemma collineation_11383 : is_collineation fp_11383 fl_11383.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11383 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11383 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11383.

Lemma collineation_11384 : is_collineation fp_11384 fl_11384.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11384 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11384 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11384.

Lemma collineation_11385 : is_collineation fp_11385 fl_11385.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11385 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11385 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11385.

Lemma collineation_11386 : is_collineation fp_11386 fl_11386.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11386 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11386 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11386.

Lemma collineation_11387 : is_collineation fp_11387 fl_11387.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11387 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11387 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11387.

Lemma collineation_11388 : is_collineation fp_11388 fl_11388.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11388 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11388 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11388.

Lemma collineation_11389 : is_collineation fp_11389 fl_11389.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11389 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11389 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11389.

Lemma collineation_11390 : is_collineation fp_11390 fl_11390.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11390 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11390 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11390.

Lemma collineation_11391 : is_collineation fp_11391 fl_11391.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11391 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11391 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11391.

Lemma collineation_11392 : is_collineation fp_11392 fl_11392.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11392 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11392 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11392.

Lemma collineation_11393 : is_collineation fp_11393 fl_11393.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11393 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11393 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11393.

Lemma collineation_11394 : is_collineation fp_11394 fl_11394.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11394 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11394 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11394.

Lemma collineation_11395 : is_collineation fp_11395 fl_11395.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11395 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11395 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11395.

Lemma collineation_11396 : is_collineation fp_11396 fl_11396.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11396 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11396 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11396.

Lemma collineation_11397 : is_collineation fp_11397 fl_11397.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11397 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11397 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11397.

Lemma collineation_11398 : is_collineation fp_11398 fl_11398.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11398 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11398 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11398.

Lemma collineation_11399 : is_collineation fp_11399 fl_11399.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11399 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11399 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11399.

Lemma collineation_11400 : is_collineation fp_11400 fl_11400.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11400 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11400 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11400.

Lemma collineation_11401 : is_collineation fp_11401 fl_11401.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11401 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11401 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11401.

Lemma collineation_11402 : is_collineation fp_11402 fl_11402.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11402 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11402 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11402.

Lemma collineation_11403 : is_collineation fp_11403 fl_11403.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11403 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11403 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11403.

Lemma collineation_11404 : is_collineation fp_11404 fl_11404.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11404 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11404 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11404.

Lemma collineation_11405 : is_collineation fp_11405 fl_11405.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11405 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11405 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11405.

Lemma collineation_11406 : is_collineation fp_11406 fl_11406.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11406 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11406 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11406.

Lemma collineation_11407 : is_collineation fp_11407 fl_11407.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11407 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11407 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11407.

Lemma collineation_11408 : is_collineation fp_11408 fl_11408.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11408 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11408 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11408.

Lemma collineation_11409 : is_collineation fp_11409 fl_11409.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11409 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11409 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11409.

Lemma collineation_11410 : is_collineation fp_11410 fl_11410.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11410 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11410 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11410.

Lemma collineation_11411 : is_collineation fp_11411 fl_11411.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11411 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11411 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11411.

Lemma collineation_11412 : is_collineation fp_11412 fl_11412.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11412 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11412 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11412.

Lemma collineation_11413 : is_collineation fp_11413 fl_11413.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11413 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11413 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11413.

Lemma collineation_11414 : is_collineation fp_11414 fl_11414.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11414 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11414 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11414.

Lemma collineation_11415 : is_collineation fp_11415 fl_11415.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11415 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11415 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11415.

Lemma collineation_11416 : is_collineation fp_11416 fl_11416.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11416 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11416 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11416.

Lemma collineation_11417 : is_collineation fp_11417 fl_11417.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11417 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11417 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11417.

Lemma collineation_11418 : is_collineation fp_11418 fl_11418.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11418 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11418 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11418.

Lemma collineation_11419 : is_collineation fp_11419 fl_11419.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11419 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11419 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11419.

Lemma collineation_11420 : is_collineation fp_11420 fl_11420.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11420 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11420 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11420.

Lemma collineation_11421 : is_collineation fp_11421 fl_11421.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11421 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11421 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11421.

Lemma collineation_11422 : is_collineation fp_11422 fl_11422.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11422 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11422 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11422.

Lemma collineation_11423 : is_collineation fp_11423 fl_11423.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11423 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11423 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11423.

Lemma collineation_11424 : is_collineation fp_11424 fl_11424.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11424 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11424 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11424.

Lemma collineation_11425 : is_collineation fp_11425 fl_11425.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11425 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11425 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11425.

Lemma collineation_11426 : is_collineation fp_11426 fl_11426.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11426 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11426 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11426.

Lemma collineation_11427 : is_collineation fp_11427 fl_11427.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11427 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11427 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11427.

Lemma collineation_11428 : is_collineation fp_11428 fl_11428.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11428 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11428 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11428.

Lemma collineation_11429 : is_collineation fp_11429 fl_11429.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11429 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11429 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11429.

Lemma collineation_11430 : is_collineation fp_11430 fl_11430.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11430 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11430 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11430.

Lemma collineation_11431 : is_collineation fp_11431 fl_11431.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11431 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11431 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11431.

Lemma collineation_11432 : is_collineation fp_11432 fl_11432.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11432 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11432 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11432.

Lemma collineation_11433 : is_collineation fp_11433 fl_11433.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11433 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11433 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11433.

Lemma collineation_11434 : is_collineation fp_11434 fl_11434.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11434 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11434 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11434.

Lemma collineation_11435 : is_collineation fp_11435 fl_11435.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11435 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11435 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11435.

Lemma collineation_11436 : is_collineation fp_11436 fl_11436.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11436 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11436 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11436.

Lemma collineation_11437 : is_collineation fp_11437 fl_11437.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11437 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11437 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11437.

Lemma collineation_11438 : is_collineation fp_11438 fl_11438.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11438 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11438 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11438.

Lemma collineation_11439 : is_collineation fp_11439 fl_11439.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11439 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11439 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11439.

Lemma collineation_11440 : is_collineation fp_11440 fl_11440.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11440 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11440 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11440.

Lemma collineation_11441 : is_collineation fp_11441 fl_11441.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11441 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11441 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11441.

Lemma collineation_11442 : is_collineation fp_11442 fl_11442.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11442 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11442 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11442.

Lemma collineation_11443 : is_collineation fp_11443 fl_11443.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11443 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11443 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11443.

Lemma collineation_11444 : is_collineation fp_11444 fl_11444.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11444 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11444 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11444.

Lemma collineation_11445 : is_collineation fp_11445 fl_11445.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11445 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11445 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11445.

Lemma collineation_11446 : is_collineation fp_11446 fl_11446.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11446 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11446 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11446.

Lemma collineation_11447 : is_collineation fp_11447 fl_11447.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11447 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11447 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11447.

Lemma collineation_11448 : is_collineation fp_11448 fl_11448.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11448 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11448 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11448.

Lemma collineation_11449 : is_collineation fp_11449 fl_11449.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11449 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11449 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11449.

Lemma collineation_11450 : is_collineation fp_11450 fl_11450.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11450 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11450 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11450.

Lemma collineation_11451 : is_collineation fp_11451 fl_11451.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11451 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11451 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11451.

Lemma collineation_11452 : is_collineation fp_11452 fl_11452.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11452 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11452 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11452.

Lemma collineation_11453 : is_collineation fp_11453 fl_11453.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11453 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11453 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11453.

Lemma collineation_11454 : is_collineation fp_11454 fl_11454.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11454 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11454 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11454.

Lemma collineation_11455 : is_collineation fp_11455 fl_11455.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11455 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11455 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11455.

Lemma collineation_11456 : is_collineation fp_11456 fl_11456.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11456 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11456 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11456.

Lemma collineation_11457 : is_collineation fp_11457 fl_11457.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11457 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11457 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11457.

Lemma collineation_11458 : is_collineation fp_11458 fl_11458.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11458 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11458 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11458.

Lemma collineation_11459 : is_collineation fp_11459 fl_11459.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11459 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11459 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11459.

Lemma collineation_11460 : is_collineation fp_11460 fl_11460.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11460 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11460 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11460.

Lemma collineation_11461 : is_collineation fp_11461 fl_11461.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11461 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11461 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11461.

Lemma collineation_11462 : is_collineation fp_11462 fl_11462.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11462 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11462 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11462.

Lemma collineation_11463 : is_collineation fp_11463 fl_11463.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11463 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11463 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11463.

Lemma collineation_11464 : is_collineation fp_11464 fl_11464.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11464 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11464 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11464.

Lemma collineation_11465 : is_collineation fp_11465 fl_11465.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11465 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11465 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11465.

Lemma collineation_11466 : is_collineation fp_11466 fl_11466.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11466 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11466 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11466.

Lemma collineation_11467 : is_collineation fp_11467 fl_11467.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11467 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11467 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11467.

Lemma collineation_11468 : is_collineation fp_11468 fl_11468.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11468 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11468 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11468.

Lemma collineation_11469 : is_collineation fp_11469 fl_11469.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11469 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11469 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11469.

Lemma collineation_11470 : is_collineation fp_11470 fl_11470.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11470 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11470 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11470.

Lemma collineation_11471 : is_collineation fp_11471 fl_11471.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11471 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11471 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11471.

Lemma collineation_11472 : is_collineation fp_11472 fl_11472.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11472 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11472 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11472.

Lemma collineation_11473 : is_collineation fp_11473 fl_11473.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11473 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11473 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11473.

Lemma collineation_11474 : is_collineation fp_11474 fl_11474.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11474 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11474 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11474.

Lemma collineation_11475 : is_collineation fp_11475 fl_11475.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11475 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11475 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11475.

Lemma collineation_11476 : is_collineation fp_11476 fl_11476.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11476 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11476 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11476.

Lemma collineation_11477 : is_collineation fp_11477 fl_11477.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11477 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11477 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11477.

Lemma collineation_11478 : is_collineation fp_11478 fl_11478.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11478 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11478 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11478.

Lemma collineation_11479 : is_collineation fp_11479 fl_11479.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11479 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11479 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11479.

Lemma collineation_11480 : is_collineation fp_11480 fl_11480.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11480 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11480 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11480.

Lemma collineation_11481 : is_collineation fp_11481 fl_11481.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11481 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11481 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11481.

Lemma collineation_11482 : is_collineation fp_11482 fl_11482.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11482 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11482 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11482.

Lemma collineation_11483 : is_collineation fp_11483 fl_11483.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11483 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11483 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11483.

Lemma collineation_11484 : is_collineation fp_11484 fl_11484.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11484 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11484 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11484.

Lemma collineation_11485 : is_collineation fp_11485 fl_11485.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11485 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11485 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11485.

Lemma collineation_11486 : is_collineation fp_11486 fl_11486.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11486 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11486 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11486.

Lemma collineation_11487 : is_collineation fp_11487 fl_11487.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11487 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11487 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11487.

Lemma collineation_11488 : is_collineation fp_11488 fl_11488.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11488 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11488 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11488.

Lemma collineation_11489 : is_collineation fp_11489 fl_11489.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11489 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11489 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11489.

Lemma collineation_11490 : is_collineation fp_11490 fl_11490.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11490 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11490 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11490.

Lemma collineation_11491 : is_collineation fp_11491 fl_11491.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11491 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11491 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11491.

Lemma collineation_11492 : is_collineation fp_11492 fl_11492.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11492 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11492 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11492.

Lemma collineation_11493 : is_collineation fp_11493 fl_11493.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11493 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11493 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11493.

Lemma collineation_11494 : is_collineation fp_11494 fl_11494.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11494 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11494 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11494.

Lemma collineation_11495 : is_collineation fp_11495 fl_11495.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11495 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11495 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11495.

Lemma collineation_11496 : is_collineation fp_11496 fl_11496.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11496 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11496 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11496.

Lemma collineation_11497 : is_collineation fp_11497 fl_11497.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11497 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11497 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11497.

Lemma collineation_11498 : is_collineation fp_11498 fl_11498.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11498 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11498 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11498.

Lemma collineation_11499 : is_collineation fp_11499 fl_11499.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11499 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11499 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11499.

Lemma collineation_11500 : is_collineation fp_11500 fl_11500.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11500 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11500 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11500.

Lemma collineation_11501 : is_collineation fp_11501 fl_11501.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11501 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11501 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11501.

Lemma collineation_11502 : is_collineation fp_11502 fl_11502.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11502 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11502 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11502.

Lemma collineation_11503 : is_collineation fp_11503 fl_11503.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11503 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11503 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11503.

Lemma collineation_11504 : is_collineation fp_11504 fl_11504.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11504 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11504 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11504.

Lemma collineation_11505 : is_collineation fp_11505 fl_11505.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11505 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11505 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11505.

Lemma collineation_11506 : is_collineation fp_11506 fl_11506.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11506 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11506 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11506.

Lemma collineation_11507 : is_collineation fp_11507 fl_11507.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11507 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11507 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11507.

Lemma collineation_11508 : is_collineation fp_11508 fl_11508.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11508 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11508 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11508.

Lemma collineation_11509 : is_collineation fp_11509 fl_11509.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11509 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11509 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11509.

Lemma collineation_11510 : is_collineation fp_11510 fl_11510.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11510 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11510 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11510.

Lemma collineation_11511 : is_collineation fp_11511 fl_11511.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11511 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11511 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11511.

Lemma collineation_11512 : is_collineation fp_11512 fl_11512.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11512 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11512 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11512.

Lemma collineation_11513 : is_collineation fp_11513 fl_11513.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11513 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11513 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11513.

Lemma collineation_11514 : is_collineation fp_11514 fl_11514.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11514 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11514 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11514.

Lemma collineation_11515 : is_collineation fp_11515 fl_11515.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11515 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11515 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11515.

Lemma collineation_11516 : is_collineation fp_11516 fl_11516.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11516 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11516 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11516.

Lemma collineation_11517 : is_collineation fp_11517 fl_11517.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11517 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11517 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11517.

Lemma collineation_11518 : is_collineation fp_11518 fl_11518.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11518 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11518 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11518.

Lemma collineation_11519 : is_collineation fp_11519 fl_11519.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11519 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11519 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11519.

Lemma collineation_11520 : is_collineation fp_11520 fl_11520.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11520 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11520 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11520.

Lemma collineation_11521 : is_collineation fp_11521 fl_11521.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11521 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11521 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11521.

Lemma collineation_11522 : is_collineation fp_11522 fl_11522.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11522 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11522 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11522.

Lemma collineation_11523 : is_collineation fp_11523 fl_11523.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11523 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11523 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11523.

Lemma collineation_11524 : is_collineation fp_11524 fl_11524.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11524 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11524 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11524.

Lemma collineation_11525 : is_collineation fp_11525 fl_11525.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11525 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11525 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11525.

Lemma collineation_11526 : is_collineation fp_11526 fl_11526.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11526 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11526 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11526.

Lemma collineation_11527 : is_collineation fp_11527 fl_11527.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11527 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11527 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11527.

Lemma collineation_11528 : is_collineation fp_11528 fl_11528.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11528 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11528 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11528.

Lemma collineation_11529 : is_collineation fp_11529 fl_11529.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11529 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11529 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11529.

Lemma collineation_11530 : is_collineation fp_11530 fl_11530.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11530 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11530 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11530.

Lemma collineation_11531 : is_collineation fp_11531 fl_11531.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11531 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11531 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11531.

Lemma collineation_11532 : is_collineation fp_11532 fl_11532.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11532 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11532 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11532.

Lemma collineation_11533 : is_collineation fp_11533 fl_11533.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11533 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11533 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11533.

Lemma collineation_11534 : is_collineation fp_11534 fl_11534.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11534 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11534 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11534.

Lemma collineation_11535 : is_collineation fp_11535 fl_11535.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11535 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11535 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11535.

Lemma collineation_11536 : is_collineation fp_11536 fl_11536.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11536 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11536 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11536.

Lemma collineation_11537 : is_collineation fp_11537 fl_11537.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11537 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11537 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11537.

Lemma collineation_11538 : is_collineation fp_11538 fl_11538.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11538 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11538 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11538.

Lemma collineation_11539 : is_collineation fp_11539 fl_11539.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11539 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11539 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11539.

Lemma collineation_11540 : is_collineation fp_11540 fl_11540.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11540 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11540 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11540.

Lemma collineation_11541 : is_collineation fp_11541 fl_11541.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11541 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11541 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11541.

Lemma collineation_11542 : is_collineation fp_11542 fl_11542.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11542 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11542 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11542.

Lemma collineation_11543 : is_collineation fp_11543 fl_11543.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11543 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11543 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11543.

Lemma collineation_11544 : is_collineation fp_11544 fl_11544.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11544 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11544 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11544.

Lemma collineation_11545 : is_collineation fp_11545 fl_11545.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11545 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11545 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11545.

Lemma collineation_11546 : is_collineation fp_11546 fl_11546.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11546 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11546 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11546.

Lemma collineation_11547 : is_collineation fp_11547 fl_11547.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11547 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11547 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11547.

Lemma collineation_11548 : is_collineation fp_11548 fl_11548.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11548 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11548 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11548.

Lemma collineation_11549 : is_collineation fp_11549 fl_11549.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11549 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11549 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11549.

Lemma collineation_11550 : is_collineation fp_11550 fl_11550.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11550 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11550 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11550.

Lemma collineation_11551 : is_collineation fp_11551 fl_11551.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11551 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11551 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11551.

Lemma collineation_11552 : is_collineation fp_11552 fl_11552.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11552 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11552 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11552.

Lemma collineation_11553 : is_collineation fp_11553 fl_11553.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11553 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11553 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11553.

Lemma collineation_11554 : is_collineation fp_11554 fl_11554.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11554 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11554 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11554.

Lemma collineation_11555 : is_collineation fp_11555 fl_11555.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11555 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11555 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11555.

Lemma collineation_11556 : is_collineation fp_11556 fl_11556.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11556 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11556 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11556.

Lemma collineation_11557 : is_collineation fp_11557 fl_11557.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11557 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11557 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11557.

Lemma collineation_11558 : is_collineation fp_11558 fl_11558.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11558 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11558 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11558.

Lemma collineation_11559 : is_collineation fp_11559 fl_11559.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11559 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11559 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11559.

Lemma collineation_11560 : is_collineation fp_11560 fl_11560.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11560 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11560 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11560.

Lemma collineation_11561 : is_collineation fp_11561 fl_11561.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11561 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11561 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11561.

Lemma collineation_11562 : is_collineation fp_11562 fl_11562.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11562 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11562 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11562.

Lemma collineation_11563 : is_collineation fp_11563 fl_11563.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11563 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11563 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11563.

Lemma collineation_11564 : is_collineation fp_11564 fl_11564.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11564 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11564 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11564.

Lemma collineation_11565 : is_collineation fp_11565 fl_11565.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11565 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11565 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11565.

Lemma collineation_11566 : is_collineation fp_11566 fl_11566.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11566 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11566 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11566.

Lemma collineation_11567 : is_collineation fp_11567 fl_11567.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11567 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11567 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11567.

Lemma collineation_11568 : is_collineation fp_11568 fl_11568.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11568 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11568 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11568.

Lemma collineation_11569 : is_collineation fp_11569 fl_11569.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11569 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11569 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11569.

Lemma collineation_11570 : is_collineation fp_11570 fl_11570.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11570 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11570 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11570.

Lemma collineation_11571 : is_collineation fp_11571 fl_11571.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11571 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11571 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11571.

Lemma collineation_11572 : is_collineation fp_11572 fl_11572.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11572 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11572 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11572.

Lemma collineation_11573 : is_collineation fp_11573 fl_11573.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11573 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11573 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11573.

Lemma collineation_11574 : is_collineation fp_11574 fl_11574.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11574 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11574 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11574.

Lemma collineation_11575 : is_collineation fp_11575 fl_11575.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11575 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11575 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11575.

Lemma collineation_11576 : is_collineation fp_11576 fl_11576.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11576 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11576 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11576.

Lemma collineation_11577 : is_collineation fp_11577 fl_11577.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11577 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11577 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11577.

Lemma collineation_11578 : is_collineation fp_11578 fl_11578.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11578 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11578 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11578.

Lemma collineation_11579 : is_collineation fp_11579 fl_11579.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11579 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11579 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11579.

Lemma collineation_11580 : is_collineation fp_11580 fl_11580.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11580 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11580 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11580.

Lemma collineation_11581 : is_collineation fp_11581 fl_11581.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11581 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11581 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11581.

Lemma collineation_11582 : is_collineation fp_11582 fl_11582.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11582 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11582 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11582.

Lemma collineation_11583 : is_collineation fp_11583 fl_11583.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11583 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11583 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11583.

Lemma collineation_11584 : is_collineation fp_11584 fl_11584.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11584 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11584 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11584.

Lemma collineation_11585 : is_collineation fp_11585 fl_11585.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11585 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11585 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11585.

Lemma collineation_11586 : is_collineation fp_11586 fl_11586.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11586 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11586 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11586.

Lemma collineation_11587 : is_collineation fp_11587 fl_11587.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11587 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11587 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11587.

Lemma collineation_11588 : is_collineation fp_11588 fl_11588.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11588 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11588 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11588.

Lemma collineation_11589 : is_collineation fp_11589 fl_11589.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11589 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11589 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11589.

Lemma collineation_11590 : is_collineation fp_11590 fl_11590.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11590 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11590 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11590.

Lemma collineation_11591 : is_collineation fp_11591 fl_11591.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11591 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11591 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11591.

Lemma collineation_11592 : is_collineation fp_11592 fl_11592.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11592 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11592 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11592.

Lemma collineation_11593 : is_collineation fp_11593 fl_11593.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11593 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11593 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11593.

Lemma collineation_11594 : is_collineation fp_11594 fl_11594.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11594 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11594 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11594.

Lemma collineation_11595 : is_collineation fp_11595 fl_11595.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11595 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11595 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11595.

Lemma collineation_11596 : is_collineation fp_11596 fl_11596.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11596 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11596 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11596.

Lemma collineation_11597 : is_collineation fp_11597 fl_11597.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11597 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11597 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11597.

Lemma collineation_11598 : is_collineation fp_11598 fl_11598.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11598 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11598 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11598.

Lemma collineation_11599 : is_collineation fp_11599 fl_11599.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11599 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11599 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11599.

Lemma collineation_11600 : is_collineation fp_11600 fl_11600.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11600 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11600 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11600.

Lemma collineation_11601 : is_collineation fp_11601 fl_11601.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11601 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11601 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11601.

Lemma collineation_11602 : is_collineation fp_11602 fl_11602.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11602 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11602 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11602.

Lemma collineation_11603 : is_collineation fp_11603 fl_11603.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11603 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11603 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11603.

Lemma collineation_11604 : is_collineation fp_11604 fl_11604.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11604 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11604 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11604.

Lemma collineation_11605 : is_collineation fp_11605 fl_11605.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11605 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11605 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11605.

Lemma collineation_11606 : is_collineation fp_11606 fl_11606.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11606 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11606 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11606.

Lemma collineation_11607 : is_collineation fp_11607 fl_11607.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11607 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11607 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11607.

Lemma collineation_11608 : is_collineation fp_11608 fl_11608.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11608 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11608 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11608.

Lemma collineation_11609 : is_collineation fp_11609 fl_11609.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11609 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11609 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11609.

Lemma collineation_11610 : is_collineation fp_11610 fl_11610.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11610 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11610 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11610.

Lemma collineation_11611 : is_collineation fp_11611 fl_11611.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11611 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11611 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11611.

Lemma collineation_11612 : is_collineation fp_11612 fl_11612.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11612 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11612 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11612.

Lemma collineation_11613 : is_collineation fp_11613 fl_11613.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11613 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11613 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11613.

Lemma collineation_11614 : is_collineation fp_11614 fl_11614.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11614 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11614 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11614.

Lemma collineation_11615 : is_collineation fp_11615 fl_11615.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11615 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11615 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11615.

Lemma collineation_11616 : is_collineation fp_11616 fl_11616.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11616 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11616 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11616.

Lemma collineation_11617 : is_collineation fp_11617 fl_11617.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11617 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11617 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11617.

Lemma collineation_11618 : is_collineation fp_11618 fl_11618.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11618 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11618 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11618.

Lemma collineation_11619 : is_collineation fp_11619 fl_11619.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11619 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11619 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11619.

Lemma collineation_11620 : is_collineation fp_11620 fl_11620.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11620 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11620 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11620.

Lemma collineation_11621 : is_collineation fp_11621 fl_11621.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11621 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11621 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11621.

Lemma collineation_11622 : is_collineation fp_11622 fl_11622.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11622 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11622 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11622.

Lemma collineation_11623 : is_collineation fp_11623 fl_11623.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11623 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11623 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11623.

Lemma collineation_11624 : is_collineation fp_11624 fl_11624.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11624 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11624 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11624.

Lemma collineation_11625 : is_collineation fp_11625 fl_11625.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11625 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11625 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11625.

Lemma collineation_11626 : is_collineation fp_11626 fl_11626.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11626 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11626 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11626.

Lemma collineation_11627 : is_collineation fp_11627 fl_11627.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11627 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11627 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11627.

Lemma collineation_11628 : is_collineation fp_11628 fl_11628.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11628 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11628 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11628.

Lemma collineation_11629 : is_collineation fp_11629 fl_11629.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11629 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11629 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11629.

Lemma collineation_11630 : is_collineation fp_11630 fl_11630.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11630 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11630 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11630.

Lemma collineation_11631 : is_collineation fp_11631 fl_11631.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11631 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11631 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11631.

Lemma collineation_11632 : is_collineation fp_11632 fl_11632.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11632 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11632 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11632.

Lemma collineation_11633 : is_collineation fp_11633 fl_11633.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11633 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11633 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11633.

Lemma collineation_11634 : is_collineation fp_11634 fl_11634.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11634 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11634 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11634.

Lemma collineation_11635 : is_collineation fp_11635 fl_11635.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11635 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11635 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11635.

Lemma collineation_11636 : is_collineation fp_11636 fl_11636.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11636 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11636 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11636.

Lemma collineation_11637 : is_collineation fp_11637 fl_11637.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11637 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11637 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11637.

Lemma collineation_11638 : is_collineation fp_11638 fl_11638.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11638 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11638 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11638.

Lemma collineation_11639 : is_collineation fp_11639 fl_11639.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11639 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11639 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11639.

Lemma collineation_11640 : is_collineation fp_11640 fl_11640.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11640 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11640 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11640.

Lemma collineation_11641 : is_collineation fp_11641 fl_11641.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11641 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11641 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11641.

Lemma collineation_11642 : is_collineation fp_11642 fl_11642.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11642 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11642 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11642.

Lemma collineation_11643 : is_collineation fp_11643 fl_11643.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11643 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11643 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11643.

Lemma collineation_11644 : is_collineation fp_11644 fl_11644.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11644 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11644 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11644.

Lemma collineation_11645 : is_collineation fp_11645 fl_11645.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11645 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11645 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11645.

Lemma collineation_11646 : is_collineation fp_11646 fl_11646.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11646 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11646 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11646.

Lemma collineation_11647 : is_collineation fp_11647 fl_11647.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11647 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11647 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11647.

Lemma collineation_11648 : is_collineation fp_11648 fl_11648.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11648 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11648 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11648.

Lemma collineation_11649 : is_collineation fp_11649 fl_11649.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11649 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11649 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11649.

Lemma collineation_11650 : is_collineation fp_11650 fl_11650.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11650 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11650 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11650.

Lemma collineation_11651 : is_collineation fp_11651 fl_11651.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11651 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11651 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11651.

Lemma collineation_11652 : is_collineation fp_11652 fl_11652.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11652 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11652 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11652.

Lemma collineation_11653 : is_collineation fp_11653 fl_11653.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11653 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11653 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11653.

Lemma collineation_11654 : is_collineation fp_11654 fl_11654.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11654 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11654 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11654.

Lemma collineation_11655 : is_collineation fp_11655 fl_11655.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11655 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11655 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11655.

Lemma collineation_11656 : is_collineation fp_11656 fl_11656.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11656 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11656 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11656.

Lemma collineation_11657 : is_collineation fp_11657 fl_11657.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11657 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11657 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11657.

Lemma collineation_11658 : is_collineation fp_11658 fl_11658.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11658 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11658 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11658.

Lemma collineation_11659 : is_collineation fp_11659 fl_11659.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11659 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11659 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11659.

Lemma collineation_11660 : is_collineation fp_11660 fl_11660.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11660 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11660 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11660.

Lemma collineation_11661 : is_collineation fp_11661 fl_11661.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11661 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11661 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11661.

Lemma collineation_11662 : is_collineation fp_11662 fl_11662.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11662 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11662 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11662.

Lemma collineation_11663 : is_collineation fp_11663 fl_11663.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11663 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11663 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11663.

Lemma collineation_11664 : is_collineation fp_11664 fl_11664.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11664 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11664 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11664.

Lemma collineation_11665 : is_collineation fp_11665 fl_11665.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11665 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11665 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11665.

Lemma collineation_11666 : is_collineation fp_11666 fl_11666.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11666 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11666 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11666.

Lemma collineation_11667 : is_collineation fp_11667 fl_11667.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11667 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11667 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11667.

Lemma collineation_11668 : is_collineation fp_11668 fl_11668.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11668 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11668 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11668.

Lemma collineation_11669 : is_collineation fp_11669 fl_11669.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11669 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11669 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11669.

Lemma collineation_11670 : is_collineation fp_11670 fl_11670.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11670 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11670 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11670.

Lemma collineation_11671 : is_collineation fp_11671 fl_11671.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11671 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11671 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11671.

Lemma collineation_11672 : is_collineation fp_11672 fl_11672.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11672 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11672 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11672.

Lemma collineation_11673 : is_collineation fp_11673 fl_11673.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11673 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11673 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11673.

Lemma collineation_11674 : is_collineation fp_11674 fl_11674.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11674 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11674 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11674.

Lemma collineation_11675 : is_collineation fp_11675 fl_11675.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11675 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11675 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11675.

Lemma collineation_11676 : is_collineation fp_11676 fl_11676.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11676 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11676 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11676.

Lemma collineation_11677 : is_collineation fp_11677 fl_11677.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11677 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11677 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11677.

Lemma collineation_11678 : is_collineation fp_11678 fl_11678.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11678 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11678 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11678.

Lemma collineation_11679 : is_collineation fp_11679 fl_11679.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11679 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11679 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11679.

Lemma collineation_11680 : is_collineation fp_11680 fl_11680.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11680 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11680 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11680.

Lemma collineation_11681 : is_collineation fp_11681 fl_11681.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11681 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11681 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11681.

Lemma collineation_11682 : is_collineation fp_11682 fl_11682.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11682 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11682 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11682.

Lemma collineation_11683 : is_collineation fp_11683 fl_11683.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11683 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11683 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11683.

Lemma collineation_11684 : is_collineation fp_11684 fl_11684.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11684 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11684 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11684.

Lemma collineation_11685 : is_collineation fp_11685 fl_11685.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11685 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11685 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11685.

Lemma collineation_11686 : is_collineation fp_11686 fl_11686.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11686 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11686 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11686.

Lemma collineation_11687 : is_collineation fp_11687 fl_11687.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11687 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11687 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11687.

Lemma collineation_11688 : is_collineation fp_11688 fl_11688.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11688 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11688 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11688.

Lemma collineation_11689 : is_collineation fp_11689 fl_11689.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11689 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11689 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11689.

Lemma collineation_11690 : is_collineation fp_11690 fl_11690.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11690 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11690 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11690.

Lemma collineation_11691 : is_collineation fp_11691 fl_11691.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11691 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11691 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11691.

Lemma collineation_11692 : is_collineation fp_11692 fl_11692.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11692 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11692 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11692.

Lemma collineation_11693 : is_collineation fp_11693 fl_11693.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11693 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11693 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11693.

Lemma collineation_11694 : is_collineation fp_11694 fl_11694.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11694 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11694 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11694.

Lemma collineation_11695 : is_collineation fp_11695 fl_11695.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11695 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11695 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11695.

Lemma collineation_11696 : is_collineation fp_11696 fl_11696.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11696 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11696 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11696.

Lemma collineation_11697 : is_collineation fp_11697 fl_11697.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11697 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11697 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11697.

Lemma collineation_11698 : is_collineation fp_11698 fl_11698.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11698 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11698 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11698.

Lemma collineation_11699 : is_collineation fp_11699 fl_11699.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11699 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11699 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11699.

Lemma collineation_11700 : is_collineation fp_11700 fl_11700.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11700 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11700 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11700.

Lemma collineation_11701 : is_collineation fp_11701 fl_11701.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11701 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11701 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11701.

Lemma collineation_11702 : is_collineation fp_11702 fl_11702.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11702 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11702 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11702.

Lemma collineation_11703 : is_collineation fp_11703 fl_11703.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11703 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11703 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11703.

Lemma collineation_11704 : is_collineation fp_11704 fl_11704.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11704 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11704 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11704.

Lemma collineation_11705 : is_collineation fp_11705 fl_11705.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11705 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11705 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11705.

Lemma collineation_11706 : is_collineation fp_11706 fl_11706.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11706 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11706 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11706.

Lemma collineation_11707 : is_collineation fp_11707 fl_11707.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11707 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11707 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11707.

Lemma collineation_11708 : is_collineation fp_11708 fl_11708.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11708 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11708 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11708.

Lemma collineation_11709 : is_collineation fp_11709 fl_11709.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11709 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11709 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11709.

Lemma collineation_11710 : is_collineation fp_11710 fl_11710.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11710 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11710 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11710.

Lemma collineation_11711 : is_collineation fp_11711 fl_11711.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11711 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11711 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11711.

Lemma collineation_11712 : is_collineation fp_11712 fl_11712.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11712 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11712 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11712.

Lemma collineation_11713 : is_collineation fp_11713 fl_11713.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11713 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11713 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11713.

Lemma collineation_11714 : is_collineation fp_11714 fl_11714.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11714 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11714 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11714.

Lemma collineation_11715 : is_collineation fp_11715 fl_11715.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11715 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11715 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11715.

Lemma collineation_11716 : is_collineation fp_11716 fl_11716.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11716 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11716 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11716.

Lemma collineation_11717 : is_collineation fp_11717 fl_11717.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11717 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11717 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11717.

Lemma collineation_11718 : is_collineation fp_11718 fl_11718.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11718 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11718 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11718.

Lemma collineation_11719 : is_collineation fp_11719 fl_11719.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11719 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11719 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11719.

Lemma collineation_11720 : is_collineation fp_11720 fl_11720.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11720 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11720 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11720.

Lemma collineation_11721 : is_collineation fp_11721 fl_11721.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11721 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11721 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11721.

Lemma collineation_11722 : is_collineation fp_11722 fl_11722.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11722 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11722 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11722.

Lemma collineation_11723 : is_collineation fp_11723 fl_11723.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11723 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11723 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11723.

Lemma collineation_11724 : is_collineation fp_11724 fl_11724.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11724 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11724 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11724.

Lemma collineation_11725 : is_collineation fp_11725 fl_11725.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11725 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11725 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11725.

Lemma collineation_11726 : is_collineation fp_11726 fl_11726.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11726 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11726 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11726.

Lemma collineation_11727 : is_collineation fp_11727 fl_11727.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11727 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11727 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11727.

Lemma collineation_11728 : is_collineation fp_11728 fl_11728.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11728 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11728 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11728.

Lemma collineation_11729 : is_collineation fp_11729 fl_11729.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11729 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11729 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11729.

Lemma collineation_11730 : is_collineation fp_11730 fl_11730.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11730 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11730 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11730.

Lemma collineation_11731 : is_collineation fp_11731 fl_11731.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11731 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11731 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11731.

Lemma collineation_11732 : is_collineation fp_11732 fl_11732.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11732 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11732 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11732.

Lemma collineation_11733 : is_collineation fp_11733 fl_11733.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11733 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11733 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11733.

Lemma collineation_11734 : is_collineation fp_11734 fl_11734.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11734 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11734 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11734.

Lemma collineation_11735 : is_collineation fp_11735 fl_11735.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11735 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11735 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11735.

Lemma collineation_11736 : is_collineation fp_11736 fl_11736.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11736 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11736 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11736.

Lemma collineation_11737 : is_collineation fp_11737 fl_11737.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11737 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11737 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11737.

Lemma collineation_11738 : is_collineation fp_11738 fl_11738.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11738 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11738 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11738.

Lemma collineation_11739 : is_collineation fp_11739 fl_11739.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11739 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11739 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11739.

Lemma collineation_11740 : is_collineation fp_11740 fl_11740.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11740 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11740 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11740.

Lemma collineation_11741 : is_collineation fp_11741 fl_11741.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11741 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11741 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11741.

Lemma collineation_11742 : is_collineation fp_11742 fl_11742.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11742 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11742 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11742.

Lemma collineation_11743 : is_collineation fp_11743 fl_11743.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11743 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11743 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11743.

Lemma collineation_11744 : is_collineation fp_11744 fl_11744.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11744 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11744 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11744.

Lemma collineation_11745 : is_collineation fp_11745 fl_11745.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11745 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11745 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11745.

Lemma collineation_11746 : is_collineation fp_11746 fl_11746.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11746 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11746 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11746.

Lemma collineation_11747 : is_collineation fp_11747 fl_11747.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11747 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11747 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11747.

Lemma collineation_11748 : is_collineation fp_11748 fl_11748.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11748 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11748 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11748.

Lemma collineation_11749 : is_collineation fp_11749 fl_11749.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11749 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11749 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11749.

Lemma collineation_11750 : is_collineation fp_11750 fl_11750.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11750 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11750 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11750.

Lemma collineation_11751 : is_collineation fp_11751 fl_11751.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11751 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11751 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11751.

Lemma collineation_11752 : is_collineation fp_11752 fl_11752.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11752 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11752 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11752.

Lemma collineation_11753 : is_collineation fp_11753 fl_11753.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11753 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11753 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11753.

Lemma collineation_11754 : is_collineation fp_11754 fl_11754.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11754 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11754 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11754.

Lemma collineation_11755 : is_collineation fp_11755 fl_11755.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11755 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11755 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11755.

Lemma collineation_11756 : is_collineation fp_11756 fl_11756.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11756 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11756 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11756.

Lemma collineation_11757 : is_collineation fp_11757 fl_11757.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11757 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11757 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11757.

Lemma collineation_11758 : is_collineation fp_11758 fl_11758.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11758 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11758 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11758.

Lemma collineation_11759 : is_collineation fp_11759 fl_11759.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11759 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11759 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11759.

Lemma collineation_11760 : is_collineation fp_11760 fl_11760.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11760 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11760 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11760.

Lemma collineation_11761 : is_collineation fp_11761 fl_11761.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11761 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11761 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11761.

Lemma collineation_11762 : is_collineation fp_11762 fl_11762.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11762 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11762 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11762.

Lemma collineation_11763 : is_collineation fp_11763 fl_11763.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11763 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11763 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11763.

Lemma collineation_11764 : is_collineation fp_11764 fl_11764.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11764 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11764 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11764.

Lemma collineation_11765 : is_collineation fp_11765 fl_11765.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11765 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11765 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11765.

Lemma collineation_11766 : is_collineation fp_11766 fl_11766.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11766 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11766 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11766.

Lemma collineation_11767 : is_collineation fp_11767 fl_11767.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11767 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11767 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11767.

Lemma collineation_11768 : is_collineation fp_11768 fl_11768.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11768 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11768 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11768.

Lemma collineation_11769 : is_collineation fp_11769 fl_11769.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11769 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11769 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11769.

Lemma collineation_11770 : is_collineation fp_11770 fl_11770.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11770 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11770 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11770.

Lemma collineation_11771 : is_collineation fp_11771 fl_11771.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11771 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11771 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11771.

Lemma collineation_11772 : is_collineation fp_11772 fl_11772.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11772 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11772 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11772.

Lemma collineation_11773 : is_collineation fp_11773 fl_11773.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11773 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11773 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11773.

Lemma collineation_11774 : is_collineation fp_11774 fl_11774.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11774 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11774 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11774.

Lemma collineation_11775 : is_collineation fp_11775 fl_11775.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11775 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11775 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11775.

Lemma collineation_11776 : is_collineation fp_11776 fl_11776.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11776 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11776 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11776.

Lemma collineation_11777 : is_collineation fp_11777 fl_11777.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11777 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11777 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11777.

Lemma collineation_11778 : is_collineation fp_11778 fl_11778.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11778 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11778 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11778.

Lemma collineation_11779 : is_collineation fp_11779 fl_11779.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11779 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11779 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11779.

Lemma collineation_11780 : is_collineation fp_11780 fl_11780.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11780 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11780 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11780.

Lemma collineation_11781 : is_collineation fp_11781 fl_11781.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11781 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11781 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11781.

Lemma collineation_11782 : is_collineation fp_11782 fl_11782.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11782 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11782 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11782.

Lemma collineation_11783 : is_collineation fp_11783 fl_11783.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11783 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11783 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11783.

Lemma collineation_11784 : is_collineation fp_11784 fl_11784.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11784 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11784 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11784.

Lemma collineation_11785 : is_collineation fp_11785 fl_11785.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11785 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11785 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11785.

Lemma collineation_11786 : is_collineation fp_11786 fl_11786.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11786 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11786 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11786.

Lemma collineation_11787 : is_collineation fp_11787 fl_11787.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11787 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11787 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11787.

Lemma collineation_11788 : is_collineation fp_11788 fl_11788.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11788 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11788 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11788.

Lemma collineation_11789 : is_collineation fp_11789 fl_11789.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11789 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11789 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11789.

Lemma collineation_11790 : is_collineation fp_11790 fl_11790.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11790 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11790 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11790.

Lemma collineation_11791 : is_collineation fp_11791 fl_11791.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11791 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11791 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11791.

Lemma collineation_11792 : is_collineation fp_11792 fl_11792.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11792 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11792 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11792.

Lemma collineation_11793 : is_collineation fp_11793 fl_11793.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11793 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11793 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11793.

Lemma collineation_11794 : is_collineation fp_11794 fl_11794.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11794 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11794 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11794.

Lemma collineation_11795 : is_collineation fp_11795 fl_11795.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11795 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11795 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11795.

Lemma collineation_11796 : is_collineation fp_11796 fl_11796.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11796 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11796 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11796.

Lemma collineation_11797 : is_collineation fp_11797 fl_11797.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11797 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11797 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11797.

Lemma collineation_11798 : is_collineation fp_11798 fl_11798.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11798 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11798 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11798.

Lemma collineation_11799 : is_collineation fp_11799 fl_11799.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11799 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11799 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11799.

Lemma collineation_11800 : is_collineation fp_11800 fl_11800.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11800 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11800 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11800.

Lemma collineation_11801 : is_collineation fp_11801 fl_11801.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11801 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11801 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11801.

Lemma collineation_11802 : is_collineation fp_11802 fl_11802.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11802 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11802 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11802.

Lemma collineation_11803 : is_collineation fp_11803 fl_11803.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11803 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11803 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11803.

Lemma collineation_11804 : is_collineation fp_11804 fl_11804.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11804 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11804 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11804.

Lemma collineation_11805 : is_collineation fp_11805 fl_11805.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11805 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11805 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11805.

Lemma collineation_11806 : is_collineation fp_11806 fl_11806.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11806 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11806 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11806.

Lemma collineation_11807 : is_collineation fp_11807 fl_11807.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11807 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11807 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11807.

Lemma collineation_11808 : is_collineation fp_11808 fl_11808.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11808 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11808 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11808.

Lemma collineation_11809 : is_collineation fp_11809 fl_11809.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11809 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11809 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11809.

Lemma collineation_11810 : is_collineation fp_11810 fl_11810.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11810 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11810 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11810.

Lemma collineation_11811 : is_collineation fp_11811 fl_11811.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11811 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11811 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11811.

Lemma collineation_11812 : is_collineation fp_11812 fl_11812.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11812 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11812 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11812.

Lemma collineation_11813 : is_collineation fp_11813 fl_11813.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11813 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11813 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11813.

Lemma collineation_11814 : is_collineation fp_11814 fl_11814.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11814 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11814 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11814.

Lemma collineation_11815 : is_collineation fp_11815 fl_11815.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11815 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11815 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11815.

Lemma collineation_11816 : is_collineation fp_11816 fl_11816.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11816 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11816 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11816.

Lemma collineation_11817 : is_collineation fp_11817 fl_11817.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11817 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11817 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11817.

Lemma collineation_11818 : is_collineation fp_11818 fl_11818.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11818 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11818 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11818.

Lemma collineation_11819 : is_collineation fp_11819 fl_11819.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11819 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11819 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11819.

Lemma collineation_11820 : is_collineation fp_11820 fl_11820.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11820 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11820 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11820.

Lemma collineation_11821 : is_collineation fp_11821 fl_11821.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11821 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11821 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11821.

Lemma collineation_11822 : is_collineation fp_11822 fl_11822.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11822 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11822 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11822.

Lemma collineation_11823 : is_collineation fp_11823 fl_11823.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11823 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11823 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11823.

Lemma collineation_11824 : is_collineation fp_11824 fl_11824.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11824 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11824 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11824.

Lemma collineation_11825 : is_collineation fp_11825 fl_11825.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11825 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11825 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11825.

Lemma collineation_11826 : is_collineation fp_11826 fl_11826.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11826 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11826 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11826.

Lemma collineation_11827 : is_collineation fp_11827 fl_11827.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11827 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11827 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11827.

Lemma collineation_11828 : is_collineation fp_11828 fl_11828.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11828 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11828 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11828.

Lemma collineation_11829 : is_collineation fp_11829 fl_11829.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11829 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11829 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11829.

Lemma collineation_11830 : is_collineation fp_11830 fl_11830.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11830 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11830 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11830.

Lemma collineation_11831 : is_collineation fp_11831 fl_11831.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11831 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11831 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11831.

Lemma collineation_11832 : is_collineation fp_11832 fl_11832.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11832 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11832 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11832.

Lemma collineation_11833 : is_collineation fp_11833 fl_11833.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11833 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11833 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11833.

Lemma collineation_11834 : is_collineation fp_11834 fl_11834.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11834 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11834 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11834.

Lemma collineation_11835 : is_collineation fp_11835 fl_11835.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11835 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11835 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11835.

Lemma collineation_11836 : is_collineation fp_11836 fl_11836.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11836 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11836 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11836.

Lemma collineation_11837 : is_collineation fp_11837 fl_11837.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11837 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11837 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11837.

Lemma collineation_11838 : is_collineation fp_11838 fl_11838.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11838 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11838 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11838.

Lemma collineation_11839 : is_collineation fp_11839 fl_11839.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11839 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11839 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11839.

Lemma collineation_11840 : is_collineation fp_11840 fl_11840.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11840 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11840 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11840.

Lemma collineation_11841 : is_collineation fp_11841 fl_11841.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11841 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11841 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11841.

Lemma collineation_11842 : is_collineation fp_11842 fl_11842.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11842 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11842 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11842.

Lemma collineation_11843 : is_collineation fp_11843 fl_11843.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11843 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11843 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11843.

Lemma collineation_11844 : is_collineation fp_11844 fl_11844.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11844 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11844 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11844.

Lemma collineation_11845 : is_collineation fp_11845 fl_11845.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11845 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11845 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11845.

Lemma collineation_11846 : is_collineation fp_11846 fl_11846.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11846 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11846 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11846.

Lemma collineation_11847 : is_collineation fp_11847 fl_11847.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11847 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11847 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11847.

Lemma collineation_11848 : is_collineation fp_11848 fl_11848.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11848 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11848 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11848.

Lemma collineation_11849 : is_collineation fp_11849 fl_11849.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11849 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11849 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11849.

Lemma collineation_11850 : is_collineation fp_11850 fl_11850.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11850 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11850 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11850.

Lemma collineation_11851 : is_collineation fp_11851 fl_11851.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11851 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11851 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11851.

Lemma collineation_11852 : is_collineation fp_11852 fl_11852.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11852 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11852 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11852.

Lemma collineation_11853 : is_collineation fp_11853 fl_11853.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11853 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11853 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11853.

Lemma collineation_11854 : is_collineation fp_11854 fl_11854.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11854 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11854 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11854.

Lemma collineation_11855 : is_collineation fp_11855 fl_11855.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11855 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11855 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11855.

Lemma collineation_11856 : is_collineation fp_11856 fl_11856.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11856 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11856 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11856.

Lemma collineation_11857 : is_collineation fp_11857 fl_11857.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11857 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11857 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11857.

Lemma collineation_11858 : is_collineation fp_11858 fl_11858.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11858 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11858 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11858.

Lemma collineation_11859 : is_collineation fp_11859 fl_11859.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11859 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11859 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11859.

Lemma collineation_11860 : is_collineation fp_11860 fl_11860.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11860 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11860 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11860.

Lemma collineation_11861 : is_collineation fp_11861 fl_11861.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11861 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11861 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11861.

Lemma collineation_11862 : is_collineation fp_11862 fl_11862.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11862 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11862 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11862.

Lemma collineation_11863 : is_collineation fp_11863 fl_11863.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11863 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11863 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11863.

Lemma collineation_11864 : is_collineation fp_11864 fl_11864.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11864 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11864 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11864.

Lemma collineation_11865 : is_collineation fp_11865 fl_11865.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11865 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11865 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11865.

Lemma collineation_11866 : is_collineation fp_11866 fl_11866.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11866 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11866 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11866.

Lemma collineation_11867 : is_collineation fp_11867 fl_11867.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11867 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11867 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11867.

Lemma collineation_11868 : is_collineation fp_11868 fl_11868.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11868 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11868 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11868.

Lemma collineation_11869 : is_collineation fp_11869 fl_11869.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11869 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11869 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11869.

Lemma collineation_11870 : is_collineation fp_11870 fl_11870.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11870 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11870 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11870.

Lemma collineation_11871 : is_collineation fp_11871 fl_11871.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11871 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11871 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11871.

Lemma collineation_11872 : is_collineation fp_11872 fl_11872.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11872 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11872 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11872.

Lemma collineation_11873 : is_collineation fp_11873 fl_11873.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11873 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11873 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11873.

Lemma collineation_11874 : is_collineation fp_11874 fl_11874.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11874 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11874 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11874.

Lemma collineation_11875 : is_collineation fp_11875 fl_11875.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11875 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11875 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11875.

Lemma collineation_11876 : is_collineation fp_11876 fl_11876.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11876 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11876 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11876.

Lemma collineation_11877 : is_collineation fp_11877 fl_11877.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11877 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11877 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11877.

Lemma collineation_11878 : is_collineation fp_11878 fl_11878.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11878 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11878 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11878.

Lemma collineation_11879 : is_collineation fp_11879 fl_11879.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11879 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11879 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11879.

Lemma collineation_11880 : is_collineation fp_11880 fl_11880.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11880 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11880 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11880.

Lemma collineation_11881 : is_collineation fp_11881 fl_11881.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11881 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11881 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11881.

Lemma collineation_11882 : is_collineation fp_11882 fl_11882.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11882 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11882 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11882.

Lemma collineation_11883 : is_collineation fp_11883 fl_11883.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11883 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11883 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11883.

Lemma collineation_11884 : is_collineation fp_11884 fl_11884.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11884 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11884 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11884.

Lemma collineation_11885 : is_collineation fp_11885 fl_11885.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11885 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11885 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11885.

Lemma collineation_11886 : is_collineation fp_11886 fl_11886.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11886 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11886 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11886.

Lemma collineation_11887 : is_collineation fp_11887 fl_11887.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11887 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11887 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11887.

Lemma collineation_11888 : is_collineation fp_11888 fl_11888.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11888 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11888 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11888.

Lemma collineation_11889 : is_collineation fp_11889 fl_11889.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11889 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11889 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11889.

Lemma collineation_11890 : is_collineation fp_11890 fl_11890.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11890 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11890 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11890.

Lemma collineation_11891 : is_collineation fp_11891 fl_11891.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11891 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11891 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11891.

Lemma collineation_11892 : is_collineation fp_11892 fl_11892.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11892 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11892 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11892.

Lemma collineation_11893 : is_collineation fp_11893 fl_11893.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11893 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11893 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11893.

Lemma collineation_11894 : is_collineation fp_11894 fl_11894.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11894 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11894 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11894.

Lemma collineation_11895 : is_collineation fp_11895 fl_11895.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11895 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11895 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11895.

Lemma collineation_11896 : is_collineation fp_11896 fl_11896.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11896 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11896 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11896.

Lemma collineation_11897 : is_collineation fp_11897 fl_11897.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11897 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11897 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11897.

Lemma collineation_11898 : is_collineation fp_11898 fl_11898.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11898 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11898 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11898.

Lemma collineation_11899 : is_collineation fp_11899 fl_11899.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11899 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11899 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11899.

Lemma collineation_11900 : is_collineation fp_11900 fl_11900.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11900 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11900 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11900.

Lemma collineation_11901 : is_collineation fp_11901 fl_11901.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11901 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11901 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11901.

Lemma collineation_11902 : is_collineation fp_11902 fl_11902.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11902 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11902 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11902.

Lemma collineation_11903 : is_collineation fp_11903 fl_11903.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11903 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11903 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11903.

Lemma collineation_11904 : is_collineation fp_11904 fl_11904.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11904 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11904 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11904.

Lemma collineation_11905 : is_collineation fp_11905 fl_11905.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11905 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11905 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11905.

Lemma collineation_11906 : is_collineation fp_11906 fl_11906.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11906 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11906 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11906.

Lemma collineation_11907 : is_collineation fp_11907 fl_11907.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11907 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11907 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11907.

Lemma collineation_11908 : is_collineation fp_11908 fl_11908.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11908 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11908 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11908.

Lemma collineation_11909 : is_collineation fp_11909 fl_11909.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11909 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11909 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11909.

Lemma collineation_11910 : is_collineation fp_11910 fl_11910.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11910 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11910 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11910.

Lemma collineation_11911 : is_collineation fp_11911 fl_11911.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11911 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11911 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11911.

Lemma collineation_11912 : is_collineation fp_11912 fl_11912.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11912 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11912 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11912.

Lemma collineation_11913 : is_collineation fp_11913 fl_11913.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11913 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11913 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11913.

Lemma collineation_11914 : is_collineation fp_11914 fl_11914.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11914 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11914 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11914.

Lemma collineation_11915 : is_collineation fp_11915 fl_11915.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11915 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11915 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11915.

Lemma collineation_11916 : is_collineation fp_11916 fl_11916.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11916 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11916 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11916.

Lemma collineation_11917 : is_collineation fp_11917 fl_11917.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11917 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11917 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11917.

Lemma collineation_11918 : is_collineation fp_11918 fl_11918.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11918 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11918 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11918.

Lemma collineation_11919 : is_collineation fp_11919 fl_11919.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11919 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11919 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11919.

Lemma collineation_11920 : is_collineation fp_11920 fl_11920.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11920 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11920 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11920.

Lemma collineation_11921 : is_collineation fp_11921 fl_11921.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11921 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11921 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11921.

Lemma collineation_11922 : is_collineation fp_11922 fl_11922.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11922 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11922 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11922.

Lemma collineation_11923 : is_collineation fp_11923 fl_11923.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11923 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11923 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11923.

Lemma collineation_11924 : is_collineation fp_11924 fl_11924.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11924 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11924 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11924.

Lemma collineation_11925 : is_collineation fp_11925 fl_11925.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11925 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11925 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11925.

Lemma collineation_11926 : is_collineation fp_11926 fl_11926.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11926 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11926 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11926.

Lemma collineation_11927 : is_collineation fp_11927 fl_11927.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11927 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11927 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11927.

Lemma collineation_11928 : is_collineation fp_11928 fl_11928.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11928 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11928 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11928.

Lemma collineation_11929 : is_collineation fp_11929 fl_11929.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11929 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11929 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11929.

Lemma collineation_11930 : is_collineation fp_11930 fl_11930.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11930 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11930 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11930.

Lemma collineation_11931 : is_collineation fp_11931 fl_11931.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11931 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11931 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11931.

Lemma collineation_11932 : is_collineation fp_11932 fl_11932.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11932 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11932 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11932.

Lemma collineation_11933 : is_collineation fp_11933 fl_11933.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11933 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11933 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11933.

Lemma collineation_11934 : is_collineation fp_11934 fl_11934.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11934 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11934 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11934.

Lemma collineation_11935 : is_collineation fp_11935 fl_11935.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11935 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11935 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11935.

Lemma collineation_11936 : is_collineation fp_11936 fl_11936.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11936 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11936 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11936.

Lemma collineation_11937 : is_collineation fp_11937 fl_11937.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11937 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11937 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11937.

Lemma collineation_11938 : is_collineation fp_11938 fl_11938.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11938 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11938 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11938.

Lemma collineation_11939 : is_collineation fp_11939 fl_11939.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11939 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11939 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11939.

Lemma collineation_11940 : is_collineation fp_11940 fl_11940.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11940 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11940 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11940.

Lemma collineation_11941 : is_collineation fp_11941 fl_11941.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11941 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11941 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11941.

Lemma collineation_11942 : is_collineation fp_11942 fl_11942.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11942 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11942 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11942.

Lemma collineation_11943 : is_collineation fp_11943 fl_11943.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11943 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11943 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11943.

Lemma collineation_11944 : is_collineation fp_11944 fl_11944.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11944 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11944 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11944.

Lemma collineation_11945 : is_collineation fp_11945 fl_11945.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11945 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11945 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11945.

Lemma collineation_11946 : is_collineation fp_11946 fl_11946.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11946 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11946 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11946.

Lemma collineation_11947 : is_collineation fp_11947 fl_11947.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11947 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11947 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11947.

Lemma collineation_11948 : is_collineation fp_11948 fl_11948.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11948 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11948 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11948.

Lemma collineation_11949 : is_collineation fp_11949 fl_11949.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11949 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11949 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11949.

Lemma collineation_11950 : is_collineation fp_11950 fl_11950.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11950 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11950 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11950.

Lemma collineation_11951 : is_collineation fp_11951 fl_11951.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11951 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11951 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11951.

Lemma collineation_11952 : is_collineation fp_11952 fl_11952.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11952 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11952 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11952.

Lemma collineation_11953 : is_collineation fp_11953 fl_11953.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11953 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11953 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11953.

Lemma collineation_11954 : is_collineation fp_11954 fl_11954.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11954 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11954 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11954.

Lemma collineation_11955 : is_collineation fp_11955 fl_11955.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11955 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11955 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11955.

Lemma collineation_11956 : is_collineation fp_11956 fl_11956.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11956 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11956 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11956.

Lemma collineation_11957 : is_collineation fp_11957 fl_11957.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11957 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11957 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11957.

Lemma collineation_11958 : is_collineation fp_11958 fl_11958.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11958 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11958 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11958.

Lemma collineation_11959 : is_collineation fp_11959 fl_11959.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11959 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11959 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11959.

Lemma collineation_11960 : is_collineation fp_11960 fl_11960.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11960 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11960 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11960.

Lemma collineation_11961 : is_collineation fp_11961 fl_11961.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11961 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11961 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11961.

Lemma collineation_11962 : is_collineation fp_11962 fl_11962.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11962 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11962 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11962.

Lemma collineation_11963 : is_collineation fp_11963 fl_11963.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11963 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11963 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11963.

Lemma collineation_11964 : is_collineation fp_11964 fl_11964.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11964 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11964 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11964.

Lemma collineation_11965 : is_collineation fp_11965 fl_11965.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11965 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11965 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11965.

Lemma collineation_11966 : is_collineation fp_11966 fl_11966.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11966 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11966 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11966.

Lemma collineation_11967 : is_collineation fp_11967 fl_11967.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11967 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11967 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11967.

Lemma collineation_11968 : is_collineation fp_11968 fl_11968.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11968 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11968 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11968.

Lemma collineation_11969 : is_collineation fp_11969 fl_11969.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11969 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11969 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11969.

Lemma collineation_11970 : is_collineation fp_11970 fl_11970.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11970 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11970 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11970.

Lemma collineation_11971 : is_collineation fp_11971 fl_11971.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11971 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11971 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11971.

Lemma collineation_11972 : is_collineation fp_11972 fl_11972.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11972 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11972 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11972.

Lemma collineation_11973 : is_collineation fp_11973 fl_11973.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11973 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11973 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11973.

Lemma collineation_11974 : is_collineation fp_11974 fl_11974.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11974 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11974 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11974.

Lemma collineation_11975 : is_collineation fp_11975 fl_11975.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11975 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11975 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11975.

Lemma collineation_11976 : is_collineation fp_11976 fl_11976.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11976 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11976 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11976.

Lemma collineation_11977 : is_collineation fp_11977 fl_11977.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11977 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11977 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11977.

Lemma collineation_11978 : is_collineation fp_11978 fl_11978.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11978 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11978 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11978.

Lemma collineation_11979 : is_collineation fp_11979 fl_11979.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11979 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11979 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11979.

Lemma collineation_11980 : is_collineation fp_11980 fl_11980.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11980 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11980 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11980.

Lemma collineation_11981 : is_collineation fp_11981 fl_11981.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11981 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11981 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11981.

Lemma collineation_11982 : is_collineation fp_11982 fl_11982.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11982 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11982 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11982.

Lemma collineation_11983 : is_collineation fp_11983 fl_11983.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11983 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11983 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11983.

Lemma collineation_11984 : is_collineation fp_11984 fl_11984.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11984 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11984 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11984.

Lemma collineation_11985 : is_collineation fp_11985 fl_11985.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11985 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11985 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11985.

Lemma collineation_11986 : is_collineation fp_11986 fl_11986.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11986 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11986 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11986.

Lemma collineation_11987 : is_collineation fp_11987 fl_11987.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11987 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11987 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11987.

Lemma collineation_11988 : is_collineation fp_11988 fl_11988.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11988 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11988 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11988.

Lemma collineation_11989 : is_collineation fp_11989 fl_11989.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11989 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11989 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11989.

Lemma collineation_11990 : is_collineation fp_11990 fl_11990.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11990 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11990 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11990.

Lemma collineation_11991 : is_collineation fp_11991 fl_11991.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11991 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11991 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11991.

Lemma collineation_11992 : is_collineation fp_11992 fl_11992.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11992 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11992 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11992.

Lemma collineation_11993 : is_collineation fp_11993 fl_11993.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11993 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11993 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11993.

Lemma collineation_11994 : is_collineation fp_11994 fl_11994.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11994 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11994 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11994.

Lemma collineation_11995 : is_collineation fp_11995 fl_11995.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11995 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11995 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11995.

Lemma collineation_11996 : is_collineation fp_11996 fl_11996.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11996 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11996 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11996.

Lemma collineation_11997 : is_collineation fp_11997 fl_11997.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11997 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11997 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11997.

Lemma collineation_11998 : is_collineation fp_11998 fl_11998.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11998 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11998 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11998.

Lemma collineation_11999 : is_collineation fp_11999 fl_11999.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_11999 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_11999 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_11999.

Lemma collineation_12000 : is_collineation fp_12000 fl_12000.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12000 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12000 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12000.

Lemma collineation_12001 : is_collineation fp_12001 fl_12001.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12001 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12001 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12001.

Lemma collineation_12002 : is_collineation fp_12002 fl_12002.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12002 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12002 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12002.

Lemma collineation_12003 : is_collineation fp_12003 fl_12003.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12003 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12003 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12003.

Lemma collineation_12004 : is_collineation fp_12004 fl_12004.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12004 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12004 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12004.

Lemma collineation_12005 : is_collineation fp_12005 fl_12005.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12005 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12005 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12005.

Lemma collineation_12006 : is_collineation fp_12006 fl_12006.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12006 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12006 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12006.

Lemma collineation_12007 : is_collineation fp_12007 fl_12007.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12007 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12007 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12007.

Lemma collineation_12008 : is_collineation fp_12008 fl_12008.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12008 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12008 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12008.

Lemma collineation_12009 : is_collineation fp_12009 fl_12009.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12009 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12009 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12009.

Lemma collineation_12010 : is_collineation fp_12010 fl_12010.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12010 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12010 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12010.

Lemma collineation_12011 : is_collineation fp_12011 fl_12011.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12011 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12011 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12011.

Lemma collineation_12012 : is_collineation fp_12012 fl_12012.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12012 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12012 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12012.

Lemma collineation_12013 : is_collineation fp_12013 fl_12013.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12013 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12013 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12013.

Lemma collineation_12014 : is_collineation fp_12014 fl_12014.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12014 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12014 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12014.

Lemma collineation_12015 : is_collineation fp_12015 fl_12015.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12015 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12015 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12015.

Lemma collineation_12016 : is_collineation fp_12016 fl_12016.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12016 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12016 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12016.

Lemma collineation_12017 : is_collineation fp_12017 fl_12017.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12017 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12017 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12017.

Lemma collineation_12018 : is_collineation fp_12018 fl_12018.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12018 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12018 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12018.

Lemma collineation_12019 : is_collineation fp_12019 fl_12019.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12019 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12019 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12019.

Lemma collineation_12020 : is_collineation fp_12020 fl_12020.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12020 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12020 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12020.

Lemma collineation_12021 : is_collineation fp_12021 fl_12021.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12021 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12021 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12021.

Lemma collineation_12022 : is_collineation fp_12022 fl_12022.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12022 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12022 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12022.

Lemma collineation_12023 : is_collineation fp_12023 fl_12023.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12023 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12023 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12023.

Lemma collineation_12024 : is_collineation fp_12024 fl_12024.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12024 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12024 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12024.

Lemma collineation_12025 : is_collineation fp_12025 fl_12025.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12025 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12025 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12025.

Lemma collineation_12026 : is_collineation fp_12026 fl_12026.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12026 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12026 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12026.

Lemma collineation_12027 : is_collineation fp_12027 fl_12027.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12027 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12027 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12027.

Lemma collineation_12028 : is_collineation fp_12028 fl_12028.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12028 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12028 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12028.

Lemma collineation_12029 : is_collineation fp_12029 fl_12029.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12029 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12029 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12029.

Lemma collineation_12030 : is_collineation fp_12030 fl_12030.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12030 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12030 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12030.

Lemma collineation_12031 : is_collineation fp_12031 fl_12031.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12031 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12031 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12031.

Lemma collineation_12032 : is_collineation fp_12032 fl_12032.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12032 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12032 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12032.

Lemma collineation_12033 : is_collineation fp_12033 fl_12033.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12033 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12033 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12033.

Lemma collineation_12034 : is_collineation fp_12034 fl_12034.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12034 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12034 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12034.

Lemma collineation_12035 : is_collineation fp_12035 fl_12035.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12035 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12035 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12035.

Lemma collineation_12036 : is_collineation fp_12036 fl_12036.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12036 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12036 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12036.

Lemma collineation_12037 : is_collineation fp_12037 fl_12037.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12037 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12037 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12037.

Lemma collineation_12038 : is_collineation fp_12038 fl_12038.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12038 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12038 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12038.

Lemma collineation_12039 : is_collineation fp_12039 fl_12039.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12039 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12039 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12039.

Lemma collineation_12040 : is_collineation fp_12040 fl_12040.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12040 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12040 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12040.

Lemma collineation_12041 : is_collineation fp_12041 fl_12041.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12041 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12041 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12041.

Lemma collineation_12042 : is_collineation fp_12042 fl_12042.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12042 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12042 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12042.

Lemma collineation_12043 : is_collineation fp_12043 fl_12043.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12043 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12043 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12043.

Lemma collineation_12044 : is_collineation fp_12044 fl_12044.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12044 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12044 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12044.

Lemma collineation_12045 : is_collineation fp_12045 fl_12045.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12045 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12045 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12045.

Lemma collineation_12046 : is_collineation fp_12046 fl_12046.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12046 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12046 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12046.

Lemma collineation_12047 : is_collineation fp_12047 fl_12047.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12047 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12047 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12047.

Lemma collineation_12048 : is_collineation fp_12048 fl_12048.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12048 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12048 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12048.

Lemma collineation_12049 : is_collineation fp_12049 fl_12049.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12049 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12049 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12049.

Lemma collineation_12050 : is_collineation fp_12050 fl_12050.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12050 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12050 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12050.

Lemma collineation_12051 : is_collineation fp_12051 fl_12051.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12051 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12051 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12051.

Lemma collineation_12052 : is_collineation fp_12052 fl_12052.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12052 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12052 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12052.

Lemma collineation_12053 : is_collineation fp_12053 fl_12053.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12053 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12053 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12053.

Lemma collineation_12054 : is_collineation fp_12054 fl_12054.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12054 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12054 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12054.

Lemma collineation_12055 : is_collineation fp_12055 fl_12055.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12055 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12055 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12055.

Lemma collineation_12056 : is_collineation fp_12056 fl_12056.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12056 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12056 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12056.

Lemma collineation_12057 : is_collineation fp_12057 fl_12057.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12057 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12057 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12057.

Lemma collineation_12058 : is_collineation fp_12058 fl_12058.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12058 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12058 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12058.

Lemma collineation_12059 : is_collineation fp_12059 fl_12059.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12059 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12059 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12059.

Lemma collineation_12060 : is_collineation fp_12060 fl_12060.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12060 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12060 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12060.

Lemma collineation_12061 : is_collineation fp_12061 fl_12061.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12061 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12061 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12061.

Lemma collineation_12062 : is_collineation fp_12062 fl_12062.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12062 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12062 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12062.

Lemma collineation_12063 : is_collineation fp_12063 fl_12063.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12063 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12063 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12063.

Lemma collineation_12064 : is_collineation fp_12064 fl_12064.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12064 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12064 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12064.

Lemma collineation_12065 : is_collineation fp_12065 fl_12065.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12065 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12065 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12065.

Lemma collineation_12066 : is_collineation fp_12066 fl_12066.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12066 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12066 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12066.

Lemma collineation_12067 : is_collineation fp_12067 fl_12067.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12067 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12067 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12067.

Lemma collineation_12068 : is_collineation fp_12068 fl_12068.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12068 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12068 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12068.

Lemma collineation_12069 : is_collineation fp_12069 fl_12069.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12069 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12069 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12069.

Lemma collineation_12070 : is_collineation fp_12070 fl_12070.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12070 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12070 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12070.

Lemma collineation_12071 : is_collineation fp_12071 fl_12071.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12071 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12071 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12071.

Lemma collineation_12072 : is_collineation fp_12072 fl_12072.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12072 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12072 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12072.

Lemma collineation_12073 : is_collineation fp_12073 fl_12073.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12073 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12073 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12073.

Lemma collineation_12074 : is_collineation fp_12074 fl_12074.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12074 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12074 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12074.

Lemma collineation_12075 : is_collineation fp_12075 fl_12075.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12075 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12075 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12075.

Lemma collineation_12076 : is_collineation fp_12076 fl_12076.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12076 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12076 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12076.

Lemma collineation_12077 : is_collineation fp_12077 fl_12077.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12077 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12077 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12077.

Lemma collineation_12078 : is_collineation fp_12078 fl_12078.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12078 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12078 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12078.

Lemma collineation_12079 : is_collineation fp_12079 fl_12079.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12079 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12079 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12079.

Lemma collineation_12080 : is_collineation fp_12080 fl_12080.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12080 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12080 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12080.

Lemma collineation_12081 : is_collineation fp_12081 fl_12081.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12081 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12081 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12081.

Lemma collineation_12082 : is_collineation fp_12082 fl_12082.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12082 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12082 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12082.

Lemma collineation_12083 : is_collineation fp_12083 fl_12083.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12083 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12083 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12083.

Lemma collineation_12084 : is_collineation fp_12084 fl_12084.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12084 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12084 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12084.

Lemma collineation_12085 : is_collineation fp_12085 fl_12085.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12085 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12085 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12085.

Lemma collineation_12086 : is_collineation fp_12086 fl_12086.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12086 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12086 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12086.

Lemma collineation_12087 : is_collineation fp_12087 fl_12087.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12087 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12087 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12087.

Lemma collineation_12088 : is_collineation fp_12088 fl_12088.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12088 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12088 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12088.

Lemma collineation_12089 : is_collineation fp_12089 fl_12089.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12089 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12089 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12089.

Lemma collineation_12090 : is_collineation fp_12090 fl_12090.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12090 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12090 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12090.

Lemma collineation_12091 : is_collineation fp_12091 fl_12091.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12091 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12091 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12091.

Lemma collineation_12092 : is_collineation fp_12092 fl_12092.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12092 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12092 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12092.

Lemma collineation_12093 : is_collineation fp_12093 fl_12093.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12093 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12093 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12093.

Lemma collineation_12094 : is_collineation fp_12094 fl_12094.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12094 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12094 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12094.

Lemma collineation_12095 : is_collineation fp_12095 fl_12095.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12095 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12095 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12095.

Lemma is_col_all_c112 : forall fp fl, In (fp,fl) (all_c112++all_c113++all_c114++all_c115++all_c116++all_c117++all_c118++all_c119++all_c120++all_c121++all_c122++all_c123++all_c124++all_c125) -> is_collineation fp fl.
Proof.
 intros fp fl HIn_S.
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10752 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10753 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10754 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10755 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10756 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10757 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10758 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10759 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10760 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10761 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10762 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10763 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10764 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10765 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10766 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10767 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10768 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10769 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10770 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10771 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10772 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10773 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10774 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10775 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10776 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10777 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10778 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10779 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10780 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10781 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10782 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10783 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10784 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10785 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10786 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10787 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10788 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10789 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10790 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10791 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10792 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10793 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10794 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10795 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10796 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10797 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10798 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10799 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10800 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10801 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10802 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10803 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10804 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10805 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10806 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10807 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10808 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10809 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10810 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10811 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10812 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10813 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10814 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10815 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10816 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10817 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10818 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10819 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10820 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10821 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10822 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10823 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10824 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10825 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10826 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10827 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10828 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10829 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10830 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10831 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10832 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10833 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10834 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10835 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10836 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10837 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10838 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10839 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10840 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10841 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10842 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10843 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10844 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10845 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10846 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10847 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10848 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10849 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10850 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10851 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10852 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10853 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10854 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10855 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10856 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10857 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10858 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10859 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10860 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10861 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10862 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10863 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10864 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10865 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10866 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10867 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10868 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10869 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10870 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10871 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10872 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10873 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10874 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10875 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10876 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10877 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10878 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10879 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10880 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10881 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10882 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10883 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10884 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10885 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10886 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10887 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10888 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10889 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10890 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10891 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10892 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10893 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10894 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10895 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10896 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10897 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10898 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10899 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10900 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10901 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10902 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10903 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10904 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10905 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10906 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10907 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10908 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10909 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10910 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10911 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10912 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10913 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10914 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10915 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10916 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10917 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10918 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10919 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10920 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10921 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10922 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10923 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10924 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10925 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10926 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10927 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10928 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10929 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10930 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10931 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10932 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10933 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10934 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10935 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10936 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10937 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10938 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10939 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10940 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10941 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10942 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10943 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10944 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10945 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10946 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10947 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10948 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10949 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10950 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10951 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10952 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10953 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10954 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10955 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10956 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10957 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10958 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10959 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10960 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10961 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10962 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10963 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10964 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10965 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10966 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10967 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10968 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10969 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10970 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10971 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10972 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10973 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10974 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10975 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10976 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10977 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10978 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10979 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10980 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10981 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10982 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10983 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10984 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10985 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10986 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10987 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10988 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10989 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10990 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10991 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10992 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10993 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10994 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10995 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10996 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10997 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10998 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10999 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11000 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11001 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11002 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11003 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11004 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11005 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11006 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11007 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11008 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11009 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11010 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11011 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11012 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11013 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11014 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11015 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11016 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11017 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11018 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11019 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11020 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11021 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11022 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11023 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11024 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11025 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11026 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11027 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11028 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11029 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11030 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11031 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11032 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11033 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11034 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11035 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11036 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11037 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11038 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11039 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11040 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11041 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11042 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11043 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11044 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11045 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11046 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11047 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11048 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11049 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11050 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11051 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11052 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11053 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11054 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11055 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11056 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11057 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11058 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11059 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11060 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11061 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11062 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11063 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11064 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11065 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11066 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11067 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11068 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11069 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11070 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11071 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11072 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11073 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11074 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11075 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11076 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11077 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11078 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11079 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11080 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11081 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11082 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11083 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11084 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11085 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11086 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11087 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11088 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11089 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11090 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11091 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11092 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11093 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11094 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11095 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11096 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11097 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11098 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11099 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11100 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11101 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11102 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11103 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11104 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11105 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11106 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11107 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11108 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11109 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11110 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11111 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11112 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11113 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11114 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11115 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11116 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11117 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11118 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11119 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11120 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11121 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11122 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11123 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11124 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11125 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11126 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11127 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11128 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11129 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11130 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11131 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11132 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11133 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11134 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11135 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11136 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11137 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11138 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11139 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11140 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11141 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11142 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11143 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11144 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11145 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11146 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11147 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11148 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11149 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11150 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11151 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11152 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11153 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11154 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11155 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11156 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11157 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11158 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11159 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11160 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11161 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11162 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11163 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11164 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11165 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11166 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11167 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11168 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11169 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11170 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11171 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11172 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11173 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11174 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11175 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11176 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11177 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11178 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11179 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11180 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11181 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11182 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11183 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11184 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11185 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11186 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11187 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11188 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11189 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11190 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11191 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11192 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11193 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11194 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11195 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11196 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11197 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11198 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11199 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11200 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11201 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11202 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11203 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11204 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11205 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11206 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11207 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11208 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11209 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11210 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11211 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11212 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11213 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11214 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11215 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11216 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11217 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11218 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11219 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11220 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11221 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11222 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11223 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11224 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11225 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11226 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11227 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11228 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11229 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11230 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11231 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11232 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11233 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11234 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11235 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11236 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11237 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11238 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11239 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11240 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11241 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11242 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11243 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11244 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11245 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11246 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11247 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11248 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11249 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11250 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11251 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11252 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11253 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11254 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11255 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11256 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11257 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11258 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11259 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11260 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11261 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11262 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11263 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11264 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11265 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11266 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11267 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11268 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11269 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11270 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11271 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11272 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11273 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11274 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11275 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11276 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11277 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11278 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11279 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11280 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11281 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11282 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11283 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11284 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11285 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11286 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11287 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11288 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11289 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11290 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11291 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11292 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11293 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11294 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11295 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11296 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11297 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11298 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11299 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11300 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11301 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11302 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11303 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11304 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11305 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11306 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11307 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11308 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11309 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11310 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11311 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11312 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11313 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11314 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11315 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11316 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11317 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11318 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11319 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11320 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11321 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11322 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11323 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11324 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11325 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11326 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11327 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11328 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11329 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11330 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11331 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11332 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11333 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11334 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11335 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11336 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11337 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11338 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11339 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11340 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11341 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11342 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11343 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11344 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11345 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11346 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11347 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11348 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11349 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11350 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11351 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11352 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11353 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11354 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11355 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11356 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11357 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11358 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11359 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11360 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11361 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11362 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11363 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11364 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11365 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11366 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11367 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11368 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11369 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11370 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11371 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11372 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11373 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11374 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11375 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11376 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11377 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11378 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11379 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11380 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11381 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11382 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11383 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11384 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11385 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11386 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11387 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11388 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11389 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11390 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11391 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11392 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11393 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11394 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11395 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11396 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11397 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11398 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11399 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11400 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11401 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11402 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11403 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11404 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11405 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11406 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11407 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11408 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11409 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11410 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11411 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11412 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11413 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11414 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11415 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11416 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11417 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11418 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11419 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11420 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11421 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11422 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11423 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11424 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11425 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11426 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11427 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11428 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11429 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11430 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11431 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11432 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11433 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11434 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11435 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11436 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11437 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11438 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11439 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11440 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11441 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11442 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11443 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11444 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11445 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11446 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11447 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11448 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11449 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11450 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11451 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11452 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11453 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11454 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11455 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11456 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11457 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11458 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11459 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11460 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11461 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11462 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11463 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11464 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11465 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11466 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11467 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11468 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11469 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11470 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11471 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11472 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11473 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11474 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11475 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11476 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11477 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11478 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11479 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11480 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11481 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11482 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11483 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11484 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11485 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11486 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11487 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11488 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11489 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11490 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11491 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11492 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11493 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11494 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11495 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11496 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11497 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11498 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11499 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11500 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11501 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11502 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11503 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11504 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11505 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11506 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11507 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11508 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11509 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11510 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11511 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11512 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11513 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11514 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11515 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11516 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11517 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11518 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11519 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11520 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11521 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11522 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11523 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11524 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11525 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11526 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11527 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11528 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11529 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11530 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11531 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11532 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11533 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11534 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11535 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11536 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11537 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11538 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11539 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11540 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11541 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11542 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11543 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11544 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11545 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11546 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11547 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11548 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11549 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11550 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11551 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11552 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11553 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11554 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11555 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11556 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11557 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11558 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11559 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11560 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11561 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11562 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11563 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11564 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11565 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11566 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11567 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11568 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11569 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11570 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11571 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11572 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11573 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11574 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11575 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11576 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11577 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11578 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11579 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11580 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11581 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11582 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11583 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11584 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11585 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11586 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11587 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11588 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11589 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11590 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11591 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11592 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11593 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11594 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11595 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11596 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11597 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11598 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11599 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11600 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11601 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11602 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11603 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11604 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11605 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11606 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11607 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11608 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11609 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11610 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11611 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11612 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11613 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11614 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11615 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11616 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11617 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11618 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11619 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11620 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11621 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11622 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11623 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11624 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11625 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11626 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11627 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11628 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11629 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11630 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11631 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11632 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11633 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11634 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11635 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11636 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11637 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11638 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11639 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11640 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11641 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11642 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11643 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11644 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11645 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11646 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11647 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11648 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11649 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11650 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11651 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11652 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11653 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11654 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11655 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11656 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11657 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11658 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11659 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11660 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11661 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11662 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11663 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11664 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11665 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11666 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11667 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11668 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11669 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11670 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11671 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11672 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11673 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11674 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11675 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11676 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11677 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11678 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11679 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11680 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11681 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11682 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11683 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11684 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11685 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11686 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11687 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11688 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11689 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11690 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11691 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11692 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11693 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11694 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11695 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11696 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11697 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11698 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11699 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11700 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11701 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11702 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11703 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11704 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11705 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11706 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11707 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11708 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11709 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11710 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11711 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11712 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11713 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11714 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11715 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11716 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11717 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11718 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11719 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11720 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11721 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11722 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11723 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11724 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11725 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11726 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11727 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11728 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11729 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11730 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11731 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11732 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11733 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11734 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11735 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11736 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11737 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11738 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11739 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11740 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11741 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11742 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11743 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11744 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11745 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11746 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11747 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11748 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11749 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11750 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11751 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11752 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11753 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11754 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11755 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11756 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11757 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11758 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11759 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11760 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11761 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11762 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11763 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11764 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11765 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11766 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11767 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11768 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11769 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11770 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11771 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11772 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11773 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11774 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11775 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11776 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11777 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11778 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11779 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11780 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11781 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11782 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11783 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11784 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11785 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11786 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11787 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11788 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11789 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11790 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11791 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11792 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11793 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11794 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11795 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11796 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11797 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11798 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11799 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11800 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11801 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11802 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11803 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11804 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11805 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11806 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11807 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11808 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11809 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11810 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11811 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11812 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11813 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11814 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11815 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11816 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11817 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11818 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11819 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11820 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11821 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11822 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11823 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11824 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11825 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11826 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11827 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11828 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11829 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11830 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11831 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11832 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11833 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11834 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11835 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11836 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11837 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11838 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11839 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11840 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11841 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11842 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11843 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11844 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11845 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11846 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11847 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11848 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11849 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11850 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11851 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11852 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11853 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11854 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11855 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11856 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11857 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11858 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11859 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11860 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11861 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11862 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11863 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11864 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11865 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11866 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11867 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11868 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11869 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11870 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11871 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11872 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11873 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11874 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11875 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11876 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11877 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11878 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11879 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11880 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11881 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11882 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11883 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11884 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11885 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11886 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11887 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11888 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11889 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11890 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11891 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11892 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11893 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11894 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11895 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11896 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11897 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11898 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11899 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11900 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11901 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11902 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11903 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11904 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11905 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11906 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11907 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11908 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11909 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11910 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11911 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11912 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11913 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11914 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11915 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11916 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11917 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11918 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11919 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11920 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11921 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11922 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11923 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11924 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11925 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11926 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11927 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11928 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11929 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11930 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11931 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11932 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11933 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11934 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11935 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11936 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11937 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11938 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11939 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11940 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11941 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11942 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11943 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11944 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11945 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11946 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11947 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11948 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11949 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11950 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11951 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11952 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11953 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11954 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11955 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11956 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11957 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11958 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11959 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11960 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11961 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11962 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11963 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11964 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11965 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11966 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11967 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11968 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11969 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11970 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11971 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11972 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11973 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11974 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11975 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11976 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11977 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11978 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11979 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11980 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11981 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11982 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11983 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11984 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11985 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11986 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11987 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11988 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11989 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11990 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11991 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11992 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11993 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11994 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11995 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11996 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11997 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11998 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_11999 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12000 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12001 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12002 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12003 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12004 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12005 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12006 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12007 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12008 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12009 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12010 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12011 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12012 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12013 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12014 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12015 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12016 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12017 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12018 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12019 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12020 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12021 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12022 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12023 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12024 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12025 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12026 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12027 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12028 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12029 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12030 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12031 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12032 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12033 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12034 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12035 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12036 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12037 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12038 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12039 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12040 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12041 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12042 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12043 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12044 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12045 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12046 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12047 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12048 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12049 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12050 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12051 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12052 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12053 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12054 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12055 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12056 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12057 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12058 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12059 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12060 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12061 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12062 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12063 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12064 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12065 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12066 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12067 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12068 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12069 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12070 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12071 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12072 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12073 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12074 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12075 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12076 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12077 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12078 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12079 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12080 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12081 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12082 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12083 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12084 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12085 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12086 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12087 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12088 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12089 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12090 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12091 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12092 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12093 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12094 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12095 | idtac].
 destruct (in_nil HIn_S).
Qed.

