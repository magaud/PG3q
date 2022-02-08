Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas.
Require Import PG32.pg32_inductive PG32.pg32_spreads_collineations.
Require Import PG32.pg32_automorphisms.
Require Import PG32.pg32_automorphisms_inv.
Require Import Lists.List.
Import ListNotations.
Require Import Arith.

Lemma collineation_6720 : is_collineation fp_6720 fl_6720.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6720 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6720 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6720.

Lemma collineation_6721 : is_collineation fp_6721 fl_6721.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6721 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6721 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6721.

Lemma collineation_6722 : is_collineation fp_6722 fl_6722.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6722 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6722 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6722.

Lemma collineation_6723 : is_collineation fp_6723 fl_6723.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6723 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6723 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6723.

Lemma collineation_6724 : is_collineation fp_6724 fl_6724.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6724 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6724 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6724.

Lemma collineation_6725 : is_collineation fp_6725 fl_6725.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6725 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6725 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6725.

Lemma collineation_6726 : is_collineation fp_6726 fl_6726.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6726 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6726 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6726.

Lemma collineation_6727 : is_collineation fp_6727 fl_6727.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6727 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6727 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6727.

Lemma collineation_6728 : is_collineation fp_6728 fl_6728.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6728 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6728 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6728.

Lemma collineation_6729 : is_collineation fp_6729 fl_6729.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6729 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6729 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6729.

Lemma collineation_6730 : is_collineation fp_6730 fl_6730.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6730 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6730 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6730.

Lemma collineation_6731 : is_collineation fp_6731 fl_6731.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6731 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6731 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6731.

Lemma collineation_6732 : is_collineation fp_6732 fl_6732.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6732 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6732 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6732.

Lemma collineation_6733 : is_collineation fp_6733 fl_6733.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6733 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6733 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6733.

Lemma collineation_6734 : is_collineation fp_6734 fl_6734.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6734 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6734 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6734.

Lemma collineation_6735 : is_collineation fp_6735 fl_6735.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6735 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6735 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6735.

Lemma collineation_6736 : is_collineation fp_6736 fl_6736.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6736 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6736 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6736.

Lemma collineation_6737 : is_collineation fp_6737 fl_6737.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6737 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6737 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6737.

Lemma collineation_6738 : is_collineation fp_6738 fl_6738.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6738 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6738 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6738.

Lemma collineation_6739 : is_collineation fp_6739 fl_6739.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6739 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6739 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6739.

Lemma collineation_6740 : is_collineation fp_6740 fl_6740.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6740 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6740 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6740.

Lemma collineation_6741 : is_collineation fp_6741 fl_6741.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6741 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6741 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6741.

Lemma collineation_6742 : is_collineation fp_6742 fl_6742.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6742 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6742 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6742.

Lemma collineation_6743 : is_collineation fp_6743 fl_6743.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6743 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6743 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6743.

Lemma collineation_6744 : is_collineation fp_6744 fl_6744.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6744 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6744 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6744.

Lemma collineation_6745 : is_collineation fp_6745 fl_6745.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6745 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6745 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6745.

Lemma collineation_6746 : is_collineation fp_6746 fl_6746.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6746 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6746 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6746.

Lemma collineation_6747 : is_collineation fp_6747 fl_6747.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6747 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6747 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6747.

Lemma collineation_6748 : is_collineation fp_6748 fl_6748.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6748 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6748 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6748.

Lemma collineation_6749 : is_collineation fp_6749 fl_6749.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6749 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6749 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6749.

Lemma collineation_6750 : is_collineation fp_6750 fl_6750.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6750 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6750 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6750.

Lemma collineation_6751 : is_collineation fp_6751 fl_6751.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6751 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6751 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6751.

Lemma collineation_6752 : is_collineation fp_6752 fl_6752.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6752 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6752 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6752.

Lemma collineation_6753 : is_collineation fp_6753 fl_6753.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6753 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6753 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6753.

Lemma collineation_6754 : is_collineation fp_6754 fl_6754.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6754 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6754 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6754.

Lemma collineation_6755 : is_collineation fp_6755 fl_6755.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6755 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6755 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6755.

Lemma collineation_6756 : is_collineation fp_6756 fl_6756.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6756 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6756 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6756.

Lemma collineation_6757 : is_collineation fp_6757 fl_6757.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6757 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6757 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6757.

Lemma collineation_6758 : is_collineation fp_6758 fl_6758.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6758 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6758 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6758.

Lemma collineation_6759 : is_collineation fp_6759 fl_6759.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6759 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6759 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6759.

Lemma collineation_6760 : is_collineation fp_6760 fl_6760.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6760 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6760 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6760.

Lemma collineation_6761 : is_collineation fp_6761 fl_6761.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6761 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6761 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6761.

Lemma collineation_6762 : is_collineation fp_6762 fl_6762.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6762 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6762 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6762.

Lemma collineation_6763 : is_collineation fp_6763 fl_6763.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6763 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6763 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6763.

Lemma collineation_6764 : is_collineation fp_6764 fl_6764.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6764 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6764 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6764.

Lemma collineation_6765 : is_collineation fp_6765 fl_6765.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6765 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6765 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6765.

Lemma collineation_6766 : is_collineation fp_6766 fl_6766.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6766 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6766 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6766.

Lemma collineation_6767 : is_collineation fp_6767 fl_6767.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6767 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6767 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6767.

Lemma collineation_6768 : is_collineation fp_6768 fl_6768.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6768 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6768 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6768.

Lemma collineation_6769 : is_collineation fp_6769 fl_6769.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6769 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6769 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6769.

Lemma collineation_6770 : is_collineation fp_6770 fl_6770.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6770 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6770 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6770.

Lemma collineation_6771 : is_collineation fp_6771 fl_6771.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6771 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6771 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6771.

Lemma collineation_6772 : is_collineation fp_6772 fl_6772.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6772 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6772 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6772.

Lemma collineation_6773 : is_collineation fp_6773 fl_6773.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6773 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6773 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6773.

Lemma collineation_6774 : is_collineation fp_6774 fl_6774.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6774 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6774 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6774.

Lemma collineation_6775 : is_collineation fp_6775 fl_6775.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6775 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6775 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6775.

Lemma collineation_6776 : is_collineation fp_6776 fl_6776.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6776 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6776 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6776.

Lemma collineation_6777 : is_collineation fp_6777 fl_6777.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6777 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6777 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6777.

Lemma collineation_6778 : is_collineation fp_6778 fl_6778.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6778 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6778 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6778.

Lemma collineation_6779 : is_collineation fp_6779 fl_6779.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6779 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6779 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6779.

Lemma collineation_6780 : is_collineation fp_6780 fl_6780.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6780 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6780 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6780.

Lemma collineation_6781 : is_collineation fp_6781 fl_6781.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6781 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6781 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6781.

Lemma collineation_6782 : is_collineation fp_6782 fl_6782.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6782 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6782 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6782.

Lemma collineation_6783 : is_collineation fp_6783 fl_6783.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6783 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6783 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6783.

Lemma collineation_6784 : is_collineation fp_6784 fl_6784.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6784 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6784 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6784.

Lemma collineation_6785 : is_collineation fp_6785 fl_6785.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6785 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6785 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6785.

Lemma collineation_6786 : is_collineation fp_6786 fl_6786.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6786 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6786 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6786.

Lemma collineation_6787 : is_collineation fp_6787 fl_6787.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6787 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6787 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6787.

Lemma collineation_6788 : is_collineation fp_6788 fl_6788.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6788 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6788 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6788.

Lemma collineation_6789 : is_collineation fp_6789 fl_6789.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6789 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6789 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6789.

Lemma collineation_6790 : is_collineation fp_6790 fl_6790.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6790 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6790 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6790.

Lemma collineation_6791 : is_collineation fp_6791 fl_6791.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6791 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6791 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6791.

Lemma collineation_6792 : is_collineation fp_6792 fl_6792.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6792 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6792 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6792.

Lemma collineation_6793 : is_collineation fp_6793 fl_6793.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6793 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6793 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6793.

Lemma collineation_6794 : is_collineation fp_6794 fl_6794.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6794 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6794 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6794.

Lemma collineation_6795 : is_collineation fp_6795 fl_6795.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6795 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6795 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6795.

Lemma collineation_6796 : is_collineation fp_6796 fl_6796.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6796 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6796 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6796.

Lemma collineation_6797 : is_collineation fp_6797 fl_6797.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6797 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6797 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6797.

Lemma collineation_6798 : is_collineation fp_6798 fl_6798.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6798 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6798 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6798.

Lemma collineation_6799 : is_collineation fp_6799 fl_6799.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6799 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6799 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6799.

Lemma collineation_6800 : is_collineation fp_6800 fl_6800.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6800 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6800 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6800.

Lemma collineation_6801 : is_collineation fp_6801 fl_6801.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6801 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6801 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6801.

Lemma collineation_6802 : is_collineation fp_6802 fl_6802.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6802 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6802 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6802.

Lemma collineation_6803 : is_collineation fp_6803 fl_6803.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6803 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6803 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6803.

Lemma collineation_6804 : is_collineation fp_6804 fl_6804.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6804 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6804 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6804.

Lemma collineation_6805 : is_collineation fp_6805 fl_6805.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6805 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6805 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6805.

Lemma collineation_6806 : is_collineation fp_6806 fl_6806.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6806 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6806 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6806.

Lemma collineation_6807 : is_collineation fp_6807 fl_6807.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6807 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6807 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6807.

Lemma collineation_6808 : is_collineation fp_6808 fl_6808.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6808 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6808 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6808.

Lemma collineation_6809 : is_collineation fp_6809 fl_6809.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6809 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6809 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6809.

Lemma collineation_6810 : is_collineation fp_6810 fl_6810.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6810 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6810 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6810.

Lemma collineation_6811 : is_collineation fp_6811 fl_6811.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6811 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6811 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6811.

Lemma collineation_6812 : is_collineation fp_6812 fl_6812.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6812 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6812 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6812.

Lemma collineation_6813 : is_collineation fp_6813 fl_6813.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6813 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6813 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6813.

Lemma collineation_6814 : is_collineation fp_6814 fl_6814.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6814 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6814 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6814.

Lemma collineation_6815 : is_collineation fp_6815 fl_6815.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6815 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6815 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6815.

Lemma collineation_6816 : is_collineation fp_6816 fl_6816.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6816 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6816 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6816.

Lemma collineation_6817 : is_collineation fp_6817 fl_6817.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6817 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6817 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6817.

Lemma collineation_6818 : is_collineation fp_6818 fl_6818.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6818 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6818 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6818.

Lemma collineation_6819 : is_collineation fp_6819 fl_6819.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6819 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6819 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6819.

Lemma collineation_6820 : is_collineation fp_6820 fl_6820.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6820 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6820 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6820.

Lemma collineation_6821 : is_collineation fp_6821 fl_6821.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6821 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6821 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6821.

Lemma collineation_6822 : is_collineation fp_6822 fl_6822.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6822 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6822 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6822.

Lemma collineation_6823 : is_collineation fp_6823 fl_6823.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6823 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6823 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6823.

Lemma collineation_6824 : is_collineation fp_6824 fl_6824.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6824 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6824 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6824.

Lemma collineation_6825 : is_collineation fp_6825 fl_6825.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6825 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6825 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6825.

Lemma collineation_6826 : is_collineation fp_6826 fl_6826.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6826 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6826 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6826.

Lemma collineation_6827 : is_collineation fp_6827 fl_6827.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6827 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6827 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6827.

Lemma collineation_6828 : is_collineation fp_6828 fl_6828.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6828 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6828 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6828.

Lemma collineation_6829 : is_collineation fp_6829 fl_6829.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6829 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6829 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6829.

Lemma collineation_6830 : is_collineation fp_6830 fl_6830.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6830 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6830 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6830.

Lemma collineation_6831 : is_collineation fp_6831 fl_6831.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6831 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6831 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6831.

Lemma collineation_6832 : is_collineation fp_6832 fl_6832.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6832 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6832 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6832.

Lemma collineation_6833 : is_collineation fp_6833 fl_6833.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6833 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6833 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6833.

Lemma collineation_6834 : is_collineation fp_6834 fl_6834.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6834 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6834 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6834.

Lemma collineation_6835 : is_collineation fp_6835 fl_6835.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6835 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6835 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6835.

Lemma collineation_6836 : is_collineation fp_6836 fl_6836.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6836 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6836 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6836.

Lemma collineation_6837 : is_collineation fp_6837 fl_6837.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6837 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6837 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6837.

Lemma collineation_6838 : is_collineation fp_6838 fl_6838.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6838 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6838 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6838.

Lemma collineation_6839 : is_collineation fp_6839 fl_6839.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6839 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6839 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6839.

Lemma collineation_6840 : is_collineation fp_6840 fl_6840.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6840 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6840 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6840.

Lemma collineation_6841 : is_collineation fp_6841 fl_6841.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6841 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6841 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6841.

Lemma collineation_6842 : is_collineation fp_6842 fl_6842.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6842 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6842 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6842.

Lemma collineation_6843 : is_collineation fp_6843 fl_6843.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6843 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6843 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6843.

Lemma collineation_6844 : is_collineation fp_6844 fl_6844.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6844 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6844 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6844.

Lemma collineation_6845 : is_collineation fp_6845 fl_6845.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6845 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6845 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6845.

Lemma collineation_6846 : is_collineation fp_6846 fl_6846.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6846 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6846 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6846.

Lemma collineation_6847 : is_collineation fp_6847 fl_6847.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6847 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6847 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6847.

Lemma collineation_6848 : is_collineation fp_6848 fl_6848.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6848 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6848 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6848.

Lemma collineation_6849 : is_collineation fp_6849 fl_6849.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6849 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6849 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6849.

Lemma collineation_6850 : is_collineation fp_6850 fl_6850.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6850 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6850 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6850.

Lemma collineation_6851 : is_collineation fp_6851 fl_6851.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6851 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6851 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6851.

Lemma collineation_6852 : is_collineation fp_6852 fl_6852.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6852 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6852 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6852.

Lemma collineation_6853 : is_collineation fp_6853 fl_6853.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6853 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6853 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6853.

Lemma collineation_6854 : is_collineation fp_6854 fl_6854.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6854 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6854 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6854.

Lemma collineation_6855 : is_collineation fp_6855 fl_6855.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6855 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6855 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6855.

Lemma collineation_6856 : is_collineation fp_6856 fl_6856.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6856 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6856 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6856.

Lemma collineation_6857 : is_collineation fp_6857 fl_6857.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6857 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6857 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6857.

Lemma collineation_6858 : is_collineation fp_6858 fl_6858.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6858 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6858 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6858.

Lemma collineation_6859 : is_collineation fp_6859 fl_6859.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6859 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6859 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6859.

Lemma collineation_6860 : is_collineation fp_6860 fl_6860.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6860 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6860 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6860.

Lemma collineation_6861 : is_collineation fp_6861 fl_6861.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6861 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6861 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6861.

Lemma collineation_6862 : is_collineation fp_6862 fl_6862.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6862 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6862 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6862.

Lemma collineation_6863 : is_collineation fp_6863 fl_6863.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6863 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6863 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6863.

Lemma collineation_6864 : is_collineation fp_6864 fl_6864.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6864 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6864 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6864.

Lemma collineation_6865 : is_collineation fp_6865 fl_6865.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6865 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6865 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6865.

Lemma collineation_6866 : is_collineation fp_6866 fl_6866.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6866 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6866 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6866.

Lemma collineation_6867 : is_collineation fp_6867 fl_6867.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6867 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6867 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6867.

Lemma collineation_6868 : is_collineation fp_6868 fl_6868.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6868 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6868 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6868.

Lemma collineation_6869 : is_collineation fp_6869 fl_6869.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6869 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6869 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6869.

Lemma collineation_6870 : is_collineation fp_6870 fl_6870.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6870 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6870 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6870.

Lemma collineation_6871 : is_collineation fp_6871 fl_6871.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6871 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6871 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6871.

Lemma collineation_6872 : is_collineation fp_6872 fl_6872.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6872 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6872 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6872.

Lemma collineation_6873 : is_collineation fp_6873 fl_6873.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6873 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6873 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6873.

Lemma collineation_6874 : is_collineation fp_6874 fl_6874.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6874 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6874 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6874.

Lemma collineation_6875 : is_collineation fp_6875 fl_6875.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6875 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6875 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6875.

Lemma collineation_6876 : is_collineation fp_6876 fl_6876.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6876 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6876 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6876.

Lemma collineation_6877 : is_collineation fp_6877 fl_6877.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6877 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6877 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6877.

Lemma collineation_6878 : is_collineation fp_6878 fl_6878.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6878 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6878 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6878.

Lemma collineation_6879 : is_collineation fp_6879 fl_6879.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6879 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6879 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6879.

Lemma collineation_6880 : is_collineation fp_6880 fl_6880.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6880 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6880 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6880.

Lemma collineation_6881 : is_collineation fp_6881 fl_6881.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6881 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6881 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6881.

Lemma collineation_6882 : is_collineation fp_6882 fl_6882.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6882 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6882 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6882.

Lemma collineation_6883 : is_collineation fp_6883 fl_6883.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6883 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6883 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6883.

Lemma collineation_6884 : is_collineation fp_6884 fl_6884.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6884 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6884 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6884.

Lemma collineation_6885 : is_collineation fp_6885 fl_6885.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6885 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6885 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6885.

Lemma collineation_6886 : is_collineation fp_6886 fl_6886.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6886 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6886 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6886.

Lemma collineation_6887 : is_collineation fp_6887 fl_6887.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6887 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6887 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6887.

Lemma collineation_6888 : is_collineation fp_6888 fl_6888.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6888 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6888 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6888.

Lemma collineation_6889 : is_collineation fp_6889 fl_6889.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6889 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6889 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6889.

Lemma collineation_6890 : is_collineation fp_6890 fl_6890.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6890 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6890 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6890.

Lemma collineation_6891 : is_collineation fp_6891 fl_6891.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6891 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6891 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6891.

Lemma collineation_6892 : is_collineation fp_6892 fl_6892.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6892 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6892 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6892.

Lemma collineation_6893 : is_collineation fp_6893 fl_6893.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6893 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6893 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6893.

Lemma collineation_6894 : is_collineation fp_6894 fl_6894.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6894 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6894 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6894.

Lemma collineation_6895 : is_collineation fp_6895 fl_6895.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6895 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6895 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6895.

Lemma collineation_6896 : is_collineation fp_6896 fl_6896.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6896 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6896 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6896.

Lemma collineation_6897 : is_collineation fp_6897 fl_6897.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6897 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6897 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6897.

Lemma collineation_6898 : is_collineation fp_6898 fl_6898.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6898 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6898 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6898.

Lemma collineation_6899 : is_collineation fp_6899 fl_6899.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6899 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6899 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6899.

Lemma collineation_6900 : is_collineation fp_6900 fl_6900.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6900 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6900 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6900.

Lemma collineation_6901 : is_collineation fp_6901 fl_6901.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6901 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6901 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6901.

Lemma collineation_6902 : is_collineation fp_6902 fl_6902.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6902 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6902 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6902.

Lemma collineation_6903 : is_collineation fp_6903 fl_6903.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6903 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6903 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6903.

Lemma collineation_6904 : is_collineation fp_6904 fl_6904.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6904 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6904 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6904.

Lemma collineation_6905 : is_collineation fp_6905 fl_6905.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6905 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6905 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6905.

Lemma collineation_6906 : is_collineation fp_6906 fl_6906.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6906 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6906 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6906.

Lemma collineation_6907 : is_collineation fp_6907 fl_6907.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6907 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6907 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6907.

Lemma collineation_6908 : is_collineation fp_6908 fl_6908.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6908 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6908 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6908.

Lemma collineation_6909 : is_collineation fp_6909 fl_6909.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6909 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6909 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6909.

Lemma collineation_6910 : is_collineation fp_6910 fl_6910.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6910 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6910 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6910.

Lemma collineation_6911 : is_collineation fp_6911 fl_6911.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6911 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6911 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6911.

Lemma collineation_6912 : is_collineation fp_6912 fl_6912.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6912 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6912 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6912.

Lemma collineation_6913 : is_collineation fp_6913 fl_6913.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6913 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6913 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6913.

Lemma collineation_6914 : is_collineation fp_6914 fl_6914.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6914 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6914 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6914.

Lemma collineation_6915 : is_collineation fp_6915 fl_6915.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6915 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6915 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6915.

Lemma collineation_6916 : is_collineation fp_6916 fl_6916.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6916 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6916 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6916.

Lemma collineation_6917 : is_collineation fp_6917 fl_6917.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6917 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6917 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6917.

Lemma collineation_6918 : is_collineation fp_6918 fl_6918.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6918 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6918 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6918.

Lemma collineation_6919 : is_collineation fp_6919 fl_6919.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6919 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6919 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6919.

Lemma collineation_6920 : is_collineation fp_6920 fl_6920.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6920 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6920 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6920.

Lemma collineation_6921 : is_collineation fp_6921 fl_6921.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6921 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6921 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6921.

Lemma collineation_6922 : is_collineation fp_6922 fl_6922.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6922 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6922 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6922.

Lemma collineation_6923 : is_collineation fp_6923 fl_6923.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6923 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6923 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6923.

Lemma collineation_6924 : is_collineation fp_6924 fl_6924.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6924 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6924 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6924.

Lemma collineation_6925 : is_collineation fp_6925 fl_6925.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6925 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6925 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6925.

Lemma collineation_6926 : is_collineation fp_6926 fl_6926.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6926 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6926 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6926.

Lemma collineation_6927 : is_collineation fp_6927 fl_6927.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6927 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6927 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6927.

Lemma collineation_6928 : is_collineation fp_6928 fl_6928.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6928 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6928 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6928.

Lemma collineation_6929 : is_collineation fp_6929 fl_6929.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6929 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6929 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6929.

Lemma collineation_6930 : is_collineation fp_6930 fl_6930.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6930 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6930 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6930.

Lemma collineation_6931 : is_collineation fp_6931 fl_6931.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6931 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6931 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6931.

Lemma collineation_6932 : is_collineation fp_6932 fl_6932.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6932 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6932 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6932.

Lemma collineation_6933 : is_collineation fp_6933 fl_6933.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6933 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6933 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6933.

Lemma collineation_6934 : is_collineation fp_6934 fl_6934.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6934 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6934 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6934.

Lemma collineation_6935 : is_collineation fp_6935 fl_6935.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6935 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6935 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6935.

Lemma collineation_6936 : is_collineation fp_6936 fl_6936.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6936 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6936 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6936.

Lemma collineation_6937 : is_collineation fp_6937 fl_6937.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6937 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6937 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6937.

Lemma collineation_6938 : is_collineation fp_6938 fl_6938.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6938 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6938 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6938.

Lemma collineation_6939 : is_collineation fp_6939 fl_6939.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6939 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6939 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6939.

Lemma collineation_6940 : is_collineation fp_6940 fl_6940.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6940 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6940 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6940.

Lemma collineation_6941 : is_collineation fp_6941 fl_6941.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6941 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6941 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6941.

Lemma collineation_6942 : is_collineation fp_6942 fl_6942.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6942 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6942 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6942.

Lemma collineation_6943 : is_collineation fp_6943 fl_6943.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6943 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6943 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6943.

Lemma collineation_6944 : is_collineation fp_6944 fl_6944.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6944 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6944 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6944.

Lemma collineation_6945 : is_collineation fp_6945 fl_6945.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6945 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6945 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6945.

Lemma collineation_6946 : is_collineation fp_6946 fl_6946.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6946 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6946 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6946.

Lemma collineation_6947 : is_collineation fp_6947 fl_6947.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6947 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6947 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6947.

Lemma collineation_6948 : is_collineation fp_6948 fl_6948.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6948 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6948 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6948.

Lemma collineation_6949 : is_collineation fp_6949 fl_6949.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6949 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6949 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6949.

Lemma collineation_6950 : is_collineation fp_6950 fl_6950.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6950 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6950 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6950.

Lemma collineation_6951 : is_collineation fp_6951 fl_6951.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6951 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6951 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6951.

Lemma collineation_6952 : is_collineation fp_6952 fl_6952.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6952 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6952 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6952.

Lemma collineation_6953 : is_collineation fp_6953 fl_6953.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6953 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6953 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6953.

Lemma collineation_6954 : is_collineation fp_6954 fl_6954.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6954 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6954 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6954.

Lemma collineation_6955 : is_collineation fp_6955 fl_6955.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6955 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6955 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6955.

Lemma collineation_6956 : is_collineation fp_6956 fl_6956.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6956 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6956 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6956.

Lemma collineation_6957 : is_collineation fp_6957 fl_6957.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6957 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6957 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6957.

Lemma collineation_6958 : is_collineation fp_6958 fl_6958.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6958 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6958 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6958.

Lemma collineation_6959 : is_collineation fp_6959 fl_6959.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6959 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6959 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6959.

Lemma collineation_6960 : is_collineation fp_6960 fl_6960.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6960 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6960 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6960.

Lemma collineation_6961 : is_collineation fp_6961 fl_6961.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6961 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6961 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6961.

Lemma collineation_6962 : is_collineation fp_6962 fl_6962.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6962 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6962 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6962.

Lemma collineation_6963 : is_collineation fp_6963 fl_6963.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6963 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6963 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6963.

Lemma collineation_6964 : is_collineation fp_6964 fl_6964.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6964 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6964 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6964.

Lemma collineation_6965 : is_collineation fp_6965 fl_6965.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6965 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6965 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6965.

Lemma collineation_6966 : is_collineation fp_6966 fl_6966.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6966 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6966 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6966.

Lemma collineation_6967 : is_collineation fp_6967 fl_6967.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6967 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6967 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6967.

Lemma collineation_6968 : is_collineation fp_6968 fl_6968.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6968 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6968 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6968.

Lemma collineation_6969 : is_collineation fp_6969 fl_6969.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6969 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6969 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6969.

Lemma collineation_6970 : is_collineation fp_6970 fl_6970.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6970 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6970 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6970.

Lemma collineation_6971 : is_collineation fp_6971 fl_6971.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6971 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6971 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6971.

Lemma collineation_6972 : is_collineation fp_6972 fl_6972.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6972 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6972 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6972.

Lemma collineation_6973 : is_collineation fp_6973 fl_6973.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6973 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6973 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6973.

Lemma collineation_6974 : is_collineation fp_6974 fl_6974.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6974 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6974 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6974.

Lemma collineation_6975 : is_collineation fp_6975 fl_6975.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6975 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6975 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6975.

Lemma collineation_6976 : is_collineation fp_6976 fl_6976.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6976 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6976 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6976.

Lemma collineation_6977 : is_collineation fp_6977 fl_6977.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6977 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6977 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6977.

Lemma collineation_6978 : is_collineation fp_6978 fl_6978.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6978 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6978 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6978.

Lemma collineation_6979 : is_collineation fp_6979 fl_6979.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6979 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6979 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6979.

Lemma collineation_6980 : is_collineation fp_6980 fl_6980.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6980 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6980 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6980.

Lemma collineation_6981 : is_collineation fp_6981 fl_6981.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6981 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6981 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6981.

Lemma collineation_6982 : is_collineation fp_6982 fl_6982.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6982 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6982 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6982.

Lemma collineation_6983 : is_collineation fp_6983 fl_6983.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6983 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6983 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6983.

Lemma collineation_6984 : is_collineation fp_6984 fl_6984.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6984 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6984 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6984.

Lemma collineation_6985 : is_collineation fp_6985 fl_6985.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6985 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6985 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6985.

Lemma collineation_6986 : is_collineation fp_6986 fl_6986.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6986 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6986 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6986.

Lemma collineation_6987 : is_collineation fp_6987 fl_6987.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6987 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6987 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6987.

Lemma collineation_6988 : is_collineation fp_6988 fl_6988.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6988 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6988 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6988.

Lemma collineation_6989 : is_collineation fp_6989 fl_6989.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6989 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6989 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6989.

Lemma collineation_6990 : is_collineation fp_6990 fl_6990.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6990 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6990 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6990.

Lemma collineation_6991 : is_collineation fp_6991 fl_6991.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6991 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6991 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6991.

Lemma collineation_6992 : is_collineation fp_6992 fl_6992.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6992 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6992 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6992.

Lemma collineation_6993 : is_collineation fp_6993 fl_6993.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6993 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6993 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6993.

Lemma collineation_6994 : is_collineation fp_6994 fl_6994.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6994 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6994 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6994.

Lemma collineation_6995 : is_collineation fp_6995 fl_6995.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6995 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6995 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6995.

Lemma collineation_6996 : is_collineation fp_6996 fl_6996.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6996 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6996 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6996.

Lemma collineation_6997 : is_collineation fp_6997 fl_6997.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6997 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6997 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6997.

Lemma collineation_6998 : is_collineation fp_6998 fl_6998.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6998 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6998 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6998.

Lemma collineation_6999 : is_collineation fp_6999 fl_6999.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6999 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6999 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6999.

Lemma collineation_7000 : is_collineation fp_7000 fl_7000.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7000 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7000 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7000.

Lemma collineation_7001 : is_collineation fp_7001 fl_7001.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7001 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7001 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7001.

Lemma collineation_7002 : is_collineation fp_7002 fl_7002.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7002 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7002 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7002.

Lemma collineation_7003 : is_collineation fp_7003 fl_7003.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7003 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7003 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7003.

Lemma collineation_7004 : is_collineation fp_7004 fl_7004.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7004 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7004 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7004.

Lemma collineation_7005 : is_collineation fp_7005 fl_7005.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7005 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7005 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7005.

Lemma collineation_7006 : is_collineation fp_7006 fl_7006.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7006 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7006 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7006.

Lemma collineation_7007 : is_collineation fp_7007 fl_7007.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7007 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7007 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7007.

Lemma collineation_7008 : is_collineation fp_7008 fl_7008.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7008 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7008 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7008.

Lemma collineation_7009 : is_collineation fp_7009 fl_7009.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7009 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7009 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7009.

Lemma collineation_7010 : is_collineation fp_7010 fl_7010.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7010 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7010 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7010.

Lemma collineation_7011 : is_collineation fp_7011 fl_7011.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7011 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7011 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7011.

Lemma collineation_7012 : is_collineation fp_7012 fl_7012.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7012 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7012 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7012.

Lemma collineation_7013 : is_collineation fp_7013 fl_7013.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7013 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7013 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7013.

Lemma collineation_7014 : is_collineation fp_7014 fl_7014.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7014 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7014 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7014.

Lemma collineation_7015 : is_collineation fp_7015 fl_7015.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7015 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7015 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7015.

Lemma collineation_7016 : is_collineation fp_7016 fl_7016.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7016 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7016 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7016.

Lemma collineation_7017 : is_collineation fp_7017 fl_7017.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7017 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7017 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7017.

Lemma collineation_7018 : is_collineation fp_7018 fl_7018.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7018 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7018 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7018.

Lemma collineation_7019 : is_collineation fp_7019 fl_7019.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7019 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7019 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7019.

Lemma collineation_7020 : is_collineation fp_7020 fl_7020.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7020 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7020 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7020.

Lemma collineation_7021 : is_collineation fp_7021 fl_7021.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7021 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7021 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7021.

Lemma collineation_7022 : is_collineation fp_7022 fl_7022.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7022 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7022 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7022.

Lemma collineation_7023 : is_collineation fp_7023 fl_7023.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7023 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7023 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7023.

Lemma collineation_7024 : is_collineation fp_7024 fl_7024.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7024 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7024 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7024.

Lemma collineation_7025 : is_collineation fp_7025 fl_7025.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7025 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7025 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7025.

Lemma collineation_7026 : is_collineation fp_7026 fl_7026.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7026 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7026 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7026.

Lemma collineation_7027 : is_collineation fp_7027 fl_7027.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7027 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7027 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7027.

Lemma collineation_7028 : is_collineation fp_7028 fl_7028.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7028 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7028 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7028.

Lemma collineation_7029 : is_collineation fp_7029 fl_7029.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7029 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7029 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7029.

Lemma collineation_7030 : is_collineation fp_7030 fl_7030.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7030 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7030 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7030.

Lemma collineation_7031 : is_collineation fp_7031 fl_7031.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7031 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7031 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7031.

Lemma collineation_7032 : is_collineation fp_7032 fl_7032.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7032 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7032 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7032.

Lemma collineation_7033 : is_collineation fp_7033 fl_7033.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7033 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7033 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7033.

Lemma collineation_7034 : is_collineation fp_7034 fl_7034.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7034 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7034 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7034.

Lemma collineation_7035 : is_collineation fp_7035 fl_7035.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7035 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7035 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7035.

Lemma collineation_7036 : is_collineation fp_7036 fl_7036.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7036 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7036 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7036.

Lemma collineation_7037 : is_collineation fp_7037 fl_7037.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7037 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7037 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7037.

Lemma collineation_7038 : is_collineation fp_7038 fl_7038.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7038 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7038 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7038.

Lemma collineation_7039 : is_collineation fp_7039 fl_7039.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7039 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7039 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7039.

Lemma collineation_7040 : is_collineation fp_7040 fl_7040.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7040 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7040 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7040.

Lemma collineation_7041 : is_collineation fp_7041 fl_7041.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7041 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7041 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7041.

Lemma collineation_7042 : is_collineation fp_7042 fl_7042.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7042 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7042 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7042.

Lemma collineation_7043 : is_collineation fp_7043 fl_7043.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7043 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7043 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7043.

Lemma collineation_7044 : is_collineation fp_7044 fl_7044.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7044 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7044 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7044.

Lemma collineation_7045 : is_collineation fp_7045 fl_7045.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7045 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7045 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7045.

Lemma collineation_7046 : is_collineation fp_7046 fl_7046.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7046 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7046 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7046.

Lemma collineation_7047 : is_collineation fp_7047 fl_7047.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7047 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7047 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7047.

Lemma collineation_7048 : is_collineation fp_7048 fl_7048.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7048 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7048 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7048.

Lemma collineation_7049 : is_collineation fp_7049 fl_7049.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7049 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7049 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7049.

Lemma collineation_7050 : is_collineation fp_7050 fl_7050.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7050 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7050 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7050.

Lemma collineation_7051 : is_collineation fp_7051 fl_7051.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7051 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7051 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7051.

Lemma collineation_7052 : is_collineation fp_7052 fl_7052.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7052 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7052 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7052.

Lemma collineation_7053 : is_collineation fp_7053 fl_7053.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7053 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7053 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7053.

Lemma collineation_7054 : is_collineation fp_7054 fl_7054.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7054 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7054 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7054.

Lemma collineation_7055 : is_collineation fp_7055 fl_7055.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7055 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7055 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7055.

Lemma collineation_7056 : is_collineation fp_7056 fl_7056.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7056 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7056 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7056.

Lemma collineation_7057 : is_collineation fp_7057 fl_7057.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7057 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7057 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7057.

Lemma collineation_7058 : is_collineation fp_7058 fl_7058.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7058 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7058 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7058.

Lemma collineation_7059 : is_collineation fp_7059 fl_7059.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7059 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7059 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7059.

Lemma collineation_7060 : is_collineation fp_7060 fl_7060.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7060 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7060 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7060.

Lemma collineation_7061 : is_collineation fp_7061 fl_7061.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7061 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7061 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7061.

Lemma collineation_7062 : is_collineation fp_7062 fl_7062.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7062 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7062 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7062.

Lemma collineation_7063 : is_collineation fp_7063 fl_7063.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7063 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7063 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7063.

Lemma collineation_7064 : is_collineation fp_7064 fl_7064.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7064 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7064 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7064.

Lemma collineation_7065 : is_collineation fp_7065 fl_7065.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7065 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7065 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7065.

Lemma collineation_7066 : is_collineation fp_7066 fl_7066.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7066 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7066 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7066.

Lemma collineation_7067 : is_collineation fp_7067 fl_7067.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7067 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7067 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7067.

Lemma collineation_7068 : is_collineation fp_7068 fl_7068.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7068 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7068 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7068.

Lemma collineation_7069 : is_collineation fp_7069 fl_7069.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7069 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7069 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7069.

Lemma collineation_7070 : is_collineation fp_7070 fl_7070.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7070 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7070 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7070.

Lemma collineation_7071 : is_collineation fp_7071 fl_7071.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7071 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7071 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7071.

Lemma collineation_7072 : is_collineation fp_7072 fl_7072.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7072 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7072 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7072.

Lemma collineation_7073 : is_collineation fp_7073 fl_7073.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7073 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7073 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7073.

Lemma collineation_7074 : is_collineation fp_7074 fl_7074.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7074 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7074 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7074.

Lemma collineation_7075 : is_collineation fp_7075 fl_7075.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7075 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7075 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7075.

Lemma collineation_7076 : is_collineation fp_7076 fl_7076.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7076 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7076 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7076.

Lemma collineation_7077 : is_collineation fp_7077 fl_7077.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7077 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7077 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7077.

Lemma collineation_7078 : is_collineation fp_7078 fl_7078.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7078 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7078 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7078.

Lemma collineation_7079 : is_collineation fp_7079 fl_7079.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7079 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7079 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7079.

Lemma collineation_7080 : is_collineation fp_7080 fl_7080.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7080 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7080 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7080.

Lemma collineation_7081 : is_collineation fp_7081 fl_7081.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7081 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7081 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7081.

Lemma collineation_7082 : is_collineation fp_7082 fl_7082.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7082 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7082 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7082.

Lemma collineation_7083 : is_collineation fp_7083 fl_7083.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7083 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7083 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7083.

Lemma collineation_7084 : is_collineation fp_7084 fl_7084.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7084 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7084 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7084.

Lemma collineation_7085 : is_collineation fp_7085 fl_7085.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7085 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7085 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7085.

Lemma collineation_7086 : is_collineation fp_7086 fl_7086.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7086 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7086 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7086.

Lemma collineation_7087 : is_collineation fp_7087 fl_7087.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7087 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7087 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7087.

Lemma collineation_7088 : is_collineation fp_7088 fl_7088.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7088 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7088 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7088.

Lemma collineation_7089 : is_collineation fp_7089 fl_7089.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7089 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7089 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7089.

Lemma collineation_7090 : is_collineation fp_7090 fl_7090.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7090 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7090 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7090.

Lemma collineation_7091 : is_collineation fp_7091 fl_7091.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7091 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7091 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7091.

Lemma collineation_7092 : is_collineation fp_7092 fl_7092.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7092 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7092 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7092.

Lemma collineation_7093 : is_collineation fp_7093 fl_7093.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7093 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7093 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7093.

Lemma collineation_7094 : is_collineation fp_7094 fl_7094.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7094 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7094 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7094.

Lemma collineation_7095 : is_collineation fp_7095 fl_7095.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7095 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7095 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7095.

Lemma collineation_7096 : is_collineation fp_7096 fl_7096.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7096 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7096 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7096.

Lemma collineation_7097 : is_collineation fp_7097 fl_7097.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7097 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7097 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7097.

Lemma collineation_7098 : is_collineation fp_7098 fl_7098.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7098 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7098 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7098.

Lemma collineation_7099 : is_collineation fp_7099 fl_7099.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7099 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7099 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7099.

Lemma collineation_7100 : is_collineation fp_7100 fl_7100.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7100 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7100 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7100.

Lemma collineation_7101 : is_collineation fp_7101 fl_7101.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7101 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7101 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7101.

Lemma collineation_7102 : is_collineation fp_7102 fl_7102.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7102 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7102 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7102.

Lemma collineation_7103 : is_collineation fp_7103 fl_7103.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7103 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7103 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7103.

Lemma collineation_7104 : is_collineation fp_7104 fl_7104.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7104 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7104 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7104.

Lemma collineation_7105 : is_collineation fp_7105 fl_7105.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7105 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7105 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7105.

Lemma collineation_7106 : is_collineation fp_7106 fl_7106.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7106 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7106 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7106.

Lemma collineation_7107 : is_collineation fp_7107 fl_7107.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7107 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7107 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7107.

Lemma collineation_7108 : is_collineation fp_7108 fl_7108.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7108 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7108 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7108.

Lemma collineation_7109 : is_collineation fp_7109 fl_7109.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7109 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7109 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7109.

Lemma collineation_7110 : is_collineation fp_7110 fl_7110.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7110 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7110 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7110.

Lemma collineation_7111 : is_collineation fp_7111 fl_7111.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7111 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7111 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7111.

Lemma collineation_7112 : is_collineation fp_7112 fl_7112.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7112 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7112 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7112.

Lemma collineation_7113 : is_collineation fp_7113 fl_7113.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7113 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7113 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7113.

Lemma collineation_7114 : is_collineation fp_7114 fl_7114.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7114 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7114 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7114.

Lemma collineation_7115 : is_collineation fp_7115 fl_7115.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7115 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7115 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7115.

Lemma collineation_7116 : is_collineation fp_7116 fl_7116.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7116 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7116 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7116.

Lemma collineation_7117 : is_collineation fp_7117 fl_7117.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7117 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7117 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7117.

Lemma collineation_7118 : is_collineation fp_7118 fl_7118.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7118 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7118 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7118.

Lemma collineation_7119 : is_collineation fp_7119 fl_7119.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7119 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7119 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7119.

Lemma collineation_7120 : is_collineation fp_7120 fl_7120.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7120 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7120 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7120.

Lemma collineation_7121 : is_collineation fp_7121 fl_7121.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7121 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7121 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7121.

Lemma collineation_7122 : is_collineation fp_7122 fl_7122.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7122 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7122 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7122.

Lemma collineation_7123 : is_collineation fp_7123 fl_7123.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7123 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7123 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7123.

Lemma collineation_7124 : is_collineation fp_7124 fl_7124.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7124 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7124 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7124.

Lemma collineation_7125 : is_collineation fp_7125 fl_7125.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7125 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7125 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7125.

Lemma collineation_7126 : is_collineation fp_7126 fl_7126.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7126 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7126 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7126.

Lemma collineation_7127 : is_collineation fp_7127 fl_7127.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7127 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7127 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7127.

Lemma collineation_7128 : is_collineation fp_7128 fl_7128.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7128 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7128 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7128.

Lemma collineation_7129 : is_collineation fp_7129 fl_7129.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7129 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7129 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7129.

Lemma collineation_7130 : is_collineation fp_7130 fl_7130.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7130 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7130 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7130.

Lemma collineation_7131 : is_collineation fp_7131 fl_7131.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7131 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7131 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7131.

Lemma collineation_7132 : is_collineation fp_7132 fl_7132.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7132 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7132 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7132.

Lemma collineation_7133 : is_collineation fp_7133 fl_7133.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7133 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7133 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7133.

Lemma collineation_7134 : is_collineation fp_7134 fl_7134.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7134 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7134 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7134.

Lemma collineation_7135 : is_collineation fp_7135 fl_7135.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7135 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7135 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7135.

Lemma collineation_7136 : is_collineation fp_7136 fl_7136.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7136 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7136 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7136.

Lemma collineation_7137 : is_collineation fp_7137 fl_7137.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7137 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7137 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7137.

Lemma collineation_7138 : is_collineation fp_7138 fl_7138.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7138 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7138 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7138.

Lemma collineation_7139 : is_collineation fp_7139 fl_7139.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7139 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7139 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7139.

Lemma collineation_7140 : is_collineation fp_7140 fl_7140.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7140 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7140 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7140.

Lemma collineation_7141 : is_collineation fp_7141 fl_7141.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7141 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7141 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7141.

Lemma collineation_7142 : is_collineation fp_7142 fl_7142.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7142 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7142 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7142.

Lemma collineation_7143 : is_collineation fp_7143 fl_7143.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7143 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7143 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7143.

Lemma collineation_7144 : is_collineation fp_7144 fl_7144.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7144 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7144 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7144.

Lemma collineation_7145 : is_collineation fp_7145 fl_7145.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7145 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7145 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7145.

Lemma collineation_7146 : is_collineation fp_7146 fl_7146.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7146 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7146 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7146.

Lemma collineation_7147 : is_collineation fp_7147 fl_7147.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7147 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7147 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7147.

Lemma collineation_7148 : is_collineation fp_7148 fl_7148.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7148 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7148 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7148.

Lemma collineation_7149 : is_collineation fp_7149 fl_7149.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7149 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7149 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7149.

Lemma collineation_7150 : is_collineation fp_7150 fl_7150.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7150 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7150 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7150.

Lemma collineation_7151 : is_collineation fp_7151 fl_7151.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7151 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7151 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7151.

Lemma collineation_7152 : is_collineation fp_7152 fl_7152.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7152 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7152 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7152.

Lemma collineation_7153 : is_collineation fp_7153 fl_7153.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7153 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7153 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7153.

Lemma collineation_7154 : is_collineation fp_7154 fl_7154.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7154 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7154 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7154.

Lemma collineation_7155 : is_collineation fp_7155 fl_7155.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7155 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7155 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7155.

Lemma collineation_7156 : is_collineation fp_7156 fl_7156.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7156 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7156 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7156.

Lemma collineation_7157 : is_collineation fp_7157 fl_7157.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7157 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7157 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7157.

Lemma collineation_7158 : is_collineation fp_7158 fl_7158.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7158 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7158 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7158.

Lemma collineation_7159 : is_collineation fp_7159 fl_7159.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7159 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7159 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7159.

Lemma collineation_7160 : is_collineation fp_7160 fl_7160.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7160 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7160 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7160.

Lemma collineation_7161 : is_collineation fp_7161 fl_7161.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7161 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7161 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7161.

Lemma collineation_7162 : is_collineation fp_7162 fl_7162.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7162 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7162 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7162.

Lemma collineation_7163 : is_collineation fp_7163 fl_7163.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7163 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7163 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7163.

Lemma collineation_7164 : is_collineation fp_7164 fl_7164.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7164 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7164 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7164.

Lemma collineation_7165 : is_collineation fp_7165 fl_7165.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7165 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7165 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7165.

Lemma collineation_7166 : is_collineation fp_7166 fl_7166.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7166 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7166 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7166.

Lemma collineation_7167 : is_collineation fp_7167 fl_7167.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7167 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7167 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7167.

Lemma collineation_7168 : is_collineation fp_7168 fl_7168.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7168 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7168 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7168.

Lemma collineation_7169 : is_collineation fp_7169 fl_7169.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7169 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7169 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7169.

Lemma collineation_7170 : is_collineation fp_7170 fl_7170.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7170 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7170 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7170.

Lemma collineation_7171 : is_collineation fp_7171 fl_7171.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7171 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7171 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7171.

Lemma collineation_7172 : is_collineation fp_7172 fl_7172.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7172 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7172 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7172.

Lemma collineation_7173 : is_collineation fp_7173 fl_7173.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7173 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7173 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7173.

Lemma collineation_7174 : is_collineation fp_7174 fl_7174.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7174 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7174 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7174.

Lemma collineation_7175 : is_collineation fp_7175 fl_7175.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7175 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7175 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7175.

Lemma collineation_7176 : is_collineation fp_7176 fl_7176.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7176 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7176 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7176.

Lemma collineation_7177 : is_collineation fp_7177 fl_7177.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7177 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7177 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7177.

Lemma collineation_7178 : is_collineation fp_7178 fl_7178.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7178 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7178 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7178.

Lemma collineation_7179 : is_collineation fp_7179 fl_7179.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7179 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7179 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7179.

Lemma collineation_7180 : is_collineation fp_7180 fl_7180.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7180 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7180 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7180.

Lemma collineation_7181 : is_collineation fp_7181 fl_7181.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7181 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7181 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7181.

Lemma collineation_7182 : is_collineation fp_7182 fl_7182.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7182 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7182 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7182.

Lemma collineation_7183 : is_collineation fp_7183 fl_7183.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7183 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7183 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7183.

Lemma collineation_7184 : is_collineation fp_7184 fl_7184.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7184 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7184 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7184.

Lemma collineation_7185 : is_collineation fp_7185 fl_7185.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7185 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7185 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7185.

Lemma collineation_7186 : is_collineation fp_7186 fl_7186.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7186 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7186 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7186.

Lemma collineation_7187 : is_collineation fp_7187 fl_7187.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7187 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7187 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7187.

Lemma collineation_7188 : is_collineation fp_7188 fl_7188.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7188 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7188 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7188.

Lemma collineation_7189 : is_collineation fp_7189 fl_7189.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7189 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7189 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7189.

Lemma collineation_7190 : is_collineation fp_7190 fl_7190.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7190 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7190 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7190.

Lemma collineation_7191 : is_collineation fp_7191 fl_7191.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7191 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7191 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7191.

Lemma collineation_7192 : is_collineation fp_7192 fl_7192.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7192 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7192 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7192.

Lemma collineation_7193 : is_collineation fp_7193 fl_7193.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7193 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7193 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7193.

Lemma collineation_7194 : is_collineation fp_7194 fl_7194.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7194 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7194 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7194.

Lemma collineation_7195 : is_collineation fp_7195 fl_7195.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7195 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7195 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7195.

Lemma collineation_7196 : is_collineation fp_7196 fl_7196.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7196 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7196 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7196.

Lemma collineation_7197 : is_collineation fp_7197 fl_7197.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7197 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7197 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7197.

Lemma collineation_7198 : is_collineation fp_7198 fl_7198.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7198 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7198 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7198.

Lemma collineation_7199 : is_collineation fp_7199 fl_7199.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7199 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7199 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7199.

Lemma collineation_7200 : is_collineation fp_7200 fl_7200.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7200 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7200 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7200.

Lemma collineation_7201 : is_collineation fp_7201 fl_7201.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7201 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7201 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7201.

Lemma collineation_7202 : is_collineation fp_7202 fl_7202.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7202 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7202 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7202.

Lemma collineation_7203 : is_collineation fp_7203 fl_7203.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7203 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7203 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7203.

Lemma collineation_7204 : is_collineation fp_7204 fl_7204.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7204 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7204 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7204.

Lemma collineation_7205 : is_collineation fp_7205 fl_7205.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7205 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7205 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7205.

Lemma collineation_7206 : is_collineation fp_7206 fl_7206.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7206 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7206 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7206.

Lemma collineation_7207 : is_collineation fp_7207 fl_7207.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7207 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7207 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7207.

Lemma collineation_7208 : is_collineation fp_7208 fl_7208.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7208 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7208 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7208.

Lemma collineation_7209 : is_collineation fp_7209 fl_7209.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7209 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7209 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7209.

Lemma collineation_7210 : is_collineation fp_7210 fl_7210.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7210 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7210 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7210.

Lemma collineation_7211 : is_collineation fp_7211 fl_7211.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7211 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7211 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7211.

Lemma collineation_7212 : is_collineation fp_7212 fl_7212.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7212 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7212 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7212.

Lemma collineation_7213 : is_collineation fp_7213 fl_7213.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7213 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7213 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7213.

Lemma collineation_7214 : is_collineation fp_7214 fl_7214.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7214 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7214 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7214.

Lemma collineation_7215 : is_collineation fp_7215 fl_7215.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7215 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7215 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7215.

Lemma collineation_7216 : is_collineation fp_7216 fl_7216.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7216 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7216 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7216.

Lemma collineation_7217 : is_collineation fp_7217 fl_7217.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7217 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7217 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7217.

Lemma collineation_7218 : is_collineation fp_7218 fl_7218.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7218 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7218 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7218.

Lemma collineation_7219 : is_collineation fp_7219 fl_7219.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7219 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7219 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7219.

Lemma collineation_7220 : is_collineation fp_7220 fl_7220.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7220 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7220 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7220.

Lemma collineation_7221 : is_collineation fp_7221 fl_7221.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7221 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7221 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7221.

Lemma collineation_7222 : is_collineation fp_7222 fl_7222.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7222 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7222 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7222.

Lemma collineation_7223 : is_collineation fp_7223 fl_7223.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7223 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7223 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7223.

Lemma collineation_7224 : is_collineation fp_7224 fl_7224.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7224 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7224 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7224.

Lemma collineation_7225 : is_collineation fp_7225 fl_7225.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7225 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7225 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7225.

Lemma collineation_7226 : is_collineation fp_7226 fl_7226.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7226 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7226 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7226.

Lemma collineation_7227 : is_collineation fp_7227 fl_7227.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7227 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7227 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7227.

Lemma collineation_7228 : is_collineation fp_7228 fl_7228.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7228 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7228 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7228.

Lemma collineation_7229 : is_collineation fp_7229 fl_7229.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7229 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7229 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7229.

Lemma collineation_7230 : is_collineation fp_7230 fl_7230.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7230 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7230 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7230.

Lemma collineation_7231 : is_collineation fp_7231 fl_7231.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7231 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7231 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7231.

Lemma collineation_7232 : is_collineation fp_7232 fl_7232.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7232 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7232 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7232.

Lemma collineation_7233 : is_collineation fp_7233 fl_7233.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7233 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7233 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7233.

Lemma collineation_7234 : is_collineation fp_7234 fl_7234.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7234 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7234 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7234.

Lemma collineation_7235 : is_collineation fp_7235 fl_7235.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7235 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7235 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7235.

Lemma collineation_7236 : is_collineation fp_7236 fl_7236.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7236 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7236 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7236.

Lemma collineation_7237 : is_collineation fp_7237 fl_7237.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7237 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7237 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7237.

Lemma collineation_7238 : is_collineation fp_7238 fl_7238.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7238 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7238 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7238.

Lemma collineation_7239 : is_collineation fp_7239 fl_7239.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7239 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7239 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7239.

Lemma collineation_7240 : is_collineation fp_7240 fl_7240.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7240 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7240 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7240.

Lemma collineation_7241 : is_collineation fp_7241 fl_7241.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7241 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7241 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7241.

Lemma collineation_7242 : is_collineation fp_7242 fl_7242.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7242 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7242 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7242.

Lemma collineation_7243 : is_collineation fp_7243 fl_7243.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7243 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7243 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7243.

Lemma collineation_7244 : is_collineation fp_7244 fl_7244.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7244 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7244 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7244.

Lemma collineation_7245 : is_collineation fp_7245 fl_7245.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7245 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7245 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7245.

Lemma collineation_7246 : is_collineation fp_7246 fl_7246.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7246 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7246 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7246.

Lemma collineation_7247 : is_collineation fp_7247 fl_7247.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7247 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7247 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7247.

Lemma collineation_7248 : is_collineation fp_7248 fl_7248.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7248 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7248 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7248.

Lemma collineation_7249 : is_collineation fp_7249 fl_7249.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7249 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7249 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7249.

Lemma collineation_7250 : is_collineation fp_7250 fl_7250.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7250 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7250 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7250.

Lemma collineation_7251 : is_collineation fp_7251 fl_7251.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7251 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7251 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7251.

Lemma collineation_7252 : is_collineation fp_7252 fl_7252.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7252 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7252 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7252.

Lemma collineation_7253 : is_collineation fp_7253 fl_7253.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7253 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7253 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7253.

Lemma collineation_7254 : is_collineation fp_7254 fl_7254.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7254 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7254 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7254.

Lemma collineation_7255 : is_collineation fp_7255 fl_7255.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7255 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7255 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7255.

Lemma collineation_7256 : is_collineation fp_7256 fl_7256.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7256 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7256 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7256.

Lemma collineation_7257 : is_collineation fp_7257 fl_7257.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7257 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7257 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7257.

Lemma collineation_7258 : is_collineation fp_7258 fl_7258.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7258 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7258 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7258.

Lemma collineation_7259 : is_collineation fp_7259 fl_7259.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7259 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7259 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7259.

Lemma collineation_7260 : is_collineation fp_7260 fl_7260.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7260 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7260 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7260.

Lemma collineation_7261 : is_collineation fp_7261 fl_7261.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7261 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7261 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7261.

Lemma collineation_7262 : is_collineation fp_7262 fl_7262.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7262 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7262 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7262.

Lemma collineation_7263 : is_collineation fp_7263 fl_7263.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7263 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7263 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7263.

Lemma collineation_7264 : is_collineation fp_7264 fl_7264.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7264 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7264 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7264.

Lemma collineation_7265 : is_collineation fp_7265 fl_7265.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7265 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7265 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7265.

Lemma collineation_7266 : is_collineation fp_7266 fl_7266.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7266 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7266 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7266.

Lemma collineation_7267 : is_collineation fp_7267 fl_7267.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7267 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7267 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7267.

Lemma collineation_7268 : is_collineation fp_7268 fl_7268.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7268 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7268 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7268.

Lemma collineation_7269 : is_collineation fp_7269 fl_7269.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7269 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7269 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7269.

Lemma collineation_7270 : is_collineation fp_7270 fl_7270.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7270 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7270 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7270.

Lemma collineation_7271 : is_collineation fp_7271 fl_7271.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7271 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7271 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7271.

Lemma collineation_7272 : is_collineation fp_7272 fl_7272.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7272 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7272 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7272.

Lemma collineation_7273 : is_collineation fp_7273 fl_7273.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7273 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7273 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7273.

Lemma collineation_7274 : is_collineation fp_7274 fl_7274.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7274 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7274 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7274.

Lemma collineation_7275 : is_collineation fp_7275 fl_7275.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7275 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7275 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7275.

Lemma collineation_7276 : is_collineation fp_7276 fl_7276.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7276 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7276 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7276.

Lemma collineation_7277 : is_collineation fp_7277 fl_7277.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7277 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7277 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7277.

Lemma collineation_7278 : is_collineation fp_7278 fl_7278.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7278 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7278 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7278.

Lemma collineation_7279 : is_collineation fp_7279 fl_7279.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7279 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7279 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7279.

Lemma collineation_7280 : is_collineation fp_7280 fl_7280.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7280 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7280 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7280.

Lemma collineation_7281 : is_collineation fp_7281 fl_7281.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7281 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7281 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7281.

Lemma collineation_7282 : is_collineation fp_7282 fl_7282.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7282 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7282 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7282.

Lemma collineation_7283 : is_collineation fp_7283 fl_7283.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7283 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7283 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7283.

Lemma collineation_7284 : is_collineation fp_7284 fl_7284.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7284 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7284 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7284.

Lemma collineation_7285 : is_collineation fp_7285 fl_7285.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7285 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7285 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7285.

Lemma collineation_7286 : is_collineation fp_7286 fl_7286.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7286 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7286 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7286.

Lemma collineation_7287 : is_collineation fp_7287 fl_7287.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7287 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7287 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7287.

Lemma collineation_7288 : is_collineation fp_7288 fl_7288.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7288 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7288 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7288.

Lemma collineation_7289 : is_collineation fp_7289 fl_7289.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7289 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7289 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7289.

Lemma collineation_7290 : is_collineation fp_7290 fl_7290.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7290 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7290 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7290.

Lemma collineation_7291 : is_collineation fp_7291 fl_7291.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7291 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7291 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7291.

Lemma collineation_7292 : is_collineation fp_7292 fl_7292.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7292 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7292 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7292.

Lemma collineation_7293 : is_collineation fp_7293 fl_7293.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7293 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7293 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7293.

Lemma collineation_7294 : is_collineation fp_7294 fl_7294.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7294 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7294 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7294.

Lemma collineation_7295 : is_collineation fp_7295 fl_7295.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7295 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7295 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7295.

Lemma collineation_7296 : is_collineation fp_7296 fl_7296.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7296 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7296 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7296.

Lemma collineation_7297 : is_collineation fp_7297 fl_7297.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7297 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7297 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7297.

Lemma collineation_7298 : is_collineation fp_7298 fl_7298.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7298 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7298 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7298.

Lemma collineation_7299 : is_collineation fp_7299 fl_7299.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7299 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7299 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7299.

Lemma collineation_7300 : is_collineation fp_7300 fl_7300.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7300 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7300 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7300.

Lemma collineation_7301 : is_collineation fp_7301 fl_7301.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7301 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7301 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7301.

Lemma collineation_7302 : is_collineation fp_7302 fl_7302.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7302 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7302 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7302.

Lemma collineation_7303 : is_collineation fp_7303 fl_7303.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7303 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7303 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7303.

Lemma collineation_7304 : is_collineation fp_7304 fl_7304.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7304 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7304 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7304.

Lemma collineation_7305 : is_collineation fp_7305 fl_7305.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7305 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7305 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7305.

Lemma collineation_7306 : is_collineation fp_7306 fl_7306.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7306 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7306 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7306.

Lemma collineation_7307 : is_collineation fp_7307 fl_7307.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7307 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7307 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7307.

Lemma collineation_7308 : is_collineation fp_7308 fl_7308.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7308 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7308 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7308.

Lemma collineation_7309 : is_collineation fp_7309 fl_7309.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7309 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7309 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7309.

Lemma collineation_7310 : is_collineation fp_7310 fl_7310.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7310 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7310 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7310.

Lemma collineation_7311 : is_collineation fp_7311 fl_7311.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7311 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7311 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7311.

Lemma collineation_7312 : is_collineation fp_7312 fl_7312.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7312 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7312 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7312.

Lemma collineation_7313 : is_collineation fp_7313 fl_7313.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7313 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7313 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7313.

Lemma collineation_7314 : is_collineation fp_7314 fl_7314.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7314 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7314 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7314.

Lemma collineation_7315 : is_collineation fp_7315 fl_7315.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7315 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7315 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7315.

Lemma collineation_7316 : is_collineation fp_7316 fl_7316.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7316 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7316 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7316.

Lemma collineation_7317 : is_collineation fp_7317 fl_7317.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7317 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7317 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7317.

Lemma collineation_7318 : is_collineation fp_7318 fl_7318.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7318 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7318 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7318.

Lemma collineation_7319 : is_collineation fp_7319 fl_7319.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7319 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7319 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7319.

Lemma collineation_7320 : is_collineation fp_7320 fl_7320.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7320 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7320 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7320.

Lemma collineation_7321 : is_collineation fp_7321 fl_7321.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7321 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7321 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7321.

Lemma collineation_7322 : is_collineation fp_7322 fl_7322.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7322 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7322 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7322.

Lemma collineation_7323 : is_collineation fp_7323 fl_7323.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7323 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7323 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7323.

Lemma collineation_7324 : is_collineation fp_7324 fl_7324.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7324 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7324 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7324.

Lemma collineation_7325 : is_collineation fp_7325 fl_7325.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7325 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7325 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7325.

Lemma collineation_7326 : is_collineation fp_7326 fl_7326.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7326 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7326 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7326.

Lemma collineation_7327 : is_collineation fp_7327 fl_7327.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7327 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7327 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7327.

Lemma collineation_7328 : is_collineation fp_7328 fl_7328.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7328 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7328 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7328.

Lemma collineation_7329 : is_collineation fp_7329 fl_7329.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7329 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7329 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7329.

Lemma collineation_7330 : is_collineation fp_7330 fl_7330.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7330 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7330 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7330.

Lemma collineation_7331 : is_collineation fp_7331 fl_7331.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7331 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7331 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7331.

Lemma collineation_7332 : is_collineation fp_7332 fl_7332.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7332 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7332 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7332.

Lemma collineation_7333 : is_collineation fp_7333 fl_7333.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7333 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7333 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7333.

Lemma collineation_7334 : is_collineation fp_7334 fl_7334.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7334 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7334 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7334.

Lemma collineation_7335 : is_collineation fp_7335 fl_7335.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7335 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7335 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7335.

Lemma collineation_7336 : is_collineation fp_7336 fl_7336.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7336 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7336 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7336.

Lemma collineation_7337 : is_collineation fp_7337 fl_7337.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7337 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7337 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7337.

Lemma collineation_7338 : is_collineation fp_7338 fl_7338.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7338 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7338 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7338.

Lemma collineation_7339 : is_collineation fp_7339 fl_7339.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7339 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7339 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7339.

Lemma collineation_7340 : is_collineation fp_7340 fl_7340.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7340 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7340 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7340.

Lemma collineation_7341 : is_collineation fp_7341 fl_7341.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7341 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7341 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7341.

Lemma collineation_7342 : is_collineation fp_7342 fl_7342.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7342 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7342 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7342.

Lemma collineation_7343 : is_collineation fp_7343 fl_7343.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7343 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7343 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7343.

Lemma collineation_7344 : is_collineation fp_7344 fl_7344.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7344 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7344 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7344.

Lemma collineation_7345 : is_collineation fp_7345 fl_7345.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7345 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7345 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7345.

Lemma collineation_7346 : is_collineation fp_7346 fl_7346.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7346 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7346 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7346.

Lemma collineation_7347 : is_collineation fp_7347 fl_7347.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7347 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7347 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7347.

Lemma collineation_7348 : is_collineation fp_7348 fl_7348.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7348 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7348 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7348.

Lemma collineation_7349 : is_collineation fp_7349 fl_7349.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7349 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7349 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7349.

Lemma collineation_7350 : is_collineation fp_7350 fl_7350.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7350 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7350 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7350.

Lemma collineation_7351 : is_collineation fp_7351 fl_7351.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7351 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7351 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7351.

Lemma collineation_7352 : is_collineation fp_7352 fl_7352.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7352 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7352 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7352.

Lemma collineation_7353 : is_collineation fp_7353 fl_7353.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7353 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7353 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7353.

Lemma collineation_7354 : is_collineation fp_7354 fl_7354.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7354 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7354 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7354.

Lemma collineation_7355 : is_collineation fp_7355 fl_7355.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7355 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7355 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7355.

Lemma collineation_7356 : is_collineation fp_7356 fl_7356.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7356 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7356 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7356.

Lemma collineation_7357 : is_collineation fp_7357 fl_7357.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7357 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7357 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7357.

Lemma collineation_7358 : is_collineation fp_7358 fl_7358.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7358 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7358 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7358.

Lemma collineation_7359 : is_collineation fp_7359 fl_7359.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7359 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7359 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7359.

Lemma collineation_7360 : is_collineation fp_7360 fl_7360.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7360 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7360 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7360.

Lemma collineation_7361 : is_collineation fp_7361 fl_7361.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7361 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7361 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7361.

Lemma collineation_7362 : is_collineation fp_7362 fl_7362.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7362 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7362 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7362.

Lemma collineation_7363 : is_collineation fp_7363 fl_7363.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7363 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7363 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7363.

Lemma collineation_7364 : is_collineation fp_7364 fl_7364.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7364 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7364 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7364.

Lemma collineation_7365 : is_collineation fp_7365 fl_7365.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7365 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7365 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7365.

Lemma collineation_7366 : is_collineation fp_7366 fl_7366.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7366 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7366 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7366.

Lemma collineation_7367 : is_collineation fp_7367 fl_7367.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7367 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7367 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7367.

Lemma collineation_7368 : is_collineation fp_7368 fl_7368.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7368 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7368 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7368.

Lemma collineation_7369 : is_collineation fp_7369 fl_7369.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7369 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7369 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7369.

Lemma collineation_7370 : is_collineation fp_7370 fl_7370.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7370 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7370 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7370.

Lemma collineation_7371 : is_collineation fp_7371 fl_7371.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7371 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7371 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7371.

Lemma collineation_7372 : is_collineation fp_7372 fl_7372.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7372 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7372 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7372.

Lemma collineation_7373 : is_collineation fp_7373 fl_7373.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7373 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7373 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7373.

Lemma collineation_7374 : is_collineation fp_7374 fl_7374.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7374 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7374 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7374.

Lemma collineation_7375 : is_collineation fp_7375 fl_7375.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7375 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7375 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7375.

Lemma collineation_7376 : is_collineation fp_7376 fl_7376.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7376 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7376 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7376.

Lemma collineation_7377 : is_collineation fp_7377 fl_7377.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7377 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7377 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7377.

Lemma collineation_7378 : is_collineation fp_7378 fl_7378.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7378 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7378 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7378.

Lemma collineation_7379 : is_collineation fp_7379 fl_7379.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7379 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7379 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7379.

Lemma collineation_7380 : is_collineation fp_7380 fl_7380.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7380 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7380 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7380.

Lemma collineation_7381 : is_collineation fp_7381 fl_7381.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7381 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7381 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7381.

Lemma collineation_7382 : is_collineation fp_7382 fl_7382.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7382 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7382 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7382.

Lemma collineation_7383 : is_collineation fp_7383 fl_7383.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7383 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7383 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7383.

Lemma collineation_7384 : is_collineation fp_7384 fl_7384.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7384 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7384 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7384.

Lemma collineation_7385 : is_collineation fp_7385 fl_7385.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7385 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7385 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7385.

Lemma collineation_7386 : is_collineation fp_7386 fl_7386.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7386 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7386 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7386.

Lemma collineation_7387 : is_collineation fp_7387 fl_7387.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7387 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7387 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7387.

Lemma collineation_7388 : is_collineation fp_7388 fl_7388.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7388 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7388 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7388.

Lemma collineation_7389 : is_collineation fp_7389 fl_7389.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7389 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7389 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7389.

Lemma collineation_7390 : is_collineation fp_7390 fl_7390.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7390 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7390 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7390.

Lemma collineation_7391 : is_collineation fp_7391 fl_7391.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7391 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7391 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7391.

Lemma collineation_7392 : is_collineation fp_7392 fl_7392.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7392 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7392 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7392.

Lemma collineation_7393 : is_collineation fp_7393 fl_7393.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7393 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7393 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7393.

Lemma collineation_7394 : is_collineation fp_7394 fl_7394.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7394 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7394 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7394.

Lemma collineation_7395 : is_collineation fp_7395 fl_7395.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7395 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7395 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7395.

Lemma collineation_7396 : is_collineation fp_7396 fl_7396.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7396 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7396 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7396.

Lemma collineation_7397 : is_collineation fp_7397 fl_7397.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7397 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7397 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7397.

Lemma collineation_7398 : is_collineation fp_7398 fl_7398.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7398 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7398 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7398.

Lemma collineation_7399 : is_collineation fp_7399 fl_7399.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7399 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7399 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7399.

Lemma collineation_7400 : is_collineation fp_7400 fl_7400.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7400 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7400 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7400.

Lemma collineation_7401 : is_collineation fp_7401 fl_7401.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7401 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7401 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7401.

Lemma collineation_7402 : is_collineation fp_7402 fl_7402.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7402 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7402 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7402.

Lemma collineation_7403 : is_collineation fp_7403 fl_7403.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7403 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7403 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7403.

Lemma collineation_7404 : is_collineation fp_7404 fl_7404.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7404 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7404 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7404.

Lemma collineation_7405 : is_collineation fp_7405 fl_7405.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7405 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7405 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7405.

Lemma collineation_7406 : is_collineation fp_7406 fl_7406.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7406 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7406 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7406.

Lemma collineation_7407 : is_collineation fp_7407 fl_7407.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7407 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7407 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7407.

Lemma collineation_7408 : is_collineation fp_7408 fl_7408.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7408 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7408 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7408.

Lemma collineation_7409 : is_collineation fp_7409 fl_7409.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7409 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7409 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7409.

Lemma collineation_7410 : is_collineation fp_7410 fl_7410.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7410 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7410 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7410.

Lemma collineation_7411 : is_collineation fp_7411 fl_7411.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7411 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7411 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7411.

Lemma collineation_7412 : is_collineation fp_7412 fl_7412.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7412 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7412 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7412.

Lemma collineation_7413 : is_collineation fp_7413 fl_7413.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7413 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7413 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7413.

Lemma collineation_7414 : is_collineation fp_7414 fl_7414.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7414 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7414 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7414.

Lemma collineation_7415 : is_collineation fp_7415 fl_7415.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7415 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7415 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7415.

Lemma collineation_7416 : is_collineation fp_7416 fl_7416.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7416 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7416 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7416.

Lemma collineation_7417 : is_collineation fp_7417 fl_7417.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7417 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7417 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7417.

Lemma collineation_7418 : is_collineation fp_7418 fl_7418.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7418 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7418 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7418.

Lemma collineation_7419 : is_collineation fp_7419 fl_7419.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7419 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7419 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7419.

Lemma collineation_7420 : is_collineation fp_7420 fl_7420.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7420 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7420 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7420.

Lemma collineation_7421 : is_collineation fp_7421 fl_7421.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7421 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7421 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7421.

Lemma collineation_7422 : is_collineation fp_7422 fl_7422.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7422 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7422 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7422.

Lemma collineation_7423 : is_collineation fp_7423 fl_7423.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7423 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7423 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7423.

Lemma collineation_7424 : is_collineation fp_7424 fl_7424.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7424 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7424 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7424.

Lemma collineation_7425 : is_collineation fp_7425 fl_7425.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7425 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7425 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7425.

Lemma collineation_7426 : is_collineation fp_7426 fl_7426.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7426 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7426 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7426.

Lemma collineation_7427 : is_collineation fp_7427 fl_7427.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7427 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7427 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7427.

Lemma collineation_7428 : is_collineation fp_7428 fl_7428.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7428 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7428 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7428.

Lemma collineation_7429 : is_collineation fp_7429 fl_7429.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7429 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7429 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7429.

Lemma collineation_7430 : is_collineation fp_7430 fl_7430.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7430 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7430 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7430.

Lemma collineation_7431 : is_collineation fp_7431 fl_7431.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7431 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7431 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7431.

Lemma collineation_7432 : is_collineation fp_7432 fl_7432.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7432 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7432 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7432.

Lemma collineation_7433 : is_collineation fp_7433 fl_7433.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7433 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7433 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7433.

Lemma collineation_7434 : is_collineation fp_7434 fl_7434.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7434 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7434 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7434.

Lemma collineation_7435 : is_collineation fp_7435 fl_7435.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7435 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7435 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7435.

Lemma collineation_7436 : is_collineation fp_7436 fl_7436.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7436 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7436 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7436.

Lemma collineation_7437 : is_collineation fp_7437 fl_7437.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7437 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7437 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7437.

Lemma collineation_7438 : is_collineation fp_7438 fl_7438.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7438 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7438 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7438.

Lemma collineation_7439 : is_collineation fp_7439 fl_7439.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7439 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7439 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7439.

Lemma collineation_7440 : is_collineation fp_7440 fl_7440.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7440 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7440 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7440.

Lemma collineation_7441 : is_collineation fp_7441 fl_7441.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7441 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7441 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7441.

Lemma collineation_7442 : is_collineation fp_7442 fl_7442.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7442 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7442 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7442.

Lemma collineation_7443 : is_collineation fp_7443 fl_7443.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7443 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7443 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7443.

Lemma collineation_7444 : is_collineation fp_7444 fl_7444.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7444 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7444 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7444.

Lemma collineation_7445 : is_collineation fp_7445 fl_7445.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7445 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7445 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7445.

Lemma collineation_7446 : is_collineation fp_7446 fl_7446.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7446 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7446 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7446.

Lemma collineation_7447 : is_collineation fp_7447 fl_7447.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7447 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7447 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7447.

Lemma collineation_7448 : is_collineation fp_7448 fl_7448.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7448 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7448 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7448.

Lemma collineation_7449 : is_collineation fp_7449 fl_7449.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7449 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7449 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7449.

Lemma collineation_7450 : is_collineation fp_7450 fl_7450.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7450 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7450 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7450.

Lemma collineation_7451 : is_collineation fp_7451 fl_7451.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7451 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7451 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7451.

Lemma collineation_7452 : is_collineation fp_7452 fl_7452.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7452 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7452 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7452.

Lemma collineation_7453 : is_collineation fp_7453 fl_7453.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7453 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7453 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7453.

Lemma collineation_7454 : is_collineation fp_7454 fl_7454.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7454 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7454 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7454.

Lemma collineation_7455 : is_collineation fp_7455 fl_7455.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7455 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7455 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7455.

Lemma collineation_7456 : is_collineation fp_7456 fl_7456.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7456 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7456 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7456.

Lemma collineation_7457 : is_collineation fp_7457 fl_7457.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7457 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7457 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7457.

Lemma collineation_7458 : is_collineation fp_7458 fl_7458.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7458 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7458 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7458.

Lemma collineation_7459 : is_collineation fp_7459 fl_7459.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7459 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7459 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7459.

Lemma collineation_7460 : is_collineation fp_7460 fl_7460.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7460 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7460 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7460.

Lemma collineation_7461 : is_collineation fp_7461 fl_7461.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7461 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7461 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7461.

Lemma collineation_7462 : is_collineation fp_7462 fl_7462.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7462 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7462 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7462.

Lemma collineation_7463 : is_collineation fp_7463 fl_7463.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7463 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7463 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7463.

Lemma collineation_7464 : is_collineation fp_7464 fl_7464.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7464 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7464 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7464.

Lemma collineation_7465 : is_collineation fp_7465 fl_7465.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7465 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7465 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7465.

Lemma collineation_7466 : is_collineation fp_7466 fl_7466.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7466 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7466 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7466.

Lemma collineation_7467 : is_collineation fp_7467 fl_7467.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7467 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7467 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7467.

Lemma collineation_7468 : is_collineation fp_7468 fl_7468.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7468 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7468 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7468.

Lemma collineation_7469 : is_collineation fp_7469 fl_7469.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7469 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7469 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7469.

Lemma collineation_7470 : is_collineation fp_7470 fl_7470.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7470 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7470 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7470.

Lemma collineation_7471 : is_collineation fp_7471 fl_7471.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7471 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7471 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7471.

Lemma collineation_7472 : is_collineation fp_7472 fl_7472.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7472 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7472 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7472.

Lemma collineation_7473 : is_collineation fp_7473 fl_7473.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7473 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7473 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7473.

Lemma collineation_7474 : is_collineation fp_7474 fl_7474.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7474 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7474 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7474.

Lemma collineation_7475 : is_collineation fp_7475 fl_7475.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7475 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7475 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7475.

Lemma collineation_7476 : is_collineation fp_7476 fl_7476.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7476 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7476 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7476.

Lemma collineation_7477 : is_collineation fp_7477 fl_7477.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7477 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7477 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7477.

Lemma collineation_7478 : is_collineation fp_7478 fl_7478.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7478 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7478 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7478.

Lemma collineation_7479 : is_collineation fp_7479 fl_7479.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7479 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7479 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7479.

Lemma collineation_7480 : is_collineation fp_7480 fl_7480.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7480 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7480 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7480.

Lemma collineation_7481 : is_collineation fp_7481 fl_7481.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7481 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7481 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7481.

Lemma collineation_7482 : is_collineation fp_7482 fl_7482.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7482 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7482 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7482.

Lemma collineation_7483 : is_collineation fp_7483 fl_7483.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7483 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7483 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7483.

Lemma collineation_7484 : is_collineation fp_7484 fl_7484.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7484 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7484 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7484.

Lemma collineation_7485 : is_collineation fp_7485 fl_7485.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7485 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7485 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7485.

Lemma collineation_7486 : is_collineation fp_7486 fl_7486.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7486 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7486 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7486.

Lemma collineation_7487 : is_collineation fp_7487 fl_7487.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7487 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7487 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7487.

Lemma collineation_7488 : is_collineation fp_7488 fl_7488.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7488 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7488 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7488.

Lemma collineation_7489 : is_collineation fp_7489 fl_7489.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7489 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7489 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7489.

Lemma collineation_7490 : is_collineation fp_7490 fl_7490.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7490 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7490 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7490.

Lemma collineation_7491 : is_collineation fp_7491 fl_7491.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7491 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7491 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7491.

Lemma collineation_7492 : is_collineation fp_7492 fl_7492.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7492 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7492 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7492.

Lemma collineation_7493 : is_collineation fp_7493 fl_7493.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7493 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7493 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7493.

Lemma collineation_7494 : is_collineation fp_7494 fl_7494.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7494 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7494 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7494.

Lemma collineation_7495 : is_collineation fp_7495 fl_7495.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7495 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7495 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7495.

Lemma collineation_7496 : is_collineation fp_7496 fl_7496.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7496 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7496 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7496.

Lemma collineation_7497 : is_collineation fp_7497 fl_7497.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7497 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7497 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7497.

Lemma collineation_7498 : is_collineation fp_7498 fl_7498.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7498 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7498 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7498.

Lemma collineation_7499 : is_collineation fp_7499 fl_7499.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7499 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7499 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7499.

Lemma collineation_7500 : is_collineation fp_7500 fl_7500.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7500 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7500 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7500.

Lemma collineation_7501 : is_collineation fp_7501 fl_7501.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7501 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7501 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7501.

Lemma collineation_7502 : is_collineation fp_7502 fl_7502.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7502 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7502 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7502.

Lemma collineation_7503 : is_collineation fp_7503 fl_7503.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7503 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7503 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7503.

Lemma collineation_7504 : is_collineation fp_7504 fl_7504.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7504 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7504 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7504.

Lemma collineation_7505 : is_collineation fp_7505 fl_7505.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7505 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7505 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7505.

Lemma collineation_7506 : is_collineation fp_7506 fl_7506.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7506 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7506 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7506.

Lemma collineation_7507 : is_collineation fp_7507 fl_7507.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7507 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7507 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7507.

Lemma collineation_7508 : is_collineation fp_7508 fl_7508.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7508 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7508 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7508.

Lemma collineation_7509 : is_collineation fp_7509 fl_7509.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7509 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7509 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7509.

Lemma collineation_7510 : is_collineation fp_7510 fl_7510.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7510 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7510 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7510.

Lemma collineation_7511 : is_collineation fp_7511 fl_7511.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7511 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7511 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7511.

Lemma collineation_7512 : is_collineation fp_7512 fl_7512.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7512 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7512 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7512.

Lemma collineation_7513 : is_collineation fp_7513 fl_7513.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7513 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7513 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7513.

Lemma collineation_7514 : is_collineation fp_7514 fl_7514.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7514 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7514 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7514.

Lemma collineation_7515 : is_collineation fp_7515 fl_7515.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7515 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7515 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7515.

Lemma collineation_7516 : is_collineation fp_7516 fl_7516.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7516 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7516 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7516.

Lemma collineation_7517 : is_collineation fp_7517 fl_7517.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7517 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7517 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7517.

Lemma collineation_7518 : is_collineation fp_7518 fl_7518.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7518 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7518 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7518.

Lemma collineation_7519 : is_collineation fp_7519 fl_7519.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7519 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7519 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7519.

Lemma collineation_7520 : is_collineation fp_7520 fl_7520.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7520 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7520 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7520.

Lemma collineation_7521 : is_collineation fp_7521 fl_7521.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7521 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7521 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7521.

Lemma collineation_7522 : is_collineation fp_7522 fl_7522.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7522 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7522 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7522.

Lemma collineation_7523 : is_collineation fp_7523 fl_7523.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7523 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7523 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7523.

Lemma collineation_7524 : is_collineation fp_7524 fl_7524.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7524 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7524 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7524.

Lemma collineation_7525 : is_collineation fp_7525 fl_7525.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7525 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7525 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7525.

Lemma collineation_7526 : is_collineation fp_7526 fl_7526.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7526 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7526 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7526.

Lemma collineation_7527 : is_collineation fp_7527 fl_7527.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7527 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7527 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7527.

Lemma collineation_7528 : is_collineation fp_7528 fl_7528.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7528 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7528 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7528.

Lemma collineation_7529 : is_collineation fp_7529 fl_7529.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7529 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7529 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7529.

Lemma collineation_7530 : is_collineation fp_7530 fl_7530.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7530 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7530 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7530.

Lemma collineation_7531 : is_collineation fp_7531 fl_7531.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7531 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7531 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7531.

Lemma collineation_7532 : is_collineation fp_7532 fl_7532.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7532 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7532 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7532.

Lemma collineation_7533 : is_collineation fp_7533 fl_7533.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7533 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7533 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7533.

Lemma collineation_7534 : is_collineation fp_7534 fl_7534.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7534 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7534 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7534.

Lemma collineation_7535 : is_collineation fp_7535 fl_7535.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7535 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7535 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7535.

Lemma collineation_7536 : is_collineation fp_7536 fl_7536.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7536 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7536 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7536.

Lemma collineation_7537 : is_collineation fp_7537 fl_7537.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7537 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7537 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7537.

Lemma collineation_7538 : is_collineation fp_7538 fl_7538.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7538 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7538 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7538.

Lemma collineation_7539 : is_collineation fp_7539 fl_7539.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7539 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7539 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7539.

Lemma collineation_7540 : is_collineation fp_7540 fl_7540.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7540 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7540 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7540.

Lemma collineation_7541 : is_collineation fp_7541 fl_7541.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7541 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7541 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7541.

Lemma collineation_7542 : is_collineation fp_7542 fl_7542.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7542 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7542 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7542.

Lemma collineation_7543 : is_collineation fp_7543 fl_7543.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7543 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7543 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7543.

Lemma collineation_7544 : is_collineation fp_7544 fl_7544.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7544 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7544 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7544.

Lemma collineation_7545 : is_collineation fp_7545 fl_7545.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7545 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7545 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7545.

Lemma collineation_7546 : is_collineation fp_7546 fl_7546.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7546 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7546 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7546.

Lemma collineation_7547 : is_collineation fp_7547 fl_7547.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7547 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7547 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7547.

Lemma collineation_7548 : is_collineation fp_7548 fl_7548.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7548 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7548 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7548.

Lemma collineation_7549 : is_collineation fp_7549 fl_7549.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7549 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7549 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7549.

Lemma collineation_7550 : is_collineation fp_7550 fl_7550.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7550 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7550 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7550.

Lemma collineation_7551 : is_collineation fp_7551 fl_7551.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7551 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7551 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7551.

Lemma collineation_7552 : is_collineation fp_7552 fl_7552.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7552 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7552 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7552.

Lemma collineation_7553 : is_collineation fp_7553 fl_7553.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7553 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7553 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7553.

Lemma collineation_7554 : is_collineation fp_7554 fl_7554.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7554 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7554 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7554.

Lemma collineation_7555 : is_collineation fp_7555 fl_7555.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7555 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7555 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7555.

Lemma collineation_7556 : is_collineation fp_7556 fl_7556.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7556 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7556 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7556.

Lemma collineation_7557 : is_collineation fp_7557 fl_7557.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7557 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7557 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7557.

Lemma collineation_7558 : is_collineation fp_7558 fl_7558.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7558 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7558 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7558.

Lemma collineation_7559 : is_collineation fp_7559 fl_7559.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7559 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7559 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7559.

Lemma collineation_7560 : is_collineation fp_7560 fl_7560.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7560 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7560 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7560.

Lemma collineation_7561 : is_collineation fp_7561 fl_7561.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7561 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7561 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7561.

Lemma collineation_7562 : is_collineation fp_7562 fl_7562.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7562 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7562 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7562.

Lemma collineation_7563 : is_collineation fp_7563 fl_7563.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7563 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7563 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7563.

Lemma collineation_7564 : is_collineation fp_7564 fl_7564.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7564 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7564 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7564.

Lemma collineation_7565 : is_collineation fp_7565 fl_7565.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7565 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7565 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7565.

Lemma collineation_7566 : is_collineation fp_7566 fl_7566.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7566 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7566 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7566.

Lemma collineation_7567 : is_collineation fp_7567 fl_7567.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7567 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7567 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7567.

Lemma collineation_7568 : is_collineation fp_7568 fl_7568.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7568 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7568 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7568.

Lemma collineation_7569 : is_collineation fp_7569 fl_7569.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7569 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7569 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7569.

Lemma collineation_7570 : is_collineation fp_7570 fl_7570.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7570 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7570 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7570.

Lemma collineation_7571 : is_collineation fp_7571 fl_7571.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7571 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7571 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7571.

Lemma collineation_7572 : is_collineation fp_7572 fl_7572.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7572 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7572 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7572.

Lemma collineation_7573 : is_collineation fp_7573 fl_7573.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7573 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7573 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7573.

Lemma collineation_7574 : is_collineation fp_7574 fl_7574.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7574 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7574 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7574.

Lemma collineation_7575 : is_collineation fp_7575 fl_7575.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7575 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7575 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7575.

Lemma collineation_7576 : is_collineation fp_7576 fl_7576.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7576 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7576 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7576.

Lemma collineation_7577 : is_collineation fp_7577 fl_7577.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7577 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7577 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7577.

Lemma collineation_7578 : is_collineation fp_7578 fl_7578.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7578 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7578 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7578.

Lemma collineation_7579 : is_collineation fp_7579 fl_7579.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7579 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7579 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7579.

Lemma collineation_7580 : is_collineation fp_7580 fl_7580.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7580 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7580 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7580.

Lemma collineation_7581 : is_collineation fp_7581 fl_7581.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7581 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7581 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7581.

Lemma collineation_7582 : is_collineation fp_7582 fl_7582.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7582 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7582 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7582.

Lemma collineation_7583 : is_collineation fp_7583 fl_7583.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7583 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7583 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7583.

Lemma collineation_7584 : is_collineation fp_7584 fl_7584.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7584 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7584 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7584.

Lemma collineation_7585 : is_collineation fp_7585 fl_7585.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7585 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7585 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7585.

Lemma collineation_7586 : is_collineation fp_7586 fl_7586.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7586 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7586 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7586.

Lemma collineation_7587 : is_collineation fp_7587 fl_7587.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7587 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7587 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7587.

Lemma collineation_7588 : is_collineation fp_7588 fl_7588.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7588 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7588 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7588.

Lemma collineation_7589 : is_collineation fp_7589 fl_7589.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7589 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7589 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7589.

Lemma collineation_7590 : is_collineation fp_7590 fl_7590.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7590 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7590 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7590.

Lemma collineation_7591 : is_collineation fp_7591 fl_7591.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7591 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7591 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7591.

Lemma collineation_7592 : is_collineation fp_7592 fl_7592.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7592 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7592 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7592.

Lemma collineation_7593 : is_collineation fp_7593 fl_7593.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7593 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7593 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7593.

Lemma collineation_7594 : is_collineation fp_7594 fl_7594.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7594 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7594 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7594.

Lemma collineation_7595 : is_collineation fp_7595 fl_7595.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7595 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7595 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7595.

Lemma collineation_7596 : is_collineation fp_7596 fl_7596.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7596 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7596 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7596.

Lemma collineation_7597 : is_collineation fp_7597 fl_7597.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7597 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7597 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7597.

Lemma collineation_7598 : is_collineation fp_7598 fl_7598.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7598 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7598 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7598.

Lemma collineation_7599 : is_collineation fp_7599 fl_7599.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7599 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7599 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7599.

Lemma collineation_7600 : is_collineation fp_7600 fl_7600.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7600 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7600 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7600.

Lemma collineation_7601 : is_collineation fp_7601 fl_7601.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7601 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7601 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7601.

Lemma collineation_7602 : is_collineation fp_7602 fl_7602.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7602 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7602 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7602.

Lemma collineation_7603 : is_collineation fp_7603 fl_7603.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7603 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7603 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7603.

Lemma collineation_7604 : is_collineation fp_7604 fl_7604.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7604 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7604 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7604.

Lemma collineation_7605 : is_collineation fp_7605 fl_7605.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7605 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7605 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7605.

Lemma collineation_7606 : is_collineation fp_7606 fl_7606.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7606 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7606 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7606.

Lemma collineation_7607 : is_collineation fp_7607 fl_7607.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7607 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7607 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7607.

Lemma collineation_7608 : is_collineation fp_7608 fl_7608.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7608 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7608 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7608.

Lemma collineation_7609 : is_collineation fp_7609 fl_7609.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7609 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7609 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7609.

Lemma collineation_7610 : is_collineation fp_7610 fl_7610.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7610 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7610 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7610.

Lemma collineation_7611 : is_collineation fp_7611 fl_7611.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7611 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7611 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7611.

Lemma collineation_7612 : is_collineation fp_7612 fl_7612.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7612 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7612 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7612.

Lemma collineation_7613 : is_collineation fp_7613 fl_7613.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7613 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7613 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7613.

Lemma collineation_7614 : is_collineation fp_7614 fl_7614.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7614 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7614 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7614.

Lemma collineation_7615 : is_collineation fp_7615 fl_7615.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7615 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7615 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7615.

Lemma collineation_7616 : is_collineation fp_7616 fl_7616.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7616 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7616 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7616.

Lemma collineation_7617 : is_collineation fp_7617 fl_7617.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7617 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7617 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7617.

Lemma collineation_7618 : is_collineation fp_7618 fl_7618.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7618 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7618 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7618.

Lemma collineation_7619 : is_collineation fp_7619 fl_7619.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7619 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7619 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7619.

Lemma collineation_7620 : is_collineation fp_7620 fl_7620.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7620 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7620 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7620.

Lemma collineation_7621 : is_collineation fp_7621 fl_7621.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7621 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7621 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7621.

Lemma collineation_7622 : is_collineation fp_7622 fl_7622.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7622 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7622 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7622.

Lemma collineation_7623 : is_collineation fp_7623 fl_7623.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7623 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7623 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7623.

Lemma collineation_7624 : is_collineation fp_7624 fl_7624.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7624 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7624 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7624.

Lemma collineation_7625 : is_collineation fp_7625 fl_7625.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7625 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7625 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7625.

Lemma collineation_7626 : is_collineation fp_7626 fl_7626.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7626 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7626 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7626.

Lemma collineation_7627 : is_collineation fp_7627 fl_7627.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7627 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7627 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7627.

Lemma collineation_7628 : is_collineation fp_7628 fl_7628.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7628 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7628 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7628.

Lemma collineation_7629 : is_collineation fp_7629 fl_7629.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7629 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7629 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7629.

Lemma collineation_7630 : is_collineation fp_7630 fl_7630.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7630 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7630 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7630.

Lemma collineation_7631 : is_collineation fp_7631 fl_7631.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7631 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7631 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7631.

Lemma collineation_7632 : is_collineation fp_7632 fl_7632.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7632 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7632 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7632.

Lemma collineation_7633 : is_collineation fp_7633 fl_7633.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7633 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7633 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7633.

Lemma collineation_7634 : is_collineation fp_7634 fl_7634.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7634 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7634 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7634.

Lemma collineation_7635 : is_collineation fp_7635 fl_7635.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7635 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7635 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7635.

Lemma collineation_7636 : is_collineation fp_7636 fl_7636.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7636 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7636 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7636.

Lemma collineation_7637 : is_collineation fp_7637 fl_7637.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7637 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7637 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7637.

Lemma collineation_7638 : is_collineation fp_7638 fl_7638.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7638 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7638 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7638.

Lemma collineation_7639 : is_collineation fp_7639 fl_7639.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7639 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7639 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7639.

Lemma collineation_7640 : is_collineation fp_7640 fl_7640.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7640 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7640 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7640.

Lemma collineation_7641 : is_collineation fp_7641 fl_7641.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7641 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7641 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7641.

Lemma collineation_7642 : is_collineation fp_7642 fl_7642.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7642 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7642 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7642.

Lemma collineation_7643 : is_collineation fp_7643 fl_7643.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7643 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7643 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7643.

Lemma collineation_7644 : is_collineation fp_7644 fl_7644.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7644 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7644 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7644.

Lemma collineation_7645 : is_collineation fp_7645 fl_7645.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7645 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7645 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7645.

Lemma collineation_7646 : is_collineation fp_7646 fl_7646.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7646 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7646 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7646.

Lemma collineation_7647 : is_collineation fp_7647 fl_7647.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7647 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7647 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7647.

Lemma collineation_7648 : is_collineation fp_7648 fl_7648.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7648 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7648 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7648.

Lemma collineation_7649 : is_collineation fp_7649 fl_7649.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7649 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7649 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7649.

Lemma collineation_7650 : is_collineation fp_7650 fl_7650.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7650 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7650 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7650.

Lemma collineation_7651 : is_collineation fp_7651 fl_7651.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7651 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7651 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7651.

Lemma collineation_7652 : is_collineation fp_7652 fl_7652.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7652 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7652 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7652.

Lemma collineation_7653 : is_collineation fp_7653 fl_7653.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7653 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7653 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7653.

Lemma collineation_7654 : is_collineation fp_7654 fl_7654.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7654 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7654 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7654.

Lemma collineation_7655 : is_collineation fp_7655 fl_7655.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7655 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7655 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7655.

Lemma collineation_7656 : is_collineation fp_7656 fl_7656.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7656 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7656 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7656.

Lemma collineation_7657 : is_collineation fp_7657 fl_7657.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7657 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7657 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7657.

Lemma collineation_7658 : is_collineation fp_7658 fl_7658.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7658 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7658 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7658.

Lemma collineation_7659 : is_collineation fp_7659 fl_7659.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7659 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7659 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7659.

Lemma collineation_7660 : is_collineation fp_7660 fl_7660.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7660 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7660 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7660.

Lemma collineation_7661 : is_collineation fp_7661 fl_7661.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7661 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7661 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7661.

Lemma collineation_7662 : is_collineation fp_7662 fl_7662.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7662 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7662 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7662.

Lemma collineation_7663 : is_collineation fp_7663 fl_7663.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7663 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7663 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7663.

Lemma collineation_7664 : is_collineation fp_7664 fl_7664.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7664 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7664 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7664.

Lemma collineation_7665 : is_collineation fp_7665 fl_7665.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7665 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7665 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7665.

Lemma collineation_7666 : is_collineation fp_7666 fl_7666.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7666 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7666 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7666.

Lemma collineation_7667 : is_collineation fp_7667 fl_7667.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7667 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7667 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7667.

Lemma collineation_7668 : is_collineation fp_7668 fl_7668.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7668 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7668 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7668.

Lemma collineation_7669 : is_collineation fp_7669 fl_7669.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7669 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7669 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7669.

Lemma collineation_7670 : is_collineation fp_7670 fl_7670.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7670 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7670 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7670.

Lemma collineation_7671 : is_collineation fp_7671 fl_7671.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7671 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7671 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7671.

Lemma collineation_7672 : is_collineation fp_7672 fl_7672.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7672 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7672 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7672.

Lemma collineation_7673 : is_collineation fp_7673 fl_7673.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7673 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7673 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7673.

Lemma collineation_7674 : is_collineation fp_7674 fl_7674.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7674 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7674 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7674.

Lemma collineation_7675 : is_collineation fp_7675 fl_7675.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7675 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7675 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7675.

Lemma collineation_7676 : is_collineation fp_7676 fl_7676.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7676 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7676 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7676.

Lemma collineation_7677 : is_collineation fp_7677 fl_7677.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7677 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7677 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7677.

Lemma collineation_7678 : is_collineation fp_7678 fl_7678.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7678 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7678 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7678.

Lemma collineation_7679 : is_collineation fp_7679 fl_7679.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7679 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7679 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7679.

Lemma collineation_7680 : is_collineation fp_7680 fl_7680.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7680 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7680 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7680.

Lemma collineation_7681 : is_collineation fp_7681 fl_7681.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7681 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7681 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7681.

Lemma collineation_7682 : is_collineation fp_7682 fl_7682.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7682 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7682 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7682.

Lemma collineation_7683 : is_collineation fp_7683 fl_7683.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7683 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7683 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7683.

Lemma collineation_7684 : is_collineation fp_7684 fl_7684.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7684 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7684 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7684.

Lemma collineation_7685 : is_collineation fp_7685 fl_7685.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7685 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7685 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7685.

Lemma collineation_7686 : is_collineation fp_7686 fl_7686.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7686 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7686 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7686.

Lemma collineation_7687 : is_collineation fp_7687 fl_7687.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7687 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7687 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7687.

Lemma collineation_7688 : is_collineation fp_7688 fl_7688.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7688 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7688 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7688.

Lemma collineation_7689 : is_collineation fp_7689 fl_7689.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7689 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7689 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7689.

Lemma collineation_7690 : is_collineation fp_7690 fl_7690.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7690 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7690 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7690.

Lemma collineation_7691 : is_collineation fp_7691 fl_7691.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7691 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7691 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7691.

Lemma collineation_7692 : is_collineation fp_7692 fl_7692.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7692 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7692 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7692.

Lemma collineation_7693 : is_collineation fp_7693 fl_7693.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7693 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7693 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7693.

Lemma collineation_7694 : is_collineation fp_7694 fl_7694.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7694 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7694 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7694.

Lemma collineation_7695 : is_collineation fp_7695 fl_7695.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7695 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7695 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7695.

Lemma collineation_7696 : is_collineation fp_7696 fl_7696.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7696 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7696 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7696.

Lemma collineation_7697 : is_collineation fp_7697 fl_7697.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7697 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7697 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7697.

Lemma collineation_7698 : is_collineation fp_7698 fl_7698.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7698 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7698 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7698.

Lemma collineation_7699 : is_collineation fp_7699 fl_7699.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7699 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7699 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7699.

Lemma collineation_7700 : is_collineation fp_7700 fl_7700.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7700 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7700 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7700.

Lemma collineation_7701 : is_collineation fp_7701 fl_7701.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7701 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7701 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7701.

Lemma collineation_7702 : is_collineation fp_7702 fl_7702.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7702 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7702 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7702.

Lemma collineation_7703 : is_collineation fp_7703 fl_7703.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7703 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7703 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7703.

Lemma collineation_7704 : is_collineation fp_7704 fl_7704.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7704 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7704 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7704.

Lemma collineation_7705 : is_collineation fp_7705 fl_7705.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7705 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7705 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7705.

Lemma collineation_7706 : is_collineation fp_7706 fl_7706.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7706 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7706 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7706.

Lemma collineation_7707 : is_collineation fp_7707 fl_7707.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7707 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7707 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7707.

Lemma collineation_7708 : is_collineation fp_7708 fl_7708.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7708 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7708 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7708.

Lemma collineation_7709 : is_collineation fp_7709 fl_7709.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7709 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7709 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7709.

Lemma collineation_7710 : is_collineation fp_7710 fl_7710.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7710 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7710 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7710.

Lemma collineation_7711 : is_collineation fp_7711 fl_7711.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7711 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7711 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7711.

Lemma collineation_7712 : is_collineation fp_7712 fl_7712.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7712 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7712 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7712.

Lemma collineation_7713 : is_collineation fp_7713 fl_7713.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7713 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7713 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7713.

Lemma collineation_7714 : is_collineation fp_7714 fl_7714.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7714 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7714 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7714.

Lemma collineation_7715 : is_collineation fp_7715 fl_7715.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7715 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7715 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7715.

Lemma collineation_7716 : is_collineation fp_7716 fl_7716.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7716 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7716 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7716.

Lemma collineation_7717 : is_collineation fp_7717 fl_7717.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7717 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7717 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7717.

Lemma collineation_7718 : is_collineation fp_7718 fl_7718.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7718 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7718 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7718.

Lemma collineation_7719 : is_collineation fp_7719 fl_7719.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7719 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7719 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7719.

Lemma collineation_7720 : is_collineation fp_7720 fl_7720.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7720 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7720 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7720.

Lemma collineation_7721 : is_collineation fp_7721 fl_7721.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7721 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7721 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7721.

Lemma collineation_7722 : is_collineation fp_7722 fl_7722.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7722 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7722 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7722.

Lemma collineation_7723 : is_collineation fp_7723 fl_7723.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7723 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7723 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7723.

Lemma collineation_7724 : is_collineation fp_7724 fl_7724.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7724 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7724 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7724.

Lemma collineation_7725 : is_collineation fp_7725 fl_7725.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7725 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7725 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7725.

Lemma collineation_7726 : is_collineation fp_7726 fl_7726.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7726 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7726 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7726.

Lemma collineation_7727 : is_collineation fp_7727 fl_7727.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7727 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7727 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7727.

Lemma collineation_7728 : is_collineation fp_7728 fl_7728.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7728 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7728 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7728.

Lemma collineation_7729 : is_collineation fp_7729 fl_7729.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7729 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7729 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7729.

Lemma collineation_7730 : is_collineation fp_7730 fl_7730.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7730 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7730 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7730.

Lemma collineation_7731 : is_collineation fp_7731 fl_7731.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7731 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7731 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7731.

Lemma collineation_7732 : is_collineation fp_7732 fl_7732.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7732 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7732 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7732.

Lemma collineation_7733 : is_collineation fp_7733 fl_7733.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7733 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7733 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7733.

Lemma collineation_7734 : is_collineation fp_7734 fl_7734.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7734 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7734 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7734.

Lemma collineation_7735 : is_collineation fp_7735 fl_7735.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7735 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7735 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7735.

Lemma collineation_7736 : is_collineation fp_7736 fl_7736.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7736 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7736 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7736.

Lemma collineation_7737 : is_collineation fp_7737 fl_7737.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7737 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7737 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7737.

Lemma collineation_7738 : is_collineation fp_7738 fl_7738.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7738 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7738 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7738.

Lemma collineation_7739 : is_collineation fp_7739 fl_7739.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7739 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7739 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7739.

Lemma collineation_7740 : is_collineation fp_7740 fl_7740.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7740 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7740 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7740.

Lemma collineation_7741 : is_collineation fp_7741 fl_7741.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7741 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7741 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7741.

Lemma collineation_7742 : is_collineation fp_7742 fl_7742.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7742 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7742 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7742.

Lemma collineation_7743 : is_collineation fp_7743 fl_7743.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7743 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7743 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7743.

Lemma collineation_7744 : is_collineation fp_7744 fl_7744.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7744 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7744 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7744.

Lemma collineation_7745 : is_collineation fp_7745 fl_7745.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7745 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7745 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7745.

Lemma collineation_7746 : is_collineation fp_7746 fl_7746.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7746 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7746 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7746.

Lemma collineation_7747 : is_collineation fp_7747 fl_7747.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7747 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7747 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7747.

Lemma collineation_7748 : is_collineation fp_7748 fl_7748.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7748 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7748 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7748.

Lemma collineation_7749 : is_collineation fp_7749 fl_7749.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7749 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7749 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7749.

Lemma collineation_7750 : is_collineation fp_7750 fl_7750.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7750 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7750 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7750.

Lemma collineation_7751 : is_collineation fp_7751 fl_7751.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7751 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7751 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7751.

Lemma collineation_7752 : is_collineation fp_7752 fl_7752.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7752 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7752 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7752.

Lemma collineation_7753 : is_collineation fp_7753 fl_7753.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7753 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7753 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7753.

Lemma collineation_7754 : is_collineation fp_7754 fl_7754.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7754 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7754 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7754.

Lemma collineation_7755 : is_collineation fp_7755 fl_7755.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7755 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7755 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7755.

Lemma collineation_7756 : is_collineation fp_7756 fl_7756.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7756 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7756 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7756.

Lemma collineation_7757 : is_collineation fp_7757 fl_7757.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7757 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7757 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7757.

Lemma collineation_7758 : is_collineation fp_7758 fl_7758.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7758 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7758 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7758.

Lemma collineation_7759 : is_collineation fp_7759 fl_7759.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7759 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7759 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7759.

Lemma collineation_7760 : is_collineation fp_7760 fl_7760.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7760 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7760 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7760.

Lemma collineation_7761 : is_collineation fp_7761 fl_7761.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7761 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7761 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7761.

Lemma collineation_7762 : is_collineation fp_7762 fl_7762.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7762 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7762 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7762.

Lemma collineation_7763 : is_collineation fp_7763 fl_7763.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7763 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7763 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7763.

Lemma collineation_7764 : is_collineation fp_7764 fl_7764.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7764 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7764 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7764.

Lemma collineation_7765 : is_collineation fp_7765 fl_7765.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7765 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7765 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7765.

Lemma collineation_7766 : is_collineation fp_7766 fl_7766.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7766 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7766 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7766.

Lemma collineation_7767 : is_collineation fp_7767 fl_7767.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7767 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7767 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7767.

Lemma collineation_7768 : is_collineation fp_7768 fl_7768.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7768 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7768 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7768.

Lemma collineation_7769 : is_collineation fp_7769 fl_7769.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7769 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7769 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7769.

Lemma collineation_7770 : is_collineation fp_7770 fl_7770.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7770 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7770 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7770.

Lemma collineation_7771 : is_collineation fp_7771 fl_7771.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7771 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7771 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7771.

Lemma collineation_7772 : is_collineation fp_7772 fl_7772.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7772 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7772 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7772.

Lemma collineation_7773 : is_collineation fp_7773 fl_7773.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7773 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7773 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7773.

Lemma collineation_7774 : is_collineation fp_7774 fl_7774.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7774 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7774 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7774.

Lemma collineation_7775 : is_collineation fp_7775 fl_7775.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7775 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7775 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7775.

Lemma collineation_7776 : is_collineation fp_7776 fl_7776.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7776 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7776 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7776.

Lemma collineation_7777 : is_collineation fp_7777 fl_7777.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7777 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7777 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7777.

Lemma collineation_7778 : is_collineation fp_7778 fl_7778.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7778 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7778 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7778.

Lemma collineation_7779 : is_collineation fp_7779 fl_7779.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7779 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7779 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7779.

Lemma collineation_7780 : is_collineation fp_7780 fl_7780.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7780 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7780 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7780.

Lemma collineation_7781 : is_collineation fp_7781 fl_7781.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7781 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7781 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7781.

Lemma collineation_7782 : is_collineation fp_7782 fl_7782.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7782 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7782 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7782.

Lemma collineation_7783 : is_collineation fp_7783 fl_7783.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7783 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7783 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7783.

Lemma collineation_7784 : is_collineation fp_7784 fl_7784.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7784 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7784 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7784.

Lemma collineation_7785 : is_collineation fp_7785 fl_7785.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7785 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7785 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7785.

Lemma collineation_7786 : is_collineation fp_7786 fl_7786.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7786 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7786 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7786.

Lemma collineation_7787 : is_collineation fp_7787 fl_7787.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7787 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7787 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7787.

Lemma collineation_7788 : is_collineation fp_7788 fl_7788.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7788 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7788 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7788.

Lemma collineation_7789 : is_collineation fp_7789 fl_7789.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7789 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7789 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7789.

Lemma collineation_7790 : is_collineation fp_7790 fl_7790.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7790 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7790 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7790.

Lemma collineation_7791 : is_collineation fp_7791 fl_7791.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7791 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7791 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7791.

Lemma collineation_7792 : is_collineation fp_7792 fl_7792.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7792 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7792 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7792.

Lemma collineation_7793 : is_collineation fp_7793 fl_7793.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7793 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7793 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7793.

Lemma collineation_7794 : is_collineation fp_7794 fl_7794.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7794 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7794 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7794.

Lemma collineation_7795 : is_collineation fp_7795 fl_7795.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7795 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7795 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7795.

Lemma collineation_7796 : is_collineation fp_7796 fl_7796.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7796 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7796 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7796.

Lemma collineation_7797 : is_collineation fp_7797 fl_7797.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7797 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7797 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7797.

Lemma collineation_7798 : is_collineation fp_7798 fl_7798.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7798 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7798 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7798.

Lemma collineation_7799 : is_collineation fp_7799 fl_7799.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7799 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7799 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7799.

Lemma collineation_7800 : is_collineation fp_7800 fl_7800.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7800 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7800 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7800.

Lemma collineation_7801 : is_collineation fp_7801 fl_7801.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7801 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7801 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7801.

Lemma collineation_7802 : is_collineation fp_7802 fl_7802.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7802 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7802 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7802.

Lemma collineation_7803 : is_collineation fp_7803 fl_7803.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7803 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7803 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7803.

Lemma collineation_7804 : is_collineation fp_7804 fl_7804.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7804 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7804 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7804.

Lemma collineation_7805 : is_collineation fp_7805 fl_7805.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7805 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7805 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7805.

Lemma collineation_7806 : is_collineation fp_7806 fl_7806.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7806 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7806 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7806.

Lemma collineation_7807 : is_collineation fp_7807 fl_7807.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7807 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7807 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7807.

Lemma collineation_7808 : is_collineation fp_7808 fl_7808.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7808 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7808 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7808.

Lemma collineation_7809 : is_collineation fp_7809 fl_7809.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7809 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7809 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7809.

Lemma collineation_7810 : is_collineation fp_7810 fl_7810.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7810 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7810 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7810.

Lemma collineation_7811 : is_collineation fp_7811 fl_7811.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7811 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7811 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7811.

Lemma collineation_7812 : is_collineation fp_7812 fl_7812.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7812 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7812 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7812.

Lemma collineation_7813 : is_collineation fp_7813 fl_7813.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7813 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7813 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7813.

Lemma collineation_7814 : is_collineation fp_7814 fl_7814.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7814 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7814 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7814.

Lemma collineation_7815 : is_collineation fp_7815 fl_7815.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7815 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7815 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7815.

Lemma collineation_7816 : is_collineation fp_7816 fl_7816.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7816 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7816 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7816.

Lemma collineation_7817 : is_collineation fp_7817 fl_7817.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7817 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7817 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7817.

Lemma collineation_7818 : is_collineation fp_7818 fl_7818.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7818 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7818 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7818.

Lemma collineation_7819 : is_collineation fp_7819 fl_7819.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7819 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7819 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7819.

Lemma collineation_7820 : is_collineation fp_7820 fl_7820.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7820 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7820 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7820.

Lemma collineation_7821 : is_collineation fp_7821 fl_7821.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7821 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7821 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7821.

Lemma collineation_7822 : is_collineation fp_7822 fl_7822.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7822 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7822 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7822.

Lemma collineation_7823 : is_collineation fp_7823 fl_7823.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7823 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7823 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7823.

Lemma collineation_7824 : is_collineation fp_7824 fl_7824.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7824 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7824 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7824.

Lemma collineation_7825 : is_collineation fp_7825 fl_7825.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7825 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7825 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7825.

Lemma collineation_7826 : is_collineation fp_7826 fl_7826.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7826 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7826 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7826.

Lemma collineation_7827 : is_collineation fp_7827 fl_7827.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7827 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7827 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7827.

Lemma collineation_7828 : is_collineation fp_7828 fl_7828.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7828 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7828 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7828.

Lemma collineation_7829 : is_collineation fp_7829 fl_7829.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7829 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7829 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7829.

Lemma collineation_7830 : is_collineation fp_7830 fl_7830.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7830 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7830 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7830.

Lemma collineation_7831 : is_collineation fp_7831 fl_7831.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7831 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7831 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7831.

Lemma collineation_7832 : is_collineation fp_7832 fl_7832.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7832 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7832 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7832.

Lemma collineation_7833 : is_collineation fp_7833 fl_7833.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7833 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7833 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7833.

Lemma collineation_7834 : is_collineation fp_7834 fl_7834.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7834 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7834 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7834.

Lemma collineation_7835 : is_collineation fp_7835 fl_7835.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7835 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7835 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7835.

Lemma collineation_7836 : is_collineation fp_7836 fl_7836.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7836 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7836 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7836.

Lemma collineation_7837 : is_collineation fp_7837 fl_7837.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7837 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7837 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7837.

Lemma collineation_7838 : is_collineation fp_7838 fl_7838.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7838 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7838 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7838.

Lemma collineation_7839 : is_collineation fp_7839 fl_7839.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7839 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7839 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7839.

Lemma collineation_7840 : is_collineation fp_7840 fl_7840.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7840 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7840 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7840.

Lemma collineation_7841 : is_collineation fp_7841 fl_7841.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7841 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7841 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7841.

Lemma collineation_7842 : is_collineation fp_7842 fl_7842.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7842 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7842 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7842.

Lemma collineation_7843 : is_collineation fp_7843 fl_7843.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7843 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7843 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7843.

Lemma collineation_7844 : is_collineation fp_7844 fl_7844.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7844 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7844 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7844.

Lemma collineation_7845 : is_collineation fp_7845 fl_7845.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7845 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7845 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7845.

Lemma collineation_7846 : is_collineation fp_7846 fl_7846.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7846 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7846 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7846.

Lemma collineation_7847 : is_collineation fp_7847 fl_7847.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7847 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7847 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7847.

Lemma collineation_7848 : is_collineation fp_7848 fl_7848.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7848 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7848 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7848.

Lemma collineation_7849 : is_collineation fp_7849 fl_7849.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7849 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7849 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7849.

Lemma collineation_7850 : is_collineation fp_7850 fl_7850.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7850 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7850 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7850.

Lemma collineation_7851 : is_collineation fp_7851 fl_7851.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7851 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7851 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7851.

Lemma collineation_7852 : is_collineation fp_7852 fl_7852.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7852 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7852 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7852.

Lemma collineation_7853 : is_collineation fp_7853 fl_7853.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7853 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7853 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7853.

Lemma collineation_7854 : is_collineation fp_7854 fl_7854.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7854 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7854 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7854.

Lemma collineation_7855 : is_collineation fp_7855 fl_7855.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7855 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7855 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7855.

Lemma collineation_7856 : is_collineation fp_7856 fl_7856.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7856 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7856 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7856.

Lemma collineation_7857 : is_collineation fp_7857 fl_7857.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7857 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7857 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7857.

Lemma collineation_7858 : is_collineation fp_7858 fl_7858.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7858 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7858 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7858.

Lemma collineation_7859 : is_collineation fp_7859 fl_7859.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7859 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7859 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7859.

Lemma collineation_7860 : is_collineation fp_7860 fl_7860.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7860 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7860 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7860.

Lemma collineation_7861 : is_collineation fp_7861 fl_7861.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7861 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7861 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7861.

Lemma collineation_7862 : is_collineation fp_7862 fl_7862.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7862 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7862 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7862.

Lemma collineation_7863 : is_collineation fp_7863 fl_7863.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7863 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7863 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7863.

Lemma collineation_7864 : is_collineation fp_7864 fl_7864.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7864 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7864 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7864.

Lemma collineation_7865 : is_collineation fp_7865 fl_7865.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7865 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7865 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7865.

Lemma collineation_7866 : is_collineation fp_7866 fl_7866.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7866 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7866 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7866.

Lemma collineation_7867 : is_collineation fp_7867 fl_7867.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7867 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7867 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7867.

Lemma collineation_7868 : is_collineation fp_7868 fl_7868.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7868 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7868 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7868.

Lemma collineation_7869 : is_collineation fp_7869 fl_7869.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7869 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7869 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7869.

Lemma collineation_7870 : is_collineation fp_7870 fl_7870.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7870 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7870 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7870.

Lemma collineation_7871 : is_collineation fp_7871 fl_7871.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7871 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7871 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7871.

Lemma collineation_7872 : is_collineation fp_7872 fl_7872.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7872 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7872 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7872.

Lemma collineation_7873 : is_collineation fp_7873 fl_7873.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7873 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7873 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7873.

Lemma collineation_7874 : is_collineation fp_7874 fl_7874.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7874 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7874 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7874.

Lemma collineation_7875 : is_collineation fp_7875 fl_7875.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7875 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7875 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7875.

Lemma collineation_7876 : is_collineation fp_7876 fl_7876.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7876 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7876 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7876.

Lemma collineation_7877 : is_collineation fp_7877 fl_7877.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7877 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7877 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7877.

Lemma collineation_7878 : is_collineation fp_7878 fl_7878.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7878 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7878 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7878.

Lemma collineation_7879 : is_collineation fp_7879 fl_7879.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7879 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7879 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7879.

Lemma collineation_7880 : is_collineation fp_7880 fl_7880.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7880 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7880 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7880.

Lemma collineation_7881 : is_collineation fp_7881 fl_7881.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7881 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7881 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7881.

Lemma collineation_7882 : is_collineation fp_7882 fl_7882.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7882 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7882 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7882.

Lemma collineation_7883 : is_collineation fp_7883 fl_7883.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7883 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7883 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7883.

Lemma collineation_7884 : is_collineation fp_7884 fl_7884.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7884 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7884 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7884.

Lemma collineation_7885 : is_collineation fp_7885 fl_7885.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7885 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7885 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7885.

Lemma collineation_7886 : is_collineation fp_7886 fl_7886.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7886 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7886 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7886.

Lemma collineation_7887 : is_collineation fp_7887 fl_7887.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7887 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7887 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7887.

Lemma collineation_7888 : is_collineation fp_7888 fl_7888.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7888 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7888 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7888.

Lemma collineation_7889 : is_collineation fp_7889 fl_7889.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7889 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7889 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7889.

Lemma collineation_7890 : is_collineation fp_7890 fl_7890.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7890 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7890 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7890.

Lemma collineation_7891 : is_collineation fp_7891 fl_7891.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7891 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7891 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7891.

Lemma collineation_7892 : is_collineation fp_7892 fl_7892.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7892 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7892 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7892.

Lemma collineation_7893 : is_collineation fp_7893 fl_7893.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7893 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7893 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7893.

Lemma collineation_7894 : is_collineation fp_7894 fl_7894.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7894 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7894 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7894.

Lemma collineation_7895 : is_collineation fp_7895 fl_7895.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7895 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7895 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7895.

Lemma collineation_7896 : is_collineation fp_7896 fl_7896.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7896 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7896 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7896.

Lemma collineation_7897 : is_collineation fp_7897 fl_7897.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7897 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7897 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7897.

Lemma collineation_7898 : is_collineation fp_7898 fl_7898.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7898 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7898 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7898.

Lemma collineation_7899 : is_collineation fp_7899 fl_7899.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7899 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7899 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7899.

Lemma collineation_7900 : is_collineation fp_7900 fl_7900.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7900 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7900 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7900.

Lemma collineation_7901 : is_collineation fp_7901 fl_7901.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7901 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7901 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7901.

Lemma collineation_7902 : is_collineation fp_7902 fl_7902.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7902 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7902 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7902.

Lemma collineation_7903 : is_collineation fp_7903 fl_7903.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7903 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7903 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7903.

Lemma collineation_7904 : is_collineation fp_7904 fl_7904.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7904 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7904 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7904.

Lemma collineation_7905 : is_collineation fp_7905 fl_7905.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7905 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7905 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7905.

Lemma collineation_7906 : is_collineation fp_7906 fl_7906.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7906 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7906 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7906.

Lemma collineation_7907 : is_collineation fp_7907 fl_7907.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7907 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7907 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7907.

Lemma collineation_7908 : is_collineation fp_7908 fl_7908.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7908 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7908 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7908.

Lemma collineation_7909 : is_collineation fp_7909 fl_7909.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7909 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7909 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7909.

Lemma collineation_7910 : is_collineation fp_7910 fl_7910.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7910 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7910 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7910.

Lemma collineation_7911 : is_collineation fp_7911 fl_7911.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7911 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7911 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7911.

Lemma collineation_7912 : is_collineation fp_7912 fl_7912.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7912 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7912 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7912.

Lemma collineation_7913 : is_collineation fp_7913 fl_7913.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7913 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7913 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7913.

Lemma collineation_7914 : is_collineation fp_7914 fl_7914.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7914 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7914 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7914.

Lemma collineation_7915 : is_collineation fp_7915 fl_7915.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7915 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7915 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7915.

Lemma collineation_7916 : is_collineation fp_7916 fl_7916.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7916 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7916 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7916.

Lemma collineation_7917 : is_collineation fp_7917 fl_7917.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7917 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7917 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7917.

Lemma collineation_7918 : is_collineation fp_7918 fl_7918.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7918 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7918 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7918.

Lemma collineation_7919 : is_collineation fp_7919 fl_7919.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7919 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7919 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7919.

Lemma collineation_7920 : is_collineation fp_7920 fl_7920.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7920 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7920 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7920.

Lemma collineation_7921 : is_collineation fp_7921 fl_7921.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7921 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7921 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7921.

Lemma collineation_7922 : is_collineation fp_7922 fl_7922.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7922 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7922 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7922.

Lemma collineation_7923 : is_collineation fp_7923 fl_7923.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7923 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7923 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7923.

Lemma collineation_7924 : is_collineation fp_7924 fl_7924.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7924 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7924 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7924.

Lemma collineation_7925 : is_collineation fp_7925 fl_7925.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7925 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7925 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7925.

Lemma collineation_7926 : is_collineation fp_7926 fl_7926.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7926 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7926 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7926.

Lemma collineation_7927 : is_collineation fp_7927 fl_7927.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7927 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7927 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7927.

Lemma collineation_7928 : is_collineation fp_7928 fl_7928.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7928 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7928 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7928.

Lemma collineation_7929 : is_collineation fp_7929 fl_7929.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7929 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7929 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7929.

Lemma collineation_7930 : is_collineation fp_7930 fl_7930.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7930 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7930 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7930.

Lemma collineation_7931 : is_collineation fp_7931 fl_7931.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7931 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7931 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7931.

Lemma collineation_7932 : is_collineation fp_7932 fl_7932.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7932 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7932 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7932.

Lemma collineation_7933 : is_collineation fp_7933 fl_7933.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7933 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7933 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7933.

Lemma collineation_7934 : is_collineation fp_7934 fl_7934.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7934 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7934 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7934.

Lemma collineation_7935 : is_collineation fp_7935 fl_7935.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7935 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7935 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7935.

Lemma collineation_7936 : is_collineation fp_7936 fl_7936.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7936 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7936 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7936.

Lemma collineation_7937 : is_collineation fp_7937 fl_7937.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7937 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7937 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7937.

Lemma collineation_7938 : is_collineation fp_7938 fl_7938.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7938 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7938 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7938.

Lemma collineation_7939 : is_collineation fp_7939 fl_7939.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7939 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7939 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7939.

Lemma collineation_7940 : is_collineation fp_7940 fl_7940.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7940 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7940 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7940.

Lemma collineation_7941 : is_collineation fp_7941 fl_7941.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7941 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7941 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7941.

Lemma collineation_7942 : is_collineation fp_7942 fl_7942.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7942 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7942 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7942.

Lemma collineation_7943 : is_collineation fp_7943 fl_7943.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7943 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7943 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7943.

Lemma collineation_7944 : is_collineation fp_7944 fl_7944.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7944 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7944 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7944.

Lemma collineation_7945 : is_collineation fp_7945 fl_7945.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7945 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7945 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7945.

Lemma collineation_7946 : is_collineation fp_7946 fl_7946.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7946 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7946 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7946.

Lemma collineation_7947 : is_collineation fp_7947 fl_7947.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7947 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7947 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7947.

Lemma collineation_7948 : is_collineation fp_7948 fl_7948.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7948 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7948 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7948.

Lemma collineation_7949 : is_collineation fp_7949 fl_7949.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7949 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7949 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7949.

Lemma collineation_7950 : is_collineation fp_7950 fl_7950.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7950 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7950 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7950.

Lemma collineation_7951 : is_collineation fp_7951 fl_7951.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7951 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7951 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7951.

Lemma collineation_7952 : is_collineation fp_7952 fl_7952.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7952 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7952 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7952.

Lemma collineation_7953 : is_collineation fp_7953 fl_7953.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7953 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7953 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7953.

Lemma collineation_7954 : is_collineation fp_7954 fl_7954.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7954 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7954 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7954.

Lemma collineation_7955 : is_collineation fp_7955 fl_7955.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7955 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7955 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7955.

Lemma collineation_7956 : is_collineation fp_7956 fl_7956.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7956 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7956 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7956.

Lemma collineation_7957 : is_collineation fp_7957 fl_7957.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7957 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7957 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7957.

Lemma collineation_7958 : is_collineation fp_7958 fl_7958.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7958 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7958 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7958.

Lemma collineation_7959 : is_collineation fp_7959 fl_7959.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7959 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7959 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7959.

Lemma collineation_7960 : is_collineation fp_7960 fl_7960.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7960 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7960 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7960.

Lemma collineation_7961 : is_collineation fp_7961 fl_7961.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7961 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7961 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7961.

Lemma collineation_7962 : is_collineation fp_7962 fl_7962.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7962 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7962 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7962.

Lemma collineation_7963 : is_collineation fp_7963 fl_7963.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7963 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7963 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7963.

Lemma collineation_7964 : is_collineation fp_7964 fl_7964.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7964 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7964 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7964.

Lemma collineation_7965 : is_collineation fp_7965 fl_7965.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7965 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7965 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7965.

Lemma collineation_7966 : is_collineation fp_7966 fl_7966.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7966 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7966 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7966.

Lemma collineation_7967 : is_collineation fp_7967 fl_7967.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7967 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7967 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7967.

Lemma collineation_7968 : is_collineation fp_7968 fl_7968.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7968 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7968 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7968.

Lemma collineation_7969 : is_collineation fp_7969 fl_7969.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7969 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7969 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7969.

Lemma collineation_7970 : is_collineation fp_7970 fl_7970.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7970 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7970 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7970.

Lemma collineation_7971 : is_collineation fp_7971 fl_7971.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7971 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7971 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7971.

Lemma collineation_7972 : is_collineation fp_7972 fl_7972.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7972 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7972 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7972.

Lemma collineation_7973 : is_collineation fp_7973 fl_7973.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7973 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7973 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7973.

Lemma collineation_7974 : is_collineation fp_7974 fl_7974.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7974 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7974 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7974.

Lemma collineation_7975 : is_collineation fp_7975 fl_7975.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7975 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7975 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7975.

Lemma collineation_7976 : is_collineation fp_7976 fl_7976.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7976 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7976 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7976.

Lemma collineation_7977 : is_collineation fp_7977 fl_7977.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7977 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7977 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7977.

Lemma collineation_7978 : is_collineation fp_7978 fl_7978.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7978 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7978 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7978.

Lemma collineation_7979 : is_collineation fp_7979 fl_7979.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7979 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7979 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7979.

Lemma collineation_7980 : is_collineation fp_7980 fl_7980.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7980 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7980 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7980.

Lemma collineation_7981 : is_collineation fp_7981 fl_7981.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7981 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7981 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7981.

Lemma collineation_7982 : is_collineation fp_7982 fl_7982.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7982 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7982 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7982.

Lemma collineation_7983 : is_collineation fp_7983 fl_7983.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7983 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7983 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7983.

Lemma collineation_7984 : is_collineation fp_7984 fl_7984.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7984 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7984 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7984.

Lemma collineation_7985 : is_collineation fp_7985 fl_7985.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7985 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7985 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7985.

Lemma collineation_7986 : is_collineation fp_7986 fl_7986.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7986 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7986 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7986.

Lemma collineation_7987 : is_collineation fp_7987 fl_7987.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7987 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7987 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7987.

Lemma collineation_7988 : is_collineation fp_7988 fl_7988.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7988 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7988 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7988.

Lemma collineation_7989 : is_collineation fp_7989 fl_7989.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7989 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7989 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7989.

Lemma collineation_7990 : is_collineation fp_7990 fl_7990.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7990 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7990 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7990.

Lemma collineation_7991 : is_collineation fp_7991 fl_7991.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7991 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7991 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7991.

Lemma collineation_7992 : is_collineation fp_7992 fl_7992.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7992 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7992 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7992.

Lemma collineation_7993 : is_collineation fp_7993 fl_7993.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7993 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7993 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7993.

Lemma collineation_7994 : is_collineation fp_7994 fl_7994.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7994 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7994 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7994.

Lemma collineation_7995 : is_collineation fp_7995 fl_7995.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7995 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7995 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7995.

Lemma collineation_7996 : is_collineation fp_7996 fl_7996.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7996 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7996 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7996.

Lemma collineation_7997 : is_collineation fp_7997 fl_7997.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7997 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7997 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7997.

Lemma collineation_7998 : is_collineation fp_7998 fl_7998.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7998 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7998 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7998.

Lemma collineation_7999 : is_collineation fp_7999 fl_7999.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_7999 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_7999 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_7999.

Lemma collineation_8000 : is_collineation fp_8000 fl_8000.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8000 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8000 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8000.

Lemma collineation_8001 : is_collineation fp_8001 fl_8001.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8001 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8001 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8001.

Lemma collineation_8002 : is_collineation fp_8002 fl_8002.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8002 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8002 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8002.

Lemma collineation_8003 : is_collineation fp_8003 fl_8003.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8003 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8003 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8003.

Lemma collineation_8004 : is_collineation fp_8004 fl_8004.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8004 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8004 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8004.

Lemma collineation_8005 : is_collineation fp_8005 fl_8005.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8005 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8005 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8005.

Lemma collineation_8006 : is_collineation fp_8006 fl_8006.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8006 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8006 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8006.

Lemma collineation_8007 : is_collineation fp_8007 fl_8007.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8007 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8007 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8007.

Lemma collineation_8008 : is_collineation fp_8008 fl_8008.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8008 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8008 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8008.

Lemma collineation_8009 : is_collineation fp_8009 fl_8009.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8009 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8009 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8009.

Lemma collineation_8010 : is_collineation fp_8010 fl_8010.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8010 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8010 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8010.

Lemma collineation_8011 : is_collineation fp_8011 fl_8011.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8011 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8011 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8011.

Lemma collineation_8012 : is_collineation fp_8012 fl_8012.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8012 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8012 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8012.

Lemma collineation_8013 : is_collineation fp_8013 fl_8013.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8013 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8013 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8013.

Lemma collineation_8014 : is_collineation fp_8014 fl_8014.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8014 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8014 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8014.

Lemma collineation_8015 : is_collineation fp_8015 fl_8015.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8015 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8015 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8015.

Lemma collineation_8016 : is_collineation fp_8016 fl_8016.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8016 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8016 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8016.

Lemma collineation_8017 : is_collineation fp_8017 fl_8017.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8017 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8017 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8017.

Lemma collineation_8018 : is_collineation fp_8018 fl_8018.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8018 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8018 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8018.

Lemma collineation_8019 : is_collineation fp_8019 fl_8019.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8019 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8019 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8019.

Lemma collineation_8020 : is_collineation fp_8020 fl_8020.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8020 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8020 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8020.

Lemma collineation_8021 : is_collineation fp_8021 fl_8021.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8021 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8021 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8021.

Lemma collineation_8022 : is_collineation fp_8022 fl_8022.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8022 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8022 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8022.

Lemma collineation_8023 : is_collineation fp_8023 fl_8023.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8023 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8023 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8023.

Lemma collineation_8024 : is_collineation fp_8024 fl_8024.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8024 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8024 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8024.

Lemma collineation_8025 : is_collineation fp_8025 fl_8025.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8025 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8025 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8025.

Lemma collineation_8026 : is_collineation fp_8026 fl_8026.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8026 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8026 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8026.

Lemma collineation_8027 : is_collineation fp_8027 fl_8027.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8027 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8027 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8027.

Lemma collineation_8028 : is_collineation fp_8028 fl_8028.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8028 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8028 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8028.

Lemma collineation_8029 : is_collineation fp_8029 fl_8029.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8029 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8029 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8029.

Lemma collineation_8030 : is_collineation fp_8030 fl_8030.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8030 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8030 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8030.

Lemma collineation_8031 : is_collineation fp_8031 fl_8031.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8031 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8031 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8031.

Lemma collineation_8032 : is_collineation fp_8032 fl_8032.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8032 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8032 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8032.

Lemma collineation_8033 : is_collineation fp_8033 fl_8033.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8033 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8033 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8033.

Lemma collineation_8034 : is_collineation fp_8034 fl_8034.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8034 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8034 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8034.

Lemma collineation_8035 : is_collineation fp_8035 fl_8035.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8035 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8035 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8035.

Lemma collineation_8036 : is_collineation fp_8036 fl_8036.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8036 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8036 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8036.

Lemma collineation_8037 : is_collineation fp_8037 fl_8037.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8037 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8037 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8037.

Lemma collineation_8038 : is_collineation fp_8038 fl_8038.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8038 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8038 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8038.

Lemma collineation_8039 : is_collineation fp_8039 fl_8039.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8039 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8039 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8039.

Lemma collineation_8040 : is_collineation fp_8040 fl_8040.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8040 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8040 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8040.

Lemma collineation_8041 : is_collineation fp_8041 fl_8041.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8041 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8041 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8041.

Lemma collineation_8042 : is_collineation fp_8042 fl_8042.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8042 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8042 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8042.

Lemma collineation_8043 : is_collineation fp_8043 fl_8043.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8043 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8043 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8043.

Lemma collineation_8044 : is_collineation fp_8044 fl_8044.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8044 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8044 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8044.

Lemma collineation_8045 : is_collineation fp_8045 fl_8045.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8045 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8045 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8045.

Lemma collineation_8046 : is_collineation fp_8046 fl_8046.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8046 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8046 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8046.

Lemma collineation_8047 : is_collineation fp_8047 fl_8047.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8047 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8047 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8047.

Lemma collineation_8048 : is_collineation fp_8048 fl_8048.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8048 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8048 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8048.

Lemma collineation_8049 : is_collineation fp_8049 fl_8049.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8049 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8049 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8049.

Lemma collineation_8050 : is_collineation fp_8050 fl_8050.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8050 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8050 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8050.

Lemma collineation_8051 : is_collineation fp_8051 fl_8051.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8051 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8051 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8051.

Lemma collineation_8052 : is_collineation fp_8052 fl_8052.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8052 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8052 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8052.

Lemma collineation_8053 : is_collineation fp_8053 fl_8053.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8053 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8053 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8053.

Lemma collineation_8054 : is_collineation fp_8054 fl_8054.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8054 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8054 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8054.

Lemma collineation_8055 : is_collineation fp_8055 fl_8055.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8055 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8055 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8055.

Lemma collineation_8056 : is_collineation fp_8056 fl_8056.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8056 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8056 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8056.

Lemma collineation_8057 : is_collineation fp_8057 fl_8057.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8057 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8057 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8057.

Lemma collineation_8058 : is_collineation fp_8058 fl_8058.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8058 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8058 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8058.

Lemma collineation_8059 : is_collineation fp_8059 fl_8059.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8059 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8059 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8059.

Lemma collineation_8060 : is_collineation fp_8060 fl_8060.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8060 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8060 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8060.

Lemma collineation_8061 : is_collineation fp_8061 fl_8061.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8061 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8061 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8061.

Lemma collineation_8062 : is_collineation fp_8062 fl_8062.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8062 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8062 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8062.

Lemma collineation_8063 : is_collineation fp_8063 fl_8063.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_8063 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_8063 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_8063.

Lemma is_col_all_c70 : forall fp fl, In (fp,fl) (all_c70++all_c71++all_c72++all_c73++all_c74++all_c75++all_c76++all_c77++all_c78++all_c79++all_c80++all_c81++all_c82++all_c83) -> is_collineation fp fl.
Proof.
 intros fp fl HIn_S.
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6720 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6721 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6722 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6723 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6724 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6725 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6726 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6727 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6728 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6729 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6730 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6731 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6732 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6733 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6734 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6735 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6736 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6737 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6738 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6739 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6740 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6741 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6742 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6743 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6744 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6745 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6746 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6747 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6748 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6749 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6750 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6751 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6752 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6753 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6754 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6755 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6756 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6757 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6758 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6759 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6760 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6761 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6762 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6763 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6764 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6765 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6766 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6767 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6768 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6769 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6770 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6771 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6772 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6773 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6774 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6775 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6776 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6777 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6778 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6779 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6780 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6781 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6782 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6783 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6784 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6785 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6786 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6787 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6788 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6789 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6790 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6791 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6792 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6793 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6794 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6795 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6796 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6797 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6798 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6799 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6800 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6801 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6802 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6803 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6804 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6805 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6806 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6807 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6808 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6809 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6810 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6811 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6812 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6813 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6814 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6815 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6816 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6817 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6818 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6819 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6820 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6821 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6822 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6823 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6824 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6825 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6826 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6827 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6828 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6829 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6830 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6831 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6832 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6833 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6834 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6835 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6836 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6837 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6838 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6839 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6840 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6841 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6842 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6843 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6844 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6845 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6846 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6847 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6848 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6849 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6850 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6851 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6852 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6853 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6854 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6855 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6856 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6857 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6858 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6859 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6860 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6861 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6862 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6863 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6864 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6865 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6866 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6867 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6868 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6869 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6870 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6871 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6872 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6873 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6874 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6875 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6876 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6877 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6878 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6879 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6880 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6881 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6882 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6883 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6884 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6885 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6886 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6887 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6888 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6889 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6890 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6891 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6892 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6893 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6894 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6895 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6896 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6897 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6898 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6899 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6900 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6901 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6902 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6903 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6904 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6905 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6906 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6907 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6908 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6909 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6910 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6911 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6912 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6913 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6914 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6915 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6916 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6917 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6918 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6919 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6920 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6921 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6922 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6923 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6924 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6925 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6926 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6927 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6928 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6929 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6930 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6931 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6932 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6933 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6934 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6935 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6936 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6937 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6938 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6939 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6940 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6941 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6942 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6943 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6944 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6945 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6946 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6947 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6948 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6949 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6950 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6951 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6952 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6953 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6954 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6955 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6956 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6957 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6958 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6959 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6960 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6961 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6962 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6963 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6964 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6965 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6966 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6967 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6968 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6969 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6970 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6971 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6972 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6973 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6974 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6975 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6976 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6977 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6978 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6979 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6980 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6981 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6982 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6983 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6984 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6985 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6986 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6987 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6988 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6989 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6990 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6991 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6992 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6993 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6994 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6995 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6996 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6997 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6998 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6999 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7000 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7001 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7002 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7003 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7004 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7005 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7006 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7007 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7008 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7009 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7010 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7011 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7012 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7013 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7014 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7015 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7016 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7017 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7018 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7019 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7020 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7021 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7022 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7023 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7024 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7025 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7026 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7027 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7028 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7029 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7030 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7031 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7032 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7033 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7034 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7035 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7036 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7037 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7038 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7039 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7040 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7041 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7042 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7043 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7044 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7045 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7046 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7047 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7048 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7049 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7050 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7051 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7052 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7053 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7054 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7055 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7056 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7057 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7058 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7059 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7060 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7061 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7062 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7063 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7064 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7065 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7066 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7067 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7068 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7069 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7070 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7071 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7072 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7073 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7074 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7075 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7076 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7077 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7078 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7079 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7080 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7081 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7082 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7083 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7084 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7085 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7086 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7087 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7088 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7089 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7090 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7091 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7092 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7093 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7094 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7095 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7096 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7097 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7098 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7099 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7100 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7101 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7102 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7103 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7104 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7105 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7106 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7107 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7108 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7109 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7110 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7111 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7112 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7113 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7114 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7115 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7116 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7117 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7118 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7119 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7120 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7121 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7122 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7123 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7124 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7125 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7126 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7127 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7128 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7129 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7130 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7131 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7132 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7133 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7134 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7135 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7136 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7137 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7138 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7139 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7140 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7141 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7142 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7143 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7144 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7145 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7146 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7147 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7148 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7149 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7150 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7151 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7152 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7153 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7154 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7155 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7156 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7157 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7158 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7159 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7160 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7161 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7162 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7163 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7164 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7165 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7166 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7167 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7168 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7169 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7170 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7171 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7172 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7173 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7174 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7175 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7176 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7177 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7178 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7179 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7180 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7181 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7182 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7183 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7184 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7185 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7186 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7187 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7188 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7189 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7190 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7191 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7192 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7193 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7194 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7195 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7196 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7197 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7198 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7199 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7200 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7201 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7202 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7203 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7204 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7205 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7206 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7207 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7208 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7209 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7210 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7211 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7212 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7213 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7214 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7215 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7216 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7217 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7218 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7219 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7220 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7221 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7222 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7223 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7224 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7225 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7226 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7227 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7228 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7229 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7230 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7231 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7232 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7233 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7234 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7235 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7236 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7237 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7238 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7239 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7240 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7241 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7242 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7243 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7244 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7245 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7246 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7247 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7248 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7249 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7250 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7251 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7252 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7253 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7254 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7255 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7256 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7257 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7258 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7259 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7260 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7261 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7262 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7263 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7264 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7265 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7266 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7267 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7268 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7269 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7270 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7271 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7272 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7273 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7274 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7275 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7276 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7277 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7278 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7279 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7280 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7281 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7282 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7283 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7284 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7285 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7286 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7287 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7288 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7289 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7290 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7291 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7292 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7293 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7294 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7295 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7296 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7297 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7298 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7299 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7300 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7301 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7302 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7303 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7304 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7305 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7306 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7307 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7308 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7309 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7310 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7311 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7312 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7313 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7314 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7315 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7316 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7317 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7318 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7319 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7320 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7321 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7322 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7323 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7324 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7325 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7326 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7327 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7328 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7329 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7330 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7331 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7332 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7333 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7334 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7335 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7336 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7337 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7338 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7339 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7340 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7341 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7342 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7343 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7344 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7345 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7346 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7347 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7348 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7349 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7350 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7351 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7352 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7353 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7354 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7355 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7356 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7357 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7358 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7359 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7360 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7361 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7362 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7363 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7364 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7365 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7366 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7367 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7368 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7369 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7370 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7371 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7372 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7373 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7374 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7375 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7376 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7377 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7378 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7379 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7380 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7381 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7382 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7383 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7384 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7385 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7386 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7387 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7388 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7389 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7390 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7391 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7392 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7393 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7394 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7395 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7396 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7397 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7398 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7399 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7400 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7401 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7402 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7403 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7404 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7405 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7406 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7407 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7408 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7409 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7410 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7411 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7412 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7413 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7414 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7415 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7416 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7417 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7418 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7419 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7420 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7421 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7422 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7423 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7424 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7425 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7426 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7427 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7428 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7429 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7430 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7431 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7432 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7433 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7434 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7435 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7436 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7437 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7438 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7439 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7440 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7441 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7442 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7443 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7444 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7445 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7446 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7447 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7448 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7449 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7450 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7451 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7452 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7453 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7454 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7455 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7456 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7457 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7458 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7459 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7460 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7461 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7462 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7463 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7464 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7465 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7466 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7467 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7468 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7469 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7470 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7471 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7472 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7473 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7474 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7475 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7476 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7477 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7478 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7479 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7480 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7481 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7482 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7483 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7484 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7485 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7486 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7487 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7488 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7489 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7490 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7491 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7492 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7493 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7494 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7495 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7496 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7497 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7498 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7499 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7500 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7501 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7502 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7503 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7504 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7505 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7506 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7507 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7508 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7509 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7510 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7511 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7512 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7513 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7514 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7515 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7516 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7517 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7518 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7519 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7520 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7521 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7522 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7523 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7524 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7525 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7526 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7527 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7528 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7529 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7530 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7531 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7532 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7533 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7534 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7535 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7536 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7537 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7538 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7539 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7540 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7541 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7542 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7543 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7544 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7545 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7546 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7547 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7548 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7549 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7550 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7551 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7552 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7553 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7554 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7555 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7556 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7557 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7558 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7559 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7560 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7561 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7562 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7563 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7564 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7565 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7566 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7567 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7568 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7569 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7570 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7571 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7572 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7573 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7574 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7575 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7576 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7577 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7578 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7579 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7580 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7581 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7582 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7583 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7584 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7585 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7586 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7587 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7588 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7589 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7590 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7591 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7592 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7593 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7594 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7595 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7596 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7597 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7598 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7599 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7600 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7601 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7602 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7603 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7604 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7605 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7606 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7607 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7608 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7609 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7610 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7611 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7612 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7613 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7614 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7615 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7616 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7617 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7618 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7619 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7620 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7621 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7622 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7623 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7624 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7625 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7626 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7627 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7628 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7629 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7630 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7631 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7632 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7633 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7634 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7635 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7636 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7637 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7638 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7639 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7640 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7641 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7642 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7643 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7644 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7645 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7646 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7647 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7648 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7649 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7650 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7651 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7652 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7653 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7654 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7655 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7656 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7657 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7658 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7659 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7660 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7661 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7662 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7663 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7664 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7665 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7666 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7667 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7668 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7669 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7670 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7671 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7672 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7673 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7674 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7675 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7676 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7677 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7678 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7679 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7680 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7681 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7682 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7683 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7684 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7685 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7686 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7687 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7688 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7689 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7690 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7691 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7692 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7693 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7694 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7695 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7696 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7697 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7698 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7699 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7700 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7701 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7702 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7703 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7704 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7705 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7706 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7707 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7708 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7709 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7710 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7711 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7712 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7713 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7714 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7715 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7716 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7717 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7718 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7719 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7720 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7721 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7722 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7723 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7724 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7725 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7726 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7727 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7728 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7729 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7730 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7731 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7732 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7733 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7734 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7735 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7736 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7737 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7738 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7739 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7740 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7741 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7742 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7743 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7744 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7745 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7746 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7747 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7748 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7749 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7750 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7751 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7752 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7753 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7754 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7755 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7756 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7757 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7758 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7759 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7760 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7761 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7762 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7763 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7764 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7765 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7766 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7767 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7768 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7769 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7770 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7771 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7772 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7773 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7774 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7775 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7776 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7777 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7778 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7779 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7780 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7781 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7782 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7783 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7784 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7785 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7786 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7787 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7788 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7789 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7790 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7791 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7792 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7793 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7794 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7795 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7796 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7797 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7798 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7799 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7800 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7801 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7802 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7803 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7804 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7805 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7806 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7807 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7808 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7809 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7810 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7811 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7812 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7813 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7814 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7815 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7816 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7817 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7818 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7819 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7820 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7821 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7822 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7823 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7824 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7825 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7826 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7827 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7828 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7829 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7830 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7831 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7832 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7833 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7834 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7835 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7836 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7837 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7838 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7839 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7840 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7841 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7842 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7843 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7844 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7845 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7846 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7847 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7848 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7849 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7850 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7851 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7852 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7853 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7854 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7855 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7856 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7857 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7858 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7859 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7860 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7861 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7862 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7863 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7864 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7865 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7866 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7867 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7868 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7869 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7870 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7871 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7872 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7873 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7874 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7875 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7876 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7877 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7878 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7879 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7880 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7881 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7882 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7883 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7884 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7885 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7886 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7887 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7888 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7889 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7890 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7891 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7892 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7893 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7894 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7895 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7896 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7897 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7898 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7899 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7900 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7901 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7902 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7903 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7904 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7905 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7906 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7907 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7908 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7909 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7910 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7911 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7912 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7913 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7914 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7915 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7916 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7917 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7918 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7919 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7920 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7921 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7922 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7923 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7924 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7925 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7926 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7927 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7928 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7929 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7930 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7931 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7932 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7933 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7934 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7935 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7936 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7937 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7938 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7939 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7940 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7941 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7942 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7943 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7944 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7945 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7946 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7947 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7948 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7949 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7950 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7951 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7952 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7953 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7954 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7955 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7956 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7957 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7958 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7959 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7960 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7961 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7962 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7963 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7964 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7965 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7966 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7967 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7968 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7969 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7970 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7971 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7972 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7973 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7974 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7975 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7976 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7977 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7978 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7979 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7980 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7981 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7982 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7983 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7984 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7985 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7986 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7987 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7988 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7989 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7990 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7991 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7992 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7993 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7994 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7995 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7996 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7997 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7998 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_7999 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8000 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8001 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8002 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8003 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8004 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8005 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8006 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8007 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8008 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8009 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8010 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8011 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8012 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8013 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8014 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8015 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8016 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8017 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8018 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8019 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8020 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8021 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8022 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8023 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8024 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8025 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8026 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8027 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8028 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8029 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8030 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8031 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8032 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8033 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8034 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8035 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8036 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8037 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8038 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8039 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8040 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8041 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8042 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8043 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8044 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8045 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8046 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8047 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8048 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8049 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8050 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8051 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8052 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8053 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8054 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8055 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8056 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8057 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8058 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8059 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8060 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8061 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8062 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_8063 | idtac].
 destruct (in_nil HIn_S).
Qed.

